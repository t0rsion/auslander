use std::sync::Arc;

use auslander::algebra::{Algebra, linear_an, truncated_poly};
use auslander::approx::{ApproxError, left_approximation};
use auslander::arquiver::IndecomposableCatalog;
use auslander::basic::AddClosureWitness;
use auslander::module::Module;
use auslander::mutation::{ExchangeShape, MutationError, SlotOutcome, mutate_at};
use auslander::supporttau::{
    AlmostCompleteClassification, AlmostCompletePair, PairRejection,
    SupportTauTiltingClassification, SupportTauTiltingPair, enumerate_over_catalog,
};
use auslander::taurigid::{TauRigidityOutcome, is_tau_rigid};

use super::checks::{decomposition, sum, support};
use super::common::f5;
use super::fixtures::walk;

/// Every witness the release adds verifies on a fixture where it holds.
///
/// One test rather than seven, because the objects all come from one A_2 pair
/// and one A_2 walk, and splitting them would rebuild the same data.
#[test]
fn every_witness_type_verifies_on_a2() {
    let algebra = linear_an(2, f5());
    let p0 = Module::projective(&algebra, 0);
    let p1 = Module::projective(&algebra, 1);
    let s0 = Module::simple(&algebra, 0);

    // SupportTauTiltingPair: (P_0 + S_0, 0), the second tilting module.
    let pair = SupportTauTiltingPair::new(decomposition(&sum(&[&p0, &s0])), support(&algebra, &[]))
        .expect("the parts share one algebra")
        .expect("P_0 + S_0 is a tau-tilting module");
    assert!(pair.verify());
    assert!(pair.is_tau_tilting());
    assert_eq!(pair.summand_count(), 2);
    assert!(pair.projective().is_empty());
    assert!(pair.rigid().verify());

    // AlmostCompletePair: drop S_0, so |M| + |P| = 1 = n - 1.
    let almost = AlmostCompletePair::new(decomposition(&p0), support(&algebra, &[]))
        .expect("the parts share one algebra")
        .expect("P_0 alone is tau-rigid");
    assert!(almost.verify());
    assert_eq!(almost.summand_count(), 1);
    assert_eq!(almost.omitted_vertex(), None);
    assert!(almost.rigid().verify());

    // CatalogEnumeration over the same algebra.
    let catalog = IndecomposableCatalog::dynkin(&algebra).expect("A_2 is Dynkin");
    let listed = enumerate_over_catalog(&catalog).expect("A_2 enumerates");
    assert!(listed.verify());
    assert_eq!(listed.len(), 5);

    // MinimalLeftApproximation: S_1 = P_1 into add(P_0). Hom(S_1, P_0) is one
    // dimensional, the socle inclusion. End(P_0) = e_0 A e_0 = k and the map
    // End(P_0) -> Hom(S_1, P_0) is injective, so K_f is zero and lies inside
    // rad End(P_0) for free.
    let left = left_approximation(&p1, std::slice::from_ref(&p0)).expect("P_0 is indecomposable");
    assert!(left.verify());
    assert_eq!(left.multiplicity(0), 1);
    assert_eq!(left.map().source().dim_vector(), [0, 1]);
    assert_eq!(left.map().target().dim_vector(), [1, 1]);
    assert_eq!(left.kernel_basis().rows(), 0);

    // MutationWitness and FacWitness, from the two slots of (P_0 + S_0, 0).
    let mut shapes = Vec::new();
    let mut fac_seen = 0;
    for slot in 0..pair.module().len() {
        match mutate_at(&pair, slot).expect("the slot is a module summand") {
            SlotOutcome::LeftMutation(mutation) => {
                assert!(mutation.verify());
                assert!(mutation.witness().verify());
                assert_eq!(mutation.witness().slot(), slot);
                assert!(mutation.witness().source_extension().verify());
                assert!(mutation.witness().target_extension().verify());
                assert!(mutation.witness().approximation().verify());
                assert!(mutation.witness().almost_complete().verify());
                assert!(mutation.target().verify());
                shapes.push(mutation.shape().clone());
            }
            SlotOutcome::NoLeftMutation(fac) => {
                fac_seen += 1;
                assert!(fac.verify());
            }
        }
    }
    // Slot P_0 moves vertex 1 into the projective support; slot S_0 is the
    // right-mutation slot of the pentagon.
    assert_eq!(shapes, vec![ExchangeShape::MovesToProjective { vertex: 1 }]);
    assert_eq!(fac_seen, 1);

    // ClosureWitness, over the same algebra.
    let graph = walk(&algebra);
    assert!(graph.witness().verify());
    assert_eq!(graph.witness().vertices().len(), 5);
    assert_eq!(graph.witness().mutations().len(), 5);

    // AddClosureWitness on its own: P_0 lies in add(P_0 + S_0), P_1 does not.
    let target = decomposition(&sum(&[&p0, &s0]));
    let inside = AddClosureWitness::new(&decomposition(&p0), &target)
        .expect("one algebra")
        .expect("P_0 is a summand of T");
    assert!(inside.verify());
    assert!(
        AddClosureWitness::new(&decomposition(&p1), &target)
            .expect("one algebra")
            .is_none(),
        "P_1 is isomorphic to no summand of P_0 + S_0"
    );
}

/// The checking constructors reject input that fails a condition, and the
/// negative witnesses they hand back verify.
///
/// This is the public half of the mutation corpus of design section 15.
/// Witness fields are private, so the corpus that corrupts a stored witness
/// runs in-module; here the tampering is in the input.
fn assert_hom_from_projective_rejection(algebra: &Arc<Algebra>, projective: &Module) {
    match SupportTauTiltingPair::classify(decomposition(projective), support(algebra, &[0]))
        .expect("the parts share one algebra")
    {
        SupportTauTiltingClassification::Rejected(PairRejection::HomFromProjectiveNonzero {
            vertex,
            dim,
        }) => assert_eq!((vertex, dim), (0, 1)),
        other => panic!("expected condition 2, got {:?}", other.rejection()),
    }
}

fn assert_tau_rigidity_rejection() {
    let algebra = truncated_poly(3, f5()).expect("x^3 is admissible");
    let simple = Module::simple(&algebra, 0);
    match SupportTauTiltingPair::classify(decomposition(&simple), support(&algebra, &[]))
        .expect("the parts share one algebra")
    {
        SupportTauTiltingClassification::Rejected(PairRejection::NotTauRigid(witness)) => {
            assert!(witness.verify());
            assert_eq!(witness.translate().dim_vector(), [1]);
            assert_eq!(witness.morphism().source().dim_vector(), [1]);
        }
        other => panic!("expected condition 3, got {:?}", other.rejection()),
    }
    match is_tau_rigid(&simple).expect("the simple is a module over its own algebra") {
        TauRigidityOutcome::NotTauRigid(witness) => assert!(witness.verify()),
        TauRigidityOutcome::TauRigid(_) => panic!("k[x]/(x^3) has no tau-rigid simple"),
    }
}

fn assert_pair_count_rejections(algebra: &Arc<Algebra>, p0: &Module, s0: &Module) {
    match SupportTauTiltingPair::classify(decomposition(p0), support(algebra, &[]))
        .expect("the parts share one algebra")
    {
        SupportTauTiltingClassification::Rejected(PairRejection::SummandCount {
            module,
            projective,
            expected,
        }) => assert_eq!((module, projective, expected), (1, 0, 2)),
        other => panic!("expected condition 4, got {:?}", other.rejection()),
    }
    let candidate = decomposition(&sum(&[p0, s0]));
    match AlmostCompletePair::classify(candidate, support(algebra, &[]))
        .expect("the parts share one algebra")
    {
        AlmostCompleteClassification::Rejected(PairRejection::SummandCount {
            module,
            projective,
            expected,
        }) => assert_eq!((module, projective, expected), (2, 0, 1)),
        other => panic!("expected condition 4, got {:?}", other.rejection()),
    }
}

fn assert_approximation_rejections(p0: &Module, p1: &Module, s0: &Module) {
    match left_approximation(s0, &[sum(&[p0, p1])]).unwrap_err() {
        ApproxError::SummandNotIndecomposable { index, .. } => assert_eq!(index, 0),
        other => panic!("expected a rejected add-generator, got {other}"),
    }
    match left_approximation(s0, &[p0.clone(), p0.clone()]).unwrap_err() {
        ApproxError::RepeatedSummand { first, second } => assert_eq!((first, second), (0, 1)),
        other => panic!("expected a repeated add-generator, got {other}"),
    }
}

fn assert_mutation_slot_rejection(algebra: &Arc<Algebra>, p0: &Module, s0: &Module) {
    let pair = SupportTauTiltingPair::new(decomposition(&sum(&[p0, s0])), support(algebra, &[]))
        .expect("one algebra")
        .expect("P_0 + S_0 is a tau-tilting module");
    match mutate_at(&pair, 2).unwrap_err() {
        MutationError::SlotOutOfRange { slot, summands } => assert_eq!((slot, summands), (2, 2)),
        other => panic!("expected a slot out of range, got {other}"),
    }
}

#[test]
fn the_checking_constructors_reject_input_that_fails_a_condition() {
    let algebra = linear_an(2, f5());
    let p0 = Module::projective(&algebra, 0);
    let p1 = Module::projective(&algebra, 1);
    let s0 = Module::simple(&algebra, 0);
    assert_hom_from_projective_rejection(&algebra, &p0);
    assert_tau_rigidity_rejection();
    assert_pair_count_rejections(&algebra, &p0, &s0);
    assert_approximation_rejections(&p0, &p1, &s0);
    assert_mutation_slot_rejection(&algebra, &p0, &s0);
}

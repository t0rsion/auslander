use auslander::algebra::{an_with_relations, linear_an};
use auslander::control::ComputationControl;
use auslander::derived::DerivedEquivalenceCertificate;
use auslander::derived_artifact::{
    ArtifactVerificationOutcome, ArtifactVerifyLimits, DerivedArtifact, verify_derived_artifact,
};
use auslander::derived_hom::{DerivedHomLimits, DerivedHomOutcome, derived_hom};
use auslander::derived_transport::{DerivedForwardOutcome, DerivedTransport};
use auslander::equivalence_discovery::{DiscoveryLimits, discover_equivalences};
use auslander::equivalence_edge::{DerivedEquivalenceEdge, DerivedEquivalenceEdgeOutcome};
use auslander::field::PrimeField;
use auslander::homotopy::BoundedComplex;
use auslander::module::{Module, direct_sum};
use auslander::perfect::{ReplacementLimits, ReplacementOutcome, replace_perfect};
use auslander::target::{TargetLimits, TargetPresentationOutcome, present_target};
use auslander::tilting::{ClassicalTiltingResult, TiltingLimits, classify};
use auslander::tilting_complex::{
    TiltingComplexLimits, TiltingComplexResult, TiltingMutationOutcome, left_tilting_mutation,
    regular_tilting_complex,
};

fn one_term(module: &Module) -> BoundedComplex {
    BoundedComplex::new(0, vec![module.clone()], Vec::new()).unwrap()
}

fn main() {
    let field = PrimeField::new(5).unwrap();
    let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
    let source = one_term(&Module::simple(&algebra, 0));
    let target = one_term(&Module::simple(&algebra, 2));

    let ReplacementOutcome::Replaced(replacement) =
        replace_perfect(&source, ReplacementLimits::default(), None).unwrap()
    else {
        panic!("the pd2 source has a bounded projective replacement")
    };
    let DerivedHomOutcome::Complete(hom) =
        derived_hom(&source, &target, DerivedHomLimits::default(), None).unwrap()
    else {
        panic!("the pd2 source has complete finite derived Hom")
    };
    assert!(replacement.verify());
    assert_eq!(hom.dimension(2), 1);

    let injectives: Vec<Module> = (0..3)
        .map(|vertex| Module::injective(&algebra, vertex))
        .collect();
    let dual = direct_sum(&injectives.iter().collect::<Vec<_>>()).0;
    let ClassicalTiltingResult::Tilting(tilting) = classify(
        &dual,
        TiltingLimits {
            max_projective_dimension: 4,
            max_generation_steps: 8,
        },
    )
    .unwrap() else {
        panic!("the dual A3/(ab) module is classical tilting")
    };
    let TargetPresentationOutcome::Presented(classical_target) =
        present_target(&tilting, &TargetLimits::default()).unwrap()
    else {
        panic!("the classical tilting target is split")
    };
    let certificate = DerivedEquivalenceCertificate::new(tilting, classical_target).unwrap();
    let transport = DerivedTransport::new(certificate).unwrap();
    let DerivedForwardOutcome::Transported(forward) = transport
        .forward(&source, ReplacementLimits::default(), None)
        .unwrap()
    else {
        panic!("automatic forward transport completes")
    };
    assert!(forward.verify());

    let mutation_algebra = linear_an(2, field);
    let graph = discover_equivalences(
        &mutation_algebra,
        DiscoveryLimits {
            max_vertices: 3,
            ..DiscoveryLimits::default()
        },
        &ComputationControl::new(),
    )
    .unwrap();
    assert!(graph.verify());

    let TiltingComplexResult::Tilting(regular) =
        regular_tilting_complex(&mutation_algebra, TiltingComplexLimits::default()).unwrap()
    else {
        panic!("the regular generator certifies")
    };
    let mutation = (0..regular.candidate().len())
        .find_map(|summand| {
            match left_tilting_mutation(&regular, summand, TiltingComplexLimits::default()).unwrap()
            {
                TiltingMutationOutcome::Tilting(value)
                    if value
                        .candidate()
                        .summands()
                        .iter()
                        .any(|part| part.complex().len() > 1) =>
                {
                    Some(*value)
                }
                _ => None,
            }
        })
        .expect("A2 has a multi-degree left mutation");
    let edge = match DerivedEquivalenceEdge::recover(mutation, &TargetLimits::default()).unwrap() {
        DerivedEquivalenceEdgeOutcome::Certified(value) => value,
        DerivedEquivalenceEdgeOutcome::Cut(_) => panic!("the fixed target recovery completes"),
    };
    let artifact = DerivedArtifact::from_edge(&edge).unwrap();
    let text = artifact.to_canonical_json();
    let ArtifactVerificationOutcome::Verified(verified) = verify_derived_artifact(
        &text,
        ArtifactVerifyLimits::default(),
        &ComputationControl::new(),
    )
    .unwrap() else {
        panic!("the fixed artifact verifies without a cut")
    };

    println!(
        "replacement={}..{}; Ext^2={}; transported={}..{}; graph vertices={}; artifact={}",
        replacement.projective().complex().lower(),
        replacement.projective().complex().upper(),
        hom.dimension(2),
        forward.output().complex().lower(),
        forward.output().complex().upper(),
        graph.vertices().len(),
        verified.artifact().fingerprint(),
    );
}

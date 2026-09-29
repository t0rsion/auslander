//! Classifications of edge-case families: empty, single, duplicated,
//! disconnected, over other fields, and cut at each stage.

use std::sync::Arc;

use super::stages::{Context, Partition, SeparationTable, assemble};
use super::tests::{classify, corpus, limits, outline, silting_limits, silting_pair};
use super::*;
use crate::algebra::{linear_an, monomial_algebra, path_algebra};
use crate::derived_invariant::{InvariantReading, InvariantValue};
use crate::field::PrimeField;
use crate::gentle::{GentleError, connected_gentle_algebras};
use crate::monomial::MonomialIdeal;
use crate::quiver::{ArrowId, Quiver};

fn field(p: u64) -> PrimeField {
    PrimeField::new(p).unwrap()
}

/// The monomial algebra over `GF(p)` with quadratic zero relations.
fn bound(p: u64, vertices: u32, arrows: &[(u32, u32)], relations: &[(u32, u32)]) -> Arc<Algebra> {
    let quiver = Quiver::new(vertices, arrows).unwrap();
    let words = relations.iter().map(|&(a, b)| vec![ArrowId(a), ArrowId(b)]);
    monomial_algebra(
        &MonomialIdeal::new(quiver, words.collect()).unwrap(),
        field(p),
    )
    .unwrap()
}

fn class_members(result: &DerivedClassification) -> Vec<Vec<usize>> {
    result
        .classes()
        .iter()
        .map(|c| c.members().to_vec())
        .collect()
}

/// An empty family has no class, and one member has nothing to walk.
/// Copies of one member merge as duplicates and are never walked.
#[test]
fn empty_single_and_duplicated_families_need_no_walk() {
    let a2 = linear_an(2, field(2));
    for (family, classes) in [
        (Vec::new(), Vec::<Vec<usize>>::new()),
        (vec![a2.clone()], vec![vec![0]]),
        (vec![a2.clone(), a2.clone(), a2], vec![vec![0, 1, 2]]),
    ] {
        let result = classify(&family);
        assert_eq!(class_members(&result), classes);
        assert!(result.walks().is_empty() && result.separations().is_empty());
        assert_eq!(result.status(), ClassificationStatus::Complete);
        assert!(result.verify());
    }
    let result = classify(&vec![linear_an(2, field(2)); 3]);
    let merges: Vec<_> = result.classes()[0]
        .merges()
        .iter()
        .map(|m| (m.source(), m.member(), m.is_duplicate()))
        .collect();
    assert_eq!(merges, [(0, 1, true), (0, 2, true)]);
}

/// `A_3/(ab)` and its reversed numbering have one gentle key, so the second
/// is a duplicate. Its merge maps vertex `v` to `2 - v`. The walk from
/// member 0 reaches `A_3`.
#[test]
fn a_relabeled_gentle_duplicate_merges_through_its_labeling() {
    let family = [
        bound(2, 3, &[(0, 1), (1, 2)], &[(0, 1)]),
        bound(2, 3, &[(1, 0), (2, 1)], &[(1, 0)]),
        linear_an(3, field(2)),
    ];
    let result = classify(&family);
    assert_eq!(class_members(&result), [vec![0, 1, 2]]);
    let duplicate = &result.classes()[0].merges()[0];
    assert!(duplicate.is_duplicate() && duplicate.member() == 1);
    assert_eq!(duplicate.isomorphism().vertex_map(), [2, 1, 0]);
    let walked: Vec<_> = result.walks().iter().map(MutationWalk::member).collect();
    assert_eq!(walked, [0]);
    assert!(result.verify());
    let text = result.to_artifact().unwrap().to_canonical_json();
    let control = ComputationControl::new();
    let replayed = verify_derived_atlas_artifact(&text, Default::default(), &control).unwrap();
    assert!(matches!(replayed, DerivedAtlasVerification::Verified(_)));
}

/// `A_2 ⊔ A_1` and `A_1 ⊔ A_2` are not connected, so both gentle kinds read
/// `NotApplicable` and never separate. The factors of `C + C^T` separate
/// them from `A_3`.
#[test]
fn disconnected_members_never_separate_by_gentle_kinds() {
    let disjoint = |arrow| path_algebra(Quiver::new(3, &[arrow]).unwrap(), field(2)).unwrap();
    let family = [disjoint((0, 1)), disjoint((1, 2)), linear_an(3, field(2))];
    let result = classify(&family);
    // The search starts at vertex 0: it reaches `A_2` in member 0 and only
    // the isolated vertex in member 1.
    for (member, reachable) in [(0, 2), (1, 1)] {
        for kind in [
            DerivedInvariantKind::AagFunction,
            DerivedInvariantKind::WindingClass,
        ] {
            let reading = result.invariants()[member].reading(kind);
            let disconnected = GentleError::Disconnected {
                vertices: 3,
                reachable,
            };
            assert_eq!(reading, &InvariantReading::NotApplicable(disconnected));
        }
    }
    assert_eq!(result.groups(), [vec![0, 1], vec![2]]);
    let kinds: Vec<_> = result
        .separations()
        .iter()
        .map(|s| s.witness().kind())
        .collect();
    assert_eq!(kinds, [DerivedInvariantKind::SymmetricFactors; 2]);
    // The two members are isomorphic, but neither is gentle and no
    // recovered target has the certificate of member 1, so they stay open.
    assert_eq!(class_members(&result), [vec![0], vec![1], vec![2]]);
    let [open] = result.unresolved() else {
        panic!("one unresolved pair expected");
    };
    assert_eq!((open.classes(), open.walks()), ((0, 1), &[0, 1][..]));
    assert!(result.verify());
}

/// Derived equivalence of gentle algebras does not depend on the field, so
/// the classes over `F_3` and `F_5` are those over `F_2`.
#[test]
fn other_fields_give_the_classes_of_f2() {
    for (p, n) in [(3, 2), (3, 3), (5, 2)] {
        let family = connected_gentle_algebras(n, field(p)).unwrap();
        let result = classify(&family);
        let f2 = &corpus()[n as usize - 1];
        assert_eq!(
            class_members(&result),
            class_members(f2),
            "p = {p}, n = {n}"
        );
        assert_eq!(result.status(), ClassificationStatus::Complete);
        assert!(result.verify());
    }
}

/// Two silting walks of one family store the same decisions in the same
/// order.
#[test]
fn silting_walks_repeat_exactly() {
    let control = ComputationControl::new();
    let run = || classify_derived(&silting_pair(), &silting_limits(), &control).unwrap();
    assert_eq!(outline(&run()), outline(&run()));
}

/// A target limit of 0 cuts every recovery, so no walk merges and the
/// derived equivalent pair `A_3`, `A_3/(ab)` stays open with typed cuts.
#[test]
fn target_cuts_leave_the_pair_open() {
    let family = [
        linear_an(3, field(2)),
        bound(2, 3, &[(0, 1), (1, 2)], &[(0, 1)]),
    ];
    let mut cut = limits();
    cut.target.max_endo_dimension = 0;
    let result = classify_derived(&family, &cut, &ComputationControl::new()).unwrap();
    assert_eq!(result.status(), ClassificationStatus::Incomplete);
    for walk in result.walks() {
        assert!(walk.examined() > 0);
        assert_eq!(walk.target_cuts(), walk.examined());
        assert_eq!((walk.unmatched(), walk.merges()), (0, 0));
    }
    let open = classify(&family);
    assert_eq!(open.status(), ClassificationStatus::Complete);
    let unmatched: usize = open.walks().iter().map(MutationWalk::unmatched).sum();
    assert!(unmatched > 0, "targets outside the family match no member");
}

/// Cancellation after the first walk keeps its merges. Each later walk
/// stops before its first mutation, and every pair it could have merged
/// stays open.
#[test]
fn cancellation_between_walks_keeps_earlier_merges() {
    let family = connected_gentle_algebras(3, field(2)).unwrap();
    let limits = limits();
    let fresh = ComputationControl::new();
    let invariants: Vec<_> = family
        .iter()
        .map(|a| DerivedInvariants::compute(a, limits.invariants, &fresh).unwrap())
        .collect();
    let index = FamilyIndex::new(&family).unwrap();
    let table = SeparationTable::new(&invariants);
    let context = Context {
        index: &index,
        table: &table,
        limits: &limits,
    };
    let mut partition = Partition::new(family.len());
    let cancelled = ComputationControl::new();
    cancelled.cancel();
    let mut walks = Vec::new();
    for member in 0..family.len() {
        if partition.has_open_partner(&table, member) {
            let control = if walks.is_empty() { &fresh } else { &cancelled };
            walks.push(partition.walk(&context, member, control).unwrap());
        }
    }
    let first = walks[0].merges();
    assert!(first > 0);
    for walk in &walks[1..] {
        let stop = DiscoveryStop::Cancelled {
            completed_mutations: 0,
        };
        assert_eq!((walk.stop(), walk.examined()), (&stop, 0));
    }
    let (classes, _, unresolved) = assemble(partition, &table, &invariants, &walks);
    let merges: usize = classes.iter().map(|c| c.merges().len()).sum();
    assert_eq!(merges, first);
    assert!(!unresolved.is_empty());
    assert!(unresolved.iter().all(|pair| !pair.walks().is_empty()));
}

/// The algebra of the quiver with no vertex is `0`. Its Cartan matrix is
/// empty, so `det C = 1` and the pencil is `1`. The vertex count separates
/// it from `A_1`, and its atlas replays.
#[test]
fn the_zero_algebra_is_separated_by_its_vertex_count() {
    use InvariantValue as Value;
    let zero = path_algebra(Quiver::new(0, &[]).unwrap(), field(2)).unwrap();
    let result = classify(&[zero, linear_an(1, field(2))]);
    let readings = DerivedInvariantKind::ALL.map(|k| result.invariants()[0].reading(k).clone());
    let finished = |value| InvariantReading::Finished(value);
    let empty = InvariantReading::NotApplicable(GentleError::EmptyQuiver);
    let expected = [
        finished(Value::Count(0)),
        finished(Value::Integer(1)),
        finished(Value::Factors(Vec::new())),
        finished(Value::Factors(Vec::new())),
        finished(Value::Factors(Vec::new())),
        finished(Value::Polynomial(vec![1])),
        empty.clone(),
        empty,
        finished(Value::Dimensions(vec![0; 3])),
        finished(Value::Count(0)),
    ];
    assert_eq!(readings, expected);
    let [separation] = result.separations() else {
        panic!("one separation expected");
    };
    assert_eq!(
        separation.witness().kind(),
        DerivedInvariantKind::VertexCount
    );
    let text = result.to_artifact().unwrap().to_canonical_json();
    let control = ComputationControl::new();
    let replayed = verify_derived_atlas_artifact(&text, Default::default(), &control).unwrap();
    assert!(matches!(replayed, DerivedAtlasVerification::Verified(_)));
}

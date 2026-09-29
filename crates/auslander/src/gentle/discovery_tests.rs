use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use super::invariant_tests::{aps_first, aps_second};
use super::presentation_tests::bound;
use super::*;
use crate::algebra::Algebra;
use crate::control::ComputationControl;
use crate::equivalence_discovery::{DiscoveryLimits, discover_equivalences};
use crate::equivalence_edge::{DerivedEquivalenceEdge, DerivedEquivalenceEdgeOutcome};
use crate::field::PrimeField;
use crate::target::TargetLimits;

fn small_limits() -> DiscoveryLimits {
    DiscoveryLimits {
        max_vertices: 8,
        max_directed_mutations: 32,
        max_total_terms: 256,
        max_matrix_entries: 16_384,
        ..DiscoveryLimits::default()
    }
}

/// The number of recovered targets and the keys of those that recognition
/// accepts. Each accepted target must share the source's complete invariant,
/// which contains the AAG function.
fn gentle_targets_agree(algebra: &Arc<Algebra>) -> (usize, BTreeSet<GentleKey>) {
    let expected = GentlePresentation::new(algebra)
        .unwrap()
        .complete_invariant();
    let graph = discover_equivalences(algebra, small_limits(), &ComputationControl::new()).unwrap();
    let mut accepted = BTreeSet::new();
    for (index, vertex) in graph.vertices().iter().enumerate() {
        let outcome = DerivedEquivalenceEdge::recover(
            vertex
                .to_tilting()
                .expect("a tilting walk stores tilting vertices"),
            &TargetLimits::default(),
        )
        .unwrap();
        let DerivedEquivalenceEdgeOutcome::Certified(edge) = outcome else {
            panic!("target recovery was cut at vertex {index}");
        };
        if let Ok(target) = GentlePresentation::new(edge.target()) {
            assert_eq!(
                target.complete_invariant(),
                expected,
                "a derived equivalent target differs at vertex {index}"
            );
            accepted.insert(target.key());
        }
    }
    (graph.vertices().len(), accepted)
}

#[test]
fn recovered_gentle_targets_share_the_complete_invariant() {
    // Every Kronecker target is the Kronecker algebra. The other sources reach
    // targets with relations and parallel arrows. Each case lists the
    // recovered targets and the least number of gentle classes among them.
    // The last three sources have a projective with a two-dimensional
    // endomorphism ring. In the genus-1 source, `abc = (ab)·c` factors through
    // a radical map, so the minimal approximation of `P_1` drops it.
    let field = PrimeField::new(3).unwrap();
    let cases = [
        ("Kronecker", crate::algebra::kronecker(2, field), 8, 1),
        ("A_3 with a source", bound(3, &[(1, 0), (1, 2)], &[]), 8, 4),
        (
            "affine A_{1,2}",
            bound(3, &[(0, 1), (0, 2), (2, 1)], &[]),
            8,
            3,
        ),
        ("A_3", crate::algebra::linear_an(3, field), 8, 4),
        (
            "A_3/(ab)",
            crate::algebra::an_with_relations(3, &[(0, 2)], field).unwrap(),
            8,
            4,
        ),
        ("k[x]/(x^2)", bound(1, &[(0, 0)], &[(0, 0)]), 8, 1),
        (
            "2-cycle with one relation",
            bound(2, &[(0, 1), (1, 0)], &[(0, 1)]),
            8,
            1,
        ),
        (
            "genus 1",
            bound(2, &[(0, 1), (1, 0), (0, 1)], &[(2, 1), (1, 0)]),
            8,
            1,
        ),
        ("APS Λ_1, gcd 0", aps_first(), 8, 1),
        // Mutations that return to a stored vertex add edges, not vertices.
        ("APS Λ_2, gcd 2", aps_second(), 7, 1),
    ];
    for (name, algebra, targets, classes) in &cases {
        let (recovered, accepted) = gentle_targets_agree(algebra);
        assert_eq!(recovered, *targets, "{name}: recovered targets");
        assert!(
            accepted.len() >= *classes,
            "{name}: {} classes",
            accepted.len()
        );
    }
}

/// Runs discovery from every presentation with `vertices` vertices over
/// `F_2` whose invariant satisfies `keep`. Every accepted target must share
/// the source's invariant. Returns the number of invariant classes and, for
/// each class that discovery leaves in more than one component, the class
/// and its component count.
fn discovery_components(
    vertices: u32,
    keep: impl Fn(&GentleDerivedInvariant) -> bool,
) -> (usize, Vec<String>) {
    let field = PrimeField::new(2).unwrap();
    let mut root: BTreeMap<GentleKey, GentleKey> = BTreeMap::new();
    let mut classes: BTreeMap<GentleDerivedInvariant, Vec<GentleKey>> = BTreeMap::new();
    for key in connected_gentle_keys(vertices) {
        let algebra = key.algebra(field).unwrap();
        let value = GentlePresentation::new(&algebra)
            .unwrap()
            .complete_invariant();
        if !keep(&value) {
            continue;
        }
        for target in gentle_targets_agree(&algebra).1 {
            let (left, right) = (find(&mut root, &key), find(&mut root, &target));
            root.insert(left, right);
        }
        classes.entry(value).or_default().push(key);
    }
    let split = classes
        .iter()
        .filter_map(|(value, keys)| {
            let roots: BTreeSet<GentleKey> = keys.iter().map(|key| find(&mut root, key)).collect();
            (roots.len() > 1).then(|| format!("{value}: {}", roots.len()))
        })
        .collect();
    (classes.len(), split)
}

fn find(root: &mut BTreeMap<GentleKey, GentleKey>, key: &GentleKey) -> GentleKey {
    let mut current = key.clone();
    while let Some(next) = root.get(&current).filter(|next| **next != current) {
        current = next.clone();
    }
    root.insert(key.clone(), current.clone());
    current
}

/// Every source of genus at least 1 at four vertices.
///
/// Ignored: 406 discovery runs. Two classes stay in two components. In each,
/// discovery from one self-opposite algebra reaches only that algebra, also
/// under 128 stored vertices and 1024 mutations. Each of these two algebras
/// has a closed curve of odd winding number, so its class is forced.
#[test]
#[ignore]
fn discovery_components_refine_the_invariant_at_four_vertices() {
    let (classes, split) = discovery_components(4, |value| value.genus() >= 1);
    assert_eq!(classes, 35);
    assert_eq!(
        split,
        [
            "[(1, 1), (1, 5)], genus 1, gcd 1: 2",
            "[(1, 7)], genus 2, odd: 2"
        ]
    );
}

/// Every source at five vertices with a defined Arf invariant.
///
/// Ignored: 23 discovery runs. No edge joins the two Arf values. Under
/// `small_limits` each class stays in three components.
#[test]
#[ignore]
fn discovery_keeps_the_arf_invariant_at_five_vertices() {
    let arf =
        |value: &GentleDerivedInvariant| matches!(value.winding_class(), WindingClass::Arf(_));
    let (classes, split) = discovery_components(5, arf);
    assert_eq!(classes, 2);
    assert_eq!(
        split,
        ["[(2, 8)], genus 2, arf 0: 3", "[(2, 8)], genus 2, arf 1: 3"]
    );
}

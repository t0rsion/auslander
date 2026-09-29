//! Every recovered discovery target has the invariants of its source.

use super::*;
use crate::algebra::{cyclic_nakayama, monomial_algebra, radical_square_zero_cycle};
use crate::equivalence_discovery::{DiscoveryLimits, discover_equivalences};
use crate::equivalence_edge::{DerivedEquivalenceEdge, DerivedEquivalenceEdgeOutcome};
use crate::monomial::MonomialIdeal;
use crate::target::TargetLimits;

fn discovery_limits() -> DiscoveryLimits {
    DiscoveryLimits {
        max_vertices: 6,
        max_directed_mutations: 24,
        max_total_terms: 128,
        max_matrix_entries: 4_096,
        ..DiscoveryLimits::default()
    }
}

/// Checks every recovered target of `algebra` and returns the number checked.
fn check_targets(algebra: &Arc<Algebra>) -> usize {
    let graph =
        discover_equivalences(algebra, discovery_limits(), &ComputationControl::new()).unwrap();
    assert!(graph.verify());
    let source = invariants(algebra, 2);
    for kind in DerivedInvariantKind::ALL {
        assert!(
            !matches!(source.reading(kind), InvariantReading::Stopped(_)),
            "{kind:?} stopped"
        );
    }
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
        let target = invariants(edge.target(), 2);
        for kind in DerivedInvariantKind::ALL {
            let (left, right) = (source.reading(kind), target.reading(kind));
            let message = format!("{kind:?} differs at vertex {index}");
            // Recognition reads one presentation, so a gentle algebra can
            // have a target that is not presented as gentle.
            if matches!(
                kind,
                DerivedInvariantKind::AagFunction | DerivedInvariantKind::WindingClass
            ) {
                assert!(!left.separates(right), "{message}");
            } else {
                assert_eq!(left, right, "{message}");
            }
        }
    }
    graph.vertices().len()
}

fn monomial(
    field: PrimeField,
    vertices: u32,
    arrows: &[(u32, u32)],
    relations: &[[u32; 2]],
) -> Arc<Algebra> {
    let quiver = Quiver::new(vertices, arrows).unwrap();
    let words = relations
        .iter()
        .map(|word| word.iter().map(|&arrow| ArrowId(arrow)).collect())
        .collect();
    monomial_algebra(&MonomialIdeal::new(quiver, words).unwrap(), field).unwrap()
}

/// `k[x]/(x^2)`, the 2-cycle `a: 0 → 1`, `b: 1 → 0` with `a·b = 0`, and the
/// genus-1 gentle algebra with arrows `a, c: 0 → 1`, `b: 1 → 0` and relations
/// `c·b = b·a = 0` have a projective with a two-dimensional endomorphism ring.
/// For Kupisch series `[3, 3, 2]`, `rad P_0 = (1, 2)` has projective cover
/// `P_1` with kernel `S_0`, so `Ω^2 S_0 = S_0`. Discovery keeps only the
/// regular complex of the radical-square-zero 2-cycle. The Kupisch walk
/// closes on three vertices: each tilting mutation of the two neighbors of
/// the regular complex returns it after minimal reduction, and every other
/// mutation is silting only. The other seven walks reach the six-vertex
/// limit, so `7·6 + 1 + 3 = 46` targets are checked.
#[test]
fn discovery_targets_keep_every_invariant() {
    for field in [field(2), field(5)] {
        let algebras = [
            ("A_3", linear_an(3, field)),
            ("A_3/(ab)", an_with_relations(3, &[(0, 2)], field).unwrap()),
            ("Kronecker", kronecker(2, field)),
            ("commutative square", commutative_square(field)),
            (
                "rad^2 = 0 on a 2-cycle",
                radical_square_zero_cycle(2, field),
            ),
            (
                "Nakayama [3, 3, 2]",
                cyclic_nakayama(&[3, 3, 2], field).unwrap(),
            ),
            ("k[x]/(x^2)", dual_numbers(field)),
            (
                "2-cycle with one relation",
                monomial(field, 2, &[(0, 1), (1, 0)], &[[0, 1]]),
            ),
            (
                "genus-1 gentle",
                monomial(field, 2, &[(0, 1), (1, 0), (0, 1)], &[[2, 1], [1, 0]]),
            ),
        ];
        let mut total = 0;
        for (name, algebra) in &algebras {
            let checked = check_targets(algebra);
            eprintln!("F_{}: {name}: {checked} targets checked", field.modulus());
            assert!(checked > 0, "{name} recovered no target");
            total += checked;
        }
        eprintln!("F_{}: {total} targets checked", field.modulus());
        assert_eq!(total, 46);
    }
}

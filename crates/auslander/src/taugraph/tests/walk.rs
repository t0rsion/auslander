use super::super::*;
use super::common::*;

use std::sync::Arc;

use crate::algebra::{Algebra, kronecker, linear_an, radical_square_zero_cycle};
use crate::mutation::FacWitness;

/// A budget equal to the true count still closes.
///
/// `max_vertices` is checked when a further distinct vertex is inserted,
/// so the fifth vertex of the A_2 pentagon fits into a budget of five.
#[test]
fn a_vertex_budget_equal_to_the_true_count_still_closes() {
    let limits = MutationGraphLimits {
        max_vertices: 5,
        ..MutationGraphLimits::default()
    };
    let outcome = support_tau_tilting_graph(&linear_an(2, f2()), &limits)
        .expect("A_2 walks without a defect");
    assert!(outcome.is_closed());
    assert_eq!(outcome.closed().expect("closed").len(), 5);

    let tight = MutationGraphLimits {
        max_vertices: 4,
        ..MutationGraphLimits::default()
    };
    let outcome =
        support_tau_tilting_graph(&linear_an(2, f2()), &tight).expect("A_2 walks without a defect");
    let graph = outcome.incomplete().expect("four vertices are one too few");
    match graph.reason() {
        IncompleteReason::BudgetExhausted(diagnostics) => {
            assert_eq!(diagnostics.limit(), GraphLimit::Vertices);
        }
        IncompleteReason::CertificationBlocked(blocker) => {
            panic!("a vertex budget is no blocked certification: {blocker}")
        }
    }
}

/// The Kronecker algebra is tau-tilting infinite, so the walk truncates
/// rather than closing or hanging.
///
/// The descending walk leaves `(A, 0)` down the preprojective ray
/// `(m, m + 1) + (m + 1, m + 2)`, which never ends. The result is a typed
/// budget diagnostic, never a completeness claim, and the vertices it did
/// reach stay individually certified.
#[test]
fn the_kronecker_walk_truncates_with_a_typed_budget() {
    let limits = MutationGraphLimits {
        max_vertices: 16,
        ..MutationGraphLimits::default()
    };
    let outcome = support_tau_tilting_graph(&kronecker(2, f2()), &limits)
        .expect("the Kronecker walk runs without a defect");
    assert!(!outcome.is_closed());
    let graph = outcome.incomplete().expect("the walk stopped short");
    let diagnostics = match graph.reason() {
        IncompleteReason::BudgetExhausted(diagnostics) => diagnostics,
        IncompleteReason::CertificationBlocked(blocker) => {
            panic!("the Kronecker walk certifies every step it takes: {blocker}")
        }
    };
    assert_eq!(diagnostics.limit(), GraphLimit::Vertices);
    assert_eq!(diagnostics.vertices_found(), 16);
    assert_eq!(graph.vertices_found().len(), 16);
    assert!(diagnostics.open_slots() > 0);
    assert!(diagnostics.work_units() > 0);
    // Rechecking the mutations as well costs 183 ms, so
    // `the_kronecker_mutations_recheck` carries that part.
    for vertex in graph.vertices_found() {
        assert!(vertex.pair().verify());
        assert_eq!(vertex.pair().summand_count(), 2);
    }
    // The bias is structural: every module part the walk reached is
    // preprojective, of dimension vector (m, m + 1), so no preinjective
    // vertex is in the sample.
    for vertex in graph.vertices_found() {
        for summand in vertex.pair().module().summands() {
            let dim = summand.module().dim_vector();
            assert!(dim[0] <= dim[1], "a preinjective summand {dim:?} appeared");
        }
    }
}

/// The work-unit counts, asserted against ceilings of about twice the
/// measured count rounded up to a power of two.
///
/// | fixture | measured | ceiling | before the size factor |
/// | --- | --- | --- | --- |
/// | A_2 | 6668 | 16384 | 1416 |
/// | A_3 | 145712 | 524288 | 12895 |
/// | A_4 | 2253257 | 8388608 | 107808 |
/// | D_4 | 3951020 | 8388608 | 140428 |
///
/// The last column is the count before every rate gained the size factor
/// `e`, which is where most of the rise comes from: `e` grows with the
/// modules the walk carries. The rest is later work in the layers below,
/// which moves the `tau` miss count the ledger reads. Neither changes what
/// the walk does, and each ceiling is about twice its measured count, so a
/// count that drifts does not fail this test.
///
/// The counts are charged by call and by module size, so they do not move
/// with the profile or the platform.
#[test]
fn the_work_unit_counts_stay_under_their_ceilings() {
    let cases: [(&str, Arc<Algebra>, u64); 4] = [
        ("A_2", linear_an(2, f2()), 16_384),
        ("A_3", linear_an(3, f2()), 524_288),
        ("A_4", linear_an(4, f2()), 8_388_608),
        ("D_4", d4(f2()), 8_388_608),
    ];
    for (name, algebra, ceiling) in cases {
        let graph = walk(&algebra);
        assert!(
            graph.work_units() <= ceiling,
            "{name}: {} units over the ceiling {ceiling}",
            graph.work_units()
        );
    }
    // The ledger counts calls, and the call sequence does not depend on
    // the field, so A_3 charges the same over F_2 and F_5.
    assert_eq!(
        walk(&linear_an(3, f2())).work_units(),
        walk(&linear_an(3, f5())).work_units()
    );
}

/// The A_2 pentagon, vertex by vertex.
///
/// The math spike computes every step of this graph by hand (section 3.2).
/// `P_1 = (1, 1)`, `P_2 = S_2 = (0, 1)`, `S_1 = (1, 0)`, and the five pairs
/// are `(P_1 + P_2, 0)`, `(P_1 + S_1, 0)`, `(S_1, P_2)`, `(S_2, P_1)`, and
/// `(0, P_1 + P_2)`. The walk leaves `(A, 0)` twice: at `P_2` the minimal
/// left `add(P_1)`-approximation is the socle inclusion `S_2 -> P_1` with
/// cokernel `S_1`, giving `(P_1 + S_1, 0)`; at `P_1` the support drops
/// vertex 1, giving `(S_2, P_1)`. Exactly one module slot has no left
/// mutation: `S_1` in `(P_1 + S_1, 0)` is the top of `P_1`, so it lies in
/// `Fac(P_1)` and that slot is a right mutation.
///
/// The undirected graph is the pentagon, 2-regular on 5 vertices with 5
/// edges, which is the exchange graph of the type A_2 cluster algebra.
#[test]
fn the_a2_walk_is_the_pentagon() {
    for field in fields() {
        let graph = walk(&linear_an(2, field));
        assert_eq!(graph.len(), 5);
        assert_eq!(graph.mutations().len(), 5);
        let mut parts: Vec<(Vec<Vec<usize>>, Vec<u32>)> = graph
            .pairs()
            .map(|pair| {
                (
                    pair.module().dim_vectors(),
                    pair.projective().vertices().to_vec(),
                )
            })
            .collect();
        parts.sort();
        assert_eq!(
            parts,
            vec![
                (vec![], vec![0, 1]),
                (vec![vec![0, 1]], vec![0]),
                (vec![vec![0, 1], vec![1, 1]], vec![]),
                (vec![vec![1, 0]], vec![1]),
                (vec![vec![1, 0], vec![1, 1]], vec![]),
            ]
        );
        let fac: Vec<&FacWitness> = graph
            .vertices()
            .iter()
            .flat_map(|vertex| vertex.slots())
            .filter_map(SlotRecord::fac_witness)
            .collect();
        assert_eq!(fac.len(), 1);
        assert_eq!(fac[0].summand().dim_vector(), [1, 0]);
        assert_eq!(fac[0].module().dim_vector(), [1, 1]);
        // (A, 0) is the maximum, so both its slots mutate out and nothing
        // mutates into it. (0, A) is the minimum: no module slot at all.
        assert_eq!(graph.vertices()[0].slots().len(), 2);
        let minima = graph
            .vertices()
            .iter()
            .filter(|vertex| vertex.pair().module().is_empty())
            .count();
        assert_eq!(minima, 1);
        assert!(graph.mutations().iter().all(|edge| edge.target() != 0));
    }
}

/// The same algebra walked twice gives the same vertex order, the same
/// edge order, and the same stored witnesses.
#[test]
fn two_runs_agree_on_order_and_witnesses() {
    for field in fields() {
        for algebra in [linear_an(3, field), radical_square_zero_cycle(3, field)] {
            let first = walk(&algebra);
            let second = walk(&algebra);
            assert_eq!(render(&first), render(&second));
            assert_eq!(first.work_units(), second.work_units());
        }
    }
}

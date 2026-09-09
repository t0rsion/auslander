use std::sync::Arc;

use crate::algebra::{Algebra, an_with_relations, kronecker, linear_an};
use crate::decompose::Certificate;
use crate::field::PrimeField;
use crate::iso::{IsoOutcome, is_isomorphic};
use crate::quiver::Quiver;

use super::constructors::star;
use super::indecomposables::{admissible_sink_sequence, reflect_endpoints};
use super::*;

fn path_algebra(quiver: Quiver, field: PrimeField) -> Arc<Algebra> {
    crate::algebra::path_algebra(quiver, field).expect("the zero ideal completes")
}

fn dynkin_types() -> Vec<DynkinType> {
    let mut types: Vec<DynkinType> = (1..=8).map(DynkinType::A).collect();
    types.extend((4..=8).map(DynkinType::D));
    types.extend([DynkinType::E6, DynkinType::E7, DynkinType::E8]);
    types
}

fn euclidean_types() -> Vec<EuclideanType> {
    let mut types: Vec<EuclideanType> = (1..=8).map(EuclideanType::A).collect();
    types.extend((4..=8).map(EuclideanType::D));
    types.extend([EuclideanType::E6, EuclideanType::E7, EuclideanType::E8]);
    types
}

#[test]
fn each_dynkin_diagram_is_recognised_as_its_own_type() {
    for t in dynkin_types() {
        let q = dynkin_quiver(t).unwrap();
        assert_eq!(q.num_vertices() as usize, t.num_vertices().unwrap());
        assert_eq!(dynkin_type(&q), Some(t), "{t}");
        assert_eq!(euclidean_type(&q), None, "{t}");
    }
}

#[test]
fn each_euclidean_diagram_is_recognised_as_its_own_type() {
    for t in euclidean_types() {
        let q = euclidean_quiver(t).unwrap();
        assert_eq!(q.num_vertices() as usize, t.num_vertices().unwrap());
        assert_eq!(euclidean_type(&q), Some(t), "{t}");
        assert_eq!(dynkin_type(&q), None, "{t}");
    }
}

#[test]
fn a_double_edge_is_affine_a_1() {
    let kronecker_quiver = Quiver::new(2, &[(0, 1), (0, 1)]).unwrap();
    assert_eq!(euclidean_type(&kronecker_quiver), Some(EuclideanType::A(1)));
    let two_cycle = Quiver::new(2, &[(0, 1), (1, 0)]).unwrap();
    assert_eq!(euclidean_type(&two_cycle), Some(EuclideanType::A(1)));
}

#[test]
fn a_triple_edge_is_neither_dynkin_nor_euclidean() {
    let q = Quiver::new(2, &[(0, 1), (0, 1), (0, 1)]).unwrap();
    assert_eq!(dynkin_type(&q), None);
    assert_eq!(euclidean_type(&q), None);
}

#[test]
fn orientation_does_not_change_the_recognised_type() {
    let forward = Quiver::new(4, &[(0, 1), (1, 2), (2, 3)]).unwrap();
    let alternating = Quiver::new(4, &[(0, 1), (2, 1), (2, 3)]).unwrap();
    assert_eq!(dynkin_type(&forward), Some(DynkinType::A(4)));
    assert_eq!(dynkin_type(&alternating), Some(DynkinType::A(4)));
}

#[test]
fn a_disconnected_graph_has_no_type() {
    let q = Quiver::new(4, &[(0, 1), (2, 3)]).unwrap();
    assert_eq!(dynkin_type(&q), None);
    assert_eq!(euclidean_type(&q), None);
}

#[test]
fn a_loop_has_no_type_and_no_generalized_cartan_matrix() {
    let q = Quiver::new(1, &[(0, 0)]).unwrap();
    assert_eq!(dynkin_type(&q), None);
    assert_eq!(euclidean_type(&q), None);
    assert_eq!(generalized_cartan_matrix(&q), None);
}

#[test]
fn the_star_with_arms_2_2_3_is_neither_dynkin_nor_euclidean() {
    let q = star(&[2, 2, 3]);
    assert_eq!(dynkin_type(&q), None);
    assert_eq!(euclidean_type(&q), None);
}

#[test]
fn the_star_with_five_arms_is_neither_dynkin_nor_euclidean() {
    let q = star(&[1, 1, 1, 1, 1]);
    assert_eq!(dynkin_type(&q), None);
    assert_eq!(euclidean_type(&q), None);
}

#[test]
fn generalized_cartan_matrix_has_minus_the_edge_multiplicity_off_diagonal() {
    let q = Quiver::new(2, &[(0, 1), (0, 1)]).unwrap();
    assert_eq!(
        generalized_cartan_matrix(&q),
        Some(vec![vec![2, -2], vec![-2, 2]])
    );
    let a3 = Quiver::new(3, &[(0, 1), (2, 1)]).unwrap();
    assert_eq!(
        generalized_cartan_matrix(&a3),
        Some(vec![vec![2, -1, 0], vec![-1, 2, -1], vec![0, -1, 2]])
    );
}

#[test]
fn positive_root_count_matches_the_dynkin_type() {
    for t in dynkin_types() {
        let q = dynkin_quiver(t).unwrap();
        let roots = positive_roots(&q).unwrap();
        assert_eq!(roots.len(), t.indecomposable_count().unwrap(), "{t}");
    }
}

#[test]
fn the_highest_root_has_the_tabulated_height() {
    for (t, height) in [
        (DynkinType::A(5), 5),
        (DynkinType::D(4), 5),
        (DynkinType::D(7), 11),
        (DynkinType::E6, 11),
        (DynkinType::E7, 17),
        (DynkinType::E8, 29),
    ] {
        let roots = positive_roots(&dynkin_quiver(t).unwrap()).unwrap();
        let highest = roots.iter().map(|r| r.iter().sum::<usize>()).max().unwrap();
        assert_eq!(highest, height, "{t}");
    }
}

#[test]
fn the_positive_roots_of_a3_are_the_six_intervals() {
    let roots = positive_roots(linear_an(3, PrimeField::new(5).unwrap()).quiver()).unwrap();
    assert_eq!(
        roots,
        vec![
            vec![0, 0, 1],
            vec![0, 1, 0],
            vec![1, 0, 0],
            vec![0, 1, 1],
            vec![1, 1, 0],
            vec![1, 1, 1],
        ]
    );
}

#[test]
fn a_euclidean_graph_has_no_positive_root_list() {
    assert_eq!(
        positive_roots(kronecker(2, PrimeField::new(5).unwrap()).quiver()),
        None
    );
}

#[test]
fn the_admissible_sequence_lists_every_vertex_and_restores_the_orientation() {
    for t in dynkin_types() {
        let q = dynkin_quiver(t).unwrap();
        let sequence = admissible_sink_sequence(&q).unwrap();
        let mut sorted = sequence.clone();
        sorted.sort_unstable();
        assert_eq!(sorted, (0..q.num_vertices()).collect::<Vec<_>>(), "{t}");
        let mut endpoints: Vec<(u32, u32)> = q.arrows().to_vec();
        for &i in &sequence {
            reflect_endpoints(&mut endpoints, i);
        }
        assert_eq!(endpoints, q.arrows(), "{t}");
    }
}

#[test]
fn a_cyclic_quiver_has_no_admissible_sink_sequence() {
    let q = Quiver::new(3, &[(0, 1), (1, 2), (2, 0)]).unwrap();
    assert_eq!(admissible_sink_sequence(&q), None);
}

#[test]
fn a_bound_algebra_is_rejected_as_a_nonzero_ideal() {
    let algebra = an_with_relations(3, &[(0, 2)], PrimeField::new(5).unwrap()).unwrap();
    assert_eq!(
        dynkin_indecomposables(&algebra).unwrap_err(),
        DynkinError::NonzeroIdeal { relations: 1 }
    );
}

#[test]
fn the_kronecker_algebra_is_rejected_as_affine_a_1() {
    assert_eq!(
        dynkin_indecomposables(&kronecker(2, PrimeField::new(5).unwrap())).unwrap_err(),
        DynkinError::NotDynkin {
            euclidean: Some(EuclideanType::A(1)),
        }
    );
}

#[test]
fn constructed_dimension_vectors_are_exactly_the_positive_roots() {
    let field = PrimeField::new(32003).unwrap();
    for t in [
        DynkinType::A(1),
        DynkinType::A(4),
        DynkinType::D(4),
        DynkinType::D(5),
    ] {
        let quiver = dynkin_quiver(t).unwrap();
        let roots = positive_roots(&quiver).unwrap();
        let algebra = path_algebra(quiver, field);
        let built: Vec<Vec<usize>> = dynkin_indecomposables(&algebra)
            .unwrap()
            .iter()
            .map(|(m, _)| m.dim_vector().to_vec())
            .collect();
        assert_eq!(built, roots, "{t}");
    }
}

#[test]
fn every_constructed_module_is_certified_indecomposable() {
    let field = PrimeField::new(2).unwrap();
    for t in [DynkinType::A(5), DynkinType::D(4)] {
        let algebra = path_algebra(dynkin_quiver(t).unwrap(), field);
        for (_, certificate) in dynkin_indecomposables(&algebra).unwrap() {
            assert_eq!(certificate, Certificate::Indecomposable, "{t}");
        }
    }
}

#[test]
fn the_exceptional_types_have_36_63_and_120_indecomposables() {
    let field = PrimeField::new(32003).unwrap();
    for (t, count) in [
        (DynkinType::E6, 36),
        (DynkinType::E7, 63),
        (DynkinType::E8, 120),
    ] {
        let algebra = path_algebra(dynkin_quiver(t).unwrap(), field);
        let modules = dynkin_indecomposables(&algebra).unwrap();
        assert_eq!(modules.len(), count, "{t}");
        assert_eq!(t.indecomposable_count(), Some(count));
    }
}

/// `n(n+1)/2` must be reported whenever it is representable, even when the
/// intermediate product `n(n+1)` is not, and `None` only when the count
/// itself does not fit.
#[test]
fn root_counts_survive_an_unrepresentable_intermediate_product() {
    // Both widths need an n whose raw product overflows while its
    // triangular number still fits; the literal is cast rather than
    // written as a usize so it also compiles at 32 bits.
    let n: usize = if usize::BITS >= 64 {
        5_000_000_000u64 as usize
    } else {
        80_000
    };
    let expected = u128::from(n as u64) * (u128::from(n as u64) + 1) / 2;
    assert_eq!(n.checked_mul(n + 1), None, "the product must overflow");
    assert_eq!(
        DynkinType::A(n).indecomposable_count().map(u128::try_from),
        Some(Ok(expected))
    );
    assert_eq!(DynkinType::A(usize::MAX).indecomposable_count(), None);
    assert_eq!(DynkinType::A(usize::MAX).num_vertices(), Some(usize::MAX));
    assert_eq!(DynkinType::D(usize::MAX).indecomposable_count(), None);
    assert_eq!(EuclideanType::A(usize::MAX).num_vertices(), None);
    assert_eq!(EuclideanType::D(usize::MAX).num_vertices(), None);
    // Odd and even n take different branches of the halving.
    assert_eq!(DynkinType::A(7).indecomposable_count(), Some(28));
    assert_eq!(DynkinType::A(8).indecomposable_count(), Some(36));
}

/// A diagram whose vertex count exceeds the `u32` indexing of `Quiver`
/// must be refused, never truncated into a small wrong quiver. The
/// abstract counts stay available: `num_vertices` answers over `usize`.
#[test]
fn diagram_quivers_reject_vertex_counts_beyond_u32() {
    // The rejected parameters exist only at 64 bits; at 32 bits usize
    // itself enforces the bound.
    if usize::BITS < 64 {
        return;
    }
    let beyond = u32::MAX as u64 as usize + 1;
    assert!(dynkin_quiver(DynkinType::A(beyond)).is_none());
    assert!(dynkin_quiver(DynkinType::D(beyond)).is_none());
    assert_eq!(DynkinType::A(beyond).num_vertices(), Some(beyond));
    // Affine A and D have one vertex more than their subscript, so the
    // boundary parameter is already unrepresentable.
    assert!(euclidean_quiver(EuclideanType::A(beyond - 1)).is_none());
    assert!(euclidean_quiver(EuclideanType::D(beyond - 1)).is_none());
    assert!(euclidean_quiver(EuclideanType::A(beyond)).is_none());
    assert_eq!(EuclideanType::A(beyond).num_vertices(), Some(beyond + 1));
}

#[test]
fn constructed_modules_are_pairwise_non_isomorphic() {
    let field = PrimeField::new(5).unwrap();
    let algebra = path_algebra(dynkin_quiver(DynkinType::D(4)).unwrap(), field);
    let modules = dynkin_indecomposables(&algebra).unwrap();
    assert_eq!(modules.len(), 12);
    for (i, (m, _)) in modules.iter().enumerate() {
        for (n, _) in modules.iter().skip(i + 1) {
            assert!(matches!(
                is_isomorphic(m, n).unwrap(),
                IsoOutcome::NotIsomorphic(_)
            ));
        }
    }
}

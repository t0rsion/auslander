use auslander::decompose::{Certificate, KrullSchmidtOutcome, decompose, krull_schmidt};
use auslander::endo::EndoAlgebra;
use auslander::iso::{IsoOutcome, Obstruction, is_isomorphic};
use auslander::module::{Module, direct_sum};
use auslander::opposite::{dual, opposite};
use auslander::radical::radical;

use super::common::preprojective_a3;
use super::fixtures::{SQUARE_CARTAN, dim_vecs, square};

/// Row 6. Over A every `e_v A e_v` is the line `k·e_v`, so `End(P_v) = k`:
/// dimension 1, radical 0, local. `rad P_0 = [0, 1, 1, 1]` is
/// indecomposable (oracle decomposition), so its endomorphism algebra is
/// local with radical codimension 1. Over B, `End(P_1) = e_1 B e_1` has
/// dimension 2 (Cartan entry) and is local with radical dimension 1.
#[test]
fn endo_of_indecomposables_is_local() {
    let a = square();
    for v in 0..4 {
        let endo = EndoAlgebra::new(&Module::projective(&a, v));
        assert_eq!(endo.dim(), 1, "dim End(P_{v})");
        assert_eq!(endo.radical_dim(), 0, "rad End(P_{v})");
        assert!(endo.is_local(), "End(P_{v}) is local");
    }
    let rad_p0 = radical(&Module::projective(&a, 0)).0;
    let endo = EndoAlgebra::new(&rad_p0);
    assert!(endo.is_local(), "End(rad P_0) is local");
    assert_eq!(endo.dim() - endo.radical_dim(), 1, "radical codimension 1");
    let b = preprojective_a3();
    let endo = EndoAlgebra::new(&Module::projective(&b, 1));
    assert_eq!(endo.dim(), 2, "dim End(P_1) = dim e_1 B e_1");
    assert_eq!(endo.radical_dim(), 1);
    assert!(endo.is_local());
}

/// Row 6. `End(P_0 ⊕ P_0) = M_2(e_0 A e_0) = M_2(k)`: dimension 4,
/// semisimple (radical 0), one Wedderburn factor, not commutative, not
/// local.
#[test]
fn square_endo_of_p0_squared_is_a_two_by_two_matrix_algebra() {
    let a = square();
    let p0 = Module::projective(&a, 0);
    let p0_again = Module::projective(&a, 0);
    let (sum, _, _) = direct_sum(&[&p0, &p0_again]);
    let endo = EndoAlgebra::new(&sum);
    assert_eq!(endo.dim(), 4);
    assert_eq!(endo.radical_dim(), 0);
    assert!(!endo.quotient_is_commutative());
    assert_eq!(endo.semisimple_factor_count(), 1);
    assert!(!endo.is_local());
}

/// Row 7. `P_0 ⊕ S_1 ⊕ S_1` groups into two isomorphism classes with
/// multiplicities 1 and 2.
#[test]
fn square_krull_schmidt_of_p0_plus_two_s1() {
    let a = square();
    let p0 = Module::projective(&a, 0);
    let s1_first = Module::simple(&a, 1);
    let s1_second = Module::simple(&a, 1);
    let (sum, _, _) = direct_sum(&[&p0, &s1_first, &s1_second]);
    let classes = match krull_schmidt(&sum) {
        KrullSchmidtOutcome::Classes(classes) => classes,
        KrullSchmidtOutcome::Unknown { reason } => panic!("grouping failed: {reason}"),
    };
    let mut found: Vec<(Vec<usize>, usize)> = classes
        .iter()
        .map(|c| (c.representative.dim_vector().to_vec(), c.multiplicity))
        .collect();
    found.sort();
    assert_eq!(found, vec![(vec![0, 1, 0, 0], 2), (vec![1, 1, 1, 1], 1)]);
}

/// Row 7. The regular module `A = ⊕_v P_v` decomposes into the four
/// pairwise non-isomorphic projectives, every summand certified.
#[test]
fn square_regular_module_decomposes_into_the_four_projectives() {
    let a = square();
    let projectives: Vec<Module> = (0..4).map(|v| Module::projective(&a, v)).collect();
    let refs: Vec<&Module> = projectives.iter().collect();
    let (regular, _, _) = direct_sum(&refs);
    let d = decompose(&regular);
    assert_eq!(d.summands().len(), 4);
    assert!(
        d.certificates()
            .iter()
            .all(|c| *c == Certificate::Indecomposable)
    );
    let mut found = dim_vecs(d.summands());
    found.sort();
    let mut expected: Vec<Vec<usize>> = SQUARE_CARTAN.iter().map(|row| row.to_vec()).collect();
    expected.sort();
    assert_eq!(found, expected);
    let classes = match krull_schmidt(&regular) {
        KrullSchmidtOutcome::Classes(classes) => classes,
        KrullSchmidtOutcome::Unknown { reason } => panic!("grouping failed: {reason}"),
    };
    assert_eq!(classes.len(), 4);
    assert!(classes.iter().all(|c| c.multiplicity == 1));
}

/// Row 8. Two separate constructions of `P_0` are isomorphic, and so is the
/// double dual of `P_0`.
#[test]
fn square_is_isomorphic_accepts_p0_copies_and_the_double_dual() {
    let a = square();
    let p0 = Module::projective(&a, 0);
    let p0_again = Module::projective(&a, 0);
    assert!(matches!(
        is_isomorphic(&p0, &p0_again).unwrap(),
        IsoOutcome::Isomorphic(_)
    ));
    let op = opposite(&a).unwrap();
    let dd = dual(&dual(&p0, &op).unwrap(), &op).unwrap();
    assert!(matches!(
        is_isomorphic(&p0, &dd).unwrap(),
        IsoOutcome::Isomorphic(_)
    ));
}

/// Row 8. `S_0` and `S_1` differ already in the dimension vector, and the
/// obstruction is typed.
#[test]
fn square_is_isomorphic_rejects_s0_vs_s1_with_a_dimension_obstruction() {
    let a = square();
    let s0 = Module::simple(&a, 0);
    let s1 = Module::simple(&a, 1);
    match is_isomorphic(&s0, &s1).unwrap() {
        IsoOutcome::NotIsomorphic(Obstruction::DimensionVector { source, target }) => {
            assert_eq!(source, vec![1, 0, 0, 0]);
            assert_eq!(target, vec![0, 1, 0, 0]);
        }
        other => panic!("expected a dimension-vector obstruction, got {other:?}"),
    }
}

/// Row 8. `P_1` and `S_1 ⊕ S_3` share the dimension vector `[0, 1, 0, 1]`
/// but not the radical series: `rad P_1 = S_3` is nonzero while the sum is
/// semisimple.
#[test]
fn square_equal_dimension_vector_pair_p1_vs_s1_plus_s3_is_not_isomorphic() {
    let a = square();
    let p1 = Module::projective(&a, 1);
    let s1 = Module::simple(&a, 1);
    let s3 = Module::simple(&a, 3);
    let (sum, _, _) = direct_sum(&[&s1, &s3]);
    assert_eq!(p1.dim_vector(), sum.dim_vector());
    match is_isomorphic(&p1, &sum).unwrap() {
        IsoOutcome::NotIsomorphic(Obstruction::LoewySeries { source, target }) => {
            assert_eq!(source, vec![vec![0, 0, 0, 1]]);
            assert_eq!(target, Vec::<Vec<usize>>::new());
        }
        other => panic!("expected a Loewy-series obstruction, got {other:?}"),
    }
}

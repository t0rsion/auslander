use super::types::check_input_relations;
use super::*;
use crate::completion::{CompletionLimits, Outcome, complete};
use crate::field::PrimeField;
use crate::monomial::{MonomialError, MonomialIdeal, MonomialPresentation, truncated_poly_ideal};
use crate::quiver::{ArrowId, PathWord, Quiver};
use crate::relation::{Presentation, Relation};
use crate::verify::verify;

fn f5() -> PrimeField {
    PrimeField::new(5).unwrap()
}

fn word(algebra: &Algebra, arrows: &[u32]) -> PathWord {
    let ids: Vec<ArrowId> = arrows.iter().copied().map(ArrowId).collect();
    PathWord::from_arrows(algebra.quiver(), &ids).unwrap()
}

/// One vertex, one loop `x`, and the relation given as
/// `(coefficient, exponent)` terms.
fn loop_presentation(field: PrimeField, terms: &[(i64, usize)]) -> Presentation {
    let quiver = Quiver::new(1, &[(0, 0)]).unwrap();
    let relation = Relation::new(
        &quiver,
        field,
        terms
            .iter()
            .map(|&(c, n)| (field.elem(c), vec![ArrowId(0); n]))
            .collect(),
    )
    .expect("the terms are parallel words of length >= 2");
    Presentation::new(quiver, field, vec![relation]).expect("built over this quiver and field")
}

/// The witness of the admissibility defect. `x³ - x²` passes every
/// relation check and completes: the leading word is `x³`, its
/// automaton is acyclic, and the verifier reports a finite quotient of
/// dimension 3. The quotient is `k[x]/(x²) × k`, where the arrow ideal
/// `J = span(x, x²)` has `J² = J³ = span(x²)` and never reaches zero.
#[test]
fn a_stable_nonzero_arrow_ideal_is_rejected_as_non_admissible() {
    let presentation = loop_presentation(f5(), &[(1, 3), (-1, 2)]);
    assert_eq!(
        Algebra::new(presentation.clone(), &CompletionLimits::default()).unwrap_err(),
        AlgebraBuildError::NonAdmissible {
            stable_power: 2,
            dimension: 1,
        }
    );
    // The completion and the verifier both accept, so the reload path
    // needs the same check as `Algebra::new`.
    let certificate = match complete(&presentation, &CompletionLimits::default()) {
        Outcome::Complete(certificate) => certificate,
        Outcome::Truncated(diagnostics) => panic!("unexpected truncation: {diagnostics:?}"),
    };
    let verified = verify(&certificate.to_canonical_json()).expect("the certificate verifies");
    assert_eq!(verified.normal_words().len(), 3);
    assert_eq!(
        Algebra::from_verified(verified).unwrap_err(),
        AlgebraBuildError::NonAdmissible {
            stable_power: 2,
            dimension: 1,
        }
    );
}

/// Arrows `a: 0 → 1`, `b: 1 → 3`, `c: 0 → 2`, `d: 2 → 4`, `e: 4 → 3`,
/// and the relation `cde - ab`. The ideal is admissible, so the algebra
/// builds. Its nilpotency degree is 4 while the longest normal word has
/// length 2: `J³ = span(ab)` because `cd·e` rewrites to `ab`.
#[test]
fn an_admissible_inhomogeneous_presentation_builds() {
    let field = f5();
    let quiver = Quiver::new(5, &[(0, 1), (1, 3), (0, 2), (2, 4), (4, 3)]).unwrap();
    let relation = Relation::new(
        &quiver,
        field,
        vec![
            (field.one(), vec![ArrowId(2), ArrowId(3), ArrowId(4)]),
            (field.elem(-1), vec![ArrowId(0), ArrowId(1)]),
        ],
    )
    .unwrap();
    let presentation = Presentation::new(quiver, field, vec![relation]).unwrap();
    let a = Algebra::new(presentation, &CompletionLimits::default()).unwrap();
    assert_eq!(a.dim(), 13);
    assert_eq!(a.basis().iter().map(PathWord::len).max(), Some(2));
    assert_eq!(a.nilpotency_degree(), 4);
}

#[test]
fn a_certificate_about_another_presentation_is_rejected() {
    let field = f5();
    let a = loop_presentation(field, &[(1, 3)]);
    let b = loop_presentation(field, &[(1, 4)]);
    let built = Algebra::new(a.clone(), &CompletionLimits::default()).unwrap();
    assert_eq!(check_input_relations(&a, built.certificate()), Ok(()));
    assert_eq!(
        check_input_relations(&b, built.certificate()),
        Err(AlgebraBuildError::InputRelationsMismatch { index: 0 })
    );
    let empty = Presentation::new(Quiver::new(1, &[(0, 0)]).unwrap(), field, Vec::new()).unwrap();
    assert_eq!(
        check_input_relations(&empty, built.certificate()),
        Err(AlgebraBuildError::InputRelationsMismatch { index: 0 })
    );
}

#[test]
fn dual_numbers_has_basis_e_x() {
    let a = dual_numbers(f5());
    assert_eq!(a.dim(), 2);
    assert!(a.basis()[0].is_trivial());
    assert_eq!(a.basis()[1].arrows(), &[ArrowId(0)]);
}

#[test]
fn truncated_poly_3_has_dim_3() {
    let a = truncated_poly(3, f5()).unwrap();
    assert_eq!(a.dim(), 3);
    assert_eq!(a.basis()[2].len(), 2);
}

/// Regression pin: x^65 needs `max_word_len = 129` for its
/// self-overlap superpositions, above the default 64. The named
/// constructor derives adequate limits; the defaults truncate.
#[test]
fn truncated_poly_65_succeeds_with_derived_limits() {
    let a = truncated_poly(65, f5()).unwrap();
    assert_eq!(a.dim(), 65);
    assert_eq!(a.completion_limits().max_word_len, 129);
    let ideal = truncated_poly_ideal(65).unwrap();
    assert!(matches!(
        Algebra::new(
            monomial_presentation(&ideal, f5()),
            &CompletionLimits::default()
        ),
        Err(AlgebraBuildError::Truncated(diagnostics))
            if diagnostics.reason == crate::completion::TruncationReason::WordLenBudget
    ));
}

#[test]
fn monomial_limits_never_fall_below_the_defaults() {
    let ideal = truncated_poly_ideal(3).unwrap();
    assert_eq!(monomial_limits(&ideal), CompletionLimits::default());
    let long = truncated_poly_ideal(100).unwrap();
    let limits = monomial_limits(&long);
    assert_eq!(limits.max_word_len, 199);
    assert_eq!(limits.max_basis, CompletionLimits::default().max_basis);
    assert_eq!(limits.max_steps, CompletionLimits::default().max_steps);
}

#[test]
fn from_verified_keeps_default_limits_and_with_limits_stores_them() {
    let a = truncated_poly(65, f5()).unwrap();
    let bytes = a.certificate().to_canonical_json();
    let reloaded = Algebra::from_verified(verify(&bytes).unwrap()).unwrap();
    assert_eq!(reloaded.completion_limits(), &CompletionLimits::default());
    let raised = CompletionLimits {
        max_word_len: 129,
        ..CompletionLimits::default()
    };
    let preserved = Algebra::from_verified_with_limits(verify(&bytes).unwrap(), &raised).unwrap();
    assert_eq!(preserved.completion_limits(), &raised);
}

#[test]
fn truncated_poly_rejects_n_below_2() {
    assert!(matches!(
        truncated_poly(1, f5()),
        Err(AlgebraBuildError::Monomial(
            MonomialError::ForbiddenWordTooShort { index: 0, len: 1 }
        ))
    ));
}

#[test]
fn linear_a3_dim_and_cartan() {
    let a = linear_an(3, f5());
    assert_eq!(a.dim(), 6);
    // Row i is the dimension vector of P_i. Upper triangular because
    // paths run from lower to higher vertices.
    assert_eq!(
        a.cartan_matrix(),
        vec![vec![1, 1, 1], vec![0, 1, 1], vec![0, 0, 1]]
    );
}

#[test]
fn linear_a3_paths_between_counts() {
    let a = linear_an(3, f5());
    for u in 0..3 {
        for v in 0..3 {
            let expected = usize::from(u <= v);
            assert_eq!(a.paths_between(u, v).len(), expected, "({u}, {v})");
        }
    }
}

#[test]
fn a3_mod_ab_has_basis_without_ab() {
    let a = an_with_relations(3, &[(0, 2)], f5()).unwrap();
    assert_eq!(a.dim(), 5);
    for v in 0..3 {
        assert!(a.basis()[v as usize].is_trivial());
    }
    assert_eq!(a.path_index(&word(&a, &[0])), Ok(Some(3)));
    assert_eq!(a.path_index(&word(&a, &[1])), Ok(Some(4)));
    assert_eq!(a.path_index(&word(&a, &[0, 1])), Ok(None));
    assert_eq!(a.nf_word(&word(&a, &[0, 1])), Ok(Vec::new()));
}

#[test]
fn kronecker_2_has_dim_4() {
    let a = kronecker(2, f5());
    assert_eq!(a.dim(), 4);
    assert_eq!(a.cartan_matrix(), vec![vec![1, 2], vec![0, 1]]);
}

#[test]
fn linear_nakayama_3_2_1_is_path_algebra_a3() {
    let a = linear_nakayama(&[3, 2, 1], f5()).unwrap();
    assert_eq!(a.dim(), 6);
    assert!(a.relations().is_empty());
}

#[test]
fn linear_nakayama_2_2_1_is_a3_mod_ab() {
    let a = linear_nakayama(&[2, 2, 1], f5()).unwrap();
    assert_eq!(a.dim(), 5);
    assert_eq!(a.relations().len(), 1);
    assert_eq!(a.relations()[0].terms(), &[(f5().one(), word(&a, &[0, 1]))]);
}

#[test]
fn cyclic_nakayama_2_2_2_has_dim_6() {
    let a = cyclic_nakayama(&[2, 2, 2], f5()).unwrap();
    assert_eq!(a.dim(), 6);
}

#[test]
fn cyclic_nakayama_3_3_3_has_dim_9() {
    let a = cyclic_nakayama(&[3, 3, 3], f5()).unwrap();
    assert_eq!(a.dim(), 9);
}

#[test]
fn linear_kupisch_3_3_2_rejected() {
    assert!(matches!(
        linear_nakayama(&[3, 3, 2], f5()),
        Err(AlgebraBuildError::Monomial(
            MonomialError::InvalidKupisch { .. }
        ))
    ));
}

#[test]
fn linear_kupisch_drop_violation_rejected() {
    assert!(matches!(
        linear_nakayama(&[4, 2, 1], f5()),
        Err(AlgebraBuildError::Monomial(
            MonomialError::InvalidKupisch { .. }
        ))
    ));
}

#[test]
fn cyclic_kupisch_entry_below_2_rejected() {
    assert!(matches!(
        cyclic_nakayama(&[2, 1, 2], f5()),
        Err(AlgebraBuildError::Monomial(
            MonomialError::InvalidKupisch { .. }
        ))
    ));
}

#[test]
fn cyclic_kupisch_drop_violation_rejected() {
    assert!(matches!(
        cyclic_nakayama(&[4, 2, 2], f5()),
        Err(AlgebraBuildError::Monomial(
            MonomialError::InvalidKupisch { .. }
        ))
    ));
}

#[test]
fn pipeline_reports_infinite_dimension_with_a_witness() {
    let quiver = Quiver::new(1, &[(0, 0)]).unwrap();
    let presentation = Presentation::new(quiver, f5(), Vec::new()).unwrap();
    match Algebra::new(presentation, &CompletionLimits::default()) {
        Err(AlgebraBuildError::InfiniteDimensional { witness, .. }) => {
            assert!(!witness.cycle.is_empty());
        }
        other => panic!("expected InfiniteDimensional, got {other:?}"),
    }
}

#[test]
fn radical_square_zero_cycle_3_has_dim_6() {
    let a = radical_square_zero_cycle(3, f5());
    assert_eq!(a.dim(), 6);
    assert_eq!(a.paths_from(0).len(), 2); // e_0 and the arrow out of 0
}

#[test]
fn multiplication_tables_match_path_composition() {
    let a = linear_an(3, f5());
    let one = f5().one();
    let (ia, ib) = (ArrowId(0), ArrowId(1));
    let a_idx = a.path_index(&word(&a, &[0])).unwrap().unwrap();
    let ab_idx = a.path_index(&word(&a, &[0, 1])).unwrap().unwrap();
    assert_eq!(a.right_mul(a.vertex_idempotent(0), ia), &[(a_idx, one)]);
    assert_eq!(a.right_mul(a_idx, ib), &[(ab_idx, one)]);
    assert_eq!(
        a.left_mul(ia, a.path_index(&word(&a, &[1])).unwrap().unwrap()),
        &[(ab_idx, one)]
    );
    assert!(a.right_mul(a_idx, ia).is_empty()); // target(a) != source(a)
}

#[test]
fn multiplication_by_forbidden_extension_is_zero() {
    let a = an_with_relations(3, &[(0, 2)], f5()).unwrap();
    let a_idx = a.path_index(&word(&a, &[0])).unwrap().unwrap();
    assert!(a.right_mul(a_idx, ArrowId(1)).is_empty());
    let b_idx = a.path_index(&word(&a, &[1])).unwrap().unwrap();
    assert!(a.left_mul(ArrowId(0), b_idx).is_empty());
}

#[test]
fn basis_starts_with_trivial_paths_then_lengths_ascend() {
    let a = linear_an(3, f5());
    for v in 0..3u32 {
        let p = &a.basis()[a.vertex_idempotent(v)];
        assert!(p.is_trivial());
        assert_eq!(p.source(), v);
    }
    let lengths: Vec<usize> = a.basis().iter().map(PathWord::len).collect();
    assert_eq!(lengths, vec![0, 0, 0, 1, 1, 2]);
}

#[test]
fn an_zero_path_out_of_range_rejected() {
    assert!(matches!(
        an_with_relations(3, &[(1, 2)], f5()),
        Err(AlgebraBuildError::Monomial(
            MonomialError::ZeroPathOutOfRange { start: 1, len: 2 }
        ))
    ));
}

#[test]
fn paths_from_lists_projective_basis() {
    let a = an_with_relations(3, &[(0, 2)], f5()).unwrap();
    assert_eq!(a.paths_from(0), &[0, 3]); // P_0: e_0, a
    assert_eq!(a.paths_from(1), &[1, 4]); // P_1: e_1, b
    assert_eq!(a.paths_from(2), &[2]); // P_2: e_2
    assert_eq!(a.paths_to(2), &[2, 4]); // A e_2: e_2, b
}

/// The runtime pipeline and the field-free analysis agree on a monomial
/// ideal: normal words are standard paths, in the same order.
#[test]
fn normal_words_equal_the_standard_paths() {
    let quiver = Quiver::new(4, &[(0, 1), (1, 2), (1, 3)]).unwrap();
    let ideal = MonomialIdeal::new(quiver, vec![vec![ArrowId(0), ArrowId(1)]]).unwrap();
    let m = MonomialPresentation::new(ideal.clone()).unwrap();
    let a = monomial_algebra(&ideal, f5()).unwrap();
    assert_eq!(a.basis(), m.basis());
    assert_eq!(a.cartan_matrix(), m.cartan_matrix());
}

#[test]
fn commutative_square_identifies_the_two_diagonals() {
    let a = commutative_square(f5());
    assert_eq!(a.dim(), 9);
    // The larger word cd reduces to ab, the unique length-2 normal word.
    let ab = a.path_index(&word(&a, &[0, 1])).unwrap().unwrap();
    assert_eq!(a.path_index(&word(&a, &[2, 3])), Ok(None));
    assert_eq!(a.nf_word(&word(&a, &[2, 3])), Ok(vec![(ab, f5().one())]));
    let c_idx = a.path_index(&word(&a, &[2])).unwrap().unwrap();
    assert_eq!(a.right_mul(c_idx, ArrowId(3)), &[(ab, f5().one())]);
}

#[test]
fn mul_basis_composes_and_respects_endpoints() {
    let a = commutative_square(f5());
    let c_idx = a.path_index(&word(&a, &[2])).unwrap().unwrap();
    let d_idx = a.path_index(&word(&a, &[3])).unwrap().unwrap();
    let ab = a.path_index(&word(&a, &[0, 1])).unwrap().unwrap();
    assert_eq!(a.mul_basis(c_idx, d_idx), vec![(ab, f5().one())]);
    assert_eq!(a.mul_basis(d_idx, c_idx), Vec::new());
    assert_eq!(
        a.mul_basis(a.vertex_idempotent(0), c_idx),
        vec![(c_idx, f5().one())]
    );
    assert_eq!(a.mul_basis(c_idx, a.vertex_idempotent(3)), Vec::new());
}

#[test]
fn certificate_round_trips_through_verify() {
    let a = commutative_square(f5());
    let bytes = a.certificate().to_canonical_json();
    let verified = verify(&bytes).expect("the stored certificate verifies");
    let rebuilt = Algebra::from_verified(verified).expect("the ideal is admissible");
    assert_eq!(rebuilt.dim(), a.dim());
    assert_eq!(rebuilt.basis(), a.basis());
    assert_eq!(rebuilt.relations(), a.relations());
}

#[test]
fn nilpotency_degree_matches_loewy_structure() {
    let f = f5();
    assert_eq!(linear_an(3, f).nilpotency_degree(), 3);
    assert_eq!(dual_numbers(f).nilpotency_degree(), 2);
    assert_eq!(truncated_poly(4, f).unwrap().nilpotency_degree(), 4);
    assert_eq!(radical_square_zero_cycle(3, f).nilpotency_degree(), 2);
    assert_eq!(commutative_square(f).nilpotency_degree(), 3);
}

#[test]
fn radical_power_matrices_descend_by_row_space_iteration() {
    let f = f5();
    let a = linear_an(3, f);
    let rank = |u, v, k| a.radical_power_matrix(u, v, k).rows();
    // e_0 A e_2 is one-dimensional (the word ab), which lies in J and J².
    assert_eq!(rank(0, 2, 0), 1);
    assert_eq!(rank(0, 2, 1), 1);
    assert_eq!(rank(0, 2, 2), 1);
    assert_eq!(rank(0, 2, 3), 0);
    // e_0 A e_1 is the arrow a: in J but not in J².
    assert_eq!(rank(0, 1, 1), 1);
    assert_eq!(rank(0, 1, 2), 0);
    // The trivial component at a vertex leaves J immediately.
    assert_eq!(rank(0, 0, 0), 1);
    assert_eq!(rank(0, 0, 1), 0);
}

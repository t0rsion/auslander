use std::sync::Arc;

use super::{ElementMatrix, OppositeError, dual, dual_morphism, nu_of_presentation_map, opposite};
use crate::algebra::{
    Algebra, an_with_relations, commutative_square, cyclic_nakayama, dual_numbers, kronecker,
    linear_an, radical_square_zero_cycle,
};
use crate::field::{Fp, PrimeField};
use crate::hom::{hom, identity, kernel};
use crate::linalg::DenseMat;
use crate::module::{Module, same_representation};
use crate::quiver::{ArrowId, PathWord, Quiver};
use crate::relation::{Presentation, Relation};

fn f5() -> PrimeField {
    PrimeField::new(5).unwrap()
}

fn mat(field: &PrimeField, rows: &[&[i64]]) -> DenseMat {
    let rows: Vec<Vec<Fp>> = rows
        .iter()
        .map(|r| r.iter().map(|&v| field.elem(v)).collect())
        .collect();
    DenseMat::from_rows(&rows)
}

#[test]
fn opposite_reverses_arrows_and_keeps_ids() {
    let a = linear_an(3, f5());
    let op = opposite(&a).unwrap();
    assert_eq!(op.opposite().quiver().arrows(), &[(1, 0), (2, 1)]);
    assert_eq!(op.arrow_to_op(ArrowId(1)), ArrowId(1));
    assert_eq!(op.arrow_from_op(ArrowId(0)), ArrowId(0));
}

#[test]
fn opposite_reverses_relation_words() {
    let a = an_with_relations(3, &[(0, 2)], f5()).unwrap();
    let op = opposite(&a).unwrap();
    let relations = op.opposite().relations();
    assert_eq!(relations.len(), 1);
    assert_eq!(
        relations[0].terms()[0].1.arrows(),
        &[ArrowId(1), ArrowId(0)]
    );
}

/// x^65 as a general relation needs `max_word_len = 129`; the default
/// 64 truncates. The opposite recompletes the reversed relation with the
/// limits stored on the algebra, so it inherits the raised budget.
/// Rebuilding the same algebra from its certificate with `from_verified`
/// resets to the defaults by policy, and there the opposite truncates.
#[test]
fn opposite_and_tau_inherit_raised_completion_limits() {
    use crate::algebra::AlgebraBuildError;
    use crate::ar::tau;
    use crate::completion::CompletionLimits;
    use crate::verify::verify;
    let field = f5();
    let quiver = Quiver::new(1, &[(0, 0)]).unwrap();
    let relation =
        Relation::new(&quiver, field, vec![(field.one(), vec![ArrowId(0); 65])]).unwrap();
    let presentation = Presentation::new(quiver, field, vec![relation]).unwrap();
    let raised = CompletionLimits {
        max_word_len: 129,
        ..CompletionLimits::default()
    };
    let a = Algebra::new(presentation, &raised).unwrap();
    assert_eq!(a.dim(), 65);
    let op = opposite(&a).unwrap();
    assert_eq!(op.opposite().dim(), 65);
    assert_eq!(op.opposite().completion_limits(), &raised);
    // Over the symmetric algebra k[x]/(x^65), tau = Omega^2 and
    // Omega(k[x]/(x)) = k[x]/(x^64), so tau S = S.
    assert_eq!(tau(&Module::simple(&a, 0)).unwrap().dim_vector(), &[1]);
    let defaults = Algebra::from_verified(verify(&a.certificate().to_canonical_json()).unwrap())
        .expect("x^65 is admissible");
    assert!(matches!(
        opposite(&defaults),
        Err(AlgebraBuildError::Truncated(_))
    ));
}

#[test]
fn opposite_preserves_dimension() {
    for a in [
        linear_an(4, f5()),
        an_with_relations(3, &[(0, 2)], f5()).unwrap(),
        kronecker(3, f5()),
        dual_numbers(f5()),
        cyclic_nakayama(&[3, 3, 3], f5()).unwrap(),
        radical_square_zero_cycle(3, f5()),
        commutative_square(f5()),
    ] {
        assert_eq!(opposite(&a).unwrap().opposite().dim(), a.dim());
    }
}

#[test]
fn opposite_of_the_opposite_restores_quiver_and_relations() {
    for a in [
        linear_an(3, f5()),
        an_with_relations(3, &[(0, 2)], f5()).unwrap(),
        cyclic_nakayama(&[3, 3, 3], f5()).unwrap(),
        commutative_square(f5()),
    ] {
        let double = opposite(opposite(&a).unwrap().opposite()).unwrap();
        assert_eq!(double.opposite().quiver(), a.quiver());
        assert_eq!(double.opposite().relations(), a.relations());
    }
}

#[test]
fn word_to_op_reverses_the_arrow_word_and_round_trips() {
    let a = linear_an(3, f5());
    let op = opposite(&a).unwrap();
    let word = PathWord::from_arrows(a.quiver(), &[ArrowId(0), ArrowId(1)]).unwrap();
    let rev = op.word_to_op(&word).unwrap();
    assert_eq!(rev.arrows(), &[ArrowId(1), ArrowId(0)]);
    assert_eq!((rev.source(), rev.target()), (2, 0));
    assert_eq!(op.word_from_op(&rev).unwrap(), word);
    let trivial = PathWord::trivial(a.quiver(), 1).unwrap();
    assert_eq!(op.word_to_op(&trivial).unwrap(), trivial);
}

#[test]
fn word_to_op_rejects_words_from_the_other_side() {
    let a = linear_an(3, f5());
    let op = opposite(&a).unwrap();
    let backwards =
        PathWord::from_arrows(op.opposite().quiver(), &[ArrowId(1), ArrowId(0)]).unwrap();
    assert!(op.word_to_op(&backwards).is_err());
    assert!(op.word_from_op(&backwards).is_ok());
}

#[test]
fn dual_transposes_each_arrow_matrix() {
    let a = dual_numbers(f5());
    let field = f5();
    let m = Module::new(a.clone(), vec![2], vec![mat(&field, &[&[0, 1], &[0, 0]])]).unwrap();
    let op = opposite(&a).unwrap();
    let d = dual(&m, &op).unwrap();
    assert!(Arc::ptr_eq(d.algebra(), op.opposite()));
    assert_eq!(d.dim_vector(), m.dim_vector());
    assert_eq!(*d.map(ArrowId(0)), m.map(ArrowId(0)).transpose());
}

#[test]
fn dual_of_a_module_over_the_opposite_lands_back_over_the_algebra() {
    let a = linear_an(3, f5());
    let op = opposite(&a).unwrap();
    let m = Module::projective(op.opposite(), 0);
    let d = dual(&m, &op).unwrap();
    assert!(Arc::ptr_eq(d.algebra(), &a));
}

#[test]
fn dual_rejects_a_module_outside_the_pair() {
    let a = linear_an(3, f5());
    let other = linear_an(3, f5());
    let op = opposite(&a).unwrap();
    let m = Module::simple(&other, 0);
    assert_eq!(
        dual(&m, &op).unwrap_err(),
        OppositeError::AlgebraOutsidePair
    );
}

#[test]
fn double_dual_is_the_identity_entry_for_entry() {
    let a = an_with_relations(3, &[(0, 2)], f5()).unwrap();
    let op = opposite(&a).unwrap();
    for v in 0..3 {
        for m in [
            Module::simple(&a, v),
            Module::projective(&a, v),
            Module::injective(&a, v),
        ] {
            let dd = dual(&dual(&m, &op).unwrap(), &op).unwrap();
            assert!(same_representation(&dd, &m), "D(D(M)) != M at vertex {v}");
        }
    }
}

#[test]
fn dual_of_the_identity_is_the_identity() {
    let a = linear_an(3, f5());
    let op = opposite(&a).unwrap();
    let p0 = Module::projective(&a, 0);
    let dp0 = dual(&p0, &op).unwrap();
    let d_id = dual_morphism(&identity(&p0), &dp0, &dp0, &op).unwrap();
    assert_eq!(d_id, identity(&dp0));
}

#[test]
fn dual_morphism_transposes_vertex_matrices() {
    let a = linear_an(3, f5());
    let op = opposite(&a).unwrap();
    let p1 = Module::projective(&a, 1);
    let p0 = Module::projective(&a, 0);
    let f = hom(&p1, &p0).unwrap().remove(0);
    let dp1 = dual(&p1, &op).unwrap();
    let dp0 = dual(&p0, &op).unwrap();
    let df = dual_morphism(&f, &dp0, &dp1, &op).unwrap();
    for v in 0..3 {
        assert_eq!(*df.map_at(v), f.map_at(v).transpose());
    }
    assert!(df.source().ptr_eq(&dp0));
    assert!(df.target().ptr_eq(&dp1));
}

#[test]
fn dual_morphism_is_contravariant_on_a_composition() {
    // Hom runs down the arrows: f: P_2 → P_1, g: P_1 → P_0.
    let a = linear_an(3, f5());
    let op = opposite(&a).unwrap();
    let p2 = Module::projective(&a, 2);
    let p1 = Module::projective(&a, 1);
    let p0 = Module::projective(&a, 0);
    let f = hom(&p2, &p1).unwrap().remove(0);
    let g = hom(&p1, &p0).unwrap().remove(0);
    let d2 = dual(&p2, &op).unwrap();
    let d1 = dual(&p1, &op).unwrap();
    let d0 = dual(&p0, &op).unwrap();
    let left = dual_morphism(&f.then(&g).unwrap(), &d0, &d2, &op).unwrap();
    let right = dual_morphism(&g, &d0, &d1, &op)
        .unwrap()
        .then(&dual_morphism(&f, &d1, &d2, &op).unwrap())
        .unwrap();
    assert!(!left.is_zero());
    assert_eq!(left, right);
}

#[test]
fn dual_morphism_rejects_a_wrong_dual() {
    let a = linear_an(3, f5());
    let op = opposite(&a).unwrap();
    let p0 = Module::projective(&a, 0);
    let f = identity(&p0);
    let dp0 = dual(&p0, &op).unwrap();
    let wrong = Module::simple(op.opposite(), 0);
    assert_eq!(
        dual_morphism(&f, &wrong, &dp0, &op).unwrap_err(),
        OppositeError::NotDualOfTarget
    );
    assert_eq!(
        dual_morphism(&f, &dp0, &wrong, &op).unwrap_err(),
        OppositeError::NotDualOfSource
    );
}

#[test]
fn element_matrix_new_rejects_shape_and_canonicity_violations() {
    let a = linear_an(3, f5());
    assert_eq!(
        ElementMatrix::new(a.clone(), vec![3], Vec::new(), vec![Vec::new()]).unwrap_err(),
        OppositeError::SummandOutOfRange {
            vertex: 3,
            num_vertices: 3
        }
    );
    assert_eq!(
        ElementMatrix::new(a.clone(), vec![0], vec![0], Vec::new()).unwrap_err(),
        OppositeError::RowCountMismatch {
            expected: 1,
            got: 0
        }
    );
    assert_eq!(
        ElementMatrix::new(a.clone(), vec![0], vec![0], vec![Vec::new()]).unwrap_err(),
        OppositeError::ColumnCountMismatch {
            row: 0,
            expected: 1,
            got: 0
        }
    );
    assert_eq!(
        ElementMatrix::new(a.clone(), vec![0], vec![0], vec![vec![Vec::new()]]).unwrap_err(),
        OppositeError::CoefficientCountMismatch {
            row: 0,
            col: 0,
            expected: 1,
            got: 0
        }
    );
    let f7 = PrimeField::new(7).unwrap();
    assert_eq!(
        ElementMatrix::new(a, vec![0], vec![0], vec![vec![vec![f7.elem(6)]]]).unwrap_err(),
        OppositeError::NonCanonicalCoefficient {
            row: 0,
            col: 0,
            index: 0
        }
    );
}

#[test]
fn element_matrix_realizes_left_multiplication() {
    // Hom(P_1, P_0) over A_3 is spanned by left multiplication by the arrow
    // a, sending e_1 ↦ a and b ↦ ab.
    let a = linear_an(3, f5());
    let em = ElementMatrix::new(a, vec![1], vec![0], vec![vec![vec![f5().one()]]]).unwrap();
    let f = em.morphism();
    assert_eq!(f.source().dim_vector(), &[0, 1, 1]);
    assert_eq!(f.target().dim_vector(), &[1, 1, 1]);
    assert_eq!(*f.map_at(0), DenseMat::zero(0, 1));
    assert_eq!(*f.map_at(1), DenseMat::identity(1));
    assert_eq!(*f.map_at(2), DenseMat::identity(1));
}

#[test]
fn element_matrix_of_morphism_round_trips() {
    let a = an_with_relations(3, &[(0, 2)], f5()).unwrap();
    let field = f5();
    let em = ElementMatrix::new(a, vec![1], vec![0], vec![vec![vec![field.elem(3)]]]).unwrap();
    let back = ElementMatrix::of_morphism(&em.morphism(), &[1], &[0]).unwrap();
    assert_eq!(back.sources(), &[1]);
    assert_eq!(back.targets(), &[0]);
    assert_eq!(back.entry(0, 0), &[field.elem(3)]);
}

#[test]
fn of_morphism_recovers_a_two_summand_matrix() {
    let a = kronecker(2, f5());
    let field = f5();
    let entries = vec![
        vec![vec![field.elem(1), field.elem(2)]],
        vec![vec![field.elem(3), field.elem(4)]],
    ];
    let em = ElementMatrix::new(a, vec![1, 1], vec![0], entries.clone()).unwrap();
    let back = ElementMatrix::of_morphism(&em.morphism(), &[1, 1], &[0]).unwrap();
    assert_eq!(back.entry(0, 0), entries[0][0].as_slice());
    assert_eq!(back.entry(1, 0), entries[1][0].as_slice());
}

#[test]
fn of_morphism_rejects_endpoints_that_are_not_the_declared_sums() {
    let a = linear_an(3, f5());
    let p0 = Module::projective(&a, 0);
    let f = identity(&p0);
    assert_eq!(
        ElementMatrix::of_morphism(&f, &[1], &[0]).unwrap_err(),
        OppositeError::SourceNotTheDeclaredSum
    );
    assert_eq!(
        ElementMatrix::of_morphism(&f, &[0], &[1]).unwrap_err(),
        OppositeError::TargetNotTheDeclaredSum
    );
}

#[test]
fn transpose_over_swaps_summands_and_reverses_words() {
    let a = linear_an(3, f5());
    let field = f5();
    let op = opposite(&a).unwrap();
    // x = ab ∈ e_0 A e_2, the map P_2 → P_0.
    let em =
        ElementMatrix::new(a.clone(), vec![2], vec![0], vec![vec![vec![field.one()]]]).unwrap();
    let t = em.transpose_over(&op).unwrap();
    assert!(Arc::ptr_eq(t.algebra(), op.opposite()));
    assert_eq!(t.sources(), &[0]);
    assert_eq!(t.targets(), &[2]);
    assert_eq!(t.entry(0, 0), &[field.one()]);
    let back = t.transpose_over(&op).unwrap();
    assert!(Arc::ptr_eq(back.algebra(), &a));
    assert_eq!(back.sources(), em.sources());
    assert_eq!(back.targets(), em.targets());
    assert_eq!(back.entry(0, 0), em.entry(0, 0));
}

#[test]
fn transpose_over_expands_a_reversed_non_normal_word() {
    // A commutative square with permuted arrow ids: a = 0: 0 → 1,
    // d = 1: 2 → 3, c = 2: 0 → 2, b = 3: 1 → 3, relation ab - cd. The
    // normal length-2 word is ab = [0, 3], but its reversal [3, 0] is the
    // Groebner leading word on the opposite side, so it is not normal
    // there. The transpose must expand it to the opposite normal form,
    // and transposing back must restore the entry.
    use crate::completion::CompletionLimits;
    let field = f5();
    let quiver = Quiver::new(4, &[(0, 1), (2, 3), (0, 2), (1, 3)]).unwrap();
    let relation = Relation::new(
        &quiver,
        field,
        vec![
            (field.one(), vec![ArrowId(0), ArrowId(3)]),
            (field.elem(-1), vec![ArrowId(2), ArrowId(1)]),
        ],
    )
    .unwrap();
    let presentation = Presentation::new(quiver, field, vec![relation]).unwrap();
    let a = Algebra::new(presentation, &CompletionLimits::default()).unwrap();
    let ab = PathWord::from_arrows(a.quiver(), &[ArrowId(0), ArrowId(3)]).unwrap();
    assert!(a.path_index(&ab).unwrap().is_some(), "ab is normal");
    let op = opposite(&a).unwrap();
    let rev_ab = PathWord::from_arrows(op.opposite().quiver(), &[ArrowId(3), ArrowId(0)]).unwrap();
    assert_eq!(
        op.opposite().path_index(&rev_ab).unwrap(),
        None,
        "the reversal of the normal word is not normal on the opposite side"
    );
    let em =
        ElementMatrix::new(a.clone(), vec![3], vec![0], vec![vec![vec![field.elem(2)]]]).unwrap();
    let t = em.transpose_over(&op).unwrap();
    assert_eq!(t.entry(0, 0), &[field.elem(2)]);
    let back = t.transpose_over(&op).unwrap();
    assert_eq!(back.entry(0, 0), em.entry(0, 0));
}

#[test]
fn nu_of_the_identity_on_p_v_is_the_identity_on_i_v() {
    let a = an_with_relations(3, &[(0, 2)], f5()).unwrap();
    let field = f5();
    for v in 0..3u32 {
        let component = a.paths_between(v, v);
        let mut coefficients = vec![field.zero(); component.len()];
        let position = component
            .iter()
            .position(|&b| b == a.vertex_idempotent(v))
            .expect("the trivial path lies in its own component");
        coefficients[position] = field.one();
        let em = ElementMatrix::new(a.clone(), vec![v], vec![v], vec![vec![coefficients]]).unwrap();
        let nu = nu_of_presentation_map(&em);
        let injective = Module::injective(&a, v);
        assert!(
            same_representation(nu.source(), &injective),
            "ν(P_{v}) source"
        );
        assert!(
            same_representation(nu.target(), &injective),
            "ν(P_{v}) target"
        );
        for w in 0..3 {
            assert_eq!(*nu.map_at(w), DenseMat::identity(injective.dim_at(w)));
        }
    }
}

#[test]
fn nu_kernel_of_the_a3_presentation_of_s0_is_s1() {
    // d_1 for S_0 over A_3 is left multiplication by a: P_1 → P_0. The
    // kernel of ν(d_1): I_1 → I_0 is the AR translate τ S_0 = S_1.
    let a = linear_an(3, f5());
    let em = ElementMatrix::new(a, vec![1], vec![0], vec![vec![vec![f5().one()]]]).unwrap();
    let nu = nu_of_presentation_map(&em);
    assert_eq!(nu.source().dim_vector(), &[1, 1, 0]);
    assert_eq!(nu.target().dim_vector(), &[1, 0, 0]);
    let (ker, _) = kernel(&nu);
    assert_eq!(ker.dim_vector(), &[0, 1, 0]);
}

#[test]
fn nu_of_an_empty_source_is_a_map_from_the_zero_module() {
    let a = linear_an(3, f5());
    let em = ElementMatrix::new(a.clone(), Vec::new(), vec![2], Vec::new()).unwrap();
    let nu = nu_of_presentation_map(&em);
    assert!(nu.source().is_zero());
    assert_eq!(
        nu.target().dim_vector(),
        Module::injective(&a, 2).dim_vector()
    );
    let (ker, _) = kernel(&nu);
    assert!(ker.is_zero());
}

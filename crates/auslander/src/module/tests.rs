use super::*;
use crate::algebra::{
    an_with_relations, commutative_square, cyclic_nakayama, dual_numbers, linear_an,
};
use crate::hom::{identity, zero_morphism};

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
fn invertible_loop_action_is_rejected() {
    let a = dual_numbers(f5());
    let result = Module::new(a, vec![1], vec![mat(&f5(), &[&[1]])]);
    assert_eq!(
        result.unwrap_err(),
        ModuleError::RelationActsNonzero { index: 0 }
    );
}

#[test]
fn nilpotent_loop_action_is_accepted() {
    let a = dual_numbers(f5());
    let m = Module::new(a, vec![2], vec![mat(&f5(), &[&[0, 1], &[0, 0]])]).unwrap();
    assert_eq!(m.total_dim(), 2);
    assert!(!m.is_zero());
}

#[test]
fn commutative_square_relation_is_enforced() {
    // One-dimensional everywhere; ab acts as 1. The relation ab - cd
    // rejects cd acting as 0 and accepts cd acting as 1.
    let a = commutative_square(f5());
    let one = mat(&f5(), &[&[1]]);
    let zero = mat(&f5(), &[&[0]]);
    let rejected = Module::new(
        a.clone(),
        vec![1, 1, 1, 1],
        vec![one.clone(), one.clone(), one.clone(), zero],
    );
    assert_eq!(
        rejected.unwrap_err(),
        ModuleError::RelationActsNonzero { index: 0 }
    );
    let accepted = Module::new(
        a,
        vec![1, 1, 1, 1],
        vec![one.clone(), one.clone(), one.clone(), one],
    );
    assert!(accepted.is_ok());
}

#[test]
fn wrong_dims_length_is_rejected() {
    let a = linear_an(3, f5());
    let result = Module::new(a, vec![1, 1], vec![DenseMat::zero(1, 1); 2]);
    assert_eq!(
        result.unwrap_err(),
        ModuleError::DimsLengthMismatch {
            expected: 3,
            got: 2
        }
    );
}

#[test]
fn wrong_map_shape_is_rejected() {
    let a = linear_an(3, f5());
    let maps = vec![DenseMat::zero(1, 1), DenseMat::zero(2, 1)];
    let result = Module::new(a, vec![1, 1, 1], maps);
    assert_eq!(
        result.unwrap_err(),
        ModuleError::MapShapeMismatch {
            arrow: ArrowId(1),
            expected: (1, 1),
            got: (2, 1)
        }
    );
}

#[test]
fn zero_module_has_dimension_zero() {
    let a = linear_an(3, f5());
    let z = Module::zero(&a);
    assert!(z.is_zero());
    assert_eq!(z.total_dim(), 0);
    assert_eq!(z.dim_vector(), &[0, 0, 0]);
}

#[test]
fn word_action_multiplies_arrow_matrices_in_word_order() {
    let a = linear_an(3, f5());
    let field = f5();
    let p0 = Module::projective(&a, 0);
    let word =
        PathWord::from_arrows(a.quiver(), &[ArrowId(0), ArrowId(1)]).expect("path a·b in A_3");
    let expected = p0.map(ArrowId(0)).mul(p0.map(ArrowId(1)), &field);
    assert_eq!(p0.word_action(&word), Ok(expected));
    let trivial = PathWord::trivial(a.quiver(), 0).unwrap();
    assert_eq!(p0.word_action(&trivial), Ok(DenseMat::identity(1)));
}

#[test]
fn word_action_rejects_a_word_from_another_quiver() {
    let a = linear_an(3, f5());
    let other = dual_numbers(f5());
    let p0 = Module::projective(&a, 0);
    let word = PathWord::from_arrows(other.quiver(), &[ArrowId(0)]).unwrap();
    assert_eq!(
        p0.word_action(&word),
        Err(QuiverError::EndpointsDisagree {
            stored: (0, 0),
            computed: (0, 1),
        })
    );
}

#[test]
fn element_action_sums_scaled_word_actions() {
    let field = f5();
    let a = commutative_square(field);
    let p0 = Module::projective(&a, 0);
    let ab = a
        .path_index(&PathWord::from_arrows(a.quiver(), &[ArrowId(0), ArrowId(1)]).unwrap())
        .unwrap()
        .unwrap();
    let action = p0.element_action(&[(ab, field.elem(3))]);
    let word_mat = p0.word_action(&a.basis()[ab]).expect("basis word is valid");
    for r in 0..action.rows() {
        for c in 0..action.cols() {
            assert_eq!(
                action.get(r, c),
                field.mul(field.elem(3), word_mat.get(r, c))
            );
        }
    }
}

#[test]
#[should_panic(expected = "mix sources")]
fn element_action_rejects_mixed_endpoints() {
    let a = linear_an(3, f5());
    let p0 = Module::projective(&a, 0);
    p0.element_action(&[(0, f5().one()), (1, f5().one())]);
}

#[test]
fn non_canonical_entry_is_rejected_before_relation_checks() {
    // The entry 3 is canonical in F_5 but not in F_2; over F_2 the loop's square
    // would also violate x² = 0, and the canonicity error must win.
    let a = dual_numbers(PrimeField::new(2).unwrap());
    let maps = vec![mat(&f5(), &[&[3]])];
    assert_eq!(
        Module::new(a, vec![1], maps).unwrap_err(),
        ModuleError::NonCanonicalEntry {
            arrow: ArrowId(0),
            row: 0,
            col: 0,
        }
    );
}

#[test]
fn simple_is_one_dimensional_at_its_vertex() {
    let a = an_with_relations(3, &[(0, 2)], f5()).unwrap();
    for v in 0..3 {
        let s = Module::simple(&a, v);
        let expected: Vec<usize> = (0..3).map(|w| usize::from(w == v as usize)).collect();
        assert_eq!(s.dim_vector(), expected.as_slice());
    }
}

// Cartan orientation: c[i][j] = dim e_i A e_j, so row i is the dimension vector of
// P_i = e_i A and column j is the dimension vector of I_j = D(A e_j).
#[test]
fn projective_dim_vectors_are_cartan_rows() {
    for algebra in [
        linear_an(3, f5()),
        an_with_relations(3, &[(0, 2)], f5()).unwrap(),
        cyclic_nakayama(&[2, 2, 2], f5()).unwrap(),
        commutative_square(f5()),
    ] {
        let cartan = algebra.cartan_matrix();
        for v in 0..algebra.quiver().num_vertices() {
            let p = Module::projective(&algebra, v);
            assert_eq!(p.dim_vector(), cartan[v as usize].as_slice(), "P_{v}");
        }
    }
}

#[test]
fn injective_dim_vectors_are_cartan_columns() {
    for algebra in [
        linear_an(3, f5()),
        an_with_relations(3, &[(0, 2)], f5()).unwrap(),
        cyclic_nakayama(&[2, 2, 2], f5()).unwrap(),
        commutative_square(f5()),
    ] {
        let cartan = algebra.cartan_matrix();
        for v in 0..algebra.quiver().num_vertices() {
            let i = Module::injective(&algebra, v);
            let column: Vec<usize> = cartan.iter().map(|row| row[v as usize]).collect();
            assert_eq!(i.dim_vector(), column.as_slice(), "I_{v}");
        }
    }
}

#[test]
fn a3_mod_ab_projective_p0_has_dimension_vector_1_1_0() {
    let a = an_with_relations(3, &[(0, 2)], f5()).unwrap();
    let p0 = Module::projective(&a, 0);
    assert_eq!(p0.dim_vector(), &[1, 1, 0]);
}

#[test]
fn direct_sum_projections_split_inclusions() {
    let a = linear_an(3, f5());
    let p0 = Module::projective(&a, 0);
    let p1 = Module::projective(&a, 1);
    let s2 = Module::simple(&a, 2);
    let parts = [&p0, &p1, &s2];
    let (sum, inclusions, projections) = direct_sum(&parts);
    for v in 0..3 {
        assert_eq!(
            sum.dim_at(v),
            parts.iter().map(|m| m.dim_at(v)).sum::<usize>()
        );
    }
    for (k, part) in parts.iter().enumerate() {
        assert_eq!(
            inclusions[k].then(&projections[k]).unwrap(),
            identity(part),
            "π_{k} ∘ ι_{k}"
        );
        for (j, other) in parts.iter().enumerate() {
            if j != k {
                assert_eq!(
                    inclusions[j].then(&projections[k]).unwrap(),
                    zero_morphism(other, part).unwrap(),
                    "π_{k} ∘ ι_{j}"
                );
            }
        }
    }
}

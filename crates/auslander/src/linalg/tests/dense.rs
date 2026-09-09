use super::support::{dense, f};
use crate::linalg::DenseMat;

#[test]
fn dense_get_set_round_trip() {
    let fp = f(7);
    let mut m = DenseMat::zero(2, 3);
    m.set(1, 2, fp.elem(5));
    assert_eq!(m.get(1, 2), fp.elem(5));
    assert_eq!(m.get(0, 0), fp.zero());
    assert_eq!(m.row(1), &[fp.zero(), fp.zero(), fp.elem(5)]);
}

#[test]
fn dense_mul_matches_hand_computation() {
    let fp = f(7);
    let a = dense(&fp, &[&[1, 2], &[3, 4]]);
    let b = dense(&fp, &[&[5, 6], &[0, 1]]);
    assert_eq!(a.mul(&b, &fp), dense(&fp, &[&[5, 1], &[1, 1]]));
    let id = DenseMat::identity(2);
    assert_eq!(a.mul(&id, &fp), a);
    assert_eq!(id.mul(&a, &fp), a);
}

#[test]
#[should_panic(expected = "mul:")]
fn dense_mul_panics_on_shape_mismatch() {
    let fp = f(7);
    let a = DenseMat::zero(2, 3);
    let b = DenseMat::zero(2, 3);
    let _ = a.mul(&b, &fp);
}

#[test]
fn dense_add_is_entrywise() {
    let fp = f(7);
    let a = dense(&fp, &[&[1, 6], &[2, 3]]);
    let b = dense(&fp, &[&[6, 3], &[0, 5]]);
    assert_eq!(a.add(&b, &fp), dense(&fp, &[&[0, 2], &[2, 1]]));
}

#[test]
fn dense_transpose_is_an_involution() {
    let fp = f(7);
    let a = dense(&fp, &[&[1, 2, 3], &[4, 5, 6]]);
    let t = a.transpose();
    assert_eq!(t.rows(), 3);
    assert_eq!(t.cols(), 2);
    assert_eq!(t.get(2, 1), fp.elem(6));
    assert_eq!(t.transpose(), a);
}

#[test]
fn dense_rref_of_a_singular_matrix_is_canonical() {
    let fp = f(101);
    let a = dense(&fp, &[&[1, 2, 3], &[4, 5, 6], &[7, 8, 9]]);
    let (r, pivots) = a.rref(&fp);
    assert_eq!(pivots, vec![0, 1]);
    assert_eq!(r, dense(&fp, &[&[1, 0, -1], &[0, 1, 2], &[0, 0, 0]]));
    assert_eq!(a.rank(&fp), 2);
}

#[test]
fn dense_solve_returns_the_unique_solution() {
    let fp = f(7);
    let a = dense(&fp, &[&[1, 2], &[3, 4]]);
    let b = vec![fp.elem(5), fp.elem(6)];
    let x = a.solve(&b, &fp).unwrap();
    assert_eq!(x, vec![fp.elem(3), fp.elem(1)]);
    assert_eq!(a.mul_vec(&x, &fp), b);
}

#[test]
fn dense_solve_sets_free_variables_to_zero() {
    let fp = f(7);
    let a = dense(&fp, &[&[1, 1]]);
    let x = a.solve(&[fp.elem(1)], &fp).unwrap();
    assert_eq!(x, vec![fp.elem(1), fp.zero()]);
}

#[test]
fn dense_solve_detects_inconsistency() {
    let fp = f(7);
    let a = dense(&fp, &[&[1, 1], &[1, 1]]);
    assert!(a.solve(&[fp.elem(1), fp.elem(2)], &fp).is_none());
    assert!(a.solve(&[fp.elem(1), fp.elem(1)], &fp).is_some());
}

#[test]
fn dense_kernel_spans_the_null_space() {
    let fp = f(7);
    let a = dense(&fp, &[&[1, 2], &[2, 4]]);
    let k = a.kernel_basis(&fp);
    assert_eq!(k.rows(), 1);
    assert_eq!(k.mul(&a.transpose(), &fp), DenseMat::zero(1, 2));
    assert_eq!(DenseMat::identity(3).kernel_basis(&fp).rows(), 0);
}

#[test]
fn dense_kernel_of_a_zero_matrix_is_the_identity() {
    let fp = f(5);
    assert_eq!(
        DenseMat::zero(2, 3).kernel_basis(&fp),
        DenseMat::identity(3)
    );
}

#[test]
fn dense_row_space_basis_lies_in_the_row_space() {
    let fp = f(7);
    let a = dense(&fp, &[&[1, 2, 3], &[2, 4, 6], &[0, 1, 1]]);
    let basis = a.row_space_basis(&fp);
    assert_eq!(basis.rows(), a.rank(&fp));
    let at = a.transpose();
    for r in 0..basis.rows() {
        assert!(at.solve(basis.row(r), &fp).is_some());
    }
}

#[test]
fn dense_image_basis_spans_the_column_space() {
    let fp = f(7);
    let a = dense(&fp, &[&[1, 0], &[0, 0], &[3, 0]]);
    let basis = a.image_basis(&fp);
    assert_eq!(basis.rows(), 1);
    for r in 0..basis.rows() {
        assert!(
            a.solve(basis.row(r), &fp).is_some(),
            "basis vector outside the image"
        );
    }
}

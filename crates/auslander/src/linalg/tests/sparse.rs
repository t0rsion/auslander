use super::support::{dense, dense_vec, f, sparse_vec};
use crate::linalg::SparseRow;

#[test]
fn sparse_row_from_entries_merges_duplicates() {
    let fp = f(7);
    let row = SparseRow::from_entries(vec![(2, fp.elem(5)), (0, fp.elem(3)), (0, fp.elem(4))], &fp);
    assert_eq!(row.nnz(), 1);
    assert_eq!(row.get(0), fp.zero());
    assert_eq!(row.get(2), fp.elem(5));
}

#[test]
fn sparse_row_add_scaled_merges_and_cancels() {
    let fp = f(7);
    let mut a = SparseRow::from_entries(vec![(0, fp.elem(3)), (2, fp.elem(5))], &fp);
    let b = SparseRow::from_entries(vec![(1, fp.elem(2)), (2, fp.elem(1))], &fp);
    a.add_scaled(&b, fp.elem(2), &fp);
    assert_eq!(a.get(0), fp.elem(3));
    assert_eq!(a.get(1), fp.elem(4));
    assert_eq!(a.get(2), fp.zero());
    assert_eq!(a.nnz(), 2);
}

#[test]
fn sparse_row_dot_matches_hand_computation() {
    let fp = f(7);
    let a = SparseRow::from_entries(vec![(0, fp.elem(3)), (2, fp.elem(5))], &fp);
    let b = SparseRow::from_entries(vec![(1, fp.elem(4)), (2, fp.elem(2))], &fp);
    assert_eq!(a.dot(&b, &fp), fp.elem(3));
}

#[test]
fn sparse_solve_matches_hand_computation() {
    let fp = f(7);
    let a = dense(&fp, &[&[1, 2], &[3, 4]]).to_sparse();
    let b = sparse_vec(&[fp.elem(5), fp.elem(6)]);
    let x = a.solve(&b, &fp).unwrap();
    assert_eq!(dense_vec(&x, 2), vec![fp.elem(3), fp.elem(1)]);
    assert_eq!(a.mul_vec(&x, &fp), b);
}

#[test]
fn sparse_solve_detects_inconsistency() {
    let fp = f(7);
    let a = dense(&fp, &[&[1, 0], &[0, 0]]).to_sparse();
    let b = sparse_vec(&[fp.elem(1), fp.elem(1)]);
    assert!(a.solve(&b, &fp).is_none());
}

#[test]
fn sparse_kernel_spans_the_null_space() {
    let fp = f(7);
    let a = dense(&fp, &[&[1, 2], &[2, 4]]).to_sparse();
    let k = a.kernel_basis(&fp);
    assert_eq!(k.rows(), 1);
    assert!(a.mul_vec(k.row(0), &fp).is_zero());
}

#[test]
fn conversions_round_trip() {
    let fp = f(7);
    let a = dense(&fp, &[&[0, 2, 0], &[3, 0, 4]]);
    assert_eq!(a.to_sparse().to_dense(), a);
    let s = a.to_sparse();
    assert_eq!(s.to_dense().to_sparse(), s);
    assert_eq!(s.transpose().to_dense(), a.transpose());
}

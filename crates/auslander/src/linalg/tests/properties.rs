use super::support::{XorShift64, dense_vec, f, random_dense, sparse_vec};
use crate::field::Fp;
use crate::linalg::{DenseMat, RowReducer};

#[test]
fn rank_nullity_and_kernel_membership_hold_on_random_matrices() {
    let mut rng = XorShift64(0xdeadbeefcafef00d);
    for p in [2, 3, 101] {
        let fp = f(p);
        for _ in 0..30 {
            let rows = 1 + rng.below(8) as usize;
            let cols = 1 + rng.below(8) as usize;
            let a = random_dense(&mut rng, &fp, rows, cols);
            let k = a.kernel_basis(&fp);
            assert_eq!(a.rank(&fp) + k.rows(), cols);
            assert_eq!(k.mul(&a.transpose(), &fp), DenseMat::zero(k.rows(), rows));
            assert_eq!(k.rank(&fp), k.rows());
        }
    }
}

#[test]
fn dense_and_sparse_elimination_agree_on_random_matrices() {
    let mut rng = XorShift64(0x9e3779b97f4a7c15);
    for p in [2, 3, 101] {
        let fp = f(p);
        for _ in 0..40 {
            let rows = 1 + rng.below(7) as usize;
            let cols = 1 + rng.below(7) as usize;
            let a = random_dense(&mut rng, &fp, rows, cols);
            let s = a.to_sparse();

            let (dr, dp) = a.rref(&fp);
            let (sr, sp) = s.rref(&fp);
            assert_eq!(dp, sp);
            assert_eq!(dr, sr.to_dense());
            assert_eq!(a.rank(&fp), s.rank(&fp));
            assert_eq!(a.kernel_basis(&fp), s.kernel_basis(&fp).to_dense());
            assert_eq!(a.row_space_basis(&fp), s.row_space_basis(&fp).to_dense());
            assert_eq!(a.image_basis(&fp), s.image_basis(&fp).to_dense());
        }
    }
}

#[test]
#[should_panic(expected = "overflow usize")]
fn dense_zero_rejects_a_shape_that_overflows() {
    let _ = DenseMat::zero(usize::MAX, 2);
}

#[test]
fn left_kernel_basis_is_the_kernel_of_the_transpose() {
    let mut rng = XorShift64(0x3c6ef372fe94f82b);
    for p in [2, 101] {
        let fp = f(p);
        for _ in 0..20 {
            let rows = 1 + rng.below(6) as usize;
            let cols = 1 + rng.below(6) as usize;
            let a = random_dense(&mut rng, &fp, rows, cols);
            let left = a.transpose().kernel_basis(&fp);
            assert_eq!(a.left_kernel_basis(&fp), left);
            assert_eq!(a.to_sparse().left_kernel_basis(&fp).to_dense(), left);
            assert_eq!(left.mul(&a, &fp), DenseMat::zero(left.rows(), cols));
        }
    }
}

#[test]
fn add_scaled_into_matches_add_scaled() {
    let mut rng = XorShift64(0x78e2c3d9a1b4f605);
    let fp = f(101);
    let mut scratch = Vec::new();
    for _ in 0..200 {
        let n = rng.below(8) as usize;
        let a: Vec<Fp> = (0..n).map(|_| fp.elem(rng.below(3) as i64)).collect();
        let b: Vec<Fp> = (0..n).map(|_| fp.elem(rng.below(3) as i64)).collect();
        let c = fp.elem(rng.below(101) as i64);
        let other = sparse_vec(&b);
        let mut x = sparse_vec(&a);
        let mut y = x.clone();
        x.add_scaled(&other, c, &fp);
        y.add_scaled_into(&other, c, &fp, &mut scratch);
        assert_eq!(x, y);
    }
}

#[test]
fn row_reducer_rank_matches_the_rank_of_the_rows_pushed() {
    let mut rng = XorShift64(0x106689d45497fdb5);
    for p in [2, 3, 101] {
        let fp = f(p);
        for _ in 0..30 {
            let rows = 1 + rng.below(8) as usize;
            let cols = 1 + rng.below(8) as usize;
            let a = random_dense(&mut rng, &fp, rows, cols);
            let mut reducer = RowReducer::new(cols);
            let mut seen: Vec<Vec<Fp>> = Vec::new();
            for r in 0..rows {
                let before = reducer.rank();
                let grew = reducer.push(a.row(r), &fp);
                seen.push(a.row(r).to_vec());
                let rank = DenseMat::from_rows(&seen).rank(&fp);
                assert_eq!(reducer.rank(), rank);
                assert_eq!(grew, rank == before + 1);
                // A row already in the span never raises the rank again.
                assert!(!reducer.push(a.row(r), &fp));
            }
        }
    }
}

#[test]
fn solve_many_agrees_with_the_column_by_column_solve() {
    let mut rng = XorShift64(0x5851f42d4c957f2d);
    for p in [2, 3, 7, 101, (1 << 31) - 1] {
        let fp = f(p);
        for _ in 0..40 {
            let rows = 1 + rng.below(6) as usize;
            let cols = 1 + rng.below(6) as usize;
            let k = rng.below(4) as usize;
            let a = random_dense(&mut rng, &fp, rows, cols);
            // One right-hand side taken at random, one built inside the
            // image, so both the consistent and the inconsistent branch run.
            let arbitrary = random_dense(&mut rng, &fp, rows, k);
            let inside = a.mul(&random_dense(&mut rng, &fp, cols, k), &fp);
            for b in [arbitrary, inside] {
                let columns: Vec<Option<Vec<Fp>>> = (0..k)
                    .map(|j| {
                        let col: Vec<Fp> = (0..rows).map(|r| b.get(r, j)).collect();
                        a.solve(&col, &fp)
                    })
                    .collect();
                match a.solve_many(&b, &fp) {
                    None => assert!(columns.iter().any(Option::is_none), "F_{p}"),
                    Some(x) => {
                        assert_eq!((x.rows(), x.cols()), (cols, k));
                        for (j, expected) in columns.iter().enumerate() {
                            let expected = expected.as_ref().expect("solve_many succeeded");
                            for (r, &v) in expected.iter().enumerate() {
                                assert_eq!(x.get(r, j), v, "entry ({r}, {j}) in F_{p}");
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn inverse_round_trips_and_reports_singular_matrices() {
    let mut rng = XorShift64(0x14057b7ef767814f);
    for p in [2, 5, 101] {
        let fp = f(p);
        for _ in 0..40 {
            let n = 1 + rng.below(5) as usize;
            let a = random_dense(&mut rng, &fp, n, n);
            match a.inverse(&fp) {
                Some(inv) => {
                    assert_eq!(a.rank(&fp), n);
                    assert_eq!(a.mul(&inv, &fp), DenseMat::identity(n));
                    assert_eq!(inv.mul(&a, &fp), DenseMat::identity(n));
                }
                None => assert!(a.rank(&fp) < n),
            }
        }
    }
}

#[test]
fn dense_and_sparse_solve_agree_on_random_systems() {
    let mut rng = XorShift64(0x2545f4914f6cdd1d);
    for p in [2, 3, 101] {
        let fp = f(p);
        for _ in 0..40 {
            let rows = 1 + rng.below(6) as usize;
            let cols = 1 + rng.below(6) as usize;
            let a = random_dense(&mut rng, &fp, rows, cols);
            let s = a.to_sparse();

            let x0: Vec<Fp> = (0..cols).map(|_| fp.elem(rng.below(p) as i64)).collect();
            let b = a.mul_vec(&x0, &fp);
            let xd = a.solve(&b, &fp).expect("b lies in the image");
            assert_eq!(a.mul_vec(&xd, &fp), b);
            let xs = s.solve(&sparse_vec(&b), &fp).expect("b lies in the image");
            assert_eq!(dense_vec(&xs, cols), xd);

            let b2: Vec<Fp> = (0..rows).map(|_| fp.elem(rng.below(p) as i64)).collect();
            let xd2 = a.solve(&b2, &fp);
            let xs2 = s.solve(&sparse_vec(&b2), &fp);
            assert_eq!(xd2.is_some(), xs2.is_some());
            if let (Some(xd2), Some(xs2)) = (xd2, xs2) {
                assert_eq!(a.mul_vec(&xd2, &fp), b2);
                assert_eq!(dense_vec(&xs2, cols), xd2);
            }
        }
    }
}

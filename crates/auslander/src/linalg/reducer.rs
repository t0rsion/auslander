use crate::field::{Fp, PrimeField};
use crate::profile::{Site, hit};

/// An incremental rank accumulator over F_p.
///
/// Rows arrive one at a time. Each is reduced against the rows kept so far.
/// A row raises the rank exactly when it does not reduce to zero against the
/// current basis, and that is what [`RowReducer::push`] returns. Building a
/// set of independent rows this way costs one reduction per row. Re-running
/// [`crate::linalg::DenseMat::rank`] on the growing set costs a full elimination per row:
/// `O(n^3)` against `O(n^4)` for `n` rows of `n` entries.
///
/// The kept rows are in row echelon form ordered by pivot column, each
/// normalized to a leading 1. They are an internal basis, not a returned one.
/// No caller depends on them.
pub struct RowReducer {
    cols: usize,
    /// One kept row per pivot, ordered by pivot column.
    rows: Vec<Vec<Fp>>,
    /// The pivot column of each kept row, increasing.
    pivots: Vec<usize>,
}

impl RowReducer {
    /// An empty accumulator for rows of `cols` entries.
    pub fn new(cols: usize) -> RowReducer {
        RowReducer {
            cols,
            rows: Vec::new(),
            pivots: Vec::new(),
        }
    }

    /// Reduces `row` against the rows kept so far, keeps it when a nonzero
    /// entry remains, and returns whether the rank went up.
    ///
    /// # Panics
    /// Panics unless `row.len()` is the column count given to
    /// [`RowReducer::new`].
    pub fn push(&mut self, row: &[Fp], f: &PrimeField) -> bool {
        hit(Site::RowReducerPush);
        assert_eq!(
            row.len(),
            self.cols,
            "push: row length vs {} columns",
            self.cols
        );
        let mut r = row.to_vec();
        // Kept rows are zero before their own pivot, so reducing in pivot
        // order never puts back an entry an earlier step cleared.
        for (kept, &pc) in self.rows.iter().zip(&self.pivots) {
            let factor = r[pc];
            if factor.is_zero() {
                continue;
            }
            for (a, &b) in r[pc..].iter_mut().zip(&kept[pc..]) {
                *a = f.sub(*a, f.mul(factor, b));
            }
        }
        let Some(pc) = r.iter().position(|v| !v.is_zero()) else {
            return false;
        };
        let inv = f.inv(r[pc]);
        for v in &mut r[pc..] {
            *v = f.mul(*v, inv);
        }
        let at = self.pivots.partition_point(|&c| c < pc);
        self.rows.insert(at, r);
        self.pivots.insert(at, pc);
        true
    }

    accessor_methods! {
        /// The rank of everything pushed so far.
        pub rank() -> usize = |this| this.pivots.len();
    }
}

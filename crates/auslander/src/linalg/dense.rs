use super::sparse::{SparseMat, SparseRow};
use crate::field::{Fp, PrimeField};
use crate::profile::{Site, hit};

/// Row-major dense matrix over F_p.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DenseMat {
    rows: usize,
    cols: usize,
    // Length rows * cols; entry (r, c) at index r * cols + c.
    data: Vec<Fp>,
}

impl DenseMat {
    /// The `rows x cols` zero matrix.
    ///
    /// # Panics
    /// Panics if `rows * cols` overflows `usize`.
    pub fn zero(rows: usize, cols: usize) -> DenseMat {
        let len = rows
            .checked_mul(cols)
            .unwrap_or_else(|| panic!("zero: {rows} by {cols} entries overflow usize"));
        DenseMat {
            rows,
            cols,
            data: vec![Fp::ZERO; len],
        }
    }

    /// The `n x n` identity matrix.
    pub fn identity(n: usize) -> DenseMat {
        let mut m = DenseMat::zero(n, n);
        for i in 0..n {
            m.data[i * n + i] = Fp::ONE;
        }
        m
    }

    /// A matrix with the given rows. An empty slice gives the 0 x 0 matrix.
    ///
    /// # Panics
    /// Panics if the rows have differing lengths.
    pub fn from_rows(rows: &[Vec<Fp>]) -> DenseMat {
        let cols = rows.first().map_or(0, Vec::len);
        Self::from_rows_with_cols(rows, cols)
    }

    /// A matrix with the given rows and explicit width.
    ///
    /// The width preserves the shape when `rows` is empty.
    pub(crate) fn from_rows_with_cols(rows: &[Vec<Fp>], cols: usize) -> DenseMat {
        for row in rows {
            assert_eq!(row.len(), cols, "from_rows: ragged rows");
        }
        DenseMat {
            rows: rows.len(),
            cols,
            data: rows.iter().flatten().copied().collect(),
        }
    }

    /// A matrix from row-major entries.
    pub(crate) fn from_flat(rows: usize, cols: usize, data: &[Fp]) -> DenseMat {
        assert_eq!(data.len(), rows * cols, "from_flat: entry count");
        DenseMat {
            rows,
            cols,
            data: data.to_vec(),
        }
    }

    /// The matrices stacked in order with an explicit width.
    pub(crate) fn stack(matrices: &[&DenseMat], cols: usize) -> DenseMat {
        assert!(matrices.iter().all(|matrix| matrix.cols == cols));
        DenseMat {
            rows: matrices.iter().map(|matrix| matrix.rows).sum(),
            cols,
            data: matrices
                .iter()
                .flat_map(|matrix| matrix.data.iter().copied())
                .collect(),
        }
    }

    accessor_methods! {
        /// Number of rows.
        pub rows() -> usize = |this| this.rows;
        /// Number of columns.
        pub cols() -> usize = |this| this.cols;
    }

    /// The entry at (r, c).
    ///
    /// # Panics
    /// Panics if `r` or `c` is out of range.
    #[inline]
    pub fn get(&self, r: usize, c: usize) -> Fp {
        assert!(
            r < self.rows && c < self.cols,
            "get: ({r}, {c}) out of range"
        );
        self.data[r * self.cols + c]
    }

    /// Sets the entry at (r, c).
    ///
    /// # Panics
    /// Panics if `r` or `c` is out of range.
    #[inline]
    pub fn set(&mut self, r: usize, c: usize, v: Fp) {
        assert!(
            r < self.rows && c < self.cols,
            "set: ({r}, {c}) out of range"
        );
        self.data[r * self.cols + c] = v;
    }

    /// Row `r` as a slice.
    ///
    /// # Panics
    /// Panics if `r` is out of range.
    #[inline]
    pub fn row(&self, r: usize) -> &[Fp] {
        assert!(r < self.rows, "row: {r} out of range");
        &self.data[r * self.cols..(r + 1) * self.cols]
    }

    /// The entries as canonical representatives in `0..p`, one inner `Vec` per row.
    pub fn entries_u64(&self) -> Vec<Vec<u64>> {
        (0..self.rows)
            .map(|r| self.row(r).iter().map(|v| v.raw()).collect())
            .collect()
    }

    /// The sum `self + rhs`.
    ///
    /// # Panics
    /// Panics unless the two matrices have the same shape.
    pub fn add(&self, rhs: &DenseMat, f: &PrimeField) -> DenseMat {
        hit(Site::DenseAdd);
        assert!(
            self.rows == rhs.rows && self.cols == rhs.cols,
            "add: {}x{} vs {}x{}",
            self.rows,
            self.cols,
            rhs.rows,
            rhs.cols
        );
        let mut out = self.clone();
        for (left, &right) in out.data.iter_mut().zip(&rhs.data) {
            *left = f.add(*left, right);
        }
        out
    }

    /// Adds `scale * rhs` to this matrix in place.
    pub(crate) fn add_scaled_assign(&mut self, rhs: &DenseMat, scale: Fp, f: &PrimeField) {
        assert_eq!((self.rows, self.cols), (rhs.rows, rhs.cols));
        for (left, &right) in self.data.iter_mut().zip(&rhs.data) {
            *left = f.add(*left, f.mul(scale, right));
        }
    }

    /// Multiplies every entry by `scale` in place.
    pub(crate) fn scale(&mut self, scale: Fp, f: &PrimeField) {
        for value in &mut self.data {
            *value = f.mul(*value, scale);
        }
    }

    /// The product `self * rhs`.
    ///
    /// # Panics
    /// Panics unless `self.cols() == rhs.rows()`.
    pub fn mul(&self, rhs: &DenseMat, f: &PrimeField) -> DenseMat {
        hit(Site::DenseMul);
        assert_eq!(
            self.cols, rhs.rows,
            "mul: {}x{} times {}x{}",
            self.rows, self.cols, rhs.rows, rhs.cols
        );
        let mut out = DenseMat::zero(self.rows, rhs.cols);
        // Each product is below 2^62 and a row adds self.cols of them, so the
        // accumulator stays inside u128 and is reduced once per output entry.
        let mut acc = vec![0u128; rhs.cols];
        for i in 0..self.rows {
            acc.fill(0);
            for (k, &a) in self.data[i * self.cols..(i + 1) * self.cols]
                .iter()
                .enumerate()
            {
                if a.is_zero() {
                    continue;
                }
                let a = a.raw();
                for (t, &b) in acc
                    .iter_mut()
                    .zip(&rhs.data[k * rhs.cols..(k + 1) * rhs.cols])
                {
                    *t += (a * b.raw()) as u128;
                }
            }
            for (o, &t) in out.data[i * rhs.cols..(i + 1) * rhs.cols]
                .iter_mut()
                .zip(&acc)
            {
                *o = f.reduce_wide(t);
            }
        }
        out
    }

    /// `A x` for a vector `x` of length `self.cols()`; the result has length
    /// `self.rows()`.
    ///
    /// # Panics
    /// Panics unless `x.len() == self.cols()`.
    pub fn mul_vec(&self, x: &[Fp], f: &PrimeField) -> Vec<Fp> {
        hit(Site::DenseMulVec);
        assert_eq!(
            x.len(),
            self.cols,
            "mul_vec: vector length vs {} columns",
            self.cols
        );
        (0..self.rows)
            .map(|r| {
                let row = &self.data[r * self.cols..(r + 1) * self.cols];
                let mut acc = 0u128;
                for (&a, &v) in row.iter().zip(x) {
                    acc += (a.raw() * v.raw()) as u128;
                }
                f.reduce_wide(acc)
            })
            .collect()
    }

    /// The transpose.
    pub fn transpose(&self) -> DenseMat {
        hit(Site::DenseTranspose);
        let mut out = DenseMat::zero(self.cols, self.rows);
        for r in 0..self.rows {
            for c in 0..self.cols {
                out.data[c * self.rows + r] = self.data[r * self.cols + c];
            }
        }
        out
    }

    /// The reduced row echelon form and its pivot columns.
    ///
    /// Pivot rows come first in pivot-column order; zero rows follow.
    pub fn rref(&self, f: &PrimeField) -> (DenseMat, Vec<usize>) {
        self.clone().into_rref(f)
    }

    /// [`DenseMat::rref`] on an owned matrix, reduced in place.
    pub(crate) fn into_rref(mut self, f: &PrimeField) -> (DenseMat, Vec<usize>) {
        hit(Site::DenseRref);
        let pivots = self.rref_in_place(f);
        (self, pivots)
    }

    fn rref_in_place(&mut self, f: &PrimeField) -> Vec<usize> {
        let pivots = self.echelon_in_place(self.cols, f);
        self.back_substitute(&pivots, f);
        pivots
    }

    /// Forward elimination, with the pivot search restricted to columns
    /// `0..limit`, in place. Returns the pivot columns in increasing order.
    ///
    /// Row operations run across the full width, so the columns from `limit`
    /// on are carried along: that is how an augmented solve moves its
    /// right-hand sides. On return, row `i` below the pivot count leads at
    /// `pivots[i]` with a 1, and the rows after that are zero in `0..limit`.
    fn echelon_in_place(&mut self, limit: usize, f: &PrimeField) -> Vec<usize> {
        hit(Site::DenseEchelon);
        let mut pivots = Vec::new();
        let mut pr = 0;
        for col in 0..limit {
            if pr == self.rows {
                break;
            }
            let Some(idx) = (pr..self.rows).find(|&r| !self.data[r * self.cols + col].is_zero())
            else {
                continue;
            };
            self.swap_rows(pr, idx);
            let inv = f.inv(self.data[pr * self.cols + col]);
            let (pivot, below) = self.data[pr * self.cols..].split_at_mut(self.cols);
            for v in &mut pivot[col..] {
                *v = f.mul(*v, inv);
            }
            eliminate(below, pivot, col, self.cols, f);
            pivots.push(col);
            pr += 1;
        }
        pivots
    }

    /// Clears each pivot column above its pivot row, turning a row echelon
    /// form into the reduced form. `pivots` must be what
    /// [`DenseMat::echelon_in_place`] returned for this matrix.
    fn back_substitute(&mut self, pivots: &[usize], f: &PrimeField) {
        for i in (0..pivots.len()).rev() {
            let (above, rest) = self.data.split_at_mut(i * self.cols);
            eliminate(above, &rest[..self.cols], pivots[i], self.cols, f);
        }
    }

    fn swap_rows(&mut self, a: usize, b: usize) {
        if a == b {
            return;
        }
        for c in 0..self.cols {
            self.data.swap(a * self.cols + c, b * self.cols + c);
        }
    }

    /// The dimension of the row space, which equals that of the column space.
    pub fn rank(&self, f: &PrimeField) -> usize {
        self.clone().into_rank(f)
    }

    /// [`DenseMat::rank`] on an owned matrix, eliminating in place.
    pub(crate) fn into_rank(mut self, f: &PrimeField) -> usize {
        hit(Site::DenseRank);
        self.echelon_in_place(self.cols, f).len()
    }

    /// A basis of the right null space {x : A x = 0}, one vector per row of the
    /// result; the result has `self.cols()` columns and `cols - rank` rows.
    ///
    /// Row `i` belongs to the `i`-th free column of the reduced row echelon
    /// form, free columns taken in increasing order, and carries a 1 there.
    /// [`SparseMat::kernel_basis`] emits the same rows in the same order, and
    /// [`crate::hom::hom`] takes its Hom basis order from that one. Change the
    /// rule here and the two paths disagree.
    pub fn kernel_basis(&self, f: &PrimeField) -> DenseMat {
        self.clone().into_kernel_basis(f)
    }

    /// [`DenseMat::kernel_basis`] on an owned matrix, reduced in place.
    pub(crate) fn into_kernel_basis(self, f: &PrimeField) -> DenseMat {
        hit(Site::DenseKernelBasis);
        let cols = self.cols;
        let (m, pivots) = self.into_rref(f);
        let mut is_pivot = vec![false; cols];
        for &c in &pivots {
            is_pivot[c] = true;
        }
        let free: Vec<usize> = (0..cols).filter(|&c| !is_pivot[c]).collect();
        let mut out = DenseMat::zero(free.len(), cols);
        // Pivot row outermost, so the reduced form is read one whole row at a
        // time instead of one column at a time down a row-major buffer.
        for (j, &pc) in pivots.iter().enumerate() {
            let row = &m.data[j * m.cols..(j + 1) * m.cols];
            for (i, &fc) in free.iter().enumerate() {
                out.data[i * cols + pc] = f.neg(row[fc]);
            }
        }
        for (i, &fc) in free.iter().enumerate() {
            out.data[i * cols + fc] = Fp::ONE;
        }
        out
    }

    /// A basis of the left null space {x : x A = 0}, one vector per row of the
    /// result (each of length `self.rows()`): the kernel basis of the
    /// transpose, row for row.
    pub fn left_kernel_basis(&self, f: &PrimeField) -> DenseMat {
        self.transpose().into_kernel_basis(f)
    }

    /// A basis of the row space: the nonzero rows of the reduced row echelon
    /// form, one vector per row of the result.
    pub fn row_space_basis(&self, f: &PrimeField) -> DenseMat {
        self.clone().into_row_space_basis(f)
    }

    /// [`DenseMat::row_space_basis`] on an owned matrix, reduced in place.
    pub(crate) fn into_row_space_basis(self, f: &PrimeField) -> DenseMat {
        hit(Site::DenseRowSpaceBasis);
        let (mut m, pivots) = self.into_rref(f);
        m.data.truncate(pivots.len() * m.cols);
        m.rows = pivots.len();
        m
    }

    /// A basis of the column space, one vector per row of the result (each of
    /// length `self.rows()`): the row-space basis of the transpose.
    pub fn image_basis(&self, f: &PrimeField) -> DenseMat {
        self.transpose().into_row_space_basis(f)
    }

    /// A solution of `A x = b` with free variables set to zero, or `None` when
    /// the system is inconsistent. `b` has length `self.rows()`. Fixing the
    /// free variables at zero makes the returned solution unique, so repeated
    /// calls on equal inputs agree.
    ///
    /// This is [`DenseMat::solve_many`] with one right-hand side.
    ///
    /// # Panics
    /// Panics unless `b.len() == self.rows()`.
    pub fn solve(&self, b: &[Fp], f: &PrimeField) -> Option<Vec<Fp>> {
        hit(Site::DenseSolve);
        assert_eq!(
            b.len(),
            self.rows,
            "solve: rhs length vs {} rows",
            self.rows
        );
        let rhs = DenseMat {
            rows: self.rows,
            cols: 1,
            data: b.to_vec(),
        };
        self.solve_many(&rhs, f).map(|x| x.data)
    }

    /// A solution of `A X = B` with free variables set to zero, or `None` when
    /// any column of `b` lies outside the image. `b` has `self.rows()` rows.
    /// The result has `self.cols()` rows and `b.cols()` columns.
    ///
    /// Column `j` of the result equals [`DenseMat::solve`] applied to column
    /// `j` of `b`, entry for entry. One elimination serves every column.
    /// Looping `solve` once per column is `O(n^4)` for a square `A` of size
    /// `n` with `n` right-hand sides; this is `O(n^3)`.
    ///
    /// # Panics
    /// Panics unless `b.rows() == self.rows()`, or if the augmented matrix
    /// does not fit in `usize` entries.
    pub fn solve_many(&self, b: &DenseMat, f: &PrimeField) -> Option<DenseMat> {
        hit(Site::DenseSolveMany);
        assert_eq!(
            b.rows, self.rows,
            "solve_many: rhs has {} rows vs {}",
            b.rows, self.rows
        );
        let k = b.cols;
        let width = self.cols.checked_add(k);
        let len = width.and_then(|w| self.rows.checked_mul(w));
        let (Some(width), Some(len)) = (width, len) else {
            panic!(
                "solve_many: {} rows by {} + {k} columns overflow usize",
                self.rows, self.cols
            )
        };
        let mut data = Vec::with_capacity(len);
        for r in 0..self.rows {
            data.extend_from_slice(&self.data[r * self.cols..(r + 1) * self.cols]);
            data.extend_from_slice(&b.data[r * k..(r + 1) * k]);
        }
        let mut aug = DenseMat {
            rows: self.rows,
            cols: width,
            data,
        };
        // The pivot search stops at self.cols, so no right-hand side column can
        // take a pivot and corrupt the others. A column is then inconsistent
        // exactly when a row left zero by the elimination is nonzero in it.
        let pivots = aug.echelon_in_place(self.cols, f);
        aug.back_substitute(&pivots, f);
        for r in pivots.len()..self.rows {
            if aug.data[r * width + self.cols..(r + 1) * width]
                .iter()
                .any(|v| !v.is_zero())
            {
                return None;
            }
        }
        let mut x = DenseMat::zero(self.cols, k);
        for (i, &pc) in pivots.iter().enumerate() {
            x.data[pc * k..(pc + 1) * k]
                .copy_from_slice(&aug.data[i * width + self.cols..(i + 1) * width]);
        }
        Some(x)
    }

    /// The inverse, or `None` when the matrix is singular.
    ///
    /// # Panics
    /// Panics unless the matrix is square.
    pub fn inverse(&self, f: &PrimeField) -> Option<DenseMat> {
        hit(Site::DenseInverse);
        assert_eq!(
            self.rows, self.cols,
            "inverse: {}x{} is not square",
            self.rows, self.cols
        );
        self.solve_many(&DenseMat::identity(self.rows), f)
    }

    /// The position of the first entry whose stored representative is not
    /// canonical for `f` (not below `f.modulus()`), or `None` when every
    /// entry is canonical. Entries are scanned row by row.
    pub(crate) fn first_noncanonical(&self, f: &PrimeField) -> Option<(usize, usize)> {
        hit(Site::DenseFirstNoncanonical);
        self.data
            .iter()
            .position(|v| v.raw() >= f.modulus())
            .map(|i| (i / self.cols, i % self.cols))
    }

    /// The same matrix in sparse form.
    pub fn to_sparse(&self) -> SparseMat {
        let data = (0..self.rows)
            .map(|r| {
                let entries = (0..self.cols)
                    .filter_map(|c| {
                        let v = self.data[r * self.cols + c];
                        (!v.is_zero()).then_some((c, v))
                    })
                    .collect();
                SparseRow { entries }
            })
            .collect();
        SparseMat {
            rows: self.rows,
            cols: self.cols,
            data,
        }
    }
}

/// Subtracts the multiple of `pivot` that clears column `col` from every row
/// of `rows`. Both slices hold whole rows of `cols` entries, and `pivot` is 1
/// at `col` and 0 before it.
///
/// Splitting the pivot row out of the buffer is what lets this run as a
/// two-slice zip: one bounds check per row, where indexing through `&mut self`
/// costs three per entry and an index multiply-add.
fn eliminate(rows: &mut [Fp], pivot: &[Fp], col: usize, cols: usize, f: &PrimeField) {
    for row in rows.chunks_exact_mut(cols) {
        let factor = row[col];
        if factor.is_zero() {
            continue;
        }
        for (a, &b) in row[col..].iter_mut().zip(&pivot[col..]) {
            *a = f.sub(*a, f.mul(factor, b));
        }
    }
}

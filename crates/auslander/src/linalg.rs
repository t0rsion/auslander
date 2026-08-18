//! Exact linear algebra over F_p.
//!
//! Two matrix types share one set of operations: [`DenseMat`] (row-major
//! contiguous, the default at module scale) and [`SparseMat`] (sorted rows,
//! Markowitz-pivoted elimination). Matrices are plain data and do not store
//! their field. Every arithmetic operation takes the [`PrimeField`] as an
//! argument, and all entries of the operands must belong to that field.
//! Direct callers must supply canonical matrices: every entry must be the
//! reduced representative for the field passed, as produced by
//! [`PrimeField::elem`]. The field arithmetic debug-asserts this and does
//! not re-reduce.
//!
//! Basis-returning operations (`kernel_basis`, `left_kernel_basis`,
//! `row_space_basis`, `image_basis`) return a matrix whose rows are the basis
//! vectors, derived from the reduced row echelon form. The reduced form is
//! unique, so these operations are deterministic and the dense and sparse
//! paths return identical rows in identical order. Callers above this module
//! depend on the exact rows and their order, so both are part of the contract.
//!
//! Every reduction has two forms. `rref`, `rank`, `kernel_basis`, and
//! `row_space_basis` take the matrix by reference and reduce a copy of it.
//! The matching `into_rref`, `into_rank`, `into_kernel_basis`, and
//! `into_row_space_basis` take the matrix by value and reduce it in place, so
//! a caller whose input is dead after the call pays for no copy. Both forms
//! return the same thing. The consuming form is crate-private.

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
        let mut data = Vec::with_capacity(rows.len() * cols);
        for row in rows {
            assert_eq!(row.len(), cols, "from_rows: ragged rows");
            data.extend_from_slice(row);
        }
        DenseMat {
            rows: rows.len(),
            cols,
            data,
        }
    }

    /// Number of rows.
    #[inline]
    pub fn rows(&self) -> usize {
        self.rows
    }

    /// Number of columns.
    #[inline]
    pub fn cols(&self) -> usize {
        self.cols
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
        let data = self
            .data
            .iter()
            .zip(&rhs.data)
            .map(|(&a, &b)| f.add(a, b))
            .collect();
        DenseMat {
            rows: self.rows,
            cols: self.cols,
            data,
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
    /// Pivot rows come first in pivot-column order; zero rows follow. The
    /// matrix is copied first. Where the input is dead after the call,
    /// `into_rref` reduces the input itself and copies nothing.
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
    ///
    /// The matrix is copied first. Where the input is dead after the call,
    /// `into_rank` eliminates in the input itself.
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
    ///
    /// The matrix is copied first. Where the input is dead after the call,
    /// `into_kernel_basis` reduces the input itself.
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
    ///
    /// The matrix is copied first. Where the input is dead after the call,
    /// `into_row_space_basis` reduces the input itself.
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
    /// the system is inconsistent; `b` has length `self.rows()`. Fixing the
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
    /// any column of `b` lies outside the image; `b` has `self.rows()` rows and
    /// the result has `self.cols()` rows and `b.cols()` columns.
    ///
    /// Column `j` of the result equals [`DenseMat::solve`] applied to column
    /// `j` of `b`, entry for entry. One elimination serves every column, where
    /// the loop over `solve` runs one per column: for a square `A` of size `n`
    /// and `n` right-hand sides that is `O(n^3)` against `O(n^4)`.
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
    /// canonical for `f` (that is, not below `f.modulus()`), or `None` when
    /// every entry is canonical. Entries are scanned row by row.
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

/// An incremental rank accumulator over F_p.
///
/// Rows arrive one at a time and each is reduced against the rows kept so
/// far. A row raises the rank exactly when it does not reduce to zero against
/// the current basis, and that is what [`RowReducer::push`] returns. Building
/// a set of independent rows this way costs one reduction per row, where
/// re-running [`DenseMat::rank`] on the growing set costs a full elimination
/// per row: `O(n^3)` against `O(n^4)` for `n` rows of `n` entries.
///
/// The kept rows are held in row echelon form ordered by pivot column, each
/// normalized to a leading 1. They are an internal basis, not a returned one;
/// no caller depends on them.
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

    /// The rank of everything pushed so far.
    pub fn rank(&self) -> usize {
        self.pivots.len()
    }
}

/// Sparse vector: (column, value) pairs sorted by column, values nonzero.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SparseRow {
    entries: Vec<(usize, Fp)>,
}

impl SparseRow {
    /// The zero vector.
    pub fn new() -> SparseRow {
        SparseRow::default()
    }

    /// A vector from arbitrary (column, value) pairs; duplicate columns are
    /// summed and zero results dropped.
    pub fn from_entries(mut entries: Vec<(usize, Fp)>, f: &PrimeField) -> SparseRow {
        entries.sort_unstable_by_key(|&(c, _)| c);
        let mut merged: Vec<(usize, Fp)> = Vec::with_capacity(entries.len());
        for (col, val) in entries {
            if val.is_zero() {
                continue;
            }
            if let Some(&mut (last_col, ref mut last_val)) = merged.last_mut()
                && last_col == col
            {
                *last_val = f.add(*last_val, val);
                if last_val.is_zero() {
                    merged.pop();
                }
                continue;
            }
            merged.push((col, val));
        }
        SparseRow { entries: merged }
    }

    /// The nonzero entries, sorted by column.
    #[inline]
    pub fn entries(&self) -> &[(usize, Fp)] {
        &self.entries
    }

    /// The value at `col`, zero when absent.
    pub fn get(&self, col: usize) -> Fp {
        self.entries
            .binary_search_by_key(&col, |&(c, _)| c)
            .map_or(Fp::ZERO, |i| self.entries[i].1)
    }

    /// Sets the value at `col`; a zero value removes the entry.
    pub fn set(&mut self, col: usize, val: Fp) {
        match self.entries.binary_search_by_key(&col, |&(c, _)| c) {
            Ok(i) => {
                if val.is_zero() {
                    self.entries.remove(i);
                } else {
                    self.entries[i].1 = val;
                }
            }
            Err(i) => {
                if !val.is_zero() {
                    self.entries.insert(i, (col, val));
                }
            }
        }
    }

    /// Whether the vector is zero.
    #[inline]
    pub fn is_zero(&self) -> bool {
        self.entries.is_empty()
    }

    /// Number of nonzero entries.
    #[inline]
    pub fn nnz(&self) -> usize {
        self.entries.len()
    }

    fn leading(&self) -> Option<(usize, Fp)> {
        self.entries.first().copied()
    }

    /// Multiplies every entry by `c`; `c = 0` clears the vector.
    pub fn scale(&mut self, c: Fp, f: &PrimeField) {
        if c.is_zero() {
            self.entries.clear();
            return;
        }
        // c is a unit, so no product can vanish.
        for (_, v) in &mut self.entries {
            *v = f.mul(*v, c);
        }
    }

    fn normalize(&mut self, f: &PrimeField) {
        if let Some((_, lc)) = self.leading()
            && lc.raw() != 1
        {
            let inv = f.inv(lc);
            self.scale(inv, f);
        }
    }

    /// Adds `c * other` to `self`, merging the two sorted entry lists.
    ///
    /// Allocates one buffer per call. In a loop, use
    /// [`SparseRow::add_scaled_into`] with a buffer you own.
    pub fn add_scaled(&mut self, other: &SparseRow, c: Fp, f: &PrimeField) {
        self.add_scaled_into(other, c, f, &mut Vec::new());
    }

    /// Adds `c * other` to `self`, merging through `scratch`.
    ///
    /// `scratch` is cleared on entry and holds the old entries of `self` on
    /// return, so a loop that passes the same buffer reuses its capacity and
    /// allocates once instead of once per call. The result matches
    /// [`SparseRow::add_scaled`] entry for entry.
    pub fn add_scaled_into(
        &mut self,
        other: &SparseRow,
        c: Fp,
        f: &PrimeField,
        scratch: &mut Vec<(usize, Fp)>,
    ) {
        if c.is_zero() || other.is_zero() {
            return;
        }
        let result = scratch;
        result.clear();
        result.reserve(self.entries.len() + other.entries.len());
        let mut i = 0;
        let mut j = 0;
        while i < self.entries.len() && j < other.entries.len() {
            let (col_a, val_a) = self.entries[i];
            let (col_b, val_b) = other.entries[j];
            match col_a.cmp(&col_b) {
                std::cmp::Ordering::Less => {
                    result.push((col_a, val_a));
                    i += 1;
                }
                std::cmp::Ordering::Greater => {
                    let scaled = f.mul(val_b, c);
                    if !scaled.is_zero() {
                        result.push((col_b, scaled));
                    }
                    j += 1;
                }
                std::cmp::Ordering::Equal => {
                    let sum = f.add(val_a, f.mul(val_b, c));
                    if !sum.is_zero() {
                        result.push((col_a, sum));
                    }
                    i += 1;
                    j += 1;
                }
            }
        }
        result.extend_from_slice(&self.entries[i..]);
        for &(col_b, val_b) in &other.entries[j..] {
            let scaled = f.mul(val_b, c);
            if !scaled.is_zero() {
                result.push((col_b, scaled));
            }
        }
        std::mem::swap(&mut self.entries, result);
    }

    /// The dot product with `other`.
    pub fn dot(&self, other: &SparseRow, f: &PrimeField) -> Fp {
        let mut i = 0;
        let mut j = 0;
        let mut acc = Fp::ZERO;
        while i < self.entries.len() && j < other.entries.len() {
            let (col_a, val_a) = self.entries[i];
            let (col_b, val_b) = other.entries[j];
            match col_a.cmp(&col_b) {
                std::cmp::Ordering::Less => i += 1,
                std::cmp::Ordering::Greater => j += 1,
                std::cmp::Ordering::Equal => {
                    acc = f.add(acc, f.mul(val_a, val_b));
                    i += 1;
                    j += 1;
                }
            }
        }
        acc
    }
}

/// Sparse matrix: one sorted row per matrix row.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SparseMat {
    rows: usize,
    cols: usize,
    data: Vec<SparseRow>,
}

impl SparseMat {
    /// The `rows x cols` zero matrix.
    pub fn zero(rows: usize, cols: usize) -> SparseMat {
        SparseMat {
            rows,
            cols,
            data: vec![SparseRow::new(); rows],
        }
    }

    /// A matrix with the given rows and `cols` columns.
    ///
    /// # Panics
    /// Panics if any entry's column index is `>= cols`.
    pub fn from_rows(rows: Vec<SparseRow>, cols: usize) -> SparseMat {
        for row in &rows {
            assert!(
                row.entries.last().is_none_or(|&(c, _)| c < cols),
                "from_rows: column index out of range"
            );
        }
        SparseMat {
            rows: rows.len(),
            cols,
            data: rows,
        }
    }

    /// Number of rows.
    #[inline]
    pub fn rows(&self) -> usize {
        self.rows
    }

    /// Number of columns.
    #[inline]
    pub fn cols(&self) -> usize {
        self.cols
    }

    /// Row `r`.
    ///
    /// # Panics
    /// Panics if `r` is out of range.
    #[inline]
    pub fn row(&self, r: usize) -> &SparseRow {
        &self.data[r]
    }

    /// The transpose.
    pub fn transpose(&self) -> SparseMat {
        let mut data = vec![SparseRow::new(); self.cols];
        // Source rows are visited in increasing order, so each output row is
        // built already sorted.
        for (r, row) in self.data.iter().enumerate() {
            for &(c, v) in &row.entries {
                data[c].entries.push((r, v));
            }
        }
        SparseMat {
            rows: self.cols,
            cols: self.rows,
            data,
        }
    }

    /// The product `self * rhs`.
    ///
    /// # Panics
    /// Panics unless `self.cols() == rhs.rows()`.
    pub fn mul(&self, rhs: &SparseMat, f: &PrimeField) -> SparseMat {
        hit(Site::SparseMul);
        assert_eq!(
            self.cols, rhs.rows,
            "mul: {}x{} times {}x{}",
            self.rows, self.cols, rhs.rows, rhs.cols
        );
        let mut scratch = Vec::new();
        let data = self
            .data
            .iter()
            .map(|lhs_row| {
                let mut row = SparseRow::new();
                for &(c, v) in &lhs_row.entries {
                    row.add_scaled_into(&rhs.data[c], v, f, &mut scratch);
                }
                row
            })
            .collect();
        SparseMat {
            rows: self.rows,
            cols: rhs.cols,
            data,
        }
    }

    /// `A x` for a sparse vector `x` indexed by column; the result is indexed
    /// by row.
    ///
    /// # Panics
    /// Panics if `x` has an index `>= self.cols()`.
    pub fn mul_vec(&self, x: &SparseRow, f: &PrimeField) -> SparseRow {
        assert!(
            x.entries.last().is_none_or(|&(c, _)| c < self.cols),
            "mul_vec: index out of range"
        );
        let entries = self
            .data
            .iter()
            .enumerate()
            .filter_map(|(r, row)| {
                let v = row.dot(x, f);
                (!v.is_zero()).then_some((r, v))
            })
            .collect();
        SparseRow { entries }
    }

    // Markowitz pivoting: among rows leading in the current column, the one
    // with the fewest entries becomes the pivot. The pivot row is normalized
    // first, so each elimination factor is the negated leading coefficient.
    fn echelon_in_place(&mut self, f: &PrimeField) -> Vec<usize> {
        hit(Site::SparseEchelon);
        let mut pivots = Vec::new();
        let mut scratch = Vec::new();
        let mut pr = 0;
        for col in 0..self.cols {
            if pr == self.rows {
                break;
            }
            let mut best = None;
            let mut best_nnz = usize::MAX;
            for r in pr..self.rows {
                if self.data[r].leading().is_some_and(|(c, _)| c == col) {
                    let nnz = self.data[r].nnz();
                    if nnz < best_nnz {
                        best_nnz = nnz;
                        best = Some(r);
                    }
                }
            }
            let Some(idx) = best else { continue };
            self.data.swap(pr, idx);
            self.data[pr].normalize(f);
            let (head, tail) = self.data.split_at_mut(pr + 1);
            let pivot = &head[pr];
            for row in tail {
                if let Some((c, coeff)) = row.leading()
                    && c == col
                {
                    row.add_scaled_into(pivot, f.neg(coeff), f, &mut scratch);
                }
            }
            pivots.push(col);
            pr += 1;
        }
        pivots
    }

    /// The reduced row echelon form and its pivot columns.
    ///
    /// Pivot rows come first in pivot-column order; zero rows follow. The
    /// matrix is copied first. Where the input is dead after the call,
    /// `into_rref` reduces the input itself and copies nothing.
    pub fn rref(&self, f: &PrimeField) -> (SparseMat, Vec<usize>) {
        self.clone().into_rref(f)
    }

    /// [`SparseMat::rref`] on an owned matrix, reduced in place.
    pub(crate) fn into_rref(mut self, f: &PrimeField) -> (SparseMat, Vec<usize>) {
        hit(Site::SparseRref);
        let pivots = self.echelon_in_place(f);
        let mut scratch = Vec::new();
        for i in (0..pivots.len()).rev() {
            let col = pivots[i];
            let (above, rest) = self.data.split_at_mut(i);
            let pivot = &rest[0];
            for row in above {
                let v = row.get(col);
                if !v.is_zero() {
                    row.add_scaled_into(pivot, f.neg(v), f, &mut scratch);
                }
            }
        }
        (self, pivots)
    }

    /// The dimension of the row space, which equals that of the column space.
    ///
    /// The matrix is copied first. Where the input is dead after the call,
    /// `into_rank` eliminates in the input itself.
    pub fn rank(&self, f: &PrimeField) -> usize {
        self.clone().into_rank(f)
    }

    /// [`SparseMat::rank`] on an owned matrix, eliminating in place.
    pub(crate) fn into_rank(mut self, f: &PrimeField) -> usize {
        self.echelon_in_place(f).len()
    }

    /// A basis of the right null space {x : A x = 0}, one vector per row of the
    /// result; the result has `self.cols()` columns and `cols - rank` rows.
    ///
    /// Rows come in the same order as [`DenseMat::kernel_basis`]: one row per
    /// free column of the reduced row echelon form, free columns increasing.
    /// [`crate::hom::hom`] builds its Hom basis from this order.
    ///
    /// The matrix is copied first. Where the input is dead after the call,
    /// `into_kernel_basis` reduces the input itself.
    pub fn kernel_basis(&self, f: &PrimeField) -> SparseMat {
        self.clone().into_kernel_basis(f)
    }

    /// [`SparseMat::kernel_basis`] on an owned matrix, reduced in place.
    pub(crate) fn into_kernel_basis(self, f: &PrimeField) -> SparseMat {
        hit(Site::SparseKernelBasis);
        let cols = self.cols;
        let (m, pivots) = self.into_rref(f);
        // Column to its index among the free columns, or none for a pivot.
        let mut slot = vec![None; cols];
        let mut free = Vec::new();
        for (c, s) in slot.iter_mut().enumerate() {
            if pivots.binary_search(&c).is_err() {
                *s = Some(free.len());
                free.push(c);
            }
        }
        let mut data = vec![SparseRow::new(); free.len()];
        // Each reduced row is walked once, and the pivot columns increase with
        // the row index, so every output row comes out sorted.
        for (i, &pc) in pivots.iter().enumerate() {
            for &(c, v) in &m.data[i].entries {
                if let Some(k) = slot[c] {
                    data[k].entries.push((pc, f.neg(v)));
                }
            }
        }
        for (k, &fc) in free.iter().enumerate() {
            let at = data[k].entries.partition_point(|&(c, _)| c < fc);
            data[k].entries.insert(at, (fc, Fp::ONE));
        }
        SparseMat {
            rows: data.len(),
            cols,
            data,
        }
    }

    /// A basis of the left null space {x : x A = 0}, one vector per row of the
    /// result (each of length `self.rows()`): the kernel basis of the
    /// transpose, row for row.
    pub fn left_kernel_basis(&self, f: &PrimeField) -> SparseMat {
        self.transpose().into_kernel_basis(f)
    }

    /// A basis of the row space: the nonzero rows of the reduced row echelon
    /// form, one vector per row of the result.
    ///
    /// The matrix is copied first. Where the input is dead after the call,
    /// `into_row_space_basis` reduces the input itself.
    pub fn row_space_basis(&self, f: &PrimeField) -> SparseMat {
        self.clone().into_row_space_basis(f)
    }

    /// [`SparseMat::row_space_basis`] on an owned matrix, reduced in place.
    pub(crate) fn into_row_space_basis(self, f: &PrimeField) -> SparseMat {
        let (mut m, pivots) = self.into_rref(f);
        m.data.truncate(pivots.len());
        m.rows = pivots.len();
        m
    }

    /// A basis of the column space, one vector per row of the result (each of
    /// length `self.rows()`): the row-space basis of the transpose.
    pub fn image_basis(&self, f: &PrimeField) -> SparseMat {
        self.transpose().into_row_space_basis(f)
    }

    /// A solution of `A x = b` with free variables set to zero, or `None` when
    /// the system is inconsistent; `b` is indexed by row. Matches
    /// [`DenseMat::solve`] entry for entry.
    ///
    /// # Panics
    /// Panics if `b` has an index `>= self.rows()`.
    pub fn solve(&self, b: &SparseRow, f: &PrimeField) -> Option<SparseRow> {
        hit(Site::SparseSolve);
        assert!(
            b.entries.last().is_none_or(|&(r, _)| r < self.rows),
            "solve: rhs index vs {} rows",
            self.rows
        );
        let mut aug_rows = Vec::with_capacity(self.rows);
        for (r, row) in self.data.iter().enumerate() {
            let mut aug = row.clone();
            let bv = b.get(r);
            if !bv.is_zero() {
                aug.entries.push((self.cols, bv));
            }
            aug_rows.push(aug);
        }
        let aug = SparseMat {
            rows: self.rows,
            cols: self.cols + 1,
            data: aug_rows,
        };
        let (m, pivots) = aug.into_rref(f);
        if pivots.last() == Some(&self.cols) {
            return None;
        }
        let mut x = SparseRow::new();
        for (i, &pc) in pivots.iter().enumerate() {
            let v = m.data[i].get(self.cols);
            if !v.is_zero() {
                x.set(pc, v);
            }
        }
        Some(x)
    }

    /// The same matrix in dense form.
    pub fn to_dense(&self) -> DenseMat {
        let mut out = DenseMat::zero(self.rows, self.cols);
        for (r, row) in self.data.iter().enumerate() {
            for &(c, v) in &row.entries {
                out.set(r, c, v);
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(p: u64) -> PrimeField {
        PrimeField::new(p).unwrap()
    }

    fn dense(fp: &PrimeField, rows: &[&[i64]]) -> DenseMat {
        let rows: Vec<Vec<Fp>> = rows
            .iter()
            .map(|r| r.iter().map(|&v| fp.elem(v)).collect())
            .collect();
        DenseMat::from_rows(&rows)
    }

    fn sparse_vec(v: &[Fp]) -> SparseRow {
        let mut row = SparseRow::new();
        for (i, &x) in v.iter().enumerate() {
            row.set(i, x);
        }
        row
    }

    fn dense_vec(row: &SparseRow, len: usize) -> Vec<Fp> {
        (0..len).map(|i| row.get(i)).collect()
    }

    struct XorShift64(u64);

    impl XorShift64 {
        fn next_u64(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }

        fn below(&mut self, n: u64) -> u64 {
            self.next_u64() % n
        }
    }

    fn random_dense(rng: &mut XorShift64, fp: &PrimeField, rows: usize, cols: usize) -> DenseMat {
        let mut m = DenseMat::zero(rows, cols);
        for r in 0..rows {
            for c in 0..cols {
                if rng.below(2) == 0 {
                    m.set(r, c, fp.elem(rng.below(fp.modulus()) as i64));
                }
            }
        }
        m
    }

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

    #[test]
    fn sparse_row_from_entries_merges_duplicates() {
        let fp = f(7);
        let row =
            SparseRow::from_entries(vec![(2, fp.elem(5)), (0, fp.elem(3)), (0, fp.elem(4))], &fp);
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
}

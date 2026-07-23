//! Exact linear algebra over F_p.
//!
//! Two matrix types share one set of operations: [`DenseMat`] (row-major
//! contiguous, the default at module scale) and [`SparseMat`] (sorted rows,
//! Markowitz-pivoted elimination). Matrices are plain data and do not store
//! their field; every arithmetic operation takes the [`PrimeField`] as an
//! argument, and all entries of the operands must belong to that field.
//! Direct callers must supply canonical matrices: every entry the reduced
//! representative of the field passed, as produced by [`PrimeField::elem`];
//! the field arithmetic debug-asserts this and does not re-reduce.
//!
//! Basis-returning operations (`kernel_basis`, `row_space_basis`,
//! `image_basis`) return a matrix whose rows are the basis vectors, derived
//! from the reduced row echelon form. Since the reduced form is unique, the
//! dense and sparse paths return identical results.

use crate::field::{Fp, PrimeField};

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
    pub fn zero(rows: usize, cols: usize) -> DenseMat {
        DenseMat {
            rows,
            cols,
            data: vec![Fp::ZERO; rows * cols],
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

    /// A matrix with the given rows.
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

    /// self + rhs.
    ///
    /// # Panics
    /// Panics on shape mismatch.
    pub fn add(&self, rhs: &DenseMat, f: &PrimeField) -> DenseMat {
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

    /// self * rhs.
    ///
    /// # Panics
    /// Panics unless `self.cols() == rhs.rows()`.
    pub fn mul(&self, rhs: &DenseMat, f: &PrimeField) -> DenseMat {
        assert_eq!(
            self.cols, rhs.rows,
            "mul: {}x{} times {}x{}",
            self.rows, self.cols, rhs.rows, rhs.cols
        );
        let mut out = DenseMat::zero(self.rows, rhs.cols);
        for i in 0..self.rows {
            for k in 0..self.cols {
                let a = self.data[i * self.cols + k];
                if a.is_zero() {
                    continue;
                }
                for j in 0..rhs.cols {
                    let t = f.mul(a, rhs.data[k * rhs.cols + j]);
                    out.data[i * rhs.cols + j] = f.add(out.data[i * rhs.cols + j], t);
                }
            }
        }
        out
    }

    /// A x for a vector `x` of length `self.cols()`; the result has length
    /// `self.rows()`.
    ///
    /// # Panics
    /// Panics on length mismatch.
    pub fn mul_vec(&self, x: &[Fp], f: &PrimeField) -> Vec<Fp> {
        assert_eq!(
            x.len(),
            self.cols,
            "mul_vec: vector length vs {} columns",
            self.cols
        );
        (0..self.rows)
            .map(|r| {
                let row = &self.data[r * self.cols..(r + 1) * self.cols];
                let mut acc = Fp::ZERO;
                for (&a, &v) in row.iter().zip(x) {
                    acc = f.add(acc, f.mul(a, v));
                }
                acc
            })
            .collect()
    }

    /// The transpose.
    pub fn transpose(&self) -> DenseMat {
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
        let mut m = self.clone();
        let pivots = m.rref_in_place(f);
        (m, pivots)
    }

    fn rref_in_place(&mut self, f: &PrimeField) -> Vec<usize> {
        let mut pivots = Vec::new();
        let mut pr = 0;
        for col in 0..self.cols {
            if pr == self.rows {
                break;
            }
            let Some(idx) = (pr..self.rows).find(|&r| !self.data[r * self.cols + col].is_zero())
            else {
                continue;
            };
            self.swap_rows(pr, idx);
            let inv = f.inv(self.data[pr * self.cols + col]);
            for c in col..self.cols {
                self.data[pr * self.cols + c] = f.mul(self.data[pr * self.cols + c], inv);
            }
            for r in 0..self.rows {
                if r == pr {
                    continue;
                }
                let factor = self.data[r * self.cols + col];
                if factor.is_zero() {
                    continue;
                }
                for c in col..self.cols {
                    let t = f.mul(factor, self.data[pr * self.cols + c]);
                    self.data[r * self.cols + c] = f.sub(self.data[r * self.cols + c], t);
                }
            }
            pivots.push(col);
            pr += 1;
        }
        pivots
    }

    fn swap_rows(&mut self, a: usize, b: usize) {
        if a == b {
            return;
        }
        for c in 0..self.cols {
            self.data.swap(a * self.cols + c, b * self.cols + c);
        }
    }

    /// dim of the row space (equivalently, of the column space).
    pub fn rank(&self, f: &PrimeField) -> usize {
        self.clone().rref_in_place(f).len()
    }

    /// A basis of the right null space {x : A x = 0}, one vector per row of the
    /// result; the result has `self.cols()` columns and `cols - rank` rows.
    pub fn kernel_basis(&self, f: &PrimeField) -> DenseMat {
        let (m, pivots) = self.rref(f);
        let mut is_pivot = vec![false; self.cols];
        for &c in &pivots {
            is_pivot[c] = true;
        }
        let free: Vec<usize> = (0..self.cols).filter(|&c| !is_pivot[c]).collect();
        let mut out = DenseMat::zero(free.len(), self.cols);
        for (i, &fc) in free.iter().enumerate() {
            out.set(i, fc, Fp::ONE);
            for (j, &pc) in pivots.iter().enumerate() {
                out.set(i, pc, f.neg(m.get(j, fc)));
            }
        }
        out
    }

    /// A basis of the row space: the nonzero rows of the reduced row echelon
    /// form, one vector per row of the result.
    pub fn row_space_basis(&self, f: &PrimeField) -> DenseMat {
        let (m, pivots) = self.rref(f);
        let k = pivots.len();
        DenseMat {
            rows: k,
            cols: m.cols,
            data: m.data[..k * m.cols].to_vec(),
        }
    }

    /// A basis of the column space, one vector per row of the result (each of
    /// length `self.rows()`): the row-space basis of the transpose.
    pub fn image_basis(&self, f: &PrimeField) -> DenseMat {
        self.transpose().row_space_basis(f)
    }

    /// A solution of A x = b with free variables set to zero, or `None` when
    /// the system is inconsistent; `b` has length `self.rows()`.
    ///
    /// # Panics
    /// Panics on length mismatch.
    pub fn solve(&self, b: &[Fp], f: &PrimeField) -> Option<Vec<Fp>> {
        assert_eq!(
            b.len(),
            self.rows,
            "solve: rhs length vs {} rows",
            self.rows
        );
        let width = self.cols + 1;
        let mut aug = DenseMat::zero(self.rows, width);
        for (r, &bv) in b.iter().enumerate() {
            aug.data[r * width..r * width + self.cols]
                .copy_from_slice(&self.data[r * self.cols..(r + 1) * self.cols]);
            aug.data[r * width + self.cols] = bv;
        }
        let pivots = aug.rref_in_place(f);
        if pivots.last() == Some(&self.cols) {
            return None;
        }
        let mut x = vec![Fp::ZERO; self.cols];
        for (i, &pc) in pivots.iter().enumerate() {
            x[pc] = aug.get(i, self.cols);
        }
        Some(x)
    }

    /// The position of the first entry whose stored representative is not
    /// canonical for `f` (that is, not below `f.modulus()`), scanning row by
    /// row, or `None` when every entry is canonical.
    pub(crate) fn first_noncanonical(&self, f: &PrimeField) -> Option<(usize, usize)> {
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

    /// self += c * other, merging sorted entries.
    pub fn add_scaled(&mut self, other: &SparseRow, c: Fp, f: &PrimeField) {
        if c.is_zero() || other.is_zero() {
            return;
        }
        let mut result = Vec::with_capacity(self.entries.len() + other.entries.len());
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
        self.entries = result;
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

    /// self * rhs.
    ///
    /// # Panics
    /// Panics unless `self.cols() == rhs.rows()`.
    pub fn mul(&self, rhs: &SparseMat, f: &PrimeField) -> SparseMat {
        assert_eq!(
            self.cols, rhs.rows,
            "mul: {}x{} times {}x{}",
            self.rows, self.cols, rhs.rows, rhs.cols
        );
        let data = self
            .data
            .iter()
            .map(|lhs_row| {
                let mut row = SparseRow::new();
                for &(c, v) in &lhs_row.entries {
                    row.add_scaled(&rhs.data[c], v, f);
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

    /// A x for a sparse vector `x` indexed by column; the result is indexed by
    /// row.
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
    // first, so each elimination factor is just the negated leading
    // coefficient.
    fn echelon_in_place(&mut self, f: &PrimeField) -> Vec<usize> {
        let mut pivots = Vec::new();
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
                    row.add_scaled(pivot, f.neg(coeff), f);
                }
            }
            pivots.push(col);
            pr += 1;
        }
        pivots
    }

    /// The reduced row echelon form and its pivot columns.
    ///
    /// Pivot rows come first in pivot-column order; zero rows follow.
    pub fn rref(&self, f: &PrimeField) -> (SparseMat, Vec<usize>) {
        let mut m = self.clone();
        let pivots = m.echelon_in_place(f);
        for i in (0..pivots.len()).rev() {
            let col = pivots[i];
            let (above, rest) = m.data.split_at_mut(i);
            let pivot = &rest[0];
            for row in above {
                let v = row.get(col);
                if !v.is_zero() {
                    row.add_scaled(pivot, f.neg(v), f);
                }
            }
        }
        (m, pivots)
    }

    /// dim of the row space (equivalently, of the column space).
    pub fn rank(&self, f: &PrimeField) -> usize {
        self.clone().echelon_in_place(f).len()
    }

    /// A basis of the right null space {x : A x = 0}, one vector per row of the
    /// result; the result has `self.cols()` columns and `cols - rank` rows.
    pub fn kernel_basis(&self, f: &PrimeField) -> SparseMat {
        let (m, pivots) = self.rref(f);
        let mut is_pivot = vec![false; self.cols];
        for &c in &pivots {
            is_pivot[c] = true;
        }
        let mut data = Vec::new();
        for free in (0..self.cols).filter(|&c| !is_pivot[c]) {
            let mut v = SparseRow::new();
            v.set(free, Fp::ONE);
            for (i, &pc) in pivots.iter().enumerate() {
                let val = m.data[i].get(free);
                if !val.is_zero() {
                    v.set(pc, f.neg(val));
                }
            }
            data.push(v);
        }
        SparseMat {
            rows: data.len(),
            cols: self.cols,
            data,
        }
    }

    /// A basis of the row space: the nonzero rows of the reduced row echelon
    /// form, one vector per row of the result.
    pub fn row_space_basis(&self, f: &PrimeField) -> SparseMat {
        let (mut m, pivots) = self.rref(f);
        m.data.truncate(pivots.len());
        m.rows = pivots.len();
        m
    }

    /// A basis of the column space, one vector per row of the result (each of
    /// length `self.rows()`): the row-space basis of the transpose.
    pub fn image_basis(&self, f: &PrimeField) -> SparseMat {
        self.transpose().row_space_basis(f)
    }

    /// A solution of A x = b with free variables set to zero, or `None` when
    /// the system is inconsistent; `b` is indexed by row.
    ///
    /// # Panics
    /// Panics if `b` has an index `>= self.rows()`.
    pub fn solve(&self, b: &SparseRow, f: &PrimeField) -> Option<SparseRow> {
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
        let (m, pivots) = aug.rref(f);
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

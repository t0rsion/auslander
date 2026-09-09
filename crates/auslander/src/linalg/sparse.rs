use super::dense::DenseMat;
use super::merge_scaled_terms;
use crate::field::{Fp, PrimeField};
use crate::profile::{Site, hit};

/// Sparse vector: (column, value) pairs sorted by column, values nonzero.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SparseRow {
    pub(in crate::linalg) entries: Vec<(usize, Fp)>,
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

    accessor_methods! {
        /// The nonzero entries, sorted by column.
        pub entries() -> &[(usize, Fp)] = |this| &this.entries;
        /// The value at `col`, zero when absent.
        pub get(col: usize) -> Fp = |this| this.entries
            .binary_search_by_key(&col, |&(c, _)| c)
            .map_or(Fp::ZERO, |i| this.entries[i].1);
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

    accessor_methods! {
        /// Whether the vector is zero.
        pub is_zero() -> bool = |this| this.entries.is_empty();
        /// Number of nonzero entries.
        pub nnz() -> usize = |this| this.entries.len();
        leading() -> Option<(usize, Fp)> = |this| this.entries.first().copied();
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
        merge_scaled_terms(
            &self.entries,
            &other.entries,
            (c, f),
            |left, right| left.0.cmp(&right.0),
            |term| term.1,
            |term, value| (term.0, value),
            scratch,
        );
        std::mem::swap(&mut self.entries, scratch);
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
    pub(in crate::linalg) rows: usize,
    pub(in crate::linalg) cols: usize,
    pub(in crate::linalg) data: Vec<SparseRow>,
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

    accessor_methods! {
        /// Number of rows.
        pub rows() -> usize = |this| this.rows;
        /// Number of columns.
        pub cols() -> usize = |this| this.cols;
        /// Row `r`.
        ///
        /// # Panics
        /// Panics if `r` is out of range.
        pub row(r: usize) -> &SparseRow = |this| &this.data[r];
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
            let Some(idx) = (pr..self.rows)
                .filter(|&r| self.data[r].leading().is_some_and(|(c, _)| c == col))
                .min_by_key(|&r| self.data[r].nnz())
            else {
                continue;
            };
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
    /// Pivot rows come first in pivot-column order; zero rows follow.
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

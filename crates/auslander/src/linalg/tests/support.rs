use crate::field::{Fp, PrimeField};
use crate::linalg::{DenseMat, SparseRow};

pub(super) fn f(p: u64) -> PrimeField {
    PrimeField::new(p).unwrap()
}

pub(super) fn dense(fp: &PrimeField, rows: &[&[i64]]) -> DenseMat {
    let rows: Vec<Vec<Fp>> = rows
        .iter()
        .map(|r| r.iter().map(|&v| fp.elem(v)).collect())
        .collect();
    DenseMat::from_rows(&rows)
}

pub(super) fn sparse_vec(v: &[Fp]) -> SparseRow {
    let mut row = SparseRow::new();
    for (i, &x) in v.iter().enumerate() {
        row.set(i, x);
    }
    row
}

pub(super) fn dense_vec(row: &SparseRow, len: usize) -> Vec<Fp> {
    (0..len).map(|i| row.get(i)).collect()
}

pub(super) struct XorShift64(pub(super) u64);

impl XorShift64 {
    pub(super) fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    pub(super) fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
}

pub(super) fn random_dense(
    rng: &mut XorShift64,
    fp: &PrimeField,
    rows: usize,
    cols: usize,
) -> DenseMat {
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

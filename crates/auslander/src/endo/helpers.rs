use crate::field::{Fp, PrimeField};
use crate::linalg::DenseMat;

/// Columns at which a coordinate row can be read off `flat`, and the inverse of
/// the submatrix there when that submatrix is not the identity.
///
/// The coordinates `x` of `f` are the solution of `x · flat = flat_row(f)`, so
/// for any `dim` columns whose submatrix `S` is invertible, `x` is
/// `flat_row(f)` restricted to those columns times `S⁻¹`. [`crate::hom::hom_rows`]
/// hands back a kernel basis carrying a 1 in its own free column and 0 in every
/// other free column, in the [`flat_row`] layout, so the free columns give
/// `S = I` and reading coordinates off is a selection. The scan finds them
/// without knowing which columns were free: a column that is a unit vector
/// claims its row. The pivot columns are the fallback for a basis without that
/// shape.
pub(super) fn coordinate_columns(
    flat: &DenseMat,
    field: &PrimeField,
) -> (Vec<usize>, Option<DenseMat>) {
    let unit_column = |c: usize| -> Option<usize> {
        let mut hit = None;
        for r in 0..flat.rows() {
            let v = flat.get(r, c);
            if v.is_zero() {
                continue;
            }
            if hit.is_some() || v != Fp::ONE {
                return None;
            }
            hit = Some(r);
        }
        hit
    };
    let mut cols = vec![usize::MAX; flat.rows()];
    let mut found = 0;
    for c in 0..flat.cols() {
        if let Some(r) = unit_column(c)
            && cols[r] == usize::MAX
        {
            cols[r] = c;
            found += 1;
            if found == flat.rows() {
                return (cols, None);
            }
        }
    }
    let (_, pivots) = flat.rref(field);
    let mut square = DenseMat::zero(flat.rows(), pivots.len());
    for (j, &c) in pivots.iter().enumerate() {
        for r in 0..flat.rows() {
            square.set(r, j, flat.get(r, c));
        }
    }
    let inverse = square
        .inverse(field)
        .expect("pivot columns are independent");
    (pivots, Some(inverse))
}

pub(super) fn unit_row(dim: usize, index: usize) -> Vec<Fp> {
    let mut row = vec![Fp::ZERO; dim];
    row[index] = Fp::ONE;
    row
}

/// Multiplies two coordinate rows through square structure constants.
pub(super) fn coordinate_product(
    a: &[Fp],
    b: &[Fp],
    table: &[Vec<Fp>],
    field: PrimeField,
) -> Vec<Fp> {
    let dim = a.len();
    let mut out = vec![Fp::ZERO; dim];
    for (i, &ai) in a.iter().enumerate().filter(|(_, c)| !c.is_zero()) {
        for (j, &bj) in b.iter().enumerate().filter(|(_, c)| !c.is_zero()) {
            let scale = field.mul(ai, bj);
            for (out, &c) in out.iter_mut().zip(&table[i * dim + j]) {
                *out = field.add(*out, field.mul(scale, c));
            }
        }
    }
    out
}

/// Seeded deterministic PRNG (splitmix64). The only randomness in the crate.
pub(crate) struct SplitMix64(pub(crate) u64);

impl SplitMix64 {
    pub(crate) fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    pub(crate) fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
}

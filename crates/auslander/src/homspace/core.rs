use crate::field::{Fp, PrimeField};
use crate::hom::Morphism;
use crate::linalg::{DenseMat, RowReducer};
use crate::module::Module;

use super::HomSpaceError;

/// The morphism as one flat row: the vertex matrices flattened row-major,
/// concatenated in vertex order. This is the layout `hom_rows` solves in, so
/// a kernel row is already a flat row.
pub(crate) fn flat_row(f: &Morphism) -> Vec<Fp> {
    let mut row = Vec::with_capacity(flat_width(f.source(), f.target()));
    for v in 0..f.source().algebra().quiver().num_vertices() {
        let map = f.map_at(v);
        for r in 0..map.rows() {
            row.extend_from_slice(map.row(r));
        }
    }
    row
}

pub(super) fn flat_width(m: &Module, n: &Module) -> usize {
    m.dim_vector()
        .iter()
        .zip(n.dim_vector())
        .map(|(&a, &b)| a * b)
        .sum()
}

/// The morphism whose flat row is `row`, the inverse of [`flat_row`].
///
/// `row` must be a linear combination of the flat rows of morphisms
/// `source -> target`, with canonical entries for the modules' field.
/// Flattening is a linear bijection between the vertex-matrix tuples and rows of
/// width [`flat_width`], so the unflattening of a combination of flat rows is
/// the same combination of morphisms. `Hom_A(M, N)` is a subspace of the tuples,
/// so that combination is A-linear and the result skips the commuting-square
/// check. The blocks are cut at `dim source_v x dim target_v`, the shape
/// `Morphism::new` would demand.
pub(super) fn morphism_from_flat(source: &Module, target: &Module, row: &[Fp]) -> Morphism {
    let num_vertices = source.algebra().quiver().num_vertices();
    let mut maps = Vec::with_capacity(num_vertices as usize);
    let mut offset = 0;
    for v in 0..num_vertices {
        let (dm, dn) = (source.dim_at(v), target.dim_at(v));
        let block = DenseMat::from_flat(dm, dn, &row[offset..offset + dm * dn]);
        offset += dm * dn;
        maps.push(block);
    }
    Morphism::new_unchecked(source, target, maps)
}

/// `row * m` over `field`, of length `m.cols()`. `row` has one entry per row
/// of `m`.
pub(crate) fn row_times(row: &[Fp], m: &DenseMat, field: &PrimeField) -> Vec<Fp> {
    let mut out = vec![Fp::ZERO; m.cols()];
    for (k, &c) in row.iter().enumerate() {
        if c.is_zero() {
            continue;
        }
        for (j, out_j) in out.iter_mut().enumerate() {
            *out_j = field.add(*out_j, field.mul(c, m.get(k, j)));
        }
    }
    out
}

/// The unique coordinates of `v` over the rows of `rref`, or `None` when `v`
/// lies outside the row space.
///
/// `rref` must be in reduced row echelon form with no zero row, as every
/// stored basis in the crate is. Then row `r` is the only row with a nonzero
/// entry in its pivot column, so the coordinate at `r` is `v` at that column
/// and no free variable exists. The final multiplication decides membership.
pub(crate) fn rref_coords(rref: &DenseMat, v: &[Fp], field: &PrimeField) -> Option<Vec<Fp>> {
    if rref.cols() != v.len() {
        return None;
    }
    let coords: Vec<Fp> = rref_pivots(rref).map(|pivot| v[pivot]).collect();
    (row_times(&coords, rref, field) == v).then_some(coords)
}

fn rref_pivots(rref: &DenseMat) -> impl Iterator<Item = usize> + '_ {
    (0..rref.rows()).map(|r| {
        rref.row(r)
            .iter()
            .position(|e| !e.is_zero())
            .expect("a reduced row echelon basis has no zero row")
    })
}

/// [`rref_coords`] over many vectors: row `r` of the result holds the
/// coordinates of row `r` of `rows`, and `None` means some row lies outside the
/// row space.
pub(crate) fn rref_coords_many(
    rref: &DenseMat,
    rows: &DenseMat,
    field: &PrimeField,
) -> Option<DenseMat> {
    if rref.cols() != rows.cols() {
        return None;
    }
    if rows.rows() == 0 {
        return Some(DenseMat::zero(0, rref.rows()));
    }
    let pivots: Vec<usize> = rref_pivots(rref).collect();
    let mut coords = DenseMat::zero(rows.rows(), rref.rows());
    for r in 0..rows.rows() {
        for (c, &pivot) in pivots.iter().enumerate() {
            coords.set(r, c, rows.get(r, pivot));
        }
    }
    (coords.mul(rref, field) == *rows).then_some(coords)
}

/// The morphism with every entry multiplied by `c`, which must be canonical for
/// the modules' field.
///
/// The result skips the commuting-square check. Scaling every entry of every
/// vertex matrix by `c` scales both sides of each square by `c`, because a scalar
/// pulls through a matrix product: `(c f)_{s(a)} · N(a) = c (f_{s(a)} · N(a))`
/// equals `c (M(a) · f_{t(a)}) = M(a) · (c f)_{t(a)}`. The blocks keep the
/// shapes of `f`, and `PrimeField::mul` returns canonical entries.
pub(crate) fn scale_morphism(f: &Morphism, c: Fp) -> Morphism {
    let field = f.source().field();
    let maps = (0..f.source().algebra().quiver().num_vertices())
        .map(|v| {
            let mut block = f.map_at(v).clone();
            block.scale(c, &field);
            block
        })
        .collect();
    Morphism::new_unchecked(f.source(), f.target(), maps)
}

pub(super) fn check_endpoints(
    source: &Module,
    target: &Module,
    f: &Morphism,
) -> Result<(), HomSpaceError> {
    if f.source().ptr_eq(source) {
        f.target()
            .ptr_eq(target)
            .then_some(())
            .ok_or(HomSpaceError::TargetMismatch)
    } else {
        Err(HomSpaceError::SourceMismatch)
    }
}

/// The matrices stacked in order, all with `cols` columns. An empty stack is
/// the `0 x cols` matrix.
pub(crate) fn stack_rows(matrices: &[&DenseMat], cols: usize) -> DenseMat {
    DenseMat::stack(matrices, cols)
}

/// The crate-wide complement rule: scan the rows of `ambient` in order and
/// keep each row that increases the rank of `inner` plus the rows kept so far.
/// The kept rows are the complement basis. This is the only complement
/// construction in the crate.
///
/// One [`RowReducer`] carries the rank test across the scan. The kept rows are
/// copies of `ambient` rows in scan order.
pub(crate) fn deterministic_complement(
    ambient: &DenseMat,
    inner: &DenseMat,
    field: &PrimeField,
) -> DenseMat {
    let empty = DenseMat::zero(0, ambient.cols());
    let mut reducer = RowReducer::new(ambient.cols());
    for r in 0..inner.rows() {
        // A dependent row of `inner` puts the rank of every stacked test
        // below its row count, so the rule keeps nothing. Both callers pass
        // an RREF basis, where this cannot happen.
        if !reducer.push(inner.row(r), field) {
            return empty;
        }
    }
    let kept: Vec<Vec<Fp>> = (0..ambient.rows())
        .filter(|&r| reducer.push(ambient.row(r), field))
        .map(|r| ambient.row(r).to_vec())
        .collect();
    DenseMat::from_rows_with_cols(&kept, ambient.cols())
}

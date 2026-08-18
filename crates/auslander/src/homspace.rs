//! `Hom_A(M, N)` as an explicit vector space: fixed basis, flat coordinates,
//! subspaces, and deterministic quotients.
//!
//! A [`HomSpace`] stores the `hom_rows` rows, in the order `hom_rows`
//! fixes: kernel variables vertex-major, then row-major inside a vertex, and
//! one basis vector per free column in increasing column order. That layout is
//! the flattening itself, the per-vertex matrices row-major concatenated in
//! vertex order, so row `i` is basis morphism `i` and a caller pays for a
//! [`Morphism`] only where it asks for one. A [`HomSubspace`] stores the
//! reduced row echelon form of its spanning set in these flat coordinates, so
//! two subspaces of compatible spaces are equal exactly when their matrices
//! are equal.
//!
//! The complement rule is fixed crate-wide: to complement a subspace `B`
//! inside an ambient subspace `Z`, scan the RREF basis rows of `Z` in order
//! and keep each row that increases the rank of `B` plus the rows kept so
//! far. [`HomQuotient`] representatives are combinations of the kept rows, so
//! rebuilding a quotient from the same modules gives the same representatives.
//! The AR quiver reads its irreducible-map classes off those representatives,
//! and `tests/determinism_ar.rs` compares the resulting renderings byte for
//! byte, in-process and across a fresh process.
//!
//! Two spaces are compatible when their sources are [`Module::ptr_eq`] and
//! their targets are [`Module::ptr_eq`]. The basis construction is
//! deterministic, so recomputed compatible spaces have identical bases and
//! coordinates transport verbatim. An operation on a morphism whose
//! endpoints do not match is a typed [`HomSpaceError`], never a silent
//! reinterpretation.
//!
//! The file also holds the crate-private helpers that the Ext, sequence, and
//! almost-split layers share with this one: `row_times`, `stack_rows`,
//! `rref_coords`, `scale_morphism`, and `deterministic_complement`. One copy
//! each, so a change to the complement rule or to a coordinate convention
//! lands in one place.

use std::fmt;
use std::sync::OnceLock;

use crate::field::{Fp, PrimeField};
use crate::hom::{HomError, Morphism, hom_rows};
use crate::linalg::{DenseMat, RowReducer};
use crate::module::Module;

/// Rejected Hom space input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HomSpaceError {
    /// The morphism's source is not this space's source module (by
    /// [`Module::ptr_eq`]).
    SourceMismatch,
    /// The morphism's target is not this space's target module (by
    /// [`Module::ptr_eq`]).
    TargetMismatch,
    /// The two subspaces do not share both endpoint modules (by
    /// [`Module::ptr_eq`]).
    IncompatibleSubspaces,
    /// The claimed inner subspace has a basis row outside the ambient
    /// subspace.
    NotContained,
    /// The morphism lies outside the ambient subspace of the quotient.
    OutsideSubspace,
}

impl fmt::Display for HomSpaceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SourceMismatch => f.write_str("the morphism's source is not the space's source"),
            Self::TargetMismatch => f.write_str("the morphism's target is not the space's target"),
            Self::IncompatibleSubspaces => {
                f.write_str("the subspaces do not share both endpoint modules")
            }
            Self::NotContained => {
                f.write_str("the inner subspace is not contained in the ambient subspace")
            }
            Self::OutsideSubspace => {
                f.write_str("the morphism lies outside the ambient subspace of the quotient")
            }
        }
    }
}

impl std::error::Error for HomSpaceError {}

/// The morphism as one flat row: the vertex matrices flattened row-major,
/// concatenated in vertex order. This is the layout `hom_rows` solves in, so
/// a kernel row is already a flat row.
pub(crate) fn flat_row(f: &Morphism) -> Vec<Fp> {
    let mut row = Vec::new();
    for v in 0..f.source().algebra().quiver().num_vertices() {
        let map = f.map_at(v);
        for r in 0..map.rows() {
            row.extend_from_slice(map.row(r));
        }
    }
    row
}

fn flat_width(m: &Module, n: &Module) -> usize {
    m.dim_vector()
        .iter()
        .zip(n.dim_vector())
        .map(|(&a, &b)| a * b)
        .sum()
}

/// The morphism whose flat row is `row`, the inverse of [`flat_row`].
///
/// `row` must be a linear combination of the flat rows of morphisms
/// `source -> target`, with canonical entries for the modules' field. Every
/// caller in this file passes one: [`HomSpace::morphism`] combines the rows of
/// `flat`, [`HomSubspace::basis_morphism`] takes a row of the row-space basis of
/// the spanning rows, [`HomQuotient::representative`] combines complement rows,
/// which are rows of that same basis, and [`HomQuotient::reduce`] combines the
/// RREF rows of the subspace.
///
/// Flattening is a linear bijection between the vertex-matrix tuples and rows of
/// width [`flat_width`], so the unflattening of a combination of flat rows is the
/// same combination of morphisms. `Hom_A(M, N)` is a subspace of the tuples, so
/// that combination is A-linear and the result skips the commuting-square check.
/// The blocks are cut at `dim source_v x dim target_v`, the shape
/// `Morphism::new` would demand.
fn morphism_from_flat(source: &Module, target: &Module, row: &[Fp]) -> Morphism {
    let num_vertices = source.algebra().quiver().num_vertices();
    let mut maps = Vec::with_capacity(num_vertices as usize);
    let mut offset = 0;
    for v in 0..num_vertices {
        let (dm, dn) = (source.dim_at(v), target.dim_at(v));
        let mut block = DenseMat::zero(dm, dn);
        for r in 0..dm {
            for c in 0..dn {
                block.set(r, c, row[offset + r * dn + c]);
            }
        }
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
    let coords: Vec<Fp> = (0..rref.rows())
        .map(|r| {
            let pivot = rref
                .row(r)
                .iter()
                .position(|e| !e.is_zero())
                .expect("a reduced row echelon basis has no zero row");
            v[pivot]
        })
        .collect();
    (row_times(&coords, rref, field) == v).then_some(coords)
}

/// [`rref_coords`] over many vectors: row `r` of the result holds the
/// coordinates of row `r` of `rows`, and `None` means some row lies outside
/// the row space.
///
/// The pivot columns are found once for the whole call and one matrix product
/// decides every row, where a loop over [`rref_coords`] rescans the pivots and
/// runs a separate `row_times` per row.
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
    let pivots: Vec<usize> = (0..rref.rows())
        .map(|r| {
            rref.row(r)
                .iter()
                .position(|e| !e.is_zero())
                .expect("a reduced row echelon basis has no zero row")
        })
        .collect();
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
/// equals `c (M(a) · f_{t(a)}) = M(a) · (c f)_{t(a)}`. The blocks keep the shapes
/// of `f`, and `PrimeField::mul` returns canonical entries.
pub(crate) fn scale_morphism(f: &Morphism, c: Fp) -> Morphism {
    let field = f.source().field();
    let maps = (0..f.source().algebra().quiver().num_vertices())
        .map(|v| {
            let block = f.map_at(v);
            let mut out = DenseMat::zero(block.rows(), block.cols());
            for r in 0..block.rows() {
                for j in 0..block.cols() {
                    out.set(r, j, field.mul(c, block.get(r, j)));
                }
            }
            out
        })
        .collect();
    Morphism::new_unchecked(f.source(), f.target(), maps)
}

fn check_endpoints(source: &Module, target: &Module, f: &Morphism) -> Result<(), HomSpaceError> {
    if !f.source().ptr_eq(source) {
        return Err(HomSpaceError::SourceMismatch);
    }
    if !f.target().ptr_eq(target) {
        return Err(HomSpaceError::TargetMismatch);
    }
    Ok(())
}

/// The matrices stacked in order, all with `cols` columns. An empty stack is
/// the `0 x cols` matrix.
pub(crate) fn stack_rows(matrices: &[&DenseMat], cols: usize) -> DenseMat {
    let rows: Vec<Vec<Fp>> = matrices
        .iter()
        .flat_map(|m| (0..m.rows()).map(|r| m.row(r).to_vec()))
        .collect();
    if rows.is_empty() {
        DenseMat::zero(0, cols)
    } else {
        DenseMat::from_rows(&rows)
    }
}

/// The crate-wide complement rule: scan the rows of `ambient` in order and
/// keep each row that increases the rank of `inner` plus the rows kept so
/// far. The kept rows are the complement basis. This is the only complement
/// construction in the crate.
///
/// One [`RowReducer`] carries the rank test across the scan, where a rank
/// call per candidate row rebuilt the whole elimination. The decision is
/// exact either way, and the kept rows are copies of `ambient` rows in scan
/// order, so the result is byte for byte what the rule names.
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
    let mut kept: Vec<Vec<Fp>> = Vec::new();
    for r in 0..ambient.rows() {
        if reducer.push(ambient.row(r), field) {
            kept.push(ambient.row(r).to_vec());
        }
    }
    if kept.is_empty() {
        empty
    } else {
        DenseMat::from_rows(&kept)
    }
}

/// `Hom_A(M, N)` as its flat rows, in the order `hom_rows` fixes.
///
/// The rows are the primary form: row `i` is basis element `i` flattened, so
/// [`HomSpace::dim`] and every coordinate operation read them directly and no
/// [`Morphism`] is built. [`HomSpace::basis_morphism`] unflattens one row,
/// [`HomSpace::basis_iter`] unflattens the rows a caller consumes, and
/// [`HomSpace::basis`] unflattens all of them once and keeps them, for callers
/// that want the whole slice.
///
/// Fields are private; construction goes through [`HomSpace::new`], so the rows
/// are always the deterministic `hom_rows` rows of the stored endpoints.
#[derive(Clone, Debug)]
pub struct HomSpace {
    source: Module,
    target: Module,
    // One row per basis element, flattened as in `flat_row`.
    flat: DenseMat,
    // The whole materialized basis, filled by the first `basis` call.
    basis: OnceLock<Vec<Morphism>>,
}

impl HomSpace {
    /// Builds `Hom(m, n)` with the `hom_rows` rows in their deterministic
    /// order. Errors when the modules do not share one algebra, as `hom_rows`.
    pub fn new(m: &Module, n: &Module) -> Result<HomSpace, HomError> {
        Ok(HomSpace {
            source: m.clone(),
            target: n.clone(),
            flat: hom_rows(m, n)?,
            basis: OnceLock::new(),
        })
    }

    /// `dim_k Hom(M, N)`.
    #[inline]
    pub fn dim(&self) -> usize {
        self.flat.rows()
    }

    /// The source module `M`.
    #[inline]
    pub fn source(&self) -> &Module {
        &self.source
    }

    /// The target module `N`.
    #[inline]
    pub fn target(&self) -> &Module {
        &self.target
    }

    /// Basis morphism `i`, unflattened from row `i`.
    ///
    /// # Panics
    /// Panics unless `i` is below [`HomSpace::dim`].
    pub fn basis_morphism(&self, i: usize) -> Morphism {
        morphism_from_flat(&self.source, &self.target, self.flat.row(i))
    }

    /// The basis morphisms in order, each unflattened as the iterator reaches
    /// it. A caller that stops early pays for nothing past the last one it took.
    pub fn basis_iter(&self) -> impl Iterator<Item = Morphism> + '_ {
        (0..self.dim()).map(|i| self.basis_morphism(i))
    }

    /// The whole basis, materialized once and kept; coordinates index into this
    /// list. Use [`HomSpace::basis_morphism`] or [`HomSpace::basis_iter`] to
    /// take fewer.
    pub fn basis(&self) -> &[Morphism] {
        self.basis.get_or_init(|| self.basis_iter().collect())
    }

    /// The whole basis, materialized and taken by value.
    pub fn into_basis(self) -> Vec<Morphism> {
        self.into_parts().1
    }

    /// The flat rows and the whole basis, both taken by value, so a caller that
    /// keeps the two does not copy the rows.
    pub(crate) fn into_parts(self) -> (DenseMat, Vec<Morphism>) {
        let HomSpace {
            source,
            target,
            flat,
            basis,
        } = self;
        let basis = basis.into_inner().unwrap_or_else(|| {
            (0..flat.rows())
                .map(|i| morphism_from_flat(&source, &target, flat.row(i)))
                .collect()
        });
        (flat, basis)
    }

    /// Whether coordinates transport verbatim between the two spaces: sources
    /// are [`Module::ptr_eq`] and targets are [`Module::ptr_eq`].
    pub fn is_compatible(&self, other: &HomSpace) -> bool {
        self.source.ptr_eq(&other.source) && self.target.ptr_eq(&other.target)
    }

    /// The morphism with the given coordinates in the basis. The coordinates
    /// must be canonical elements of the modules' field.
    ///
    /// # Panics
    /// Panics unless `coords` has length [`HomSpace::dim`].
    pub fn morphism(&self, coords: &[Fp]) -> Morphism {
        assert_eq!(
            coords.len(),
            self.dim(),
            "morphism: needs one coordinate per basis element"
        );
        let field = self.source.field();
        let row = row_times(coords, &self.flat, &field);
        morphism_from_flat(&self.source, &self.target, &row)
    }

    /// Coordinates of `f` in the basis. Errors when either endpoint of `f` is
    /// not the matching endpoint of this space (by [`Module::ptr_eq`]).
    pub fn coords(&self, f: &Morphism) -> Result<Vec<Fp>, HomSpaceError> {
        check_endpoints(&self.source, &self.target, f)?;
        let field = self.source.field();
        Ok(self
            .flat
            .transpose()
            .solve(&flat_row(f), &field)
            .expect("the hom basis spans every morphism between the endpoints"))
    }

    /// The subspace spanned by the given morphisms, stored as the RREF of
    /// their flat rows. Errors when a spanning morphism has an endpoint that
    /// is not the matching endpoint of this space.
    pub fn subspace(&self, spanning: &[Morphism]) -> Result<HomSubspace, HomSpaceError> {
        HomSubspace::spanned_by(&self.source, &self.target, spanning)
    }

    /// The whole space as a subspace of itself.
    pub fn full_subspace(&self) -> HomSubspace {
        let field = self.source.field();
        HomSubspace {
            source: self.source.clone(),
            target: self.target.clone(),
            basis: self.flat.row_space_basis(&field),
        }
    }
}

/// A subspace of a Hom space, stored as the RREF of its spanning set in flat
/// coordinates.
///
/// Fields are private; construction goes through [`HomSpace::subspace`] or
/// [`HomSpace::full_subspace`], so the stored matrix is always the RREF.
#[derive(Clone, Debug)]
pub struct HomSubspace {
    source: Module,
    target: Module,
    // One basis vector per row, in reduced row echelon form.
    basis: DenseMat,
}

/// Two subspaces are equal when their endpoints are pointer-identical (see
/// [`Module::ptr_eq`]) and their RREF matrices are equal. The RREF is unique,
/// so equality does not depend on the spanning set.
impl PartialEq for HomSubspace {
    fn eq(&self, other: &HomSubspace) -> bool {
        self.source.ptr_eq(&other.source)
            && self.target.ptr_eq(&other.target)
            && self.basis == other.basis
    }
}

impl Eq for HomSubspace {}

impl HomSubspace {
    /// The subspace of `Hom(source, target)` spanned by the given morphisms,
    /// stored as the RREF of their flat rows.
    ///
    /// The `hom_rows` rows play no part, so a caller that needs only a span
    /// skips building the whole [`HomSpace`]. Errors when a spanning morphism
    /// has an endpoint that is not the matching module (by [`Module::ptr_eq`]).
    pub(crate) fn spanned_by(
        source: &Module,
        target: &Module,
        spanning: &[Morphism],
    ) -> Result<HomSubspace, HomSpaceError> {
        for f in spanning {
            check_endpoints(source, target, f)?;
        }
        let field = source.field();
        let rows: Vec<Vec<Fp>> = spanning.iter().map(flat_row).collect();
        let stacked = if rows.is_empty() {
            DenseMat::zero(0, flat_width(source, target))
        } else {
            DenseMat::from_rows(&rows)
        };
        Ok(HomSubspace {
            source: source.clone(),
            target: target.clone(),
            basis: stacked.row_space_basis(&field),
        })
    }

    /// The source module of the parent space.
    #[inline]
    pub fn source(&self) -> &Module {
        &self.source
    }

    /// The target module of the parent space.
    #[inline]
    pub fn target(&self) -> &Module {
        &self.target
    }

    /// The dimension of the subspace.
    #[inline]
    pub fn dim(&self) -> usize {
        self.basis.rows()
    }

    /// The basis over flat coordinates, one vector per row, in reduced row
    /// echelon form.
    #[inline]
    pub fn rref_basis(&self) -> &DenseMat {
        &self.basis
    }

    /// The morphism of RREF basis row `r`.
    ///
    /// # Panics
    /// Panics if `r` is out of range.
    pub fn basis_morphism(&self, r: usize) -> Morphism {
        morphism_from_flat(&self.source, &self.target, self.basis.row(r))
    }

    /// Whether `f` lies in the subspace: a row-space membership test. Errors
    /// when an endpoint of `f` does not match (by [`Module::ptr_eq`]).
    pub fn contains(&self, f: &Morphism) -> Result<bool, HomSpaceError> {
        Ok(self.witness_contains(f)?.is_some())
    }

    /// The solving coordinates of `f` over the RREF basis, or `None` when `f`
    /// lies outside the subspace. To recheck membership, multiply the
    /// coordinates against [`HomSubspace::rref_basis`]. Errors when an
    /// endpoint of `f` does not match (by [`Module::ptr_eq`]).
    pub fn witness_contains(&self, f: &Morphism) -> Result<Option<Vec<Fp>>, HomSpaceError> {
        check_endpoints(&self.source, &self.target, f)?;
        let field = self.source.field();
        Ok(rref_coords(&self.basis, &flat_row(f), &field))
    }

    /// The quotient of this subspace by `sub`, with the complement built by
    /// the crate-wide rule: scan the RREF rows of `self` in order and keep
    /// each row that increases the rank of `sub` plus the rows kept so far.
    ///
    /// Errors with [`HomSpaceError::IncompatibleSubspaces`] when the
    /// endpoints differ and with [`HomSpaceError::NotContained`] when a basis
    /// row of `sub` lies outside `self`.
    pub fn quotient_by(&self, sub: &HomSubspace) -> Result<HomQuotient, HomSpaceError> {
        if !(self.source.ptr_eq(&sub.source) && self.target.ptr_eq(&sub.target)) {
            return Err(HomSpaceError::IncompatibleSubspaces);
        }
        let field = self.source.field();
        if rref_coords_many(&self.basis, &sub.basis, &field).is_none() {
            return Err(HomSpaceError::NotContained);
        }
        let complement = deterministic_complement(&self.basis, &sub.basis, &field);
        Ok(HomQuotient {
            subspace: sub.clone(),
            complement,
        })
    }
}

/// A quotient of Hom subspaces with deterministic representatives: the
/// denominator subspace plus the complement rows kept by the crate-wide rule.
///
/// Fields are private; construction goes through [`HomSubspace::quotient_by`].
#[derive(Clone, Debug)]
pub struct HomQuotient {
    subspace: HomSubspace,
    // Rows of the ambient RREF kept by the complement rule, in scan order.
    complement: DenseMat,
}

impl HomQuotient {
    /// The source module of the parent space.
    #[inline]
    pub fn source(&self) -> &Module {
        &self.subspace.source
    }

    /// The target module of the parent space.
    #[inline]
    pub fn target(&self) -> &Module {
        &self.subspace.target
    }

    /// The dimension of the quotient.
    #[inline]
    pub fn dim(&self) -> usize {
        self.complement.rows()
    }

    /// The denominator subspace.
    #[inline]
    pub fn subspace(&self) -> &HomSubspace {
        &self.subspace
    }

    /// The complement rows over flat coordinates, one vector per row, in the
    /// scan order of the complement rule.
    #[inline]
    pub fn complement_basis(&self) -> &DenseMat {
        &self.complement
    }

    /// The representative morphism with the given coordinates over the
    /// complement basis. The coordinates must be canonical elements of the
    /// modules' field.
    ///
    /// # Panics
    /// Panics unless `coords` has length [`HomQuotient::dim`].
    pub fn representative(&self, coords: &[Fp]) -> Morphism {
        assert_eq!(
            coords.len(),
            self.dim(),
            "representative: needs one coordinate per complement row"
        );
        let field = self.subspace.source.field();
        let row = row_times(coords, &self.complement, &field);
        morphism_from_flat(&self.subspace.source, &self.subspace.target, &row)
    }

    /// Splits `f` as representative plus subspace member: the coordinates
    /// over the complement basis, and the member of the denominator subspace
    /// with `representative(coords) + member = f`. The split solves against
    /// the stacked complement-plus-RREF system, so it is deterministic.
    ///
    /// Errors when an endpoint of `f` does not match (by [`Module::ptr_eq`])
    /// and with [`HomSpaceError::OutsideSubspace`] when `f` lies outside the
    /// ambient subspace.
    pub fn reduce(&self, f: &Morphism) -> Result<(Vec<Fp>, Morphism), HomSpaceError> {
        check_endpoints(&self.subspace.source, &self.subspace.target, f)?;
        let field = self.subspace.source.field();
        let stacked = stack_rows(
            &[&self.complement, &self.subspace.basis],
            self.complement.cols(),
        );
        let Some(x) = stacked.transpose().solve(&flat_row(f), &field) else {
            return Err(HomSpaceError::OutsideSubspace);
        };
        let coords = x[..self.complement.rows()].to_vec();
        let member_row = row_times(&x[self.complement.rows()..], &self.subspace.basis, &field);
        let member = morphism_from_flat(&self.subspace.source, &self.subspace.target, &member_row);
        Ok((coords, member))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{commutative_square, dual_numbers, linear_an};
    use crate::decompose::add_morphisms;
    use crate::field::PrimeField;
    use crate::hom::zero_morphism;
    use crate::module::direct_sum;

    fn f5() -> PrimeField {
        PrimeField::new(5).unwrap()
    }

    fn fixture_endpoints() -> Vec<(Module, Module)> {
        let field = f5();
        let mut endpoints = Vec::new();
        for algebra in [
            linear_an(3, field),
            dual_numbers(field),
            commutative_square(field),
        ] {
            let last = algebra.quiver().num_vertices() - 1;
            let p = Module::projective(&algebra, 0);
            let s = Module::simple(&algebra, last);
            let (sum, _, _) = direct_sum(&[&p, &s, &p]);
            endpoints.push((sum.clone(), sum));
            endpoints.push((p, direct_sum(&[&s, &s]).0));
        }
        endpoints
    }

    fn fixture_spaces() -> Vec<HomSpace> {
        fixture_endpoints()
            .iter()
            .map(|(m, n)| HomSpace::new(m, n).unwrap())
            .collect()
    }

    fn unit(dim: usize, k: usize, field: &PrimeField) -> Vec<Fp> {
        let mut v = vec![field.zero(); dim];
        v[k] = field.one();
        v
    }

    #[test]
    fn basis_round_trip_recovers_coordinates() {
        for space in fixture_spaces() {
            let field = space.source().field();
            for k in 0..space.dim() {
                let coords = unit(space.dim(), k, &field);
                let f = space.morphism(&coords);
                assert_eq!(f, space.basis()[k], "unit {k} rebuilds basis element {k}");
                assert_eq!(space.coords(&f).unwrap(), coords);
            }
            let mixed: Vec<Fp> = (0..space.dim() as i64).map(|i| field.elem(i + 1)).collect();
            assert_eq!(space.coords(&space.morphism(&mixed)).unwrap(), mixed);
        }
    }

    #[test]
    fn flat_rows_stack_the_vertex_matrices_row_major() {
        let algebra = linear_an(3, f5());
        let p0 = Module::projective(&algebra, 0);
        let space = HomSpace::new(&p0, &p0).unwrap();
        assert_eq!(space.flat.cols(), 3);
        assert_eq!(space.dim(), 1);
        let expected = flat_row(&space.basis()[0]);
        assert_eq!(space.flat.row(0), expected.as_slice());
    }

    #[test]
    fn recomputed_compatible_spaces_have_identical_bases() {
        for (m, n) in fixture_endpoints() {
            let first = HomSpace::new(&m, &n).unwrap();
            let second = HomSpace::new(&m, &n).unwrap();
            assert!(first.is_compatible(&second));
            assert_eq!(first.flat.entries_u64(), second.flat.entries_u64());
            for (f, g) in first.basis().iter().zip(second.basis()) {
                assert_eq!(f, g);
            }
        }
    }

    #[test]
    fn coords_rejects_wrong_endpoints_with_typed_errors() {
        let algebra = linear_an(3, f5());
        let p0 = Module::projective(&algebra, 0);
        let s0 = Module::simple(&algebra, 0);
        let space = HomSpace::new(&p0, &s0).unwrap();
        let p0_copy = Module::projective(&algebra, 0);
        let s0_copy = Module::simple(&algebra, 0);
        let wrong_source = HomSpace::new(&p0_copy, &s0).unwrap().basis_morphism(0);
        assert_eq!(
            space.coords(&wrong_source).unwrap_err(),
            HomSpaceError::SourceMismatch
        );
        let wrong_target = HomSpace::new(&p0, &s0_copy).unwrap().basis_morphism(0);
        assert_eq!(
            space.coords(&wrong_target).unwrap_err(),
            HomSpaceError::TargetMismatch
        );
        assert_eq!(
            space
                .subspace(std::slice::from_ref(&wrong_target))
                .unwrap_err(),
            HomSpaceError::TargetMismatch
        );
        let full = space.full_subspace();
        assert_eq!(
            full.contains(&wrong_source).unwrap_err(),
            HomSpaceError::SourceMismatch
        );
        let quotient = full.quotient_by(&space.subspace(&[]).unwrap()).unwrap();
        assert_eq!(
            quotient.reduce(&wrong_source).unwrap_err(),
            HomSpaceError::SourceMismatch
        );
    }

    #[test]
    fn hom_space_new_rejects_modules_over_different_algebras() {
        let a = linear_an(3, f5());
        let b = linear_an(3, f5());
        let m = Module::simple(&a, 0);
        let n = Module::simple(&b, 0);
        assert_eq!(
            HomSpace::new(&m, &n).unwrap_err(),
            HomError::DifferentAlgebras
        );
    }

    #[test]
    fn subspace_rref_is_invariant_under_permuted_and_rescaled_spanning_sets() {
        for space in fixture_spaces() {
            if space.dim() < 2 {
                continue;
            }
            let field = space.source().field();
            let f = space.morphism(&unit(space.dim(), 0, &field));
            let g = space.morphism(&unit(space.dim(), 1, &field));
            let mut mixed = unit(space.dim(), 0, &field);
            mixed[1] = field.elem(2);
            let h = space.morphism(&mixed);
            let scaled_coords: Vec<Fp> = unit(space.dim(), 1, &field)
                .iter()
                .map(|&c| field.mul(c, field.elem(3)))
                .collect();
            let g_scaled = space.morphism(&scaled_coords);
            let first = space.subspace(&[f.clone(), g.clone(), h.clone()]).unwrap();
            let second = space.subspace(&[h, g_scaled, f]).unwrap();
            assert_eq!(first, second);
            assert_eq!(
                first.rref_basis().entries_u64(),
                second.rref_basis().entries_u64()
            );
            assert_eq!(first.dim(), 2);
        }
    }

    #[test]
    fn empty_spanning_set_gives_the_zero_subspace() {
        for space in fixture_spaces() {
            let sub = space.subspace(&[]).unwrap();
            assert_eq!(sub.dim(), 0);
            let zero = zero_morphism(space.source(), space.target()).unwrap();
            assert_eq!(sub.witness_contains(&zero).unwrap(), Some(Vec::new()));
            if space.dim() > 0 {
                assert!(!sub.contains(&space.basis()[0]).unwrap());
            }
        }
    }

    #[test]
    fn witness_contains_returns_solving_coordinates() {
        for space in fixture_spaces() {
            if space.dim() < 2 {
                continue;
            }
            let field = space.source().field();
            let sub = space
                .subspace(&[space.basis()[0].clone(), space.basis()[1].clone()])
                .unwrap();
            let mut coords = unit(space.dim(), 0, &field);
            coords[1] = field.elem(4);
            let f = space.morphism(&coords);
            let witness = sub.witness_contains(&f).unwrap().expect("f spans inside");
            let rebuilt = morphism_from_flat(
                space.source(),
                space.target(),
                &row_times(&witness, sub.rref_basis(), &field),
            );
            assert_eq!(rebuilt, f, "witness coordinates rebuild the morphism");
            if space.dim() > 2 {
                let outside = space.morphism(&unit(space.dim(), 2, &field));
                assert_eq!(sub.witness_contains(&outside).unwrap(), None);
            }
        }
    }

    #[test]
    fn complement_rule_is_deterministic_across_recomputation() {
        for (m, n) in fixture_endpoints() {
            let build = |space: &HomSpace| {
                let z = space.full_subspace();
                let sub = space.subspace(&space.basis()[..1]).unwrap();
                z.quotient_by(&sub).unwrap()
            };
            let first_space = HomSpace::new(&m, &n).unwrap();
            let second_space = HomSpace::new(&m, &n).unwrap();
            if first_space.dim() == 0 {
                continue;
            }
            let first = build(&first_space);
            let second = build(&second_space);
            assert_eq!(
                first.complement_basis().entries_u64(),
                second.complement_basis().entries_u64()
            );
            assert_eq!(
                first.subspace().rref_basis().entries_u64(),
                second.subspace().rref_basis().entries_u64()
            );
        }
    }

    #[test]
    fn complement_rows_come_from_the_ambient_rref_in_scan_order() {
        for space in fixture_spaces() {
            let z = space.full_subspace();
            let sub = space.subspace(&[]).unwrap();
            let quotient = z.quotient_by(&sub).unwrap();
            assert_eq!(
                quotient.complement_basis().entries_u64(),
                z.rref_basis().entries_u64(),
                "the complement of the zero subspace keeps every ambient row"
            );
        }
    }

    #[test]
    fn quotient_reduce_returns_complement_coordinates_plus_a_subspace_member() {
        for space in fixture_spaces() {
            let field = space.source().field();
            let z = space.full_subspace();
            for sub_size in 0..=space.dim().min(2) {
                let sub = space.subspace(&space.basis()[..sub_size]).unwrap();
                let quotient = z.quotient_by(&sub).unwrap();
                assert_eq!(quotient.dim() + sub.dim(), z.dim());
                let mut probes: Vec<Morphism> = space.basis().to_vec();
                if space.dim() > 0 {
                    let mixed: Vec<Fp> =
                        (0..space.dim() as i64).map(|i| field.elem(i + 2)).collect();
                    probes.push(space.morphism(&mixed));
                }
                for f in &probes {
                    let (coords, member) = quotient.reduce(f).unwrap();
                    assert_eq!(coords.len(), quotient.dim());
                    assert!(sub.contains(&member).unwrap());
                    let rebuilt = add_morphisms(&quotient.representative(&coords), &member);
                    assert_eq!(rebuilt, *f, "representative + member = original");
                }
            }
        }
    }

    #[test]
    fn reduce_rejects_an_element_outside_the_ambient_subspace() {
        for space in fixture_spaces() {
            if space.dim() < 2 {
                continue;
            }
            let z = space.subspace(&space.basis()[..1]).unwrap();
            let sub = space.subspace(&[]).unwrap();
            let quotient = z.quotient_by(&sub).unwrap();
            assert_eq!(
                quotient.reduce(&space.basis()[1]).unwrap_err(),
                HomSpaceError::OutsideSubspace
            );
        }
    }

    #[test]
    fn quotient_by_rejects_incompatible_and_uncontained_subspaces() {
        let algebra = linear_an(3, f5());
        let p0 = Module::projective(&algebra, 0);
        let s0 = Module::simple(&algebra, 0);
        let space = HomSpace::new(&p0, &s0).unwrap();
        assert!(space.dim() >= 1);
        let small = space.subspace(&[]).unwrap();
        let full = space.full_subspace();
        assert_eq!(
            small.quotient_by(&full).unwrap_err(),
            HomSpaceError::NotContained
        );
        let p0_copy = Module::projective(&algebra, 0);
        let other_space = HomSpace::new(&p0_copy, &s0).unwrap();
        assert_eq!(
            full.quotient_by(&other_space.full_subspace()).unwrap_err(),
            HomSpaceError::IncompatibleSubspaces
        );
    }
}

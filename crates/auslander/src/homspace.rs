//! `Hom_A(M, N)` as an explicit vector space: fixed basis, flat coordinates,
//! subspaces, and deterministic quotients.
//!
//! The basis of a [`HomSpace`] is exactly [`hom`] in its deterministic order.
//! Each basis morphism flattens to one row: the per-vertex matrices row-major,
//! concatenated in vertex order. A [`HomSubspace`] stores the reduced row
//! echelon form of its spanning set in these flat coordinates, so two
//! subspaces of compatible spaces are equal exactly when their matrices are
//! equal.
//!
//! The complement rule is fixed crate-wide: to complement a subspace `B`
//! inside an ambient subspace `Z`, scan the RREF basis rows of `Z` in order
//! and keep each row that increases the rank of `B` plus the rows kept so
//! far. [`HomQuotient`] representatives are combinations of the kept rows,
//! so they are deterministic.
//!
//! Two spaces are compatible when their sources are [`Module::ptr_eq`] and
//! their targets are [`Module::ptr_eq`]. The basis construction is
//! deterministic, so recomputed compatible spaces have identical bases and
//! coordinates transport verbatim. An operation on a morphism whose
//! endpoints do not match is a typed [`HomSpaceError`], never a silent
//! reinterpretation.

use std::fmt;

use crate::field::{Fp, PrimeField};
use crate::hom::{HomError, Morphism, hom};
use crate::linalg::DenseMat;
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

/// One row per morphism: the vertex matrices flattened row-major and
/// concatenated in vertex order.
fn flat_row(f: &Morphism) -> Vec<Fp> {
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

fn morphism_from_flat(source: &Module, target: &Module, row: &[Fp]) -> Morphism {
    let mut maps = Vec::new();
    let mut offset = 0;
    for v in 0..source.algebra().quiver().num_vertices() {
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
    Morphism::new(source, target, maps).expect("flat rows in the span of a hom basis are A-linear")
}

fn combine_rows(rows: &DenseMat, coords: &[Fp], field: &PrimeField) -> Vec<Fp> {
    let mut out = vec![Fp::ZERO; rows.cols()];
    for (k, &c) in coords.iter().enumerate() {
        if c.is_zero() {
            continue;
        }
        for (j, out_j) in out.iter_mut().enumerate() {
            *out_j = field.add(*out_j, field.mul(c, rows.get(k, j)));
        }
    }
    out
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

fn stack_rows(matrices: &[&DenseMat], cols: usize) -> DenseMat {
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
pub(crate) fn deterministic_complement(
    ambient: &DenseMat,
    inner: &DenseMat,
    field: &PrimeField,
) -> DenseMat {
    let mut rows: Vec<Vec<Fp>> = (0..inner.rows()).map(|r| inner.row(r).to_vec()).collect();
    let mut kept: Vec<Vec<Fp>> = Vec::new();
    for r in 0..ambient.rows() {
        rows.push(ambient.row(r).to_vec());
        if DenseMat::from_rows(&rows).rank(field) == rows.len() {
            kept.push(ambient.row(r).to_vec());
        } else {
            rows.pop();
        }
    }
    if kept.is_empty() {
        DenseMat::zero(0, ambient.cols())
    } else {
        DenseMat::from_rows(&kept)
    }
}

/// `Hom_A(M, N)` with the [`hom`] basis and its flat coordinates.
///
/// Fields are private; construction goes through [`HomSpace::new`], so the
/// basis is always the deterministic [`hom`] basis of the stored endpoints.
#[derive(Clone, Debug)]
pub struct HomSpace {
    source: Module,
    target: Module,
    basis: Vec<Morphism>,
    // One row per basis morphism, flattened as in `flat_row`.
    flat: DenseMat,
}

impl HomSpace {
    /// Builds `Hom(m, n)` with the [`hom`] basis in its deterministic order.
    /// Errors when the modules do not share one algebra, as [`hom`].
    pub fn new(m: &Module, n: &Module) -> Result<HomSpace, HomError> {
        let basis = hom(m, n)?;
        let cols = flat_width(m, n);
        let mut flat = DenseMat::zero(basis.len(), cols);
        for (r, f) in basis.iter().enumerate() {
            for (c, &v) in flat_row(f).iter().enumerate() {
                flat.set(r, c, v);
            }
        }
        Ok(HomSpace {
            source: m.clone(),
            target: n.clone(),
            basis,
            flat,
        })
    }

    /// `dim_k Hom(M, N)`.
    #[inline]
    pub fn dim(&self) -> usize {
        self.basis.len()
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

    /// The basis morphisms; coordinates index into this list.
    #[inline]
    pub fn basis(&self) -> &[Morphism] {
        &self.basis
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
        assert_eq!(coords.len(), self.dim(), "morphism: coordinate count");
        let field = self.source.field();
        let row = combine_rows(&self.flat, coords, &field);
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
        for f in spanning {
            check_endpoints(&self.source, &self.target, f)?;
        }
        let field = self.source.field();
        let rows: Vec<Vec<Fp>> = spanning.iter().map(flat_row).collect();
        let stacked = if rows.is_empty() {
            DenseMat::zero(0, self.flat.cols())
        } else {
            DenseMat::from_rows(&rows)
        };
        Ok(HomSubspace {
            source: self.source.clone(),
            target: self.target.clone(),
            basis: stacked.row_space_basis(&field),
        })
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
    /// lies outside the subspace. A caller rechecks membership by multiplying
    /// the coordinates against [`HomSubspace::rref_basis`]. Errors when an
    /// endpoint of `f` does not match (by [`Module::ptr_eq`]).
    pub fn witness_contains(&self, f: &Morphism) -> Result<Option<Vec<Fp>>, HomSpaceError> {
        check_endpoints(&self.source, &self.target, f)?;
        let field = self.source.field();
        Ok(self.basis.transpose().solve(&flat_row(f), &field))
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
        let basis_t = self.basis.transpose();
        for r in 0..sub.basis.rows() {
            if basis_t.solve(sub.basis.row(r), &field).is_none() {
                return Err(HomSpaceError::NotContained);
            }
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
        assert_eq!(coords.len(), self.dim(), "representative: coordinate count");
        let field = self.subspace.source.field();
        let row = combine_rows(&self.complement, coords, &field);
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
        let member_row = combine_rows(&self.subspace.basis, &x[self.complement.rows()..], &field);
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
        let wrong_source = hom(&p0_copy, &s0).unwrap().remove(0);
        assert_eq!(
            space.coords(&wrong_source).unwrap_err(),
            HomSpaceError::SourceMismatch
        );
        let wrong_target = hom(&p0, &s0_copy).unwrap().remove(0);
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
                &combine_rows(sub.rref_basis(), &witness, &field),
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

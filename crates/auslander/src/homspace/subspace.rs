use crate::field::Fp;
use crate::hom::Morphism;
use crate::linalg::DenseMat;
use crate::module::Module;

use super::core::{
    check_endpoints, deterministic_complement, flat_row, flat_width, rref_coords, rref_coords_many,
};
use super::{HomQuotient, HomSpaceError, HomSubspace};

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
    /// Does not build the whole [`super::HomSpace`]. Errors when a spanning
    /// morphism has an endpoint that is not the matching module (by
    /// [`Module::ptr_eq`]).
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
        let stacked = DenseMat::from_rows_with_cols(&rows, flat_width(source, target));
        Ok(HomSubspace {
            source: source.clone(),
            target: target.clone(),
            basis: stacked.row_space_basis(&field),
        })
    }

    accessor_methods! {
        /// The source module of the parent space.
        pub source() -> &Module = |this| &this.source;
        /// The target module of the parent space.
        pub target() -> &Module = |this| &this.target;
        /// The dimension of the subspace.
        pub dim() -> usize = |this| this.basis.rows();
        /// The basis over flat coordinates, one vector per row, in reduced row
        /// echelon form.
        pub rref_basis() -> &DenseMat = |this| &this.basis;
        /// The morphism of RREF basis row `r`.
        ///
        /// # Panics
        /// Panics if `r` is out of range.
        pub basis_morphism(r: usize) -> Morphism = |this| super::core::morphism_from_flat(&this.source, &this.target, this.basis.row(r));
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

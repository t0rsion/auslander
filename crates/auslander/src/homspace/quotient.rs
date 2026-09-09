use crate::field::Fp;
use crate::hom::Morphism;
use crate::linalg::DenseMat;
use crate::module::Module;

use super::core::{check_endpoints, flat_row, morphism_from_flat, row_times, stack_rows};
use super::{HomQuotient, HomSpaceError, HomSubspace};

impl HomQuotient {
    accessor_methods! {
        /// The source module of the parent space.
        pub source() -> &Module = |this| &this.subspace.source;
        /// The target module of the parent space.
        pub target() -> &Module = |this| &this.subspace.target;
        /// The dimension of the quotient.
        pub dim() -> usize = |this| this.complement.rows();
        /// The denominator subspace.
        pub subspace() -> &HomSubspace = |this| &this.subspace;
        /// The complement rows over flat coordinates, one vector per row, in the
        /// scan order of the complement rule.
        pub complement_basis() -> &DenseMat = |this| &this.complement;
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

    /// Splits `f` as representative plus subspace member: the coordinates over
    /// the complement basis, and the member of the denominator subspace with
    /// `representative(coords) + member = f`. The split solves against the
    /// stacked complement-plus-RREF system, so it is deterministic.
    ///
    /// Errors when an endpoint of `f` does not match (by
    /// [`Module::ptr_eq`])
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

use std::sync::OnceLock;

use crate::field::Fp;
use crate::hom::{HomError, Morphism, hom_rows};
use crate::linalg::DenseMat;
use crate::module::Module;
use crate::profile::{Site, hit};

use super::core::{flat_row, morphism_from_flat, row_times};
use super::{HomSpace, HomSpaceError, HomSubspace};

impl HomSpace {
    /// Builds `Hom(m, n)` with the `hom_rows` rows in their deterministic
    /// order. Errors when the modules do not share one algebra, as `hom_rows`.
    pub fn new(m: &Module, n: &Module) -> Result<HomSpace, HomError> {
        hit(Site::HomSpaceNew);
        hom_rows(m, n).map(|flat| HomSpace {
            source: m.clone(),
            target: n.clone(),
            flat,
            basis: OnceLock::new(),
        })
    }

    /// Builds a Hom space from rows proved to be the commuting-square kernel.
    ///
    /// The rows must use the flat variable order fixed by [`HomSpace`]. Debug
    /// builds recompute [`HomSpace::new`] and compare the exact basis.
    pub(crate) fn from_checked_flat(source: &Module, target: &Module, flat: DenseMat) -> HomSpace {
        debug_assert!(
            HomSpace::new(source, target).is_ok_and(|generic| generic.flat == flat),
            "from_checked_flat: rows differ from the generic Hom basis"
        );
        HomSpace {
            source: source.clone(),
            target: target.clone(),
            flat,
            basis: OnceLock::new(),
        }
    }

    accessor_methods! {
        /// `dim_k Hom(M, N)`.
        pub dim() -> usize = |this| this.flat.rows();
        /// The source module `M`.
        pub source() -> &Module = |this| &this.source;
        /// The target module `N`.
        pub target() -> &Module = |this| &this.target;
        /// Basis morphism `i`, unflattened from row `i`.
        ///
        /// # Panics
        /// Panics unless `i` is below [`HomSpace::dim`].
        pub basis_morphism(i: usize) -> Morphism = |this| morphism_from_flat(&this.source, &this.target, this.flat.row(i));
    }

    /// The basis morphisms in order, each unflattened as the iterator reaches it.
    pub fn basis_iter(&self) -> impl Iterator<Item = Morphism> + '_ {
        (0..self.dim()).map(|i| self.basis_morphism(i))
    }

    /// The whole basis, built once and kept. Coordinates index into this list.
    /// Use [`HomSpace::basis_morphism`] or [`HomSpace::basis_iter`] to take fewer.
    pub fn basis(&self) -> &[Morphism] {
        self.basis.get_or_init(|| self.basis_iter().collect())
    }

    /// The whole basis, taken by value.
    pub fn into_basis(self) -> Vec<Morphism> {
        self.into_parts().1
    }

    /// The flat rows and the whole basis, both taken by value.
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
        super::core::check_endpoints(&self.source, &self.target, f)?;
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

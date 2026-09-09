use crate::hom::Morphism;
use crate::module::Module;
use crate::profile::{Site, hit};

use super::common::{is_direct_sum, trace_dims};

/// A proof that `X_j` lies in `Fac(M/X_j)`, so slot `j` admits no left
/// mutation.
///
/// `X in Fac U` exactly when finitely many maps `f_i : U -> X` have images
/// summing to all of `X`, which is to say the induced `U^r -> X` is onto. The
/// witness is that family. It does not claim the family spans `Hom(U, X)`:
/// spanning is stronger than the definition of `Fac` and nothing here needs
/// it. The only constructor is [`crate::mutation::mutate_at`].
///
/// By AIR Definition-Proposition 2.28 the mutation at this slot is then a
/// right mutation. This is a statement about the slot, not a failure.
#[derive(Clone, Debug)]
pub struct FacWitness {
    pub(super) module: Module,
    // The summands of U, shared with the decomposition of the source pair.
    pub(super) summands: Vec<Module>,
    pub(super) summand: Module,
    pub(super) maps: Vec<Morphism>,
}

impl FacWitness {
    accessor_methods! {
        /// `U = M/X_j`, the module part with the slot summand dropped.
        pub module() -> &Module = |this| &this.module;
        /// The summands of `U`, in the order they hold in the source pair.
        ///
        /// These are the module values of the source decomposition, not copies,
        /// so a caller binds the witness to its pair by [`Module::ptr_eq`] on each
        /// one. A dimension vector does not bind: two non-isomorphic modules can
        /// share one, as three of the `kronecker(2)` indecomposables do.
        pub summands() -> &[Module] = |this| &this.summands;
        /// `X_j`, the summand the slot addresses.
        pub summand() -> &Module = |this| &this.summand;
        /// The maps `U -> X_j` whose images were summed.
        pub maps() -> &[Morphism] = |this| &this.maps;
        /// The dimension of the sum of the images at each vertex, recomputed from
        /// the stored maps. On a witness that verifies it is the dimension vector
        /// of `X_j`.
        pub image_dims() -> Vec<usize> = |this| trace_dims(&this.maps, &this.summand);
    }

    /// Recomputes the rank equality from the stored maps.
    ///
    /// `U` must be the direct sum of the stored summands in order, entry for
    /// entry. Every stored map must run from `U` to `X_j`. The images must
    /// sum to the dimension vector of `X_j` at every vertex. A dropped map
    /// fails the rank check as soon as the remaining images stop covering
    /// `X_j`. No [`crate::homspace::HomSpace`] is rebuilt.
    ///
    /// The first check binds `U` to the summands. A caller that also compares
    /// [`FacWitness::summands`] against its own pair by [`Module::ptr_eq`]
    /// knows which module the rank equality was proved over.
    pub fn verify(&self) -> bool {
        hit(Site::FacWitnessVerify);
        is_direct_sum(&self.module, &self.summands)
            && self
                .maps
                .iter()
                .all(|f| f.source().ptr_eq(&self.module) && f.target().ptr_eq(&self.summand))
            && trace_dims(&self.maps, &self.summand) == self.summand.dim_vector()
    }
}

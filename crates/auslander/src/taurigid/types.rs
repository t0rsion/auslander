use crate::ar::TauError;
use crate::context::VerificationContext;
use crate::hom::{HomError, Morphism};
use crate::homspace::HomSpace;
use crate::iso::{IsoOutcome, is_isomorphic};
use crate::linalg::DenseMat;
use crate::module::Module;
use crate::profile::{Site, hit};

/// Why a tau-rigidity decision could not be reached.
///
/// Neither variant is an answer about the module. A tau-rigidity answer is a
/// [`super::TauRigidityOutcome`].
#[derive(Clone, Debug)]
pub enum TauRigidError {
    /// The AR translate of a summand did not come back certified. See
    /// [`TauError`] for the three cases.
    Tau(TauError),
    /// A Hom space could not be built. That happens when two summands do not
    /// share one algebra [`std::sync::Arc`].
    Hom(HomError),
}

display_error! { TauRigidError {
    Self::Tau(error) => "the AR translate of a summand failed: {error}";
    Self::Hom(error) => "a Hom space between summands failed: {error}";
} }

error_source!(TauRigidError {
    Self::Tau(error) => Some(error),
    Self::Hom(error) => Some(error),
});

from_variants!(TauRigidError {
    TauError => Tau,
    HomError => Hom,
});

/// A module certified tau-rigid, stored by its summands.
///
/// Construction goes through [`super::is_tau_rigid_summandwise`] or
/// [`super::is_tau_rigid`], so every value carries a certified translate per
/// summand and a checked `dim Hom(X_i, tau X_j) = 0` for every ordered pair.
/// The vanishing is not stored: a zero space has no element to exhibit, so the
/// type itself is the proof token and [`TauRigidModule::verify`] recomputes
/// both the translates and the dimensions.
///
/// The module itself is not stored. It is the direct sum of
/// [`TauRigidModule::summands`]. Assembling it would put `tau` on a
/// decomposable module. An empty summand list is the zero module, which is
/// tau-rigid with no pairs to check. The support tau-tilting pair `(0, A)`
/// depends on that case.
#[derive(Clone, Debug)]
pub struct TauRigidModule {
    // The caller's stable index and the module, in the order supplied. The
    // index is a label for witnesses and bindings, never a cache key.
    pub(super) summands: Vec<(usize, Module)>,
    // translates[j] is the certified AR translate of summands[j]. Zero
    // exactly when the summand is projective.
    pub(super) translates: Vec<Module>,
}

impl TauRigidModule {
    accessor_methods! {
        /// The summands with the caller's stable indices, in the order supplied.
        /// An empty slice is the zero module.
        pub summands() -> &[(usize, Module)] = |this| &this.summands;
        /// The certified translate of each summand, in summand order. Zero
        /// exactly on a projective summand. See [`crate::ar::tau`].
        pub translates() -> &[Module] = |this| &this.translates;
    }

    /// The ordered summand pairs `(i, j)` whose `Hom(X_i, tau X_j)` was
    /// checked, by the caller's indices, in `(i, j)` lexicographic order over
    /// summand positions.
    ///
    /// A pair with `tau X_j = 0` is not listed: `Hom(X_i, 0)` is zero for
    /// every `X_i` and no Hom system runs for it.
    pub fn vanishing_pairs(&self) -> Vec<(usize, usize)> {
        let mut out = Vec::new();
        for (source_index, _) in &self.summands {
            for ((target_index, _), translate) in self.summands.iter().zip(&self.translates) {
                if !translate.is_zero() {
                    out.push((*source_index, *target_index));
                }
            }
        }
        out
    }

    accessor_methods! {
        /// Whether the certified module is the zero module, meaning it has no
        /// summands.
        pub is_zero_module() -> bool = |this| this.summands.is_empty();
    }

    verify_methods!(pub(crate), { hit(Site::TauRigidVerify); },
        /// Rechecks the claim against the live modules.
        ///
        /// The vanishing is not stored, so both the translates and the Hom
        /// dimensions are recomputed. Each summand's translate, through the
        /// certified double route of [`crate::ar::tau`], must match the stored
        /// one: both zero, or both nonzero and certified isomorphic. Then
        /// `dim Hom(X_i, tau X_j)` against the fresh translate is zero for
        /// every ordered pair whose translate is nonzero.
        |self, context| {
        verify_guard!(self.translates.len() == self.summands.len());
        let mut fresh = Vec::with_capacity(self.summands.len());
        for ((_, x), stored) in self.summands.iter().zip(&self.translates) {
            let_or_false!(Ok(live) = context.tau_for(x));
            verify_guard!(live.is_zero() == stored.is_zero());
            // The stored translate is a different module value than a fresh
            // one, so the comparison is a certified isomorphism and never
            // pointer identity.
            verify_guard!(live.is_zero()
                || matches!(
                    is_isomorphic(live.as_ref(), stored),
                    Ok(IsoOutcome::Isomorphic(_))
                ));
            fresh.push(live);
        }
        for (_, x) in &self.summands {
            for live in &fresh {
                if live.is_zero() {
                    continue;
                }
                verify_guard!(matches!(context.hom_dim_for(x, live), Ok(0)));
            }
        }
        true
    });
}

/// One nonzero morphism `X_i -> tau X_j`, which proves `M` is not tau-rigid.
///
/// Construction goes through [`super::is_tau_rigid_summandwise`]. The stored
/// morphism is the first basis morphism of the first nonzero
/// `Hom(X_i, tau X_j)` in `(i, j)` lexicographic order. The choice is
/// deterministic, not canonical.
///
/// The morphism is a summand-level map. `Hom(X_i, tau X_j)` is a direct
/// summand of `Hom(M, tau M)` under additivity of `tau` and `Hom`, so a
/// nonzero element of it is a nonzero element of `Hom(M, tau M)`.
#[derive(Clone, Debug)]
pub struct NonTauRigidWitness {
    pub(super) source_index: usize,
    pub(super) target_index: usize,
    pub(super) source: Module,
    // The summand X_j itself, so verification can recompute its translate.
    pub(super) target_summand: Module,
    // tau X_j as computed, the target of the stored morphism.
    pub(super) translate: Module,
    pub(super) morphism: Morphism,
}

impl NonTauRigidWitness {
    accessor_methods! {
        /// The caller's index of the summand `X_i` the morphism starts at.
        pub source_index() -> usize = |this| this.source_index;
        /// The caller's index of the summand `X_j` whose translate the morphism
        /// ends at.
        pub target_index() -> usize = |this| this.target_index;
        /// The summand `X_i`.
        pub source() -> &Module = |this| &this.source;
        /// The summand `X_j`, whose translate is the morphism's target.
        pub target_summand() -> &Module = |this| &this.target_summand;
        /// `tau X_j`, as computed by the double route.
        pub translate() -> &Module = |this| &this.translate;
        /// The nonzero morphism `X_i -> tau X_j`.
        pub morphism() -> &Morphism = |this| &this.morphism;
    }

    verify_methods!(pub(crate), {},
        /// Rechecks that the stored morphism is a nonzero element of
        /// `Hom(X_i, tau X_j)`.
        ///
        /// The morphism must run from the stored source to the stored
        /// translate, and its vertex matrices must pass [`Morphism::new`]
        /// again. `tau X_j`, through the certified double route, must be
        /// nonzero and certified isomorphic to the stored translate.
        /// `Hom(X_i, tau X_j)`, rebuilt from the endpoints, must contain the
        /// morphism, and the morphism must be nonzero.
        |self, context| {
        verify_guard!(self.morphism.source().ptr_eq(&self.source)
            && self.morphism.target().ptr_eq(&self.translate));
        let vertices = self.source.algebra().quiver().num_vertices();
        let maps: Vec<DenseMat> = (0..vertices)
            .map(|v| self.morphism.map_at(v).clone())
            .collect();
        let_or_false!(Ok(rebuilt) = Morphism::new(&self.source, &self.translate, maps));
        verify_guard!(rebuilt == self.morphism);
        let_or_false!(Ok(live) = context.tau_for(&self.target_summand));
        verify_guard!(!live.is_zero());
        verify_guard!(matches!(
            is_isomorphic(live.as_ref(), &self.translate),
            Ok(IsoOutcome::Isomorphic(_))
        ));
        let_or_false!(Ok(space) = HomSpace::new(&self.source, &self.translate));
        verify_guard!(matches!(
            space.full_subspace().contains(&self.morphism),
            Ok(true)
        ));
        !self.morphism.is_zero()
    });
}

/// The answer to a tau-rigidity question.
#[derive(Clone, Debug)]
pub enum TauRigidityOutcome {
    /// `Hom(M, tau M) = 0`, with a certified translate per summand.
    TauRigid(TauRigidModule),
    /// `Hom(M, tau M)` is nonzero, with one nonzero morphism that proves it.
    NotTauRigid(NonTauRigidWitness),
}

impl TauRigidityOutcome {
    accessor_methods! {
        /// Whether the outcome is [`TauRigidityOutcome::TauRigid`].
        pub is_tau_rigid() -> bool = |this| matches!(this, Self::TauRigid(_));
    }
}

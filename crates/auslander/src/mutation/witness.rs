use std::sync::Arc;

use crate::basic::{
    AddClosureWitness, BasicDecomposition, ProjectiveSupport, SupportPairIsoOutcome,
    SupportPairObstruction,
};
use crate::context::VerificationContext;
use crate::decompose::Certificate;
use crate::hom::Morphism;
use crate::indec::IndecomposableModule;
use crate::iso::indecomposable_iso;
use crate::module::Module;
use crate::profile::{Site, hit};
use crate::supporttau::{AlmostCompletePair, SupportTauTiltingPair};

use super::common::is_cokernel;

/// The shape of a left mutation at a module summand slot.
///
/// The two shapes are AIR Theorem 2.30(a) and (b). There is no third: a
/// projective summand is never exchanged for a projective, and a module
/// summand is never exchanged for two summands.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExchangeShape {
    /// `supp(U)` is smaller than `supp(M)`. The approximation has zero
    /// cokernel, the module part loses `X_j`, and `vertex` joins the
    /// projective support.
    MovesToProjective {
        /// The one vertex of `supp(M) \ supp(U)`.
        vertex: u32,
    },
    /// `supp(U)` equals `supp(M)`. The cokernel is `multiplicity` copies of
    /// one indecomposable, which enters the module part.
    ReplacedByModule {
        /// The number of summands of the cokernel.
        multiplicity: usize,
    },
}

/// The five checks that identify the target as the mutation, plus the exchange
/// sequence that built it.
///
/// The only constructor is [`crate::mutation::mutate_at`], so a value of this
/// type carries a certified almost complete pair, an `add` closure witness per
/// endpoint, a proof that the endpoints differ, and a certified target pair.
/// [`MutationWitness::verify`] recomputes all of it.
///
/// The approximation and the cokernel map are construction data. They record
/// how the target was built. AIR Theorem 2.18 is what proves the target is the
/// mutation. See the module documentation.
#[derive(Debug)]
pub struct MutationWitness {
    pub(super) slot: usize,
    pub(super) exchanged: Module,
    pub(super) almost_complete: AlmostCompletePair,
    pub(super) source_module: Module,
    pub(super) source_projective: Vec<u32>,
    pub(super) source_extension: AddClosureWitness,
    pub(super) target_module: Module,
    pub(super) target_projective: Vec<u32>,
    pub(super) target_extension: AddClosureWitness,
    pub(super) distinct: SupportPairObstruction,
    pub(super) approximation: crate::approx::MinimalLeftApproximation,
    // g: B -> Y, the cokernel of the approximation.
    pub(super) exchange: Morphism,
    pub(super) shape: ExchangeShape,
    // Y_1, present exactly for ExchangeShape::ReplacedByModule.
    pub(super) replacement: Option<Module>,
}

impl MutationWitness {
    accessor_methods! {
        /// The slot the mutation was taken at.
        pub slot() -> usize = |this| this.slot;
        /// `X_j`, the summand the slot addresses.
        pub exchanged() -> &Module = |this| &this.exchanged;
        /// The almost complete pair `(U, Q) = (M/X_j, P)` both endpoints extend.
        pub almost_complete() -> &AlmostCompletePair = |this| &this.almost_complete;
        /// The proof that `U` is a direct summand of the source module part.
        pub source_extension() -> &AddClosureWitness = |this| &this.source_extension;
        /// The proof that `U` is a direct summand of the target module part.
        pub target_extension() -> &AddClosureWitness = |this| &this.target_extension;
        /// The proof that the two completions are not isomorphic.
        pub distinct() -> &SupportPairObstruction = |this| &this.distinct;
        /// The minimal left `add(U)`-approximation `f: X_j -> B`.
        pub approximation() -> &crate::approx::MinimalLeftApproximation = |this| &this.approximation;
        /// The cokernel map `g: B -> Y` of the approximation.
        ///
        /// With [`MutationWitness::approximation`] this is the exchange sequence
        /// `X_j -> B -> Y -> 0`.
        pub exchange() -> &Morphism = |this| &this.exchange;
        /// Which of the two shapes the mutation took.
        pub shape() -> &ExchangeShape = |this| &this.shape;
        /// `Y_1`, the indecomposable that enters the module part, or `None` when
        /// the slot moved to the projective part.
        pub replacement() -> Option<&Module> = |this| this.replacement.as_ref();
        /// The module part of the source pair.
        pub source_module() -> &Module = |this| &this.source_module;
        /// The projective support of the source pair.
        pub source_projective() -> &[u32] = |this| &this.source_projective;
        /// The module part of the target pair.
        pub target_module() -> &Module = |this| &this.target_module;
        /// The projective support of the target pair.
        pub target_projective() -> &[u32] = |this| &this.target_projective;
    }

    verify_methods!(pub(crate), { hit(Site::MutationWitnessVerify); },
        /// Recomputes every claim from the stored modules and maps.
        ///
        /// Both endpoints are decomposed again. The almost complete pair
        /// reruns all four of its conditions. The `add` closures are rebuilt
        /// as well as rechecked. The endpoints are compared again. The target
        /// is classified again from its parts. The exchange sequence is
        /// recomputed from the approximation. A witness borrowed from another
        /// slot fails, because its approximation does not start at the stored
        /// `X_j`.
        |self, context| {
        verify_guard!(self.almost_complete.verify_with_context(context));
        let u = self.almost_complete.module();
        let algebra = u.module().algebra();
        verify_guard!(Arc::ptr_eq(algebra, self.source_module.algebra())
            && Arc::ptr_eq(algebra, self.target_module.algebra()));
        let_or_false!((Ok(source_dec), Ok(target_dec)) = (
            BasicDecomposition::new_with_context(&self.source_module, context),
            BasicDecomposition::new_with_context(&self.target_module, context),
        ));
        let_or_false!((Ok(source_proj), Ok(target_proj)) = (
            ProjectiveSupport::new(algebra, &self.source_projective),
            ProjectiveSupport::new(algebra, &self.target_projective),
        ));
        // Check 2. The source keeps the projective part of the almost complete
        // pair, since a left mutation at a module slot leaves it alone.
        verify_guard!(self.almost_complete.projective().vertices() == source_proj.vertices()
            && extends(u, &source_dec, &self.source_extension));
        // Check 3.
        verify_guard!(self
            .almost_complete
            .projective()
            .vertices()
            .iter()
            .all(|&v| target_proj.contains(v))
            && extends(u, &target_dec, &self.target_extension));
        // Check 4.
        verify_guard!(matches!(
            context.pair_iso_for(&source_dec, &source_proj, &target_dec, &target_proj),
            Ok(outcome)
                if matches!(outcome.as_ref(), SupportPairIsoOutcome::NotIsomorphic(found) if found == &self.distinct)
        ));
        // Check 5. The decomposition and the support are rebuilt once more,
        // because classification takes them by value.
        let_or_false!((Ok(fresh_dec), Ok(fresh_proj)) = (
            BasicDecomposition::new_with_context(&self.target_module, context),
            ProjectiveSupport::new(algebra, &self.target_projective),
        ));
        matches!(
            SupportTauTiltingPair::classify_with_context(fresh_dec, fresh_proj, context),
            Ok(classification) if classification.is_pair()
        ) && self.exchange_holds(
                u,
                &source_dec,
                &target_dec,
                &source_proj,
                &target_proj,
                context,
            )
    });

    /// Rechecks the construction data: the approximation, the exchange
    /// sequence, and the shape.
    fn exchange_holds(
        &self,
        u: &BasicDecomposition,
        source_dec: &BasicDecomposition,
        target_dec: &BasicDecomposition,
        source_proj: &ProjectiveSupport,
        target_proj: &ProjectiveSupport,
        context: &VerificationContext,
    ) -> bool {
        let f = self.approximation.map();
        verify_guard!(f.source().ptr_eq(&self.exchanged));
        verify_guard!(
            self.approximation.summands().len() == u.len()
                && self
                    .approximation
                    .summands()
                    .iter()
                    .zip(u.summands())
                    .all(|(a, b)| a.module().ptr_eq(b.module()))
        );
        verify_guard!(
            self.approximation.verify_with_context(context) && is_cokernel(f, &self.exchange)
        );
        // The slot summand is a summand of the source module part, and the
        // slot is its position there.
        let_or_false!(Some(slot_summand) = source_dec.summands().get(self.slot));
        verify_guard!(
            indecomposable_iso(slot_summand.module(), &self.exchanged, slot_summand.endo())
                .is_some()
        );
        let y = self.exchange.target();
        match &self.shape {
            ExchangeShape::MovesToProjective { vertex } => {
                let mut expected = source_proj.vertices().to_vec();
                expected.push(*vertex);
                expected.sort_unstable();
                y.is_zero()
                    && self.replacement.is_none()
                    && !source_proj.contains(*vertex)
                    && target_proj.contains(*vertex)
                    && expected == target_proj.vertices()
                    && target_dec.len() == u.len()
            }
            ExchangeShape::ReplacedByModule { multiplicity } => {
                let_or_false!(Some(replacement) = &self.replacement);
                verify_guard!(!y.is_zero() && source_proj.vertices() == target_proj.vertices());
                verify_guard!(target_dec.len() == u.len() + 1);
                let split = context.decompose_for(y);
                verify_guard!(
                    split.summands().len() == *multiplicity
                        && !split
                            .certificates()
                            .iter()
                            .any(|c| *c != Certificate::Indecomposable)
                );
                let_or_false!(
                    Ok(y1) = IndecomposableModule::new_with_context(replacement, context)
                );
                verify_guard!(
                    split
                        .summands()
                        .iter()
                        .all(|s| indecomposable_iso(y1.module(), s, y1.endo()).is_some())
                );
                // AIR Theorem 2.30(b): Y_1 is outside add(T), so in particular
                // it repeats no summand of the source.
                verify_guard!(
                    !source_dec.summands().iter().any(|s| indecomposable_iso(
                        y1.module(),
                        s.module(),
                        y1.endo()
                    )
                    .is_some())
                );
                target_dec
                    .summands()
                    .iter()
                    .any(|s| indecomposable_iso(y1.module(), s.module(), y1.endo()).is_some())
            }
        }
    }
}

/// Whether `whole` contains `u` as a direct summand, both by a rebuilt match
/// and by the stored witness.
pub(super) fn extends(
    u: &BasicDecomposition,
    whole: &BasicDecomposition,
    stored: &AddClosureWitness,
) -> bool {
    let_or_false!(Ok(Some(live)) = AddClosureWitness::new(u, whole));
    verify_guard!(
        live.matches().len() == stored.matches().len()
            && stored.module().ptr_eq(u.module())
            && stored.target().ptr_eq(whole.module())
    );
    let mut seen: Vec<usize> = stored.matches().iter().map(|m| m.target_index()).collect();
    seen.sort_unstable();
    let distinct = seen.windows(2).all(|w| w[0] != w[1]);
    distinct && stored.verify()
}

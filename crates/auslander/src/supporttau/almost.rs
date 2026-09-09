use crate::basic::{BasicDecomposition, ProjectiveSupport};
use crate::context::VerificationContext;
use crate::profile::{Site, hit};
use crate::taurigid::{TauCache, TauRigidModule};

use super::conditions::{
    as_support, check_conditions, checked_omissions, positional, recheck_shared,
    support_complement, vertex_count,
};
use super::errors::{Checked, PairRejection, SupportTauError};
/// A pair `(M, P)` with every condition of a support tau-tilting pair except
/// that `|M| + |P| = n - 1`.
///
/// Mutation is defined through this type. An almost complete pair has exactly
/// two completions to a support tau-tilting pair (Adachi, Iyama, and Reiten,
/// "tau-tilting theory", Compositio Math. 150 (2014), Theorem 2.18), and the
/// two completions are the two ends of a mutation.
///
/// The constructors run the same checks as
/// [`crate::supporttau::SupportTauTiltingPair`] with the
/// smaller total.
///
/// `P` is not stored. With `r = |M|`, `s` the number of vertices where `M` is
/// nonzero, and `C` the other vertices, `P` is the sum of `P_v` over `C` when
/// `s = r + 1`, and over `C` minus one vertex when `s = r`. So the only free
/// datum is that one omitted vertex, and
/// [`AlmostCompletePair::projective`] rebuilds the rest. The proof is on
/// [`AlmostCompletePair::classify_with_cache`].
pub struct AlmostCompletePair {
    pub(super) module: BasicDecomposition,
    pub(super) rigid: TauRigidModule,
    // None when the support is the whole support complement, which is the
    // case s = r + 1.
    pub(super) omitted: Option<u32>,
}

debug_fields!(AlmostCompletePair |this| {
    "module_dim_vectors" => this.module.dim_vectors();
    "projective_support" => this.support();
    "omitted_vertex" => this.omitted;
});

/// Whether a candidate `(M, P)` is an almost complete pair, and if not, which
/// condition failed.
#[derive(Debug)]
pub enum AlmostCompleteClassification {
    /// Every condition holds.
    Pair(AlmostCompletePair),
    /// One condition failed, with its witness.
    Rejected(PairRejection),
}

impl AlmostCompleteClassification {
    binary_outcome_accessors!(
        Pair,
        Rejected,
        pair -> AlmostCompletePair = |value| value,
        rejection -> PairRejection = |value| value,
        is_pair,
        into_pair -> AlmostCompletePair = |value| value;
        flag = "Whether the candidate is an almost complete pair.";
        positive = "The pair, or `None` for a rejection.";
        negative = "The rejection, or `None` for a pair.";
        into = "Takes the pair out, or `None` for a rejection.";
    );
}

impl AlmostCompletePair {
    /// Classifies `(module, projective)` against `|M| + |P| = n - 1`, taking
    /// AR translates from `cache`.
    ///
    /// `summand_indices` and `cache` work as in
    /// [`crate::supporttau::SupportTauTiltingPair::classify_with_cache`].
    ///
    /// # Errors
    /// As [`crate::supporttau::SupportTauTiltingPair::classify_with_cache`], with
    /// [`SupportTauError::Defect`] when an accepted candidate leaves more than
    /// one vertex out of the support complement.
    pub fn classify_with_cache(
        module: BasicDecomposition,
        projective: ProjectiveSupport,
        summand_indices: &[usize],
        cache: Option<&mut TauCache>,
    ) -> Result<AlmostCompleteClassification, SupportTauError> {
        hit(Site::AlmostCompleteClassify);
        // Every algebra this crate builds has at least one vertex, so the
        // saturating step never fires; it keeps the arithmetic total anyway.
        let expected = vertex_count(&module).saturating_sub(1);
        match check_conditions(&module, &projective, expected, summand_indices, cache)? {
            Checked::Accepted(rigid) => {
                // At most one vertex of C is left out. Condition 2 puts the
                // vertex set S of P inside C, and condition 4 gives
                // |S| = n - 1 - r, so |C| - |S| = (n - s) - (n - 1 - r) =
                // r - s + 1. The bound r <= s proved on
                // SupportTauTiltingPair::classify_with_cache makes that at
                // most 1, and S inside C makes it at least 0. So s is r or
                // r + 1, and P is C or C minus one vertex.
                let omitted =
                    checked_omissions(&module, &projective, 1, "an almost complete pair")?;
                Ok(AlmostCompleteClassification::Pair(AlmostCompletePair {
                    module,
                    rigid,
                    omitted: omitted.first().copied(),
                }))
            }
            Checked::Rejected(rejection) => Ok(AlmostCompleteClassification::Rejected(rejection)),
        }
    }

    /// Classifies `(module, projective)` over a cache of its own, with
    /// summands indexed by position.
    pub fn classify(
        module: BasicDecomposition,
        projective: ProjectiveSupport,
    ) -> Result<AlmostCompleteClassification, SupportTauError> {
        let indices = positional(&module);
        Self::classify_with_cache(module, projective, &indices, None)
    }

    /// The pair, or `Ok(None)` when a condition fails.
    pub fn new(
        module: BasicDecomposition,
        projective: ProjectiveSupport,
    ) -> Result<Option<AlmostCompletePair>, SupportTauError> {
        Ok(Self::classify(module, projective)?.into_pair())
    }

    accessor_methods! {
        /// The module part `M`.
        pub module() -> &BasicDecomposition = |this| &this.module;
        /// The vertex of the support complement that `P` leaves out, and `None`
        /// when `P` is the whole complement.
        pub omitted_vertex() -> Option<u32> = |this| this.omitted;
        /// The tau-rigidity witness of `M`.
        pub rigid() -> &TauRigidModule = |this| &this.rigid;
    }

    /// The vertex support of `P`: the support complement of `M`, minus the
    /// omitted vertex when there is one.
    fn support(&self) -> Vec<u32> {
        support_complement(&self.module)
            .into_iter()
            .filter(|vertex| Some(*vertex) != self.omitted)
            .collect()
    }

    accessor_methods! {
        /// The projective part `P`, as its vertex support.
        ///
        /// Rebuilt on each call from the module part and the omitted vertex.
        pub projective() -> ProjectiveSupport = |this|
            as_support(&this.module, &this.support());
        /// `|M| + |P|`, which equals the number of vertices minus one.
        pub summand_count() -> usize = |this| this.module.len() + this.support().len();
    }

    verify_methods!(pub(crate), { hit(Site::AlmostCompleteVerify); },
        /// Recomputes every condition against the live parts, as
        /// [`crate::supporttau::SupportTauTiltingPair::verify`].
        ///
        /// The omitted vertex is rechecked against the live support complement.
        /// An omitted vertex that is not in the complement fails here.
        |self, context| {
        let complement = support_complement(&self.module);
        verify_guard!(self.omitted.is_none_or(|omitted| complement.contains(&omitted)));
        recheck_shared(
            &self.module,
            self.support().len(),
            &self.rigid,
            vertex_count(&self.module).saturating_sub(1),
        ) && self.rigid.verify_with_context(context)
    });
}

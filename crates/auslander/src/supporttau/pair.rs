use crate::basic::{BasicDecomposition, ProjectiveSupport};
use crate::context::VerificationContext;
use crate::profile::{Site, hit};
use crate::taurigid::{TauCache, TauRigidModule};

use super::conditions::{
    as_support, check_conditions, check_conditions_with_context, checked_omissions, positional,
    recheck_shared, support_complement, vertex_count,
};
use super::errors::{Checked, PairRejection, SupportTauError};

/// A pair `(M, P)` certified to satisfy every condition of
/// `docs/support-tau-tilting.md` section 6.
///
/// Every constructor runs all four checks, so a value of this type is a
/// proof: `M` is basic and certified, `Hom(P, M) = 0`, `M` is tau-rigid with
/// a [`TauRigidModule`], and `|M| + |P| = n`.
///
/// `P` is not stored. It is forced to be the sum of `P_v` over the vertices
/// where `M` vanishes, so [`SupportTauTiltingPair::projective`] derives it.
/// The proof is on [`SupportTauTiltingPair::classify_with_cache`].
///
/// Tau-rigidity is decided summandwise. `tau` runs once per indecomposable
/// summand, never on the assembled `M`.
pub struct SupportTauTiltingPair {
    pub(super) module: BasicDecomposition,
    pub(super) rigid: TauRigidModule,
}

debug_fields!(SupportTauTiltingPair |this| {
    "module_dim_vectors" => this.module.dim_vectors();
    "projective_support" => support_complement(&this.module);
});

/// Whether a candidate `(M, P)` is a support tau-tilting pair, and if not,
/// which condition failed.
#[derive(Debug)]
pub enum SupportTauTiltingClassification {
    /// Every condition holds.
    Pair(SupportTauTiltingPair),
    /// One condition failed, with its witness.
    Rejected(PairRejection),
}

impl SupportTauTiltingClassification {
    binary_outcome_accessors!(
        Pair,
        Rejected,
        pair -> SupportTauTiltingPair = |value| value,
        rejection -> PairRejection = |value| value,
        is_pair,
        into_pair -> SupportTauTiltingPair = |value| value;
        flag = "Whether the candidate is a pair.";
        positive = "The pair, or `None` for a rejection.";
        negative = "The rejection, or `None` for a pair.";
        into = "Takes the pair out, or `None` for a rejection.";
    );
}

impl SupportTauTiltingPair {
    /// Classifies `(module, projective)`, taking AR translates from `cache`.
    ///
    /// `summand_indices[i]` is the caller's stable label for summand `i` of
    /// `module`. It labels the entries of [`TauRigidModule::summands`] and
    /// [`TauRigidModule::vanishing_pairs`], nothing else;
    /// [`crate::supporttau::enumerate_over_catalog`] passes catalog positions.
    ///
    /// With `cache` as `None` the call builds a cache, uses it, and drops it.
    ///
    /// # Errors
    /// [`SupportTauError::SummandIndexCount`] when the index list and the
    /// summand list have different lengths, the wrapped errors of the Hom and
    /// tau layers when a check could not be run, and
    /// [`SupportTauError::Defect`] when an accepted candidate has a support
    /// strictly inside the support complement.
    pub fn classify_with_cache(
        module: BasicDecomposition,
        projective: ProjectiveSupport,
        summand_indices: &[usize],
        cache: Option<&mut TauCache>,
    ) -> Result<SupportTauTiltingClassification, SupportTauError> {
        hit(Site::SupportPairClassify);
        let expected = vertex_count(&module);
        let checked = check_conditions(&module, &projective, expected, summand_indices, cache)?;
        Self::from_checked(module, projective, checked)
    }

    pub(crate) fn classify_with_context(
        module: BasicDecomposition,
        projective: ProjectiveSupport,
        context: &VerificationContext,
    ) -> Result<SupportTauTiltingClassification, SupportTauError> {
        hit(Site::SupportPairClassify);
        let expected = vertex_count(&module);
        let checked = check_conditions_with_context(
            &module,
            &projective,
            expected,
            &positional(&module),
            context,
        )?;
        Self::from_checked(module, projective, checked)
    }

    fn from_checked(
        module: BasicDecomposition,
        projective: ProjectiveSupport,
        checked: Checked,
    ) -> Result<SupportTauTiltingClassification, SupportTauError> {
        match checked {
            Checked::Accepted(rigid) => {
                checked_omissions(&module, &projective, 0, "a pair")?;
                Ok(SupportTauTiltingClassification::Pair(
                    SupportTauTiltingPair { module, rigid },
                ))
            }
            Checked::Rejected(rejection) => {
                Ok(SupportTauTiltingClassification::Rejected(rejection))
            }
        }
    }

    /// Classifies `(module, projective)` over a cache of its own.
    ///
    /// Summands are indexed by position, which is stable within this one call.
    /// Use [`SupportTauTiltingPair::classify_with_cache`] to share translates
    /// across several pairs.
    pub fn classify(
        module: BasicDecomposition,
        projective: ProjectiveSupport,
    ) -> Result<SupportTauTiltingClassification, SupportTauError> {
        let indices = positional(&module);
        Self::classify_with_cache(module, projective, &indices, None)
    }

    /// The pair, or `Ok(None)` when a condition fails.
    ///
    /// `Ok(None)` names no condition. Call
    /// [`SupportTauTiltingPair::classify`] when the reason matters.
    pub fn new(
        module: BasicDecomposition,
        projective: ProjectiveSupport,
    ) -> Result<Option<SupportTauTiltingPair>, SupportTauError> {
        Ok(Self::classify(module, projective)?.into_pair())
    }

    accessor_methods! {
        /// The module part `M`.
        pub module() -> &BasicDecomposition = |this| &this.module;
        /// The tau-rigidity witness of `M`, one certified translate per summand.
        pub rigid() -> &TauRigidModule = |this| &this.rigid;
        /// The projective part `P`, derived as the sum of `P_v` over the vertices
        /// where `M` vanishes.
        ///
        /// The value is rebuilt on each call. It is not stored: the four
        /// conditions force it.
        pub projective() -> ProjectiveSupport = |this|
            as_support(&this.module, &support_complement(&this.module));
        /// Whether the projective part is empty, which makes `M` a tau-tilting
        /// module.
        ///
        /// The projective part is the support complement of `M`, so this is
        /// exactly sincerity of `M`.
        pub is_tau_tilting() -> bool = |this|
            this.module.module().dim_vector().iter().all(|&d| d > 0);
        /// `|M| + |P|`, which equals the number of vertices.
        pub summand_count() -> usize = |this|
            this.module.len() + support_complement(&this.module).len();
    }

    verify_methods!(pub(crate), { hit(Site::SupportPairVerify); },
        /// Recomputes every condition against the live parts.
        ///
        /// `P` is derived again from the module part. The counts are
        /// recomputed. Every summand's `tau` is recomputed through the
        /// certified double route inside [`TauRigidModule::verify`]. A
        /// tau-rigidity witness borrowed from another pair fails here.
        |self, context| {
        recheck_shared(
            &self.module,
            support_complement(&self.module).len(),
            &self.rigid,
            vertex_count(&self.module),
        ) && self.rigid.verify_with_context(context)
    });
}

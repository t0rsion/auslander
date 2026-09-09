use crate::approx::ApproxError;
use crate::basic::BasicError;
use crate::hom::HomError;
use crate::indec::IndecError;
use crate::supporttau::{PairRejection, SupportTauError};

/// Which end of a mutation edge a report is about.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Endpoint {
    /// The pair the mutation starts from.
    Source,
    /// The pair the mutation lands on.
    Target,
}

display_error! { Endpoint {
    Self::Source => "source";
    Self::Target => "target";
} }

/// A failed internal cross-check of the mutation layer.
///
/// Every variant signals a crate defect: the hypotheses of AIR Theorem 2.18 or
/// Theorem 2.30 hold on the input, and a consequence the code checked did not.
/// None of these is a statement about the input pair.
#[derive(Clone, Debug)]
pub enum MutationDefect {
    /// Dropping the slot summand left a pair that is not almost complete. A
    /// direct summand of a tau-rigid pair is tau-rigid, and the summand count
    /// drops by exactly one, so this cannot happen.
    AlmostCompleteRejected(PairRejection),
    /// The built pair failed a support tau-tilting condition. AIR Theorem 2.30
    /// says it is one.
    TargetRejected(PairRejection),
    /// `supp(M) \ supp(U)` has a size other than one. AIR's proof of Theorem
    /// 2.30(a) forces a singleton.
    DroppedVertexCount {
        /// The vertices of `supp(M)` that `supp(U)` misses.
        dropped: Vec<u32>,
    },
    /// `supp(U)` is smaller than `supp(M)` and the cokernel of the
    /// approximation is not zero, against AIR Theorem 2.30(a).
    CokernelNonzero {
        /// The dimension vector of the cokernel.
        dim_vector: Vec<usize>,
    },
    /// `supp(U)` equals `supp(M)` and the cokernel is zero, against AIR
    /// Theorem 2.30(b).
    CokernelZero,
    /// The cokernel summand at this position is not isomorphic to the first
    /// one. AIR Theorem 2.30(b) makes the cokernel a sum of copies of one
    /// indecomposable.
    CokernelSummandsDiffer {
        /// Position of the summand in decomposition order.
        summand: usize,
    },
    /// The cokernel summand is isomorphic to summand `summand` of `M`, against
    /// AIR Theorem 2.30(b), which puts `Y` outside `add(T)`.
    ReplacementRepeatsSummand {
        /// Position of the summand in the module part of the source pair.
        summand: usize,
    },
    /// `U` is not a direct summand of the named endpoint's module part.
    AddClosureMissing {
        /// Which endpoint failed.
        endpoint: Endpoint,
    },
    /// The named endpoint's projective support does not contain `Q`.
    ProjectiveSupportNotExtended {
        /// Which endpoint failed.
        endpoint: Endpoint,
    },
    /// The two completions of the almost complete pair are isomorphic, against
    /// AIR Theorem 2.18.
    EndpointsIsomorphic,
}

display_error! { error MutationDefect {
    Self::AlmostCompleteRejected(rejection) => "dropping the slot summand left condition {} unmet: {rejection}; crate defect", rejection.condition();
    Self::TargetRejected(rejection) => "the built pair left condition {} unmet: {rejection}; crate defect", rejection.condition();
    Self::DroppedVertexCount { dropped } => "dropping the slot summand lost {} vertices, not one; crate defect", dropped.len();
    Self::CokernelNonzero { dim_vector } => "the approximation has cokernel of dimension vector {dim_vector:?} where the \
                                             support test says zero; crate defect";
    Self::CokernelZero => "the approximation has zero cokernel where the support test says nonzero; \
                          crate defect";
    Self::CokernelSummandsDiffer { summand } => "cokernel summand {summand} is not isomorphic to the first one; crate defect";
    Self::ReplacementRepeatsSummand { summand } => "the cokernel summand repeats summand {summand} of the module part; crate defect";
    Self::AddClosureMissing { endpoint } => "the {endpoint} pair does not contain U; crate defect";
    Self::ProjectiveSupportNotExtended { endpoint } => "the {endpoint} projective support does not contain Q; crate defect";
    Self::EndpointsIsomorphic => "the two completions are isomorphic; crate defect";
} }

/// Rejected input, a blocked certification, or a failed internal cross-check
/// of the mutation layer.
///
/// A slot with no left mutation is no error. It comes back as
/// [`crate::mutation::SlotOutcome::NoLeftMutation`] with its witness.
#[derive(Clone, Debug)]
pub enum MutationError {
    /// The slot index is not a module summand of the pair.
    SlotOutOfRange {
        /// The requested slot.
        slot: usize,
        /// `|M|`, the number of module summands.
        summands: usize,
    },
    /// The caller's index list and the module summands have different lengths.
    SummandIndexCount {
        /// Number of indices supplied.
        indices: usize,
        /// `|M|`, the number of module summands.
        summands: usize,
    },
    /// The basic layer rejected an input or could not certify a summand.
    Basic(BasicError),
    /// The support tau-tilting layer rejected an input or could not run a
    /// check.
    SupportTau(SupportTauError),
    /// The approximation layer rejected the add-generators of `U`.
    Approx(ApproxError),
    /// A Hom computation rejected its input.
    Hom(HomError),
    /// A cokernel summand failed the indecomposability gate.
    /// [`IndecError::Undetermined`] is a blocked certification, not budget
    /// exhaustion, and it must poison any completeness claim built on it.
    Indec(IndecError),
    /// An internal cross-check failed.
    Defect(MutationDefect),
}

display_error! { MutationError {
    Self::SlotOutOfRange { slot, summands } => "slot {slot} is out of range, the module part has {summands} summands";
    Self::SummandIndexCount { indices, summands } => "{indices} summand indices for {summands} summands";
    Self::Basic(error) => "basic layer: {error}";
    Self::SupportTau(error) => "support tau-tilting layer: {error}";
    Self::Approx(error) => "approximation layer: {error}";
    Self::Hom(error) => "hom: {error}";
    Self::Indec(error) => "cokernel summand: {error}";
    Self::Defect(defect) => "{defect}";
} }

error_source!(MutationError {
    Self::Basic(error) => Some(error),
    Self::SupportTau(error) => Some(error),
    Self::Approx(error) => Some(error),
    Self::Hom(error) => Some(error),
    Self::Indec(error) => Some(error),
    Self::Defect(defect) => Some(defect),
    Self::SlotOutOfRange { .. } | Self::SummandIndexCount { .. } => None,
});

from_variants!(MutationError {
    BasicError => Basic,
    SupportTauError => SupportTau,
    HomError => Hom,
});

pub(super) fn defect(defect: MutationDefect) -> MutationError {
    MutationError::Defect(defect)
}

use std::collections::BTreeMap;

use crate::certificate::Certificate;
use crate::field::Fp;
use crate::quiver::ArrowId;

/// Budgets for one completion run, each checked inside the reduction,
/// ambiguity, and emission loops.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompletionLimits {
    /// Maximum number of working-basis elements.
    pub max_basis: usize,
    /// Maximum arrow count of any input word or superposition word.
    pub max_word_len: usize,
    /// Maximum number of work units across the whole run. Each reduction
    /// step and each emitted normal word costs one unit. The budget is
    /// checked before the next word is allocated, so a huge finite
    /// normal-word language truncates rather than exhausting memory.
    pub max_steps: usize,
    /// Maximum number of provenance terms in one origin. One reduction step
    /// adds up to the whole origin of the basis element it uses, so
    /// provenance compounds across the basis while `max_steps` charges one
    /// unit per step. The budget is checked at every origin mutation.
    pub max_origin_terms: usize,
    /// Maximum number of ambiguity keys held at once, and of entries in the
    /// certificate's `ambiguities` list. Enumeration over all pairs of
    /// leading words is quadratic in the basis and independent of
    /// `max_steps`: over a monomial ideal every composition is zero, so the
    /// queue drains at zero step cost however large it is.
    pub max_ambiguities: usize,
}

impl Default for CompletionLimits {
    /// The budgets sit far above the sizes this crate targets. A runaway
    /// completion still stops.
    fn default() -> Self {
        CompletionLimits {
            max_basis: 4096,
            max_word_len: 64,
            max_steps: 1_000_000,
            max_origin_terms: 4096,
            max_ambiguities: 65_536,
        }
    }
}

/// Which budget of [`CompletionLimits`] ran out.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TruncationReason {
    /// The working basis would exceed `max_basis`.
    BasisBudget,
    /// An input word or a superposition word exceeds `max_word_len`.
    WordLenBudget,
    /// The run needed more than `max_steps` work units.
    StepBudget,
    /// One origin would exceed `max_origin_terms` provenance terms.
    OriginBudget,
    /// The ambiguity enumeration would exceed `max_ambiguities` keys.
    AmbiguityBudget,
}

/// Where a truncated run stopped.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TruncationDiagnostics {
    /// Working basis size at the stop.
    pub basis_len: usize,
    /// Ambiguities that still need work at the stop. During completion
    /// this counts the queue plus the ambiguity in hand. During
    /// certificate emission it counts the traces not yet recorded; during
    /// normal-word emission every trace is recorded, so it is zero.
    pub pending_ambiguities: usize,
    /// Work units consumed before the stop: reduction steps plus emitted
    /// normal words.
    pub steps_used: usize,
    pub reason: TruncationReason,
}

/// Result of [`crate::completion::complete`]. A truncated outcome carries no certificate.
// An Outcome is built once and matched once, so the size gap between the
// variants never costs a hot copy.
#[derive(Clone, Debug, PartialEq, Eq)]
#[allow(clippy::large_enum_variant)]
pub enum Outcome {
    Complete(Certificate),
    Truncated(TruncationDiagnostics),
}

/// Terms descend strictly under the sealed order.
#[derive(Clone, Debug, Default)]
pub(super) struct Poly {
    pub(super) terms: Vec<(Fp, Word)>,
}

impl Poly {
    pub(super) fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }
}

/// Provenance of a basis element: a map from `(input index, left word,
/// right word)` to a coefficient. The element equals `Σ c · u · r_i · v`.
pub(super) type Origin = BTreeMap<(usize, Word, Word), Fp>;

#[derive(Clone, Debug)]
pub(super) struct BasisElem {
    pub(super) poly: Poly,
    pub(super) origin: Origin,
}

pub(super) type Word = Vec<ArrowId>;

/// Which budget stopped a routine that reports the reason and nothing else.
#[derive(Clone, Copy, Debug)]
pub(super) enum Exhausted {
    Steps,
    Origin,
    Ambiguities,
}

impl Exhausted {
    pub(super) fn reason(self) -> TruncationReason {
        match self {
            Exhausted::Steps => TruncationReason::StepBudget,
            Exhausted::Origin => TruncationReason::OriginBudget,
            Exhausted::Ambiguities => TruncationReason::AmbiguityBudget,
        }
    }
}

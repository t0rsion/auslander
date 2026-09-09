use crate::homotopy::BoundedComplex;

use super::cover::ComplexProjectiveCover;
use super::replacement::PerfectReplacement;

/// Resource limits for automatic perfect replacement.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ReplacementLimits {
    /// The greatest accepted complex-resolution differential count.
    pub max_resolution_steps: usize,
    /// The greatest cumulative stored complex-term count.
    pub max_complex_terms: usize,
    /// The greatest cumulative sum of module dimensions.
    pub max_total_dimension: usize,
    /// The greatest cumulative count of stored morphism entries.
    pub max_matrix_entries: usize,
    /// The greatest cumulative deterministic work count.
    pub max_work_units: usize,
}

impl Default for ReplacementLimits {
    fn default() -> Self {
        ReplacementLimits {
            max_resolution_steps: 16,
            max_complex_terms: 4_096,
            max_total_dimension: 1_000_000,
            max_matrix_entries: 16_000_000,
            max_work_units: 20_000_000,
        }
    }
}

/// The replacement resource whose next reservation exceeded its limit.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ReplacementResource {
    /// Complex-resolution differentials.
    ResolutionSteps,
    /// Stored complex terms.
    ComplexTerms,
    /// Module dimensions across stored terms.
    TotalDimension,
    /// Entries across stored morphism matrices.
    MatrixEntries,
    /// Deterministic work units.
    WorkUnits,
}

/// The first rejected replacement reservation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ReplacementReservation {
    pub(super) resource: ReplacementResource,
    pub(super) requested: usize,
    pub(super) limit: usize,
}

impl ReplacementReservation {
    accessor_methods! {
        /// The bounded resource.
        pub resource() -> ReplacementResource = |this| this.resource;
        /// The cumulative count requested.
        pub requested() -> usize = |this| this.requested;
        /// The effective limit.
        pub limit() -> usize = |this| this.limit;
    }
}

/// Exact deterministic work accepted by replacement.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct ReplacementWork {
    pub(super) resolution_steps: usize,
    pub(super) complex_terms: usize,
    pub(super) total_dimension: usize,
    pub(super) matrix_entries: usize,
    pub(super) work_units: usize,
}

impl ReplacementWork {
    accessor_methods! {
        /// The accepted complex-resolution differential count.
        pub resolution_steps() -> usize = |this| this.resolution_steps;
        /// The cumulative stored complex-term count.
        pub complex_terms() -> usize = |this| this.complex_terms;
        /// The cumulative sum of module dimensions.
        pub total_dimension() -> usize = |this| this.total_dimension;
        /// The cumulative count of stored morphism entries.
        pub matrix_entries() -> usize = |this| this.matrix_entries;
        /// The cumulative deterministic work count.
        pub work_units() -> usize = |this| this.work_units;
    }
}

/// The replacement stage at which a resource limit rejected work.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ReplacementCutStage {
    /// The next projective-object cover was not accepted.
    Resolution,
    /// The finite resolution completed, but its totalization was not accepted.
    Totalization,
}

/// A checked replacement prefix that ended at a resource limit.
#[derive(Clone, Debug)]
pub struct ReplacementCut {
    pub(super) prefix: Vec<ComplexProjectiveCover>,
    pub(super) next_kernel: Option<BoundedComplex>,
    pub(super) stage: ReplacementCutStage,
    pub(super) limits: ReplacementLimits,
    pub(super) work: ReplacementWork,
    pub(super) rejected: ReplacementReservation,
}

fn cut_stage_matches(cut: &ReplacementCut) -> bool {
    cut.rejected.requested > cut.rejected.limit
        && (cut.next_kernel.is_some() == matches!(cut.stage, ReplacementCutStage::Resolution))
}

impl ReplacementCut {
    accessor_methods! {
        /// The accepted complex-resolution prefix.
        pub prefix() -> &[ComplexProjectiveCover] = |this| &this.prefix;
        /// The next nonzero kernel, when resolution is unfinished.
        pub next_kernel() -> Option<&BoundedComplex> = |this| this.next_kernel.as_ref();
        /// The stage that rejected its next reservation.
        pub stage() -> ReplacementCutStage = |this| this.stage;
        /// The effective limits.
        pub limits() -> ReplacementLimits = |this| this.limits;
        /// The exact accepted work.
        pub work() -> ReplacementWork = |this| this.work;
        /// The first rejected reservation.
        pub rejected() -> ReplacementReservation = |this| this.rejected;
    }

    /// Rechecks every accepted cover and the cut boundary.
    pub fn verify(&self) -> bool {
        self.prefix.iter().all(ComplexProjectiveCover::verify)
            && self.next_kernel.as_ref().is_none_or(|kernel| {
                !kernel.is_zero()
                    && kernel.verify()
                    && self
                        .prefix
                        .last()
                        .is_none_or(|cover| cover.kernel().agrees_with(kernel))
            })
            && cut_stage_matches(self)
    }
}

/// The last complete stage before cooperative cancellation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ReplacementCompletedStage {
    /// No projective-object cover completed.
    Input,
    /// The named complex-resolution step completed.
    Cover { resolution_step: usize },
    /// The finite complex resolution reached its zero kernel.
    Resolution,
}

/// A checked replacement prefix stopped by cooperative cancellation.
#[derive(Clone, Debug)]
pub struct ReplacementCancellation {
    pub(super) prefix: Vec<ComplexProjectiveCover>,
    pub(super) next_kernel: Option<BoundedComplex>,
    pub(super) last_completed: ReplacementCompletedStage,
    pub(super) limits: ReplacementLimits,
    pub(super) work: ReplacementWork,
}

fn verified_nonzero_kernel(
    prefix: &[ComplexProjectiveCover],
    next_kernel: Option<&BoundedComplex>,
) -> bool {
    next_kernel.is_some_and(|kernel| {
        kernel.verify()
            && !kernel.is_zero()
            && prefix
                .last()
                .is_none_or(|cover| cover.kernel().agrees_with(kernel))
    })
}

fn cancellation_check(condition: bool, check: impl FnOnce() -> bool) -> bool {
    if condition { check() } else { false }
}

fn cancellation_boundary_matches(cancellation: &ReplacementCancellation) -> bool {
    let prefix = &cancellation.prefix;
    let next_kernel = cancellation.next_kernel.as_ref();
    let check = || verified_nonzero_kernel(prefix, next_kernel);
    match cancellation.last_completed {
        ReplacementCompletedStage::Input => cancellation_check(prefix.is_empty(), check),
        ReplacementCompletedStage::Cover { resolution_step } => {
            cancellation_check(resolution_step.checked_add(1) == Some(prefix.len()), check)
        }
        ReplacementCompletedStage::Resolution => cancellation_check(next_kernel.is_none(), || {
            prefix.last().is_some_and(|cover| cover.kernel().is_zero())
        }),
    }
}

impl ReplacementCancellation {
    accessor_methods! {
        /// The accepted complex-resolution prefix.
        pub prefix() -> &[ComplexProjectiveCover] = |this| &this.prefix;
        /// The next unchecked kernel complex, when resolution is unfinished.
        pub next_kernel() -> Option<&BoundedComplex> = |this| this.next_kernel.as_ref();
        /// The last complete certificate stage.
        pub last_completed() -> ReplacementCompletedStage = |this| this.last_completed;
        /// The effective limits.
        pub limits() -> ReplacementLimits = |this| this.limits;
        /// The exact accepted work.
        pub work() -> ReplacementWork = |this| this.work;
    }

    /// Rechecks every accepted cover and the cancellation boundary.
    pub fn verify(&self) -> bool {
        let prefix = &self.prefix;
        prefix.iter().all(ComplexProjectiveCover::verify) && cancellation_boundary_matches(self)
    }
}

/// A complete replacement, a checked cut, or cooperative cancellation.
#[derive(Clone, Debug)]
pub enum ReplacementOutcome {
    /// A checked bounded projective replacement.
    Replaced(PerfectReplacement),
    /// A resource limit stopped a checked prefix.
    Cut(ReplacementCut),
    /// Cooperative cancellation stopped a checked prefix.
    Cancelled(ReplacementCancellation),
}

impl ReplacementOutcome {
    optional_accessors! {
        /// The complete replacement, when one finished.
        pub replacement() -> &PerfectReplacement = Self::Replaced(value) => value;
        /// The checked resource cut, when one occurred.
        pub cut() -> &ReplacementCut = Self::Cut(value) => value;
        /// The checked cancellation, when one occurred.
        pub cancellation() -> &ReplacementCancellation = Self::Cancelled(value) => value;
    }

    /// Whether replacement completed.
    pub fn is_replaced(&self) -> bool {
        matches!(self, ReplacementOutcome::Replaced(_))
    }
}

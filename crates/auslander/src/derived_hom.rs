//! Derived Hom from checked bounded projective replacements.

mod class;

pub use class::{DerivedHomClass, DerivedHomClassError, DerivedHomCompositionError};

use crate::control::{ComputationControl, ProgressStage};
use crate::homotopy::{
    BoundedComplex, ChainMapError, DegreeRange, HomotopyHom, HomotopyHomQuotient,
};
use crate::perfect::{
    PerfectReplacement, ReplacementCancellation, ReplacementCut, ReplacementError,
    ReplacementLimits, ReplacementOutcome, replace_perfect,
};

/// Resource limits for derived Hom.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DerivedHomLimits {
    /// Limits for the source replacement.
    pub replacement: ReplacementLimits,
    /// The greatest number of completed shift degrees.
    pub max_degrees: usize,
    /// The greatest deterministic Hom work count.
    pub max_work_units: usize,
}

impl Default for DerivedHomLimits {
    fn default() -> Self {
        DerivedHomLimits {
            replacement: ReplacementLimits::default(),
            max_degrees: 256,
            max_work_units: 16_000_000,
        }
    }
}

/// Exact deterministic work accepted by derived Hom.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct DerivedHomWork {
    completed_degrees: usize,
    chain_map_dimensions: usize,
    quotient_dimensions: usize,
    work_units: usize,
}

impl DerivedHomWork {
    accessor_methods! {
        /// The number of completed shift degrees.
        pub completed_degrees() -> usize = |this| this.completed_degrees;
        /// The sum of ambient chain-map dimensions.
        pub chain_map_dimensions() -> usize = |this| this.chain_map_dimensions;
        /// The sum of derived Hom dimensions.
        pub quotient_dimensions() -> usize = |this| this.quotient_dimensions;
        /// The deterministic work count.
        pub work_units() -> usize = |this| this.work_units;
    }
}

/// Why derived Hom stopped before its finite support completed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DerivedHomCutReason {
    /// The next degree would exceed `max_degrees`.
    DegreeLimit { requested: usize, limit: usize },
    /// The next degree would exceed `max_work_units`.
    WorkLimit { requested: usize, limit: usize },
}

fn spaces_match_support(support: DegreeRange, spaces: &[HomotopyHomQuotient]) -> bool {
    spaces.iter().enumerate().all(|(offset, space)| {
        i32::try_from(offset).is_ok_and(|offset| {
            support
                .lower()
                .checked_add(offset)
                .is_some_and(|degree| degree == space.degree())
                && space.verify()
        })
    })
}

fn replacement_matches(source: &BoundedComplex, replacement: &PerfectReplacement) -> bool {
    source.verify() && replacement.verify() && replacement.original().agrees_with(source)
}

#[derive(Clone, Debug)]
struct DerivedHomPrefix {
    replacement: PerfectReplacement,
    target: BoundedComplex,
    support: DegreeRange,
    spaces: Vec<HomotopyHomQuotient>,
    next_degree: i32,
    limits: DerivedHomLimits,
    work: DerivedHomWork,
}

impl DerivedHomPrefix {
    fn verify(&self) -> bool {
        let Ok(completed) = i32::try_from(self.spaces.len()) else {
            return false;
        };
        self.replacement.verify()
            && self.target.verify()
            && self.spaces.len() == self.work.completed_degrees
            && self.next_degree
                == self
                    .support
                    .lower()
                    .checked_add(completed)
                    .unwrap_or(i32::MIN)
            && spaces_match_support(self.support, &self.spaces)
    }
}

/// A checked prefix of the finite derived Hom support.
#[derive(Clone, Debug)]
pub struct DerivedHomCut {
    prefix: DerivedHomPrefix,
    reason: DerivedHomCutReason,
}

impl DerivedHomCut {
    accessor_methods! {
        /// The checked source replacement.
        pub replacement() -> &PerfectReplacement = |this| &this.prefix.replacement;
        /// The ordinary target complex.
        pub target() -> &BoundedComplex = |this| &this.prefix.target;
        /// The full finite support that was requested.
        pub support() -> DegreeRange = |this| this.prefix.support;
        /// The completed quotient spaces in increasing degree order.
        pub spaces() -> &[HomotopyHomQuotient] = |this| &this.prefix.spaces;
        /// The first unfinished shift degree.
        pub next_degree() -> i32 = |this| this.prefix.next_degree;
        /// The effective limits.
        pub limits() -> DerivedHomLimits = |this| this.prefix.limits;
        /// The exact accepted work.
        pub work() -> DerivedHomWork = |this| this.prefix.work;
        /// The first rejected reservation.
        pub reason() -> DerivedHomCutReason = |this| this.reason;
    }

    /// Rechecks the replacement and every completed quotient.
    pub fn verify(&self) -> bool {
        self.prefix.verify()
            && match self.reason {
                DerivedHomCutReason::DegreeLimit { requested, limit }
                | DerivedHomCutReason::WorkLimit { requested, limit } => requested > limit,
            }
    }
}

/// A checked derived Hom prefix stopped by cooperative cancellation.
#[derive(Clone, Debug)]
pub struct DerivedHomCancellation {
    prefix: DerivedHomPrefix,
}

impl DerivedHomCancellation {
    accessor_methods! {
        /// The checked source replacement.
        pub replacement() -> &PerfectReplacement = |this| &this.prefix.replacement;
        /// The ordinary target complex.
        pub target() -> &BoundedComplex = |this| &this.prefix.target;
        /// The full finite support that was requested.
        pub support() -> DegreeRange = |this| this.prefix.support;
        /// The completed quotient spaces in increasing degree order.
        pub spaces() -> &[HomotopyHomQuotient] = |this| &this.prefix.spaces;
        /// The first unfinished shift degree.
        pub next_degree() -> i32 = |this| this.prefix.next_degree;
        /// The effective limits.
        pub limits() -> DerivedHomLimits = |this| this.prefix.limits;
        /// The exact accepted work.
        pub work() -> DerivedHomWork = |this| this.prefix.work;
    }

    /// Rechecks the replacement and every completed quotient.
    pub fn verify(&self) -> bool {
        self.prefix.verify()
    }
}

/// The complete finite graded derived Hom value.
#[derive(Clone, Debug)]
pub struct DerivedHom {
    source: BoundedComplex,
    target: BoundedComplex,
    replacement: PerfectReplacement,
    support: DegreeRange,
    spaces: Vec<HomotopyHomQuotient>,
    work: DerivedHomWork,
}

impl DerivedHom {
    accessor_methods! {
        /// The ordinary source complex.
        pub source() -> &BoundedComplex = |this| &this.source;
        /// The ordinary target complex.
        pub target() -> &BoundedComplex = |this| &this.target;
        /// The checked source replacement.
        pub replacement() -> &PerfectReplacement = |this| &this.replacement;
        /// The exact finite shift support.
        pub support() -> DegreeRange = |this| this.support;
        /// One quotient space per support degree.
        pub spaces() -> &[HomotopyHomQuotient] = |this| &this.spaces;
        /// The exact deterministic work.
        pub work() -> DerivedHomWork = |this| this.work;
    }

    /// Returns the quotient at `degree`, or exact zero outside the support.
    pub fn space(&self, degree: i32) -> Option<&HomotopyHomQuotient> {
        self.support
            .contains(degree)
            .then(|| &self.spaces[(degree - self.support.lower()) as usize])
    }

    /// Returns the exact derived Hom dimension at `degree`.
    pub fn dimension(&self, degree: i32) -> usize {
        self.space(degree).map_or(0, HomotopyHomQuotient::dim)
    }

    /// Recomputes every quotient in the finite support.
    pub fn verify(&self) -> bool {
        replacement_matches(&self.source, &self.replacement)
            && self.complete_spaces_match()
            && self.spaces.len() == self.work.completed_degrees
    }

    fn complete_spaces_match(&self) -> bool {
        self.target.verify()
            && support(self.replacement.projective().complex(), &self.target)
                .is_ok_and(|range| range == self.support)
            && self.spaces.len() == self.support.len()
            && spaces_match_support(self.support, &self.spaces)
    }
}

/// A complete result or one typed incomplete branch.
#[derive(Clone, Debug)]
pub enum DerivedHomOutcome {
    /// Every degree in the finite support completed.
    Complete(DerivedHom),
    /// Source replacement reached a resource limit.
    ReplacementCut(ReplacementCut),
    /// Source replacement was cancelled.
    ReplacementCancelled(ReplacementCancellation),
    /// Derived Hom reached its own resource limit.
    WorkCut(DerivedHomCut),
    /// Derived Hom was cancelled after replacement.
    Cancelled(DerivedHomCancellation),
}

impl DerivedHomOutcome {
    optional_accessors! {
        /// The complete derived Hom value.
        pub complete() -> &DerivedHom = Self::Complete(value) => value;
        /// The source replacement cut.
        pub replacement_cut() -> &ReplacementCut = Self::ReplacementCut(value) => value;
        /// The source replacement cancellation.
        pub replacement_cancellation() -> &ReplacementCancellation = Self::ReplacementCancelled(value) => value;
        /// The derived Hom work cut.
        pub work_cut() -> &DerivedHomCut = Self::WorkCut(value) => value;
        /// The derived Hom cancellation.
        pub cancellation() -> &DerivedHomCancellation = Self::Cancelled(value) => value;
    }
}

/// Why derived Hom could not construct its next checked value.
#[derive(Clone, Debug)]
pub enum DerivedHomError {
    /// Source replacement failed structurally.
    Replacement(ReplacementError),
    /// A finite support endpoint overflowed.
    DegreeOverflow,
    /// A homotopy Hom quotient failed construction.
    Chain(ChainMapError),
    /// A deterministic work count overflowed.
    Arithmetic,
}

display_error! { DerivedHomError {
    Self::Replacement(error) => "derived Hom source replacement failed: {error}";
    Self::DegreeOverflow => "derived Hom support degree overflowed";
    Self::Chain(error) => "derived Hom quotient failed: {error}";
    Self::Arithmetic => "derived Hom work count overflowed";
} }

error_source! { DerivedHomError {
    Self::Replacement(error) => Some(error),
    Self::Chain(error) => Some(error),
    Self::DegreeOverflow | Self::Arithmetic => None,
} }

from_variants! { DerivedHomError {
    ReplacementError => Replacement,
    ChainMapError => Chain,
} }

fn support(
    projective: &BoundedComplex,
    target: &BoundedComplex,
) -> Result<DegreeRange, DerivedHomError> {
    let lower = projective
        .lower()
        .checked_sub(target.upper())
        .ok_or(DerivedHomError::DegreeOverflow)?;
    let upper = projective
        .upper()
        .checked_sub(target.lower())
        .ok_or(DerivedHomError::DegreeOverflow)?;
    DegreeRange::new(lower, upper).map_err(|_| DerivedHomError::DegreeOverflow)
}

fn checked_add(left: usize, right: usize) -> Result<usize, DerivedHomError> {
    left.checked_add(right).ok_or(DerivedHomError::Arithmetic)
}

fn update_progress(control: Option<&ComputationControl>, work: DerivedHomWork) {
    if let Some(control) = control {
        control.update(ProgressStage::DerivedHom, work.work_units, work.work_units);
    }
}

enum DerivedHomStop {
    Cancelled,
    Cut(DerivedHomCutReason),
}

fn degree_candidate(
    replacement: &PerfectReplacement,
    target: &BoundedComplex,
    degree: i32,
) -> Result<(HomotopyHomQuotient, usize, usize, usize), DerivedHomError> {
    let hom = HomotopyHom::new(replacement.projective().complex(), target, degree)?;
    let chain_dimension = hom.dim();
    let quotient = hom.quotient()?;
    let quotient_dimension = quotient.dim();
    let degree_work = checked_add(checked_add(chain_dimension, quotient_dimension)?, 1)?;
    Ok((quotient, chain_dimension, quotient_dimension, degree_work))
}

struct DerivedHomComputation<'a> {
    source: &'a BoundedComplex,
    target: &'a BoundedComplex,
    replacement: PerfectReplacement,
    support: DegreeRange,
    limits: DerivedHomLimits,
    control: Option<&'a ComputationControl>,
    spaces: Vec<HomotopyHomQuotient>,
    work: DerivedHomWork,
}

impl<'a> DerivedHomComputation<'a> {
    fn new(
        source: &'a BoundedComplex,
        target: &'a BoundedComplex,
        limits: DerivedHomLimits,
        control: Option<&'a ComputationControl>,
        replacement: PerfectReplacement,
    ) -> Result<Self, DerivedHomError> {
        let support = support(replacement.projective().complex(), target)?;
        let spaces = Vec::with_capacity(support.len().min(limits.max_degrees));
        Ok(Self {
            source,
            target,
            replacement,
            support,
            limits,
            control,
            spaces,
            work: DerivedHomWork::default(),
        })
    }

    fn step(&mut self, degree: i32) -> Result<Option<DerivedHomStop>, DerivedHomError> {
        if self.control.is_some_and(ComputationControl::is_cancelled) {
            return Ok(Some(DerivedHomStop::Cancelled));
        }
        let requested_degrees = checked_add(self.work.completed_degrees, 1)?;
        if requested_degrees > self.limits.max_degrees {
            return Ok(Some(DerivedHomStop::Cut(
                DerivedHomCutReason::DegreeLimit {
                    requested: requested_degrees,
                    limit: self.limits.max_degrees,
                },
            )));
        }
        update_progress(self.control, self.work);
        let candidate = degree_candidate(&self.replacement, self.target, degree)?;
        self.accept(requested_degrees, candidate)
    }

    fn accept(
        &mut self,
        requested_degrees: usize,
        candidate: (HomotopyHomQuotient, usize, usize, usize),
    ) -> Result<Option<DerivedHomStop>, DerivedHomError> {
        let (quotient, chain_dimension, quotient_dimension, degree_work) = candidate;
        let requested_work = checked_add(self.work.work_units, degree_work)?;
        if requested_work > self.limits.max_work_units {
            return Ok(Some(DerivedHomStop::Cut(DerivedHomCutReason::WorkLimit {
                requested: requested_work,
                limit: self.limits.max_work_units,
            })));
        }
        self.record_work(
            requested_degrees,
            chain_dimension,
            quotient_dimension,
            requested_work,
        )?;
        self.spaces.push(quotient);
        Ok(None)
    }

    fn record_work(
        &mut self,
        requested_degrees: usize,
        chain_dimension: usize,
        quotient_dimension: usize,
        requested_work: usize,
    ) -> Result<(), DerivedHomError> {
        self.work.completed_degrees = requested_degrees;
        self.work.chain_map_dimensions =
            checked_add(self.work.chain_map_dimensions, chain_dimension)?;
        self.work.quotient_dimensions =
            checked_add(self.work.quotient_dimensions, quotient_dimension)?;
        self.work.work_units = requested_work;
        Ok(())
    }

    fn stopped(self, next_degree: i32, stop: DerivedHomStop) -> DerivedHomOutcome {
        let prefix = DerivedHomPrefix {
            replacement: self.replacement,
            target: self.target.clone(),
            support: self.support,
            spaces: self.spaces,
            next_degree,
            limits: self.limits,
            work: self.work,
        };
        match stop {
            DerivedHomStop::Cancelled => {
                DerivedHomOutcome::Cancelled(DerivedHomCancellation { prefix })
            }
            DerivedHomStop::Cut(reason) => {
                DerivedHomOutcome::WorkCut(DerivedHomCut { prefix, reason })
            }
        }
    }

    fn complete(self) -> DerivedHomOutcome {
        let work = self.work;
        let value = DerivedHom {
            source: self.source.clone(),
            target: self.target.clone(),
            replacement: self.replacement,
            support: self.support,
            spaces: self.spaces,
            work,
        };
        debug_assert!(value.verify());
        if let Some(control) = self.control {
            control.update(ProgressStage::Complete, work.work_units, work.work_units);
        }
        DerivedHomOutcome::Complete(value)
    }
}

fn replaced_derived_hom(
    source: &BoundedComplex,
    target: &BoundedComplex,
    limits: DerivedHomLimits,
    control: Option<&ComputationControl>,
    replacement: PerfectReplacement,
) -> Result<DerivedHomOutcome, DerivedHomError> {
    let mut computation = DerivedHomComputation::new(source, target, limits, control, replacement)?;
    let support = computation.support;
    for degree in support.lower()..=support.upper() {
        if let Some(stop) = computation.step(degree)? {
            return Ok(computation.stopped(degree, stop));
        }
    }
    Ok(computation.complete())
}

fn derived_hom_after_replacement(
    source: &BoundedComplex,
    target: &BoundedComplex,
    limits: DerivedHomLimits,
    control: Option<&ComputationControl>,
    replacement_outcome: ReplacementOutcome,
) -> Result<DerivedHomOutcome, DerivedHomError> {
    match replacement_outcome {
        ReplacementOutcome::Replaced(replacement) => {
            replaced_derived_hom(source, target, limits, control, replacement)
        }
        ReplacementOutcome::Cut(value) => Ok(DerivedHomOutcome::ReplacementCut(value)),
        ReplacementOutcome::Cancelled(value) => Ok(DerivedHomOutcome::ReplacementCancelled(value)),
    }
}

/// Computes the finite graded derived Hom value from an ordinary source.
pub fn derived_hom(
    source: &BoundedComplex,
    target: &BoundedComplex,
    limits: DerivedHomLimits,
    control: Option<&ComputationControl>,
) -> Result<DerivedHomOutcome, DerivedHomError> {
    let replacement = replace_perfect(source, limits.replacement, control)?;
    derived_hom_after_replacement(source, target, limits, control, replacement)
}

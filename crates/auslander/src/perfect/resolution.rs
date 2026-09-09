use crate::control::{ComputationControl, ProgressStage};
use crate::homotopy::BoundedComplex;

use super::budget::{
    ReplacementCancellation, ReplacementCompletedStage, ReplacementCut, ReplacementCutStage,
    ReplacementLimits, ReplacementOutcome, ReplacementReservation, ReplacementResource,
    ReplacementWork,
};
use super::cover::{ComplexProjectiveCover, projective_complex_cover};
use super::replacement::{PerfectReplacement, ReplacementError};
use super::term::ProjectiveComplex;
use super::totalization::{replacement_cost, totalize_replacement};
use super::work::{cover_work_for, rejected, reserve};

fn progress(control: Option<&ComputationControl>, stage: ProgressStage, work: ReplacementWork) {
    if let Some(control) = control {
        control.update(stage, work.work_units, work.work_units);
    }
}

enum ResolutionResult {
    Complete {
        prefix: Vec<ComplexProjectiveCover>,
        work: ReplacementWork,
    },
    Stopped(Box<ReplacementOutcome>),
}

enum ResolutionStep {
    Complete,
    Cut(ReplacementReservation),
}

fn stopped(outcome: ReplacementOutcome) -> ResolutionResult {
    ResolutionResult::Stopped(Box::new(outcome))
}

fn completed_stage(
    prefix: &[ComplexProjectiveCover],
    resolution_step: usize,
) -> ReplacementCompletedStage {
    prefix.last().map_or(ReplacementCompletedStage::Input, |_| {
        ReplacementCompletedStage::Cover {
            resolution_step: resolution_step - 1,
        }
    })
}

fn cancelled(
    prefix: Vec<ComplexProjectiveCover>,
    next_kernel: Option<BoundedComplex>,
    last_completed: ReplacementCompletedStage,
    limits: ReplacementLimits,
    work: ReplacementWork,
) -> ResolutionResult {
    stopped(ReplacementOutcome::Cancelled(ReplacementCancellation {
        prefix,
        next_kernel,
        last_completed,
        limits,
        work,
    }))
}

fn cut_outcome(
    prefix: Vec<ComplexProjectiveCover>,
    next_kernel: Option<BoundedComplex>,
    stage: ReplacementCutStage,
    limits: ReplacementLimits,
    work: ReplacementWork,
    rejected: ReplacementReservation,
) -> ReplacementOutcome {
    ReplacementOutcome::Cut(ReplacementCut {
        prefix,
        next_kernel,
        stage,
        limits,
        work,
        rejected,
    })
}

fn advance_resolution(
    prefix: &mut Vec<ComplexProjectiveCover>,
    next_kernel: &mut BoundedComplex,
    work: &mut ReplacementWork,
    resolution_step: usize,
    limits: ReplacementLimits,
) -> Result<Option<ResolutionStep>, ReplacementError> {
    let cover = projective_complex_cover(next_kernel)?;
    let delta = cover_work_for(&cover)?;
    let terminal = cover.kernel().is_zero();
    if let Err(rejected) = reserve(work, delta, resolution_step, limits)? {
        return Ok(Some(ResolutionStep::Cut(rejected)));
    }
    *next_kernel = cover.kernel().clone();
    prefix.push(cover);
    Ok(terminal.then_some(ResolutionStep::Complete))
}

fn resolution_step_outcome(
    step: ResolutionStep,
    prefix: Vec<ComplexProjectiveCover>,
    next_kernel: BoundedComplex,
    limits: ReplacementLimits,
    work: ReplacementWork,
    control: Option<&ComputationControl>,
) -> ResolutionResult {
    match step {
        ResolutionStep::Complete if control.is_some_and(ComputationControl::is_cancelled) => {
            cancelled(
                prefix,
                None,
                ReplacementCompletedStage::Resolution,
                limits,
                work,
            )
        }
        ResolutionStep::Complete => ResolutionResult::Complete { prefix, work },
        ResolutionStep::Cut(rejected) => stopped(cut_outcome(
            prefix,
            Some(next_kernel),
            ReplacementCutStage::Resolution,
            limits,
            work,
            rejected,
        )),
    }
}

fn resolve_prefix(
    input: &BoundedComplex,
    limits: ReplacementLimits,
    control: Option<&ComputationControl>,
) -> Result<ResolutionResult, ReplacementError> {
    let mut prefix = Vec::new();
    let mut next_kernel = input.clone();
    let mut work = ReplacementWork::default();
    loop {
        let resolution_step = prefix.len();
        if control.is_some_and(ComputationControl::is_cancelled) {
            let last_completed = completed_stage(&prefix, resolution_step);
            return Ok(cancelled(
                prefix,
                Some(next_kernel),
                last_completed,
                limits,
                work,
            ));
        }
        if let Err(rejected) = rejected(
            ReplacementResource::ResolutionSteps,
            resolution_step,
            limits.max_resolution_steps,
        ) {
            return Ok(stopped(cut_outcome(
                prefix,
                Some(next_kernel),
                ReplacementCutStage::Resolution,
                limits,
                work,
                rejected,
            )));
        }
        progress(control, ProgressStage::ReplacementCover, work);
        let Some(step) = advance_resolution(
            &mut prefix,
            &mut next_kernel,
            &mut work,
            resolution_step,
            limits,
        )?
        else {
            continue;
        };
        return Ok(resolution_step_outcome(
            step,
            prefix,
            next_kernel,
            limits,
            work,
            control,
        ));
    }
}

fn totalize_prefix(
    input: &BoundedComplex,
    prefix: Vec<ComplexProjectiveCover>,
    limits: ReplacementLimits,
    control: Option<&ComputationControl>,
    mut work: ReplacementWork,
) -> Result<ReplacementOutcome, ReplacementError> {
    progress(control, ProgressStage::ReplacementTotalize, work);
    let output_cost = replacement_cost(&prefix, input)?;
    if let Err(rejected) = reserve(&mut work, output_cost, prefix.len() - 1, limits)? {
        return Ok(cut_outcome(
            prefix,
            None,
            ReplacementCutStage::Totalization,
            limits,
            work,
            rejected,
        ));
    }
    progress(control, ProgressStage::ReplacementVerify, work);
    let replacement = totalize_replacement(input, &prefix)?;
    progress(control, ProgressStage::Complete, work);
    Ok(ReplacementOutcome::Replaced(replacement))
}

/// Replaces an ordinary bounded complex by a checked bounded projective model.
pub fn replace_perfect(
    input: &BoundedComplex,
    limits: ReplacementLimits,
    control: Option<&ComputationControl>,
) -> Result<ReplacementOutcome, ReplacementError> {
    if let Ok(projective) = ProjectiveComplex::new(input.clone()) {
        let replacement = PerfectReplacement::identity(projective);
        progress(control, ProgressStage::Complete, ReplacementWork::default());
        return Ok(ReplacementOutcome::Replaced(replacement));
    }
    match resolve_prefix(input, limits, control)? {
        ResolutionResult::Stopped(outcome) => Ok(*outcome),
        ResolutionResult::Complete { prefix, work } => {
            totalize_prefix(input, prefix, limits, control, work)
        }
    }
}

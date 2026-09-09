use crate::hom::Morphism;
use crate::module::Module;

use super::budget::{
    ReplacementLimits, ReplacementReservation, ReplacementResource, ReplacementWork,
};
use super::cover::ComplexProjectiveCover;
use super::replacement::ReplacementError;

pub(super) fn checked_sum(
    values: impl IntoIterator<Item = usize>,
) -> Result<usize, ReplacementError> {
    values.into_iter().try_fold(0usize, |sum, value| {
        sum.checked_add(value).ok_or(ReplacementError::Arithmetic)
    })
}

fn morphism_entries(map: &Morphism) -> Result<usize, ReplacementError> {
    checked_sum_results(
        (0..map.source().algebra().quiver().num_vertices()).map(|vertex| {
            let matrix = map.map_at(vertex);
            matrix
                .rows()
                .checked_mul(matrix.cols())
                .ok_or(ReplacementError::Arithmetic)
        }),
    )
}

fn cover_work(cover: &ComplexProjectiveCover) -> Result<ReplacementWork, ReplacementError> {
    let complex = cover.projective().complex();
    let complex_terms = complex.len();
    let total_dimension = checked_sum(complex.terms().iter().map(Module::total_dim))?;
    let maps = complex
        .differentials()
        .iter()
        .chain(cover.augmentation().components())
        .chain(cover.kernel().differentials())
        .chain(cover.kernel_inclusion().components());
    let matrix_entries = checked_sum_results(maps.map(morphism_entries))?;
    replacement_work(complex_terms, total_dimension, matrix_entries)
}

pub(super) fn checked_sum_results(
    values: impl IntoIterator<Item = Result<usize, ReplacementError>>,
) -> Result<usize, ReplacementError> {
    values.into_iter().try_fold(0usize, |sum, value| {
        sum.checked_add(value?).ok_or(ReplacementError::Arithmetic)
    })
}

fn replacement_work(
    complex_terms: usize,
    total_dimension: usize,
    matrix_entries: usize,
) -> Result<ReplacementWork, ReplacementError> {
    Ok(ReplacementWork {
        resolution_steps: 0,
        complex_terms,
        total_dimension,
        matrix_entries,
        work_units: checked_sum([complex_terms, total_dimension, matrix_entries, 1])?,
    })
}

pub(super) fn rejected(
    resource: ReplacementResource,
    requested: usize,
    limit: usize,
) -> Result<(), ReplacementReservation> {
    if requested > limit {
        Err(ReplacementReservation {
            resource,
            requested,
            limit,
        })
    } else {
        Ok(())
    }
}

fn first_rejection(
    work: ReplacementWork,
    resolution_steps: usize,
    limits: ReplacementLimits,
) -> Option<ReplacementReservation> {
    use ReplacementResource::*;
    [
        (ResolutionSteps, resolution_steps),
        (ComplexTerms, work.complex_terms),
        (TotalDimension, work.total_dimension),
        (MatrixEntries, work.matrix_entries),
        (WorkUnits, work.work_units),
    ]
    .into_iter()
    .zip([
        limits.max_resolution_steps,
        limits.max_complex_terms,
        limits.max_total_dimension,
        limits.max_matrix_entries,
        limits.max_work_units,
    ])
    .find_map(|((resource, requested), limit)| rejected(resource, requested, limit).err())
}

pub(super) fn reserve(
    work: &mut ReplacementWork,
    delta: ReplacementWork,
    resolution_steps: usize,
    limits: ReplacementLimits,
) -> Result<Result<(), ReplacementReservation>, ReplacementError> {
    let next = (|| -> Result<ReplacementWork, ReplacementError> {
        Ok(ReplacementWork {
            resolution_steps,
            complex_terms: checked_sum([work.complex_terms, delta.complex_terms])?,
            total_dimension: checked_sum([work.total_dimension, delta.total_dimension])?,
            matrix_entries: checked_sum([work.matrix_entries, delta.matrix_entries])?,
            work_units: checked_sum([work.work_units, delta.work_units])?,
        })
    })()?;
    if let Some(rejected) = first_rejection(next, resolution_steps, limits) {
        return Ok(Err(rejected));
    }
    *work = next;
    Ok(Ok(()))
}

pub(super) fn cover_work_for(
    cover: &ComplexProjectiveCover,
) -> Result<ReplacementWork, ReplacementError> {
    cover_work(cover)
}

pub(super) fn replacement_work_for(
    complex_terms: usize,
    total_dimension: usize,
    matrix_entries: usize,
) -> Result<ReplacementWork, ReplacementError> {
    replacement_work(complex_terms, total_dimension, matrix_entries)
}

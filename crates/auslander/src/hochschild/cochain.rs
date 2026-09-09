use crate::field::PrimeField;
use crate::homspace::deterministic_complement;
use crate::linalg::DenseMat;

use super::bar::{BuildFailure, BuildResult, InnerResult, Ledger};
use super::limits::{BarCutReason, BarStage, HochschildError};

pub(super) fn check_square(
    left: &DenseMat,
    right: &DenseMat,
    field: &PrimeField,
    degree: usize,
    ledger: &mut Ledger,
) -> InnerResult<()> {
    let work = ledger.budget(degree, BarStage::Square).product([
        left.rows() as u128,
        left.cols() as u128,
        right.cols() as u128,
    ])?;
    ledger.work(degree, BarStage::Square, work)?;
    for row in 0..left.rows() {
        for column in 0..right.cols() {
            let mut sum = field.zero();
            for middle in 0..left.cols() {
                sum = field.add(
                    sum,
                    field.mul(left.get(row, middle), right.get(middle, column)),
                );
            }
            if !sum.is_zero() {
                return Err(BuildFailure::Defect(HochschildError::DifferentialSquare {
                    degree,
                }));
            }
        }
    }
    Ok(())
}

fn reserve_cocycle_work(
    rows: usize,
    cols: usize,
    degree: usize,
    stage: BarStage,
    ledger: &mut Ledger,
) -> BuildResult<()> {
    let budget = ledger.budget(degree, stage);
    let matrix = budget.product([2, rows as u128, cols as u128])?;
    let row_square = budget.product([rows as u128, rows as u128])?;
    let scratch = budget.sum(matrix, row_square)?;
    ledger.scratch_u128(degree, stage, scratch)?;
    let kernel_product = budget.product([rows as u128, cols as u128])?;
    let elimination = elimination_work(cols, rows, ledger, degree, stage)?;
    let square = budget.product([rows as u128, rows as u128])?;
    let elimination_square = budget.sum(elimination, square)?;
    let kernel_work = budget.sum(kernel_product, elimination_square)?;
    ledger.work(degree, stage, kernel_work)
}

pub(super) fn cocycles(
    differential: &DenseMat,
    field: &PrimeField,
    degree: usize,
    ledger: &mut Ledger,
) -> BuildResult<DenseMat> {
    let (rows, cols) = (differential.rows(), differential.cols());
    let stage = BarStage::Cocycles;
    reserve_cocycle_work(rows, cols, degree, stage, ledger)?;
    let raw = differential.left_kernel_basis(field);
    ledger.work_elim(degree, stage, raw.rows(), raw.cols())?;
    let cocycles = raw.into_row_space_basis(field);
    ledger.retain_matrix(degree, stage, &cocycles)?;
    Ok(cocycles)
}

pub(super) fn coboundaries(
    differential: &DenseMat,
    field: &PrimeField,
    degree: usize,
    ledger: &mut Ledger,
) -> BuildResult<DenseMat> {
    let stage = BarStage::Coboundaries;
    let budget = ledger.budget(degree, stage);
    let entries =
        budget.size(budget.product([differential.rows() as u128, differential.cols() as u128])?)?;
    let scratch = budget.product([2, entries as u128])?;
    ledger.scratch_u128(degree, stage, scratch)?;
    ledger.work_elim(degree, stage, differential.rows(), differential.cols())?;
    let coboundaries = differential.row_space_basis(field);
    ledger.retain_matrix(degree, stage, &coboundaries)?;
    Ok(coboundaries)
}

pub(super) fn complement(
    cocycles: &DenseMat,
    coboundaries: &DenseMat,
    field: &PrimeField,
    degree: usize,
    ledger: &mut Ledger,
) -> BuildResult<DenseMat> {
    let stage = BarStage::Complement;
    let rows = ledger.checked_usize(
        degree,
        stage,
        cocycles.rows().checked_add(coboundaries.rows()),
    )?;
    let width = cocycles.cols();
    let budget = ledger.budget(degree, stage);
    let scratch_rows = budget.sum(
        rows.min(width) as u128,
        budget.product([2, cocycles.rows() as u128])?,
    )?;
    let scratch = budget.product([scratch_rows, width as u128])?;
    ledger.scratch_u128(degree, stage, scratch)?;
    ledger.work_elim(degree, stage, rows, width)?;
    let complement = deterministic_complement(cocycles, coboundaries, field);
    ledger.retain_matrix(degree, stage, &complement)?;
    Ok(complement)
}

pub(super) fn elimination_work(
    rows: usize,
    cols: usize,
    ledger: &Ledger,
    degree: usize,
    stage: BarStage,
) -> BuildResult<u128> {
    let budget = ledger.budget(degree, stage);
    let pivot = rows.min(cols) as u128;
    let inner = budget.sum(1, budget.product([2, cols as u128])?)?;
    let next_cols = next_usize(ledger, degree, stage, cols)?;
    let updates = budget.product([2, rows as u128, next_cols as u128])?;
    let per_pivot = budget.sum(inner, updates)?;
    let body = budget.product([pivot, per_pivot])?;
    budget.sum(budget.product([rows as u128, cols as u128])?, body)
}

pub(super) fn checked_product(
    ledger: &Ledger,
    degree: usize,
    stage: BarStage,
    values: &[u128],
) -> BuildResult<u128> {
    values.iter().try_fold(1u128, |total, &value| {
        total.checked_mul(value).ok_or_else(|| {
            ledger.diagnostics(BarCutReason::SizeOverflow, stage, degree, 0, 0, None)
        })
    })
}

pub(super) fn checked_add(
    ledger: &Ledger,
    degree: usize,
    stage: BarStage,
    left: u128,
    right: u128,
) -> BuildResult<u128> {
    left.checked_add(right)
        .ok_or_else(|| ledger.diagnostics(BarCutReason::SizeOverflow, stage, degree, 0, 0, None))
}

pub(super) fn as_usize(
    ledger: &Ledger,
    degree: usize,
    stage: BarStage,
    value: u128,
) -> BuildResult<usize> {
    usize::try_from(value)
        .map_err(|_| ledger.diagnostics(BarCutReason::SizeOverflow, stage, degree, 0, value, None))
}

pub(super) fn next_usize(
    ledger: &Ledger,
    degree: usize,
    stage: BarStage,
    value: usize,
) -> BuildResult<usize> {
    value
        .checked_add(1)
        .ok_or_else(|| ledger.diagnostics(BarCutReason::SizeOverflow, stage, degree, 0, 0, None))
}

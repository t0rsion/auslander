use crate::linalg::DenseMat;

use super::super::cochain::{as_usize, checked_add, checked_product, elimination_work};
use super::super::limits::{
    BarBudgetDiagnostics, BarCutReason, BarLimit, BarLimits, BarStage, HochschildError,
};

#[derive(Debug)]
pub(crate) struct Ledger {
    pub(crate) limits: BarLimits,
    pub(crate) requested_degree: usize,
    pub(crate) completed_degree_count: usize,
    pub(crate) work_units: u64,
    pub(crate) matrix_entries: usize,
    pub(crate) degrees: Vec<super::super::outcome::HochschildDegree>,
}

#[derive(Debug)]
pub(crate) struct Stop(pub(crate) BarBudgetDiagnostics);

pub(crate) type BuildResult<T> = Result<T, Stop>;

#[derive(Debug)]
pub(crate) enum BuildFailure {
    Stop(Stop),
    Defect(HochschildError),
}

pub(crate) type InnerResult<T> = Result<T, BuildFailure>;

from_variants!(BuildFailure { Stop => Stop });

impl Ledger {
    pub(crate) fn diagnostics(
        &self,
        reason: BarCutReason,
        stage: BarStage,
        degree: usize,
        used: u128,
        proposed: u128,
        ceiling: Option<u128>,
    ) -> Stop {
        Stop(BarBudgetDiagnostics {
            reason,
            stage,
            requested_degree: self.requested_degree,
            completed_degree_count: self.completed_degree_count,
            first_uncomputed_differential: degree,
            work_units: self.work_units,
            matrix_entries: self.matrix_entries,
            used,
            proposed,
            ceiling,
        })
    }

    pub(crate) fn overflow<T>(&self, degree: usize, stage: BarStage) -> BuildResult<T> {
        Err(self.diagnostics(BarCutReason::SizeOverflow, stage, degree, 0, 0, None))
    }

    pub(crate) fn checked_usize(
        &self,
        degree: usize,
        stage: BarStage,
        value: Option<usize>,
    ) -> BuildResult<usize> {
        value.ok_or_else(|| self.diagnostics(BarCutReason::SizeOverflow, stage, degree, 0, 0, None))
    }

    pub(crate) fn limit(
        &self,
        kind: BarLimit,
        stage: BarStage,
        degree: usize,
        used: u128,
        proposed: u128,
        ceiling: u128,
    ) -> BuildResult<()> {
        if proposed <= ceiling {
            Ok(())
        } else {
            Err(self.diagnostics(
                BarCutReason::Limit(kind),
                stage,
                degree,
                used,
                proposed,
                Some(ceiling),
            ))
        }
    }

    pub(crate) fn work(&mut self, degree: usize, stage: BarStage, units: u128) -> BuildResult<()> {
        let Some(units) = u64::try_from(units).ok() else {
            return self.overflow(degree, stage);
        };
        let Some(proposed) = self.work_units.checked_add(units) else {
            return self.overflow(degree, stage);
        };
        self.limit(
            BarLimit::WorkUnits,
            stage,
            degree,
            self.work_units.into(),
            proposed.into(),
            self.limits.max_work_units.into(),
        )?;
        self.work_units = proposed;
        Ok(())
    }

    fn per_degree(
        &self,
        degree: usize,
        stage: BarStage,
        kind: BarLimit,
        proposed: usize,
        ceiling: usize,
    ) -> BuildResult<()> {
        self.limit(kind, stage, degree, 0, proposed as u128, ceiling as u128)
    }

    pub(crate) fn shape(
        &self,
        degree: usize,
        tuples: usize,
        cochain_dim: usize,
    ) -> BuildResult<()> {
        self.per_degree(
            degree,
            BarStage::Shape,
            BarLimit::TensorTuples,
            tuples,
            self.limits.max_tensor_tuples,
        )?;
        self.per_degree(
            degree,
            BarStage::Shape,
            BarLimit::CochainDimension,
            cochain_dim,
            self.limits.max_cochain_dim,
        )
    }

    pub(crate) fn scratch(
        &self,
        degree: usize,
        stage: BarStage,
        entries: usize,
    ) -> BuildResult<()> {
        let Some(proposed) = self.matrix_entries.checked_add(entries) else {
            return self.overflow(degree, stage);
        };
        self.limit(
            BarLimit::MatrixEntries,
            stage,
            degree,
            self.matrix_entries as u128,
            proposed as u128,
            self.limits.max_matrix_entries as u128,
        )
    }

    pub(crate) fn work_elim(
        &mut self,
        degree: usize,
        stage: BarStage,
        rows: usize,
        cols: usize,
    ) -> BuildResult<()> {
        self.work(
            degree,
            stage,
            elimination_work(rows, cols, self, degree, stage)?,
        )
    }

    pub(crate) fn retain(
        &mut self,
        degree: usize,
        stage: BarStage,
        entries: usize,
    ) -> BuildResult<()> {
        self.scratch(degree, stage, entries)?;
        self.matrix_entries += entries;
        Ok(())
    }

    pub(crate) fn retain_matrix(
        &mut self,
        degree: usize,
        stage: BarStage,
        matrix: &DenseMat,
    ) -> BuildResult<()> {
        let budget = self.budget(degree, stage);
        let entries =
            budget.size(budget.product([matrix.rows() as u128, matrix.cols() as u128])?)?;
        self.retain(degree, stage, entries)
    }

    accessor_methods! {
        pub(crate) budget(degree: usize, stage: BarStage) -> Budget<'_> = |this| Budget {
            ledger: this,
            degree,
            stage,
        };
        pub(crate) scratch_u128(degree: usize, stage: BarStage, entries: u128) -> BuildResult<()> = |this|
            this.scratch(degree, stage, as_usize(this, degree, stage, entries)?);
    }
}

#[derive(Clone, Copy)]
pub(crate) struct Budget<'a> {
    ledger: &'a Ledger,
    degree: usize,
    stage: BarStage,
}

impl Budget<'_> {
    pub(crate) fn product<const N: usize>(&self, values: [u128; N]) -> BuildResult<u128> {
        checked_product(self.ledger, self.degree, self.stage, &values)
    }

    accessor_methods! {
        pub(crate) sum(left: u128, right: u128) -> BuildResult<u128> = |this|
            checked_add(this.ledger, this.degree, this.stage, left, right);
        pub(crate) size(value: u128) -> BuildResult<usize> = |this|
            as_usize(this.ledger, this.degree, this.stage, value);
    }
}

use std::sync::Arc;

use crate::algebra::Algebra;

use super::limits::{BarLimits, HochschildError};
use super::outcome::{HochschildCohomology, HochschildOutcome, IncompleteHochschildCohomology};

#[path = "bar/budget.rs"]
mod budget;
#[path = "bar/builder.rs"]
mod builder;
#[path = "bar/differential.rs"]
mod differential;
#[path = "bar/shape.rs"]
mod shape;
#[path = "bar/tuple.rs"]
mod tuple;

pub(super) use budget::{Budget, BuildFailure, BuildResult, InnerResult, Ledger, Stop};
pub(super) use shape::{Layout, Shape, TupleOffsets};
pub(super) use tuple::{decode_tuple, input_rank, tuple_starts};

/// Computes normalized relative bar Hochschild cohomology through `max_degree`.
pub fn bar_hochschild(
    algebra: &Arc<Algebra>,
    max_degree: usize,
    limits: BarLimits,
) -> Result<HochschildOutcome, HochschildError> {
    let mut ledger = Ledger {
        limits,
        requested_degree: max_degree,
        completed_degree_count: 0,
        work_units: 0,
        matrix_entries: 0,
        degrees: Vec::new(),
    };
    match builder::DegreeBuilder::new(algebra, &mut ledger).run(max_degree) {
        Ok(()) => Ok(HochschildOutcome::Complete(HochschildCohomology {
            algebra: algebra.clone(),
            requested_degree: max_degree,
            limits,
            degrees: std::mem::take(&mut ledger.degrees),
            diagnostics: super::limits::BarRunDiagnostics {
                work_units: ledger.work_units,
                matrix_entries: ledger.matrix_entries,
            },
        })),
        Err(BuildFailure::Stop(Stop(diagnostics))) => {
            Ok(HochschildOutcome::Cut(IncompleteHochschildCohomology {
                algebra: algebra.clone(),
                requested_degree: max_degree,
                limits,
                degrees: std::mem::take(&mut ledger.degrees),
                diagnostics,
            }))
        }
        Err(BuildFailure::Defect(error)) => Err(error),
    }
}

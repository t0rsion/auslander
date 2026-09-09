//! Split bound quiver presentations of tilting target algebras.
//!
//! For a classical tilting right module `T`, the right-module target is
//! `End_A(T)^op`. A successful value stores a checked presentation of that
//! opposite algebra and the coordinate map back to `End_A(T)`.

#[path = "target_parts/construction.rs"]
mod construction;
#[path = "target_parts/coordinate.rs"]
mod coordinate;
#[path = "target_parts/presentation.rs"]
mod presentation;
#[path = "target_parts/types.rs"]
mod types;
#[path = "target_parts/verification.rs"]
mod verification;

pub(crate) use coordinate::{CoordinateAlgebra, CoordinateTargetData, CoordinateTargetOutcome};
pub use presentation::present_target;
pub(crate) use presentation::recover_coordinate_target;
pub use types::{
    NonSplitTarget, TargetBudgetCut, TargetCutReason, TargetCutStage, TargetError, TargetLimits,
    TargetPresentationCut, TargetPresentationOutcome, TargetWork, VerifiedTargetPresentation,
};
pub(crate) use verification::{verify_coordinate_target_data, verify_target};

#[cfg(test)]
#[path = "target_parts/tests/mod.rs"]
mod tests;

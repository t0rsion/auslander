//! Cooperative cancellation and deterministic progress snapshots.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, RwLock};

/// The current stage of a controlled computation.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum ProgressStage {
    /// No controlled computation has started.
    #[default]
    Idle,
    /// A projective-object cover is being built.
    ReplacementCover,
    /// A finite complex resolution is being totalized.
    ReplacementTotalize,
    /// A replacement mapping cone is being checked.
    ReplacementVerify,
    /// Derived Hom spaces are being computed.
    DerivedHom,
    /// A bounded homological batch stream is being consumed.
    HomologicalBatch,
    /// A finite module census is being enumerated.
    Census,
    /// Tilting-complex obligations are being checked.
    Tilting,
    /// A mutation frontier is being explored.
    Mutation,
    /// A portable artifact is being verified.
    ArtifactVerify,
    /// The controlled computation completed.
    Complete,
}

/// A deterministic progress report.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct ProgressSnapshot {
    stage: ProgressStage,
    completed_work: usize,
    reserved_work: usize,
}

impl ProgressSnapshot {
    accessor_methods! {
        /// The current computation stage.
        pub stage() -> ProgressStage = |this| this.stage;
        /// The number of completed deterministic work units.
        pub completed_work() -> usize = |this| this.completed_work;
        /// The number of accepted deterministic work units.
        pub reserved_work() -> usize = |this| this.reserved_work;
    }
}

/// A thread-safe cooperative cancellation flag.
#[derive(Clone, Debug, Default)]
pub struct CancellationToken(Arc<AtomicBool>);

impl CancellationToken {
    /// Creates a clear cancellation flag.
    pub fn new() -> CancellationToken {
        CancellationToken::default()
    }

    /// Requests cancellation.
    pub fn cancel(&self) {
        self.0.store(true, Ordering::Release);
    }

    /// Whether cancellation has been requested.
    pub fn is_cancelled(&self) -> bool {
        self.0.load(Ordering::Acquire)
    }
}

/// Shared cancellation and progress state for one computation.
#[derive(Clone, Debug, Default)]
pub struct ComputationControl {
    cancellation: CancellationToken,
    progress: Arc<RwLock<ProgressSnapshot>>,
}

impl ComputationControl {
    /// Creates clear control state.
    pub fn new() -> ComputationControl {
        ComputationControl::default()
    }

    /// Returns a shared cancellation flag.
    pub fn cancellation_token(&self) -> CancellationToken {
        self.cancellation.clone()
    }

    /// Requests cancellation.
    pub fn cancel(&self) {
        self.cancellation.cancel();
    }

    /// Whether cancellation has been requested.
    pub fn is_cancelled(&self) -> bool {
        self.cancellation.is_cancelled()
    }

    /// Returns the latest deterministic progress snapshot.
    pub fn progress(&self) -> ProgressSnapshot {
        *self
            .progress
            .read()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    pub(crate) fn update(&self, stage: ProgressStage, completed_work: usize, reserved_work: usize) {
        *self
            .progress
            .write()
            .unwrap_or_else(std::sync::PoisonError::into_inner) = ProgressSnapshot {
            stage,
            completed_work,
            reserved_work,
        };
    }
}

/// A cancellation request observed before a charged work unit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Cancelled;

/// Checks cancellation before each work unit of one controlled computation.
///
/// A cancelled computation finishes at most the unit already running. A meter
/// without a control never observes cancellation.
#[derive(Debug, Default)]
pub(crate) struct WorkMeter {
    control: Option<ComputationControl>,
    #[cfg(test)]
    charged: usize,
    #[cfg(test)]
    cancel_at: Option<usize>,
}

impl WorkMeter {
    /// A meter that observes the cancellation flag of `control`.
    pub(crate) fn new(control: &ComputationControl) -> WorkMeter {
        WorkMeter {
            control: Some(control.clone()),
            #[cfg(test)]
            charged: 0,
            #[cfg(test)]
            cancel_at: None,
        }
    }

    /// A meter that cancels `control` when `units` work units have run.
    #[cfg(test)]
    pub(crate) fn cancelling_at(control: &ComputationControl, units: usize) -> WorkMeter {
        WorkMeter {
            cancel_at: Some(units),
            ..WorkMeter::new(control)
        }
    }

    /// Starts one work unit, or reports cancellation without starting it.
    pub(crate) fn charge(&mut self) -> Result<(), Cancelled> {
        let Some(control) = &self.control else {
            return Ok(());
        };
        #[cfg(test)]
        if self.cancel_at == Some(self.charged) {
            control.cancel();
        }
        if control.is_cancelled() {
            return Err(Cancelled);
        }
        #[cfg(test)]
        {
            self.charged += 1;
        }
        Ok(())
    }

    /// The number of started work units.
    #[cfg(test)]
    pub(crate) fn charged(&self) -> usize {
        self.charged
    }
}

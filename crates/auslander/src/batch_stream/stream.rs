use std::sync::Arc;

use super::{
    HomologicalBatchStreamChunk, HomologicalBatchStreamCutReason, HomologicalBatchStreamError,
    HomologicalBatchStreamLimits, HomologicalBatchStreamRow, HomologicalBatchStreamStatus,
    HomologicalBatchStreamStep, HomologicalBatchStreamWork,
};
use crate::algebra::Algebra;
use crate::batch::HomologicalBatch;
use crate::control::{CancellationToken, ComputationControl, ProgressStage};
use crate::module::Module;

/// A bounded-memory stream of self-pair rows.
pub struct HomologicalSelfPairStream<I> {
    modules: I,
    max_degree: usize,
    limits: HomologicalBatchStreamLimits,
    cancellation: Option<CancellationToken>,
    control: Option<ComputationControl>,
    algebra: Option<Arc<Algebra>>,
    next_source: usize,
    work: HomologicalBatchStreamWork,
    state: StreamState,
}

enum StreamState {
    Active,
    Complete,
    Cut(HomologicalBatchStreamCutReason),
    Failed {
        source: usize,
        error: HomologicalBatchStreamError,
    },
}

/// Builds a bounded-memory self-pair stream from an input iterator.
pub fn stream_self_pairs<I>(
    modules: I,
    max_degree: usize,
    limits: HomologicalBatchStreamLimits,
    control: Option<&ComputationControl>,
) -> Result<HomologicalSelfPairStream<I::IntoIter>, HomologicalBatchStreamError>
where
    I: IntoIterator<Item = Module>,
{
    HomologicalSelfPairStream::new(modules, max_degree, limits, control)
}

impl<I> HomologicalSelfPairStream<I>
where
    I: Iterator<Item = Module>,
{
    /// Creates a stream with optional chunk-boundary cancellation.
    pub fn new<J>(
        modules: J,
        max_degree: usize,
        limits: HomologicalBatchStreamLimits,
        control: Option<&ComputationControl>,
    ) -> Result<HomologicalSelfPairStream<I>, HomologicalBatchStreamError>
    where
        J: IntoIterator<IntoIter = I, Item = Module>,
    {
        if limits.max_live_sources == 0 {
            return Err(HomologicalBatchStreamError::InvalidMaxLiveSources);
        }
        let degree_steps = max_degree
            .checked_add(1)
            .ok_or(HomologicalBatchStreamError::DegreeOverflow { degree: max_degree })?;
        if limits.max_pairs == 0 || limits.max_ext_cells.checked_div(degree_steps).unwrap_or(0) == 0
        {
            return Err(HomologicalBatchStreamError::NoPairCapacity {
                max_pairs: limits.max_pairs,
                max_ext_cells: limits.max_ext_cells,
                degree_steps,
            });
        }
        if let Some(control) = control {
            control.update(ProgressStage::HomologicalBatch, 0, 0);
        }
        Ok(HomologicalSelfPairStream {
            modules: modules.into_iter(),
            max_degree,
            limits,
            cancellation: control.map(ComputationControl::cancellation_token),
            control: control.cloned(),
            algebra: None,
            next_source: 0,
            work: HomologicalBatchStreamWork::default(),
            state: StreamState::Active,
        })
    }

    accessor_methods! {
        /// The next global source index.
        pub next_source() -> usize = |this| this.next_source;
        /// Cumulative exact work.
        pub work() -> HomologicalBatchStreamWork = |this| this.work;
        /// The configured largest Ext degree.
        pub max_degree() -> usize = |this| this.max_degree;
        /// The configured limits.
        pub limits() -> HomologicalBatchStreamLimits = |this| this.limits;
    }

    /// The current stream status.
    pub fn status(&self) -> HomologicalBatchStreamStatus {
        match &self.state {
            StreamState::Active => HomologicalBatchStreamStatus::Active,
            StreamState::Complete => HomologicalBatchStreamStatus::Complete,
            StreamState::Cut(reason) => HomologicalBatchStreamStatus::Cut(*reason),
            StreamState::Failed { source, error } => HomologicalBatchStreamStatus::Failed {
                source: *source,
                error: error.clone(),
            },
        }
    }

    /// Computes the next source chunk or a typed terminal step.
    pub fn next_chunk(&mut self) -> HomologicalBatchStreamStep {
        if !matches!(self.state, StreamState::Active) {
            return self.terminal_step();
        }
        if self.cancelled() {
            self.state = StreamState::Cut(HomologicalBatchStreamCutReason::Cancelled);
            return self.terminal_step();
        }
        let first_source = self.next_source;
        let capacity = self.chunk_capacity();
        let modules: Vec<Module> = self.modules.by_ref().take(capacity).collect();
        if modules.is_empty() {
            self.state = StreamState::Complete;
            self.update_progress(true);
            return self.terminal_step();
        }
        let chunk = match self.build_chunk(first_source, modules) {
            Ok(chunk) => chunk,
            Err(error) => return self.failed(first_source, error),
        };
        if let Err(error) = self.commit_chunk(&chunk) {
            return self.failed(first_source, error);
        }
        self.update_progress(false);
        HomologicalBatchStreamStep::Chunk(chunk)
    }

    fn cancelled(&self) -> bool {
        self.cancellation
            .as_ref()
            .is_some_and(CancellationToken::is_cancelled)
    }

    fn build_chunk(
        &mut self,
        first_source: usize,
        modules: Vec<Module>,
    ) -> Result<HomologicalBatchStreamChunk, HomologicalBatchStreamError> {
        validate_stream_algebra(&mut self.algebra, first_source, &modules)?;
        let batch = HomologicalBatch::self_pairs(modules, self.max_degree, self.limits.batch())
            .map_err(HomologicalBatchStreamError::Batch)?;
        make_chunk(first_source, batch)
    }

    fn commit_chunk(
        &mut self,
        chunk: &HomologicalBatchStreamChunk,
    ) -> Result<(), HomologicalBatchStreamError> {
        let source_count = chunk.source_count();
        self.work.add_chunk(chunk.work, source_count)?;
        self.next_source = self.next_source.checked_add(source_count).ok_or(
            HomologicalBatchStreamError::IndexOverflow {
                source: self.next_source,
            },
        )?;
        Ok(())
    }

    fn chunk_capacity(&self) -> usize {
        let degree_steps = self
            .max_degree
            .checked_add(1)
            .expect("stream constructor checks degree overflow");
        self.limits
            .max_live_sources
            .min(self.limits.max_pairs)
            .min(self.limits.max_ext_cells / degree_steps)
    }

    fn failed(
        &mut self,
        source: usize,
        error: HomologicalBatchStreamError,
    ) -> HomologicalBatchStreamStep {
        self.state = StreamState::Failed {
            source,
            error: error.clone(),
        };
        self.terminal_step()
    }

    fn update_progress(&self, complete: bool) {
        let Some(control) = &self.control else {
            return;
        };
        let stage = if complete {
            ProgressStage::Complete
        } else {
            ProgressStage::HomologicalBatch
        };
        control.update(stage, self.next_source, self.next_source);
    }

    fn terminal_step(&self) -> HomologicalBatchStreamStep {
        match &self.state {
            StreamState::Active => unreachable!("active stream has no terminal step"),
            StreamState::Complete => HomologicalBatchStreamStep::Complete {
                next_source: self.next_source,
                work: self.work,
            },
            StreamState::Cut(reason) => HomologicalBatchStreamStep::Cut {
                next_source: self.next_source,
                reason: *reason,
                work: self.work,
            },
            StreamState::Failed { source, error } => HomologicalBatchStreamStep::Failed {
                source: *source,
                error: error.clone(),
                work: self.work,
            },
        }
    }
}

fn validate_stream_algebra(
    expected: &mut Option<Arc<Algebra>>,
    first_source: usize,
    modules: &[Module],
) -> Result<(), HomologicalBatchStreamError> {
    let Some(first) = modules.first() else {
        return Ok(());
    };
    let algebra = expected.get_or_insert_with(|| first.algebra().clone());
    for (local, module) in modules.iter().enumerate() {
        if !Arc::ptr_eq(algebra, module.algebra()) {
            let source = first_source.checked_add(local).ok_or(
                HomologicalBatchStreamError::IndexOverflow {
                    source: first_source,
                },
            )?;
            return Err(HomologicalBatchStreamError::DifferentAlgebra { source });
        }
    }
    Ok(())
}

pub(crate) fn make_chunk(
    first_source: usize,
    batch: HomologicalBatch,
) -> Result<HomologicalBatchStreamChunk, HomologicalBatchStreamError> {
    let rows = batch
        .pairs()
        .iter()
        .enumerate()
        .map(|(local, pair)| {
            let source = first_source.checked_add(local).ok_or(
                HomologicalBatchStreamError::IndexOverflow {
                    source: first_source,
                },
            )?;
            let resolution = batch
                .resolution(local)
                .ok_or(HomologicalBatchStreamError::MissingResolution { source })?;
            Ok(HomologicalBatchStreamRow {
                source,
                target: source,
                hom_dim: pair.hom_dim(),
                stable_hom_dim: pair.stable_hom_dim(),
                ext_dimensions: pair.ext_dimensions().to_vec(),
                resolution_end: resolution.end,
            })
        })
        .collect::<Result<Vec<_>, HomologicalBatchStreamError>>()?;
    Ok(HomologicalBatchStreamChunk {
        first_source,
        work: batch.work(),
        batch,
        rows,
    })
}

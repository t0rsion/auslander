use crate::batch::{HomologicalBatch, HomologicalBatchError, HomologicalBatchLimits};
use crate::resolution::{ProjectiveResolution, ResolutionEnd};

/// Limits for one chunk of a self-pair stream.
///
/// `max_live_sources` is a hard upper bound on the number of source modules
/// passed to one [`HomologicalBatch`]. Pair and Ext-cell limits apply to each
/// chunk. A stream does not retain completed chunks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HomologicalBatchStreamLimits {
    /// Maximum number of source modules retained in one chunk.
    pub max_live_sources: usize,
    /// Maximum number of self-pairs in one chunk.
    pub max_pairs: usize,
    /// Maximum number of Ext dimension cells in one chunk.
    pub max_ext_cells: usize,
}

impl Default for HomologicalBatchStreamLimits {
    fn default() -> Self {
        let batch = HomologicalBatchLimits::default();
        Self {
            max_live_sources: 1,
            max_pairs: batch.max_pairs,
            max_ext_cells: batch.max_ext_cells,
        }
    }
}

impl HomologicalBatchStreamLimits {
    pub(super) fn batch(self) -> HomologicalBatchLimits {
        HomologicalBatchLimits {
            max_pairs: self.max_pairs,
            max_ext_cells: self.max_ext_cells,
        }
    }
}

/// A stream configuration error or a failed chunk computation.
#[derive(Clone, Debug)]
pub enum HomologicalBatchStreamError {
    /// No source can fit the requested live-source limit.
    InvalidMaxLiveSources,
    /// The Ext bound has no representable successor.
    DegreeOverflow { degree: usize },
    /// Pair and Ext-cell limits leave no capacity for one source.
    NoPairCapacity {
        max_pairs: usize,
        max_ext_cells: usize,
        degree_steps: usize,
    },
    /// One source does not share the stream's first algebra object.
    DifferentAlgebra { source: usize },
    /// The ordinary batch rejected a source chunk.
    Batch(HomologicalBatchError),
    /// A self-pair batch did not retain the resolution for one source.
    MissingResolution { source: usize },
    /// A global row index has no representable successor.
    IndexOverflow { source: usize },
    /// Cumulative work counters overflowed.
    WorkOverflow,
}

display_error! { error HomologicalBatchStreamError {
    Self::InvalidMaxLiveSources => "max_live_sources must be positive";
    Self::DegreeOverflow { degree } => "Ext degree {degree} has no representable successor";
    Self::NoPairCapacity { max_pairs, max_ext_cells, degree_steps } => "stream limits cannot fit one source: max_pairs {max_pairs}, max_ext_cells {max_ext_cells}, degree steps {degree_steps}";
    Self::DifferentAlgebra { source } => "source {source} does not share the stream algebra";
    Self::Batch(error) => "self-pair chunk failed: {error}";
    Self::MissingResolution { source } => "self-pair chunk has no resolution for source {source}";
    Self::IndexOverflow { source } => "global source index {source} has no representable successor";
    Self::WorkOverflow => "stream work counters overflowed";
} }

/// Why a self-pair stream stopped before its input ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HomologicalBatchStreamCutReason {
    /// Cancellation was requested at a chunk boundary.
    Cancelled,
}

/// One exact self-pair row with its source resolution status.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HomologicalBatchStreamRow {
    pub(super) source: usize,
    pub(super) target: usize,
    pub(super) hom_dim: usize,
    pub(super) stable_hom_dim: usize,
    pub(super) ext_dimensions: Vec<usize>,
    pub(super) resolution_end: ResolutionEnd,
}

impl HomologicalBatchStreamRow {
    pub(crate) fn from_parts(
        source: usize,
        target: usize,
        hom_dim: usize,
        stable_hom_dim: usize,
        ext_dimensions: Vec<usize>,
        resolution_end: ResolutionEnd,
    ) -> Self {
        Self {
            source,
            target,
            hom_dim,
            stable_hom_dim,
            ext_dimensions,
            resolution_end,
        }
    }

    accessor_methods! {
        /// The global source index.
        pub source() -> usize = |this| this.source;
        /// The global target index.
        pub target() -> usize = |this| this.target;
        /// `dim_k Hom(source, target)`.
        pub hom_dim() -> usize = |this| this.hom_dim;
        /// `dim_k stable Hom(source, target)`.
        pub stable_hom_dim() -> usize = |this| this.stable_hom_dim;
        /// Ext dimensions in degrees zero through the stream bound.
        pub ext_dimensions() -> &[usize] = |this| &this.ext_dimensions;
        /// The end status of the source resolution used for this row.
        pub resolution_end() -> ResolutionEnd = |this| this.resolution_end;
    }
}

/// Exact rows and witnesses for one source chunk.
///
/// The embedded [`HomologicalBatch`] owns the source modules and their
/// resolutions. It remains available for verification until this chunk is
/// dropped. Holding every returned chunk defeats the stream's memory bound.
#[derive(Clone)]
pub struct HomologicalBatchStreamChunk {
    pub(super) first_source: usize,
    pub(super) batch: HomologicalBatch,
    pub(super) rows: Vec<HomologicalBatchStreamRow>,
    pub(super) work: crate::batch::HomologicalBatchWork,
}

impl HomologicalBatchStreamChunk {
    accessor_methods! {
        /// The global index of the first source in this chunk.
        pub first_source() -> usize = |this| this.first_source;
        /// Exact rows in global source order.
        pub rows() -> &[HomologicalBatchStreamRow] = |this| &this.rows;
        /// Exact work for this chunk.
        pub work() -> crate::batch::HomologicalBatchWork = |this| this.work;
        /// The ordinary batch witness for this chunk.
        pub batch() -> &HomologicalBatch = |this| &this.batch;
    }

    /// The number of source modules retained by this chunk.
    pub fn source_count(&self) -> usize {
        self.batch.modules().len()
    }

    /// The source resolution witness for a local row index.
    pub fn resolution(&self, row: usize) -> Option<&ProjectiveResolution> {
        self.batch.resolution(row)
    }

    /// Recomputes the chunk and checks global row indices and resolution ends.
    pub fn verify(&self) -> bool {
        self.batch.verify()
            && self.rows.len() == self.batch.pairs().len()
            && self.rows.iter().enumerate().all(|(local, row)| {
                let Some(pair) = self.batch.pairs().get(local) else {
                    return false;
                };
                let Some(resolution) = self.batch.resolution(local) else {
                    return false;
                };
                let Some(global) = self.first_source.checked_add(local) else {
                    return false;
                };
                row.source == global
                    && row.target == global
                    && row.hom_dim == pair.hom_dim()
                    && row.stable_hom_dim == pair.stable_hom_dim()
                    && row.ext_dimensions == pair.ext_dimensions()
                    && row.resolution_end == resolution.end
            })
    }
}

debug_fields! { HomologicalBatchStreamChunk |this| {
    "first_source" => this.first_source;
    "sources" => this.source_count();
    "rows" => this.rows.len();
    "work" => this.work;
} }

/// Cumulative exact work and the largest source chunk retained so far.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct HomologicalBatchStreamWork {
    /// Number of completed chunks.
    pub chunks: usize,
    /// Number of completed source rows.
    pub sources: usize,
    /// Number of ordinary source resolutions.
    pub resolutions: usize,
    /// Number of target projective covers.
    pub target_covers: usize,
    /// Number of ordinary Hom spaces.
    pub hom_spaces: usize,
    /// Number of Hom spaces into target covers.
    pub projective_factor_spaces: usize,
    /// Number of Ext tables.
    pub ext_tables: usize,
    /// Largest number of sources held by one chunk.
    pub peak_live_sources: usize,
}

impl HomologicalBatchStreamWork {
    pub(crate) fn add_chunk(
        &mut self,
        work: crate::batch::HomologicalBatchWork,
        sources: usize,
    ) -> Result<(), HomologicalBatchStreamError> {
        self.chunks = self
            .chunks
            .checked_add(1)
            .ok_or(HomologicalBatchStreamError::WorkOverflow)?;
        self.sources = self
            .sources
            .checked_add(sources)
            .ok_or(HomologicalBatchStreamError::WorkOverflow)?;
        self.resolutions = self
            .resolutions
            .checked_add(work.resolutions)
            .ok_or(HomologicalBatchStreamError::WorkOverflow)?;
        self.target_covers = self
            .target_covers
            .checked_add(work.target_covers)
            .ok_or(HomologicalBatchStreamError::WorkOverflow)?;
        self.hom_spaces = self
            .hom_spaces
            .checked_add(work.hom_spaces)
            .ok_or(HomologicalBatchStreamError::WorkOverflow)?;
        self.projective_factor_spaces = self
            .projective_factor_spaces
            .checked_add(work.projective_factor_spaces)
            .ok_or(HomologicalBatchStreamError::WorkOverflow)?;
        self.ext_tables = self
            .ext_tables
            .checked_add(work.ext_tables)
            .ok_or(HomologicalBatchStreamError::WorkOverflow)?;
        self.peak_live_sources = self.peak_live_sources.max(sources);
        Ok(())
    }
}

/// The terminal or active state of a self-pair stream.
#[derive(Clone, Debug)]
pub enum HomologicalBatchStreamStatus {
    /// The stream can produce another chunk.
    Active,
    /// The input iterator ended after `next_source` rows.
    Complete,
    /// The stream stopped before the input iterator ended.
    Cut(HomologicalBatchStreamCutReason),
    /// A chunk or internal invariant failed.
    Failed {
        /// The first source index in the failed chunk.
        source: usize,
        /// The failure.
        error: HomologicalBatchStreamError,
    },
}

/// One call to [`crate::batch_stream::HomologicalSelfPairStream::next_chunk`].
#[derive(Debug)]
pub enum HomologicalBatchStreamStep {
    /// One exact chunk. The stream retains no reference to it.
    Chunk(HomologicalBatchStreamChunk),
    /// The input ended and all returned rows are complete.
    Complete {
        /// The first source index after the completed prefix.
        next_source: usize,
        /// Cumulative exact work.
        work: HomologicalBatchStreamWork,
    },
    /// The stream stopped before input exhaustion.
    Cut {
        /// The first source index not returned.
        next_source: usize,
        /// The stopping reason.
        reason: HomologicalBatchStreamCutReason,
        /// Cumulative exact work.
        work: HomologicalBatchStreamWork,
    },
    /// A chunk failed. Rows before `source` remain exact.
    Failed {
        /// The first source index in the failed chunk.
        source: usize,
        /// The failure.
        error: HomologicalBatchStreamError,
        /// Cumulative exact work before the failed chunk.
        work: HomologicalBatchStreamWork,
    },
}

impl HomologicalBatchStreamStep {
    /// The status represented by this step.
    pub fn status(&self) -> HomologicalBatchStreamStatus {
        match self {
            Self::Chunk(_) => HomologicalBatchStreamStatus::Active,
            Self::Complete { .. } => HomologicalBatchStreamStatus::Complete,
            Self::Cut { reason, .. } => HomologicalBatchStreamStatus::Cut(*reason),
            Self::Failed { source, error, .. } => HomologicalBatchStreamStatus::Failed {
                source: *source,
                error: error.clone(),
            },
        }
    }
}

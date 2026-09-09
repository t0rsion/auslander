use super::portable_encode::{canonical_without_fingerprint, fingerprint};
use super::portable_parser;
use super::portable_types::{
    HomologicalStreamBudget, HomologicalStreamConfig, HomologicalStreamCutReason,
    HomologicalStreamParseLimits, HomologicalStreamPortableError, HomologicalStreamPortableStatus,
    HomologicalStreamStep, HomologicalStreamVerifyLimits, VerifiedHomologicalStream,
};
use super::{
    HomologicalBatchStreamChunk, HomologicalBatchStreamLimits, HomologicalBatchStreamWork,
};
use crate::batch::{HomologicalBatch, HomologicalBatchLimits};
use crate::census::{CensusOutcome, CensusPortableStatus, VerifiedCensus};
use crate::control::{CancellationToken, ComputationControl};
use crate::field::Fp;
use crate::linalg::DenseMat;
use crate::module::Module;
use crate::quiver::ArrowId;

/// A canonical homological self-pair stream checkpoint.
#[derive(Clone, Debug)]
pub struct HomologicalStreamPortable {
    pub(super) census: String,
    pub(super) census_fingerprint: String,
    pub(super) max_degree: usize,
    pub(super) config: HomologicalStreamConfig,
    pub(super) next_source: usize,
    pub(super) rows: Vec<super::HomologicalBatchStreamRow>,
    pub(super) work: HomologicalBatchStreamWork,
    pub(super) chunk_sizes: Vec<usize>,
    pub(super) status: HomologicalStreamPortableStatus,
    pub(super) fingerprint: String,
}

impl HomologicalStreamPortable {
    /// Starts an active checkpoint over a verified complete census.
    pub fn from_verified_census(
        census: &VerifiedCensus,
        max_degree: usize,
        config: HomologicalStreamConfig,
    ) -> Result<Self, HomologicalStreamPortableError> {
        validate_config(max_degree, config.chunk_limits)?;
        require_complete_census(census)?;
        let mut portable = Self {
            census: census.portable().to_canonical_json(),
            census_fingerprint: census.portable().fingerprint().to_string(),
            max_degree,
            config,
            next_source: 0,
            rows: Vec::new(),
            work: HomologicalBatchStreamWork::default(),
            chunk_sizes: Vec::new(),
            status: HomologicalStreamPortableStatus::Active,
            fingerprint: String::new(),
        };
        portable.fingerprint = fingerprint(&canonical_without_fingerprint(&portable));
        Ok(portable)
    }

    accessor_methods! {
        /// The embedded complete census JSON.
        pub census() -> &str = |this| &this.census;
        /// The fingerprint of the embedded complete census.
        pub census_fingerprint() -> &str = |this| &this.census_fingerprint;
        /// The largest Ext degree in each stored row.
        pub max_degree() -> usize = |this| this.max_degree;
        /// The fixed chunk limits and absolute ceilings.
        pub config() -> HomologicalStreamConfig = |this| this.config;
        /// The first representative without a stored row.
        pub next_source() -> usize = |this| this.next_source;
        /// The exact completed rows in representative order.
        pub rows() -> &[super::HomologicalBatchStreamRow] = |this| &this.rows;
        /// The cumulative exact batch work.
        pub work() -> HomologicalBatchStreamWork = |this| this.work;
        /// The source count of each committed chunk, in order.
        pub chunk_sizes() -> &[usize] = |this| &this.chunk_sizes;
        /// The active, complete, or cut checkpoint status.
        pub status() -> &HomologicalStreamPortableStatus = |this| &this.status;
        /// The canonical FNV-1a fingerprint of the preceding fields.
        pub fingerprint() -> &str = |this| &this.fingerprint;
    }

    /// Serializes this checkpoint to byte-exact canonical JSON.
    pub fn to_canonical_json(&self) -> String {
        let mut output = canonical_without_fingerprint(self);
        output.push_str(",\"fingerprint\":\"");
        output.push_str(&self.fingerprint);
        output.push_str("\"}");
        output
    }

    /// Parses one canonical checkpoint under explicit limits.
    pub fn from_json(
        text: &str,
        limits: HomologicalStreamParseLimits,
    ) -> Result<Self, HomologicalStreamPortableError> {
        let raw = portable_parser::parse(text, limits)?;
        let census =
            String::from_utf8(raw.census).map_err(|_| HomologicalStreamPortableError::Syntax {
                byte: 0,
                message: "embedded census bytes are not UTF-8".to_string(),
            })?;
        validate_fingerprint(&raw.census_fingerprint)?;
        validate_fingerprint(&raw.fingerprint)?;
        let portable = Self {
            census,
            census_fingerprint: raw.census_fingerprint,
            max_degree: raw.max_degree,
            config: raw.config,
            next_source: raw.next_source,
            rows: raw.rows,
            work: raw.work,
            chunk_sizes: raw.chunk_sizes,
            status: raw.status,
            fingerprint: raw.fingerprint,
        };
        if portable.to_canonical_json() != text {
            return Err(HomologicalStreamPortableError::NonCanonical);
        }
        if !portable.has_valid_fingerprint() {
            return Err(HomologicalStreamPortableError::FingerprintMismatch);
        }
        Ok(portable)
    }

    /// Whether the outer fingerprint matches the canonical preceding fields.
    pub fn has_valid_fingerprint(&self) -> bool {
        self.fingerprint == fingerprint(&canonical_without_fingerprint(self))
    }

    /// Independently reconstructs the census and replays every stored row.
    pub fn verify(
        &self,
        limits: HomologicalStreamVerifyLimits,
    ) -> Result<VerifiedHomologicalStream, HomologicalStreamPortableError> {
        super::portable_verify::verify_portable(self, limits)
    }
}

/// Builds a resumable homological stream from a verified complete census.
pub fn homological_stream_from_census(
    census: &VerifiedCensus,
    max_degree: usize,
    config: HomologicalStreamConfig,
    control: Option<&ComputationControl>,
) -> Result<HomologicalSelfPairCheckpointStream, HomologicalStreamPortableError> {
    HomologicalSelfPairCheckpointStream::from_verified_census(census, max_degree, config, control)
}

/// A bounded-memory stream that commits one complete chunk at a time.
pub struct HomologicalSelfPairCheckpointStream {
    census: VerifiedCensus,
    portable: HomologicalStreamPortable,
    cancellation: Option<CancellationToken>,
}

impl HomologicalSelfPairCheckpointStream {
    pub(super) fn from_verified_census(
        census: &VerifiedCensus,
        max_degree: usize,
        config: HomologicalStreamConfig,
        control: Option<&ComputationControl>,
    ) -> Result<Self, HomologicalStreamPortableError> {
        let portable = HomologicalStreamPortable::from_verified_census(census, max_degree, config)?;
        Ok(Self {
            census: census.clone(),
            portable,
            cancellation: control.map(ComputationControl::cancellation_token),
        })
    }

    pub(super) fn from_verified_checkpoint(
        verified: &VerifiedHomologicalStream,
        budget: HomologicalStreamBudget,
        control: Option<&ComputationControl>,
    ) -> Result<Self, HomologicalStreamPortableError> {
        let mut portable = verified.portable.clone();
        let committed_work = primitive_work_units(portable.work)?;
        if budget.max_sources < portable.next_source {
            return Err(HomologicalStreamPortableError::ResumeBudget {
                field: "max_sources",
                committed: portable.next_source,
                limit: budget.max_sources,
            });
        }
        if budget.max_work_units < committed_work {
            return Err(HomologicalStreamPortableError::ResumeBudget {
                field: "max_work_units",
                committed: committed_work,
                limit: budget.max_work_units,
            });
        }
        portable.config.budget = budget;
        let cancellation = control.map(ComputationControl::cancellation_token);
        portable.status = HomologicalStreamPortableStatus::Active;
        portable.fingerprint = fingerprint(&canonical_without_fingerprint(&portable));
        let mut stream = Self {
            census: verified.census.clone(),
            portable,
            cancellation,
        };
        if let Some(HomologicalStreamStep::Failed { error, .. }) = stream.boundary_step() {
            return Err(error);
        }
        Ok(stream)
    }

    accessor_methods! {
        /// The first representative without a stored row.
        pub next_source() -> usize = |this| this.portable.next_source();
        /// The cumulative exact batch work.
        pub work() -> HomologicalBatchStreamWork = |this| this.portable.work();
        /// The current active, complete, or cut status.
        pub status() -> &HomologicalStreamPortableStatus = |this| this.portable.status();
        /// The fixed chunk limits and current absolute ceilings.
        pub config() -> HomologicalStreamConfig = |this| this.portable.config();
    }

    /// Returns the latest checkpoint, which contains only committed chunks.
    pub fn checkpoint(&self) -> HomologicalStreamPortable {
        self.portable.clone()
    }

    /// Computes and commits the next complete chunk.
    pub fn next_chunk(&mut self) -> HomologicalStreamStep {
        if !matches!(
            self.portable.status,
            HomologicalStreamPortableStatus::Active
        ) {
            return self.terminal_step();
        }
        if let Some(step) = self.boundary_step() {
            return step;
        }
        self.compute_chunk()
    }

    fn boundary_step(&mut self) -> Option<HomologicalStreamStep> {
        if self.cancelled() {
            self.portable.status =
                HomologicalStreamPortableStatus::Cut(HomologicalStreamCutReason::Cancelled);
            self.refresh_fingerprint();
            return Some(self.terminal_step());
        }
        let total = source_count(&self.census);
        if self.portable.next_source >= total {
            self.portable.status = HomologicalStreamPortableStatus::Complete;
            self.refresh_fingerprint();
            return Some(self.terminal_step());
        }
        if self.portable.next_source >= self.portable.config.budget.max_sources {
            self.cut(HomologicalStreamCutReason::SourceLimit {
                limit: self.portable.config.budget.max_sources,
            });
            return Some(self.terminal_step());
        }
        let current_units = match primitive_work_units(self.portable.work) {
            Ok(units) => units,
            Err(error) => return Some(self.failed(error)),
        };
        if current_units >= self.portable.config.budget.max_work_units {
            self.cut(HomologicalStreamCutReason::WorkLimit {
                limit: self.portable.config.budget.max_work_units,
            });
            return Some(self.terminal_step());
        }
        None
    }

    fn compute_chunk(&mut self) -> HomologicalStreamStep {
        let total = source_count(&self.census);
        let capacity = self.chunk_capacity();
        let remaining_budget = self
            .portable
            .config
            .budget
            .max_sources
            .saturating_sub(self.portable.next_source);
        let count = capacity
            .min(total - self.portable.next_source)
            .min(remaining_budget);
        let chunk = match build_chunk(
            &self.census,
            self.portable.next_source,
            count,
            self.portable.max_degree,
            self.portable.config.chunk_limits,
        ) {
            Ok(chunk) => chunk,
            Err(error) => return self.failed(error),
        };
        let mut next_work = self.portable.work;
        if let Err(error) = next_work.add_chunk(chunk.work(), count) {
            return self.failed(error.into());
        }
        let next_units = match primitive_work_units(next_work) {
            Ok(units) => units,
            Err(error) => return self.failed(error),
        };
        if next_units > self.portable.config.budget.max_work_units {
            self.cut(HomologicalStreamCutReason::WorkLimit {
                limit: self.portable.config.budget.max_work_units,
            });
            return self.terminal_step();
        }
        self.commit_chunk(&chunk, next_work);
        self.set_boundary_status(total, next_units);
        HomologicalStreamStep::Chunk(chunk)
    }

    fn commit_chunk(
        &mut self,
        chunk: &HomologicalBatchStreamChunk,
        work: HomologicalBatchStreamWork,
    ) {
        self.portable.rows.extend_from_slice(chunk.rows());
        self.portable.work = work;
        self.portable.chunk_sizes.push(chunk.source_count());
        self.portable.next_source = self
            .portable
            .next_source
            .checked_add(chunk.source_count())
            .expect("verified census source count cannot overflow usize");
        self.refresh_fingerprint();
    }

    fn set_boundary_status(&mut self, total: usize, units: usize) {
        if self.portable.next_source == total {
            self.portable.status = HomologicalStreamPortableStatus::Complete;
        } else if self.portable.next_source >= self.portable.config.budget.max_sources {
            self.cut(HomologicalStreamCutReason::SourceLimit {
                limit: self.portable.config.budget.max_sources,
            });
        } else if units >= self.portable.config.budget.max_work_units {
            self.cut(HomologicalStreamCutReason::WorkLimit {
                limit: self.portable.config.budget.max_work_units,
            });
        }
        self.refresh_fingerprint();
    }

    fn cut(&mut self, reason: HomologicalStreamCutReason) {
        self.portable.status = HomologicalStreamPortableStatus::Cut(reason);
        self.refresh_fingerprint();
    }

    fn failed(&mut self, error: HomologicalStreamPortableError) -> HomologicalStreamStep {
        HomologicalStreamStep::Failed {
            source: self.portable.next_source,
            error,
            work: self.portable.work,
        }
    }

    fn refresh_fingerprint(&mut self) {
        self.portable.fingerprint = fingerprint(&canonical_without_fingerprint(&self.portable));
    }

    fn cancelled(&self) -> bool {
        self.cancellation
            .as_ref()
            .is_some_and(CancellationToken::is_cancelled)
    }

    fn chunk_capacity(&self) -> usize {
        let degree_steps = self
            .portable
            .max_degree
            .checked_add(1)
            .expect("stream configuration validates degree overflow");
        self.portable
            .config
            .chunk_limits
            .max_live_sources
            .min(self.portable.config.chunk_limits.max_pairs)
            .min(self.portable.config.chunk_limits.max_ext_cells / degree_steps)
    }

    fn terminal_step(&self) -> HomologicalStreamStep {
        match &self.portable.status {
            HomologicalStreamPortableStatus::Active => {
                unreachable!("active checkpoint has no terminal step")
            }
            HomologicalStreamPortableStatus::Complete => HomologicalStreamStep::Complete {
                next_source: self.portable.next_source,
                work: self.portable.work,
            },
            HomologicalStreamPortableStatus::Cut(reason) => HomologicalStreamStep::Cut {
                next_source: self.portable.next_source,
                reason: *reason,
                work: self.portable.work,
            },
        }
    }
}

fn require_complete_census(census: &VerifiedCensus) -> Result<(), HomologicalStreamPortableError> {
    if matches!(census.portable().status(), CensusPortableStatus::Complete)
        && matches!(census.outcome(), CensusOutcome::Complete(_))
    {
        Ok(())
    } else {
        Err(HomologicalStreamPortableError::CensusNotComplete)
    }
}

pub(super) fn validate_config(
    max_degree: usize,
    limits: HomologicalBatchStreamLimits,
) -> Result<(), HomologicalStreamPortableError> {
    let degree_steps = max_degree.checked_add(1).ok_or_else(|| {
        HomologicalStreamPortableError::InvalidConfig(
            "max_degree has no representable successor".to_string(),
        )
    })?;
    if limits.max_live_sources == 0 {
        return Err(HomologicalStreamPortableError::InvalidConfig(
            "max_live_sources must be positive".to_string(),
        ));
    }
    if limits.max_pairs == 0 || limits.max_ext_cells / degree_steps == 0 {
        return Err(HomologicalStreamPortableError::InvalidConfig(
            "chunk limits cannot fit one source".to_string(),
        ));
    }
    Ok(())
}

pub(super) fn source_count(census: &VerifiedCensus) -> usize {
    census.portable().representatives().len()
}

pub(super) fn build_chunk(
    census: &VerifiedCensus,
    first_source: usize,
    count: usize,
    max_degree: usize,
    limits: HomologicalBatchStreamLimits,
) -> Result<HomologicalBatchStreamChunk, HomologicalStreamPortableError> {
    let modules = (first_source..first_source + count)
        .map(|index| representative_module(census, index))
        .collect::<Result<Vec<_>, _>>()?;
    let batch = HomologicalBatch::self_pairs(
        modules,
        max_degree,
        HomologicalBatchLimits {
            max_pairs: limits.max_pairs,
            max_ext_cells: limits.max_ext_cells,
        },
    )
    .map_err(HomologicalStreamPortableError::Batch)?;
    super::stream::make_chunk(first_source, batch).map_err(HomologicalStreamPortableError::Stream)
}

fn representative_module(
    census: &VerifiedCensus,
    index: usize,
) -> Result<Module, HomologicalStreamPortableError> {
    let domain = census.census().domain();
    let representative = census
        .portable()
        .representatives()
        .get(index)
        .ok_or_else(|| HomologicalStreamPortableError::CountMismatch {
            field: "representative index".to_string(),
        })?;
    let coordinates = representative.coordinates();
    if coordinates.len() != domain.coordinate_count() {
        return Err(HomologicalStreamPortableError::CountMismatch {
            field: "representative coordinate count".to_string(),
        });
    }
    let algebra = domain.algebra();
    let field = algebra.field();
    let mut maps = Vec::with_capacity(algebra.quiver().num_arrows());
    let mut offset = 0usize;
    for arrow_index in 0..algebra.quiver().num_arrows() {
        let arrow = ArrowId(arrow_index as u32);
        let rows = domain.dimensions()[algebra.quiver().source(arrow) as usize];
        let columns = domain.dimensions()[algebra.quiver().target(arrow) as usize];
        let entries = rows.checked_mul(columns).ok_or_else(|| {
            HomologicalStreamPortableError::DomainMismatch {
                field: format!("arrow {arrow_index} coordinate count"),
            }
        })?;
        let end = offset.checked_add(entries).ok_or_else(|| {
            HomologicalStreamPortableError::DomainMismatch {
                field: "representative coordinate layout".to_string(),
            }
        })?;
        let values = coordinates.get(offset..end).ok_or_else(|| {
            HomologicalStreamPortableError::CountMismatch {
                field: "representative coordinate layout".to_string(),
            }
        })?;
        if let Some((row, &_value)) = values
            .iter()
            .enumerate()
            .find(|(_, value)| **value >= field.modulus())
        {
            return Err(HomologicalStreamPortableError::Module(
                crate::module::ModuleError::NonCanonicalEntry {
                    arrow,
                    row: row / columns,
                    col: row % columns,
                },
            ));
        }
        let values: Vec<Fp> = values
            .iter()
            .map(|&value| field.elem(value as i64))
            .collect();
        maps.push(DenseMat::from_flat(rows, columns, &values));
        offset = end;
    }
    Module::new(algebra.clone(), domain.dimensions().to_vec(), maps)
        .map_err(HomologicalStreamPortableError::Module)
}

pub(super) fn primitive_work_units(
    work: HomologicalBatchStreamWork,
) -> Result<usize, HomologicalStreamPortableError> {
    [
        work.resolutions,
        work.target_covers,
        work.hom_spaces,
        work.projective_factor_spaces,
        work.ext_tables,
    ]
    .into_iter()
    .try_fold(0usize, |total, value| {
        total
            .checked_add(value)
            .ok_or(HomologicalStreamPortableError::CounterOverflow {
                field: "primitive work units",
            })
    })
}

fn validate_fingerprint(value: &str) -> Result<(), HomologicalStreamPortableError> {
    if value.len() == 16
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        Ok(())
    } else {
        Err(HomologicalStreamPortableError::FingerprintShape)
    }
}

use super::portable::HomologicalStreamPortable;
use crate::batch::HomologicalBatchError;
use crate::census::{CensusPortableError, CensusVerifyLimits};
use crate::module::ModuleError;

/// The schema shared by portable computation values.
pub const HOMOLOGICAL_STREAM_PORTABLE_SCHEMA: &str = "auslander-computation-v1";

/// The payload kind for a homological self-pair stream checkpoint.
pub const HOMOLOGICAL_STREAM_PORTABLE_KIND: &str = "homological-self-pair-stream-v2";

/// The deterministic engine identifier for homological stream replay.
pub const HOMOLOGICAL_STREAM_ENGINE_ID: &str = "raw-arrow-matrix-v1+homological-self-pair-v1";

/// Absolute source and primitive-work ceilings for one stream run.
///
/// `max_sources` counts representatives from source zero. `max_work_units`
/// counts source resolutions, target covers, Hom spaces, projective-factor
/// spaces, and Ext tables. A zero ceiling cuts before the first chunk.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct HomologicalStreamBudget {
    /// The greatest number of representative rows that may be committed.
    pub max_sources: usize,
    /// The greatest cumulative primitive-work count that may be committed.
    pub max_work_units: usize,
}

impl Default for HomologicalStreamBudget {
    fn default() -> Self {
        Self {
            max_sources: usize::MAX,
            max_work_units: usize::MAX,
        }
    }
}

/// Fixed chunk limits and absolute ceilings for a homological stream.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct HomologicalStreamConfig {
    /// The limits used for every `HomologicalBatch` chunk.
    pub chunk_limits: super::HomologicalBatchStreamLimits,
    /// The absolute source and primitive-work ceilings.
    pub budget: HomologicalStreamBudget,
}

/// Limits applied before a homological stream parser allocates containers.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct HomologicalStreamParseLimits {
    /// The greatest byte count of the complete portable value.
    pub max_input_bytes: usize,
    /// The greatest byte count of the embedded complete census JSON.
    pub max_census_bytes: usize,
    /// The greatest number of stored rows.
    pub max_rows: usize,
    /// The greatest number of Ext entries in one row.
    pub max_ext_dimensions: usize,
    /// The greatest number of numeric values in the document.
    pub max_numeric_values: usize,
    /// The greatest number of array elements in the document.
    pub max_array_elements: usize,
    /// The greatest digit count in one unsigned integer.
    pub max_integer_digits: usize,
    /// The greatest byte count of a non-census string.
    pub max_string_bytes: usize,
}

impl Default for HomologicalStreamParseLimits {
    fn default() -> Self {
        Self {
            max_input_bytes: 1 << 30,
            max_census_bytes: 1 << 29,
            max_rows: 1_000_000,
            max_ext_dimensions: 4096,
            max_numeric_values: 10_000_000,
            max_array_elements: 10_000_000,
            max_integer_digits: 39,
            max_string_bytes: 4096,
        }
    }
}

/// Limits applied while a homological checkpoint is independently verified.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct HomologicalStreamVerifyLimits {
    /// Limits applied by the homological parser.
    pub parse: HomologicalStreamParseLimits,
    /// Limits applied while parsing and replaying the embedded census.
    pub census: CensusVerifyLimits,
    /// The greatest representative catalog size replayed by one checkpoint.
    pub max_representatives: usize,
    /// The greatest Ext degree accepted by one checkpoint.
    pub max_degree: usize,
    /// The greatest cumulative primitive-work count replayed.
    pub max_work_units: usize,
}

impl Default for HomologicalStreamVerifyLimits {
    fn default() -> Self {
        Self {
            parse: HomologicalStreamParseLimits::default(),
            census: CensusVerifyLimits::default(),
            max_representatives: 1_000_000,
            max_degree: 4096,
            max_work_units: 10_000_000,
        }
    }
}

/// Why a homological stream stopped at a chunk boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum HomologicalStreamCutReason {
    /// Cancellation was observed before the next chunk.
    Cancelled,
    /// The next source would exceed the absolute source ceiling.
    SourceLimit { limit: usize },
    /// The next chunk would exceed the absolute primitive-work ceiling.
    WorkLimit { limit: usize },
}

display_error! { HomologicalStreamCutReason {
    Self::Cancelled => "homological stream was cancelled";
    Self::SourceLimit { limit } => "homological source limit {limit} reached";
    Self::WorkLimit { limit } => "homological work limit {limit} reached";
} }

/// The durable status of a homological stream checkpoint.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HomologicalStreamPortableStatus {
    /// More representatives remain and no boundary cut was recorded.
    Active,
    /// Every representative in the complete census has a stored row.
    Complete,
    /// The stored prefix stopped at a typed boundary.
    Cut(HomologicalStreamCutReason),
}

/// A parser, verification, or replay error for a homological checkpoint.
#[derive(Clone, Debug)]
pub enum HomologicalStreamPortableError {
    /// A declared parser container or scalar limit was exceeded.
    ParseLimit {
        path: String,
        used: usize,
        limit: usize,
    },
    /// The bounded parser rejected one byte.
    Syntax { byte: usize, message: String },
    /// The top-level schema identifier is not supported.
    Schema { found: String },
    /// The payload kind is not supported.
    Kind { found: String },
    /// The deterministic engine identifier is not supported.
    Engine { found: String },
    /// The parsed bytes are valid but not canonical JSON.
    NonCanonical,
    /// The outer or census fingerprint has the wrong shape.
    FingerprintShape,
    /// The outer fingerprint does not match the canonical fields.
    FingerprintMismatch,
    /// The embedded census fingerprint differs from the census value.
    CensusFingerprintMismatch,
    /// The embedded census was rejected or failed replay verification.
    Census(CensusPortableError),
    /// The embedded census is a cut or failed value.
    CensusNotComplete,
    /// A declared checkpoint workload exceeds the caller's ceiling.
    VerificationLimit {
        field: &'static str,
        declared: usize,
        limit: usize,
    },
    /// A serialized counter does not fit the host `usize` type.
    CounterOverflow { field: &'static str },
    /// A checkpoint field is inconsistent with the complete census.
    DomainMismatch { field: String },
    /// A checkpoint count or row is inconsistent.
    CountMismatch { field: String },
    /// Replay does not reproduce the stored prefix.
    ReplayMismatch { field: String },
    /// The fixed chunk limits cannot compute one source.
    InvalidConfig(String),
    /// A resume ceiling is below work already committed to the checkpoint.
    ResumeBudget {
        field: &'static str,
        committed: usize,
        limit: usize,
    },
    /// A reconstructed representative is not a module.
    Module(ModuleError),
    /// A homological chunk failed.
    Batch(HomologicalBatchError),
    /// The existing stream invariant failed.
    Stream(super::HomologicalBatchStreamError),
}

display_error! { HomologicalStreamPortableError {
    Self::ParseLimit { path, used, limit } => "portable field {path} needs {used} units, limit {limit}";
    Self::Syntax { byte, message } => "invalid homological stream JSON at byte {byte}: {message}";
    Self::Schema { found } => "unsupported homological stream schema {found:?}";
    Self::Kind { found } => "unsupported homological stream payload kind {found:?}";
    Self::Engine { found } => "unsupported homological stream engine {found:?}";
    Self::NonCanonical => "homological stream JSON is not canonical";
    Self::FingerprintShape => "homological stream fingerprints must contain 16 lowercase hexadecimal digits";
    Self::FingerprintMismatch => "homological stream fingerprint does not match its canonical fields";
    Self::CensusFingerprintMismatch => "embedded census fingerprint does not match its stored fingerprint";
    Self::Census(error) => "embedded census rejected: {error}";
    Self::CensusNotComplete => "homological stream requires a complete embedded census";
    Self::VerificationLimit { field, declared, limit } => "homological verification field {field} has {declared}, limit {limit}";
    Self::CounterOverflow { field } => "homological stream field {field} does not fit usize";
    Self::DomainMismatch { field } => "homological stream domain field {field} is inconsistent";
    Self::CountMismatch { field } => "homological stream field {field} is inconsistent";
    Self::ReplayMismatch { field } => "homological stream replay differs at {field}";
    Self::InvalidConfig(message) => "invalid homological stream configuration: {message}";
    Self::ResumeBudget { field, committed, limit } => "homological resume budget {field} has limit {limit}, below committed value {committed}";
    Self::Module(error) => "representative reconstruction failed: {error}";
    Self::Batch(error) => "homological chunk failed: {error}";
    Self::Stream(error) => "homological stream failed: {error}";
} }

error_source! { HomologicalStreamPortableError {
    Self::Census(error) => Some(error),
    Self::Module(error) => Some(error),
    Self::Batch(error) => Some(error),
    Self::Stream(error) => Some(error),
    _ => None,
} }

impl From<CensusPortableError> for HomologicalStreamPortableError {
    fn from(error: CensusPortableError) -> Self {
        Self::Census(error)
    }
}

impl From<ModuleError> for HomologicalStreamPortableError {
    fn from(error: ModuleError) -> Self {
        Self::Module(error)
    }
}

impl From<HomologicalBatchError> for HomologicalStreamPortableError {
    fn from(error: HomologicalBatchError) -> Self {
        Self::Batch(error)
    }
}

impl From<super::HomologicalBatchStreamError> for HomologicalStreamPortableError {
    fn from(error: super::HomologicalBatchStreamError) -> Self {
        Self::Stream(error)
    }
}

/// A verified checkpoint and the independently reconstructed census.
#[derive(Clone, Debug)]
pub struct VerifiedHomologicalStream {
    pub(crate) portable: HomologicalStreamPortable,
    pub(crate) census: crate::census::VerifiedCensus,
}

impl VerifiedHomologicalStream {
    accessor_methods! {
        /// The canonical checkpoint that was verified.
        pub portable() -> &HomologicalStreamPortable = |this| &this.portable;
        /// The complete census reconstructed during verification.
        pub census() -> &crate::census::VerifiedCensus = |this| &this.census;
    }
}

/// A stream step that carries one bounded batch or a typed terminal state.
#[derive(Debug)]
pub enum HomologicalStreamStep {
    /// One completed source chunk. The caller can drop it after consuming rows.
    Chunk(super::HomologicalBatchStreamChunk),
    /// Every representative has been processed.
    Complete {
        /// The first representative index after the completed prefix.
        next_source: usize,
        /// Cumulative exact work.
        work: super::HomologicalBatchStreamWork,
    },
    /// The stream stopped before the census catalog ended.
    Cut {
        /// The first representative index not returned.
        next_source: usize,
        /// The stopping reason.
        reason: HomologicalStreamCutReason,
        /// Cumulative exact work.
        work: super::HomologicalBatchStreamWork,
    },
    /// A chunk failed before it was committed.
    Failed {
        /// The first representative index in the failed chunk.
        source: usize,
        /// The failure.
        error: HomologicalStreamPortableError,
        /// Cumulative exact work before the failed chunk.
        work: super::HomologicalBatchStreamWork,
    },
}

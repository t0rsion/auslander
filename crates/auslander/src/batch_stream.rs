//! Bounded-memory self-pair batches.
//!
//! A stream owns one source chunk at a time. Each chunk keeps the ordinary
//! [`crate::batch::HomologicalBatch`] witness until the caller drops it. Source
//! indices stay global across chunks, and a terminal status names completion,
//! cancellation, or failure.

mod portable;
mod portable_encode;
mod portable_parser;
mod portable_types;
mod portable_verify;
mod stream;
mod types;

pub use portable::{
    HomologicalSelfPairCheckpointStream, HomologicalStreamPortable, homological_stream_from_census,
};
pub use portable_types::{
    HOMOLOGICAL_STREAM_ENGINE_ID, HOMOLOGICAL_STREAM_PORTABLE_KIND,
    HOMOLOGICAL_STREAM_PORTABLE_SCHEMA, HomologicalStreamBudget, HomologicalStreamConfig,
    HomologicalStreamCutReason, HomologicalStreamParseLimits, HomologicalStreamPortableError,
    HomologicalStreamPortableStatus, HomologicalStreamStep, HomologicalStreamVerifyLimits,
    VerifiedHomologicalStream,
};
pub use stream::{HomologicalSelfPairStream, stream_self_pairs};
pub use types::{
    HomologicalBatchStreamChunk, HomologicalBatchStreamCutReason, HomologicalBatchStreamError,
    HomologicalBatchStreamLimits, HomologicalBatchStreamRow, HomologicalBatchStreamStatus,
    HomologicalBatchStreamStep, HomologicalBatchStreamWork,
};

#[cfg(test)]
mod tests;

#[cfg(test)]
mod portable_tests;

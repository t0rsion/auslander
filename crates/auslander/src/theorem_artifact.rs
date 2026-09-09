//! Portable finite-census claims with independent homological verification.

mod errors;
mod model;
mod parser;
mod verify;

pub use errors::SelfExtLocusArtifactError;
pub use model::{
    SELF_EXT_LOCUS_ARTIFACT_KIND, SELF_EXT_LOCUS_ARTIFACT_SCHEMA, SelfExtLocusArtifact,
    SelfExtLocusParseLimits, SelfExtLocusVerifyLimits,
};
pub use verify::{VerifiedSelfExtLocusArtifact, verify_self_ext_locus_artifact};

#[cfg(test)]
mod tests;

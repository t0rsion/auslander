//! Canonical portable artifacts for certified derived-equivalence edges.

#[path = "derived_artifact_parts/errors.rs"]
mod errors;
#[path = "derived_artifact_parts/model.rs"]
mod model;
#[path = "derived_artifact_parts/parser.rs"]
mod parser;
#[path = "derived_artifact_parts/serialization.rs"]
mod serialization;
#[path = "derived_artifact_parts/verification.rs"]
mod verification;

/// The portable derived-equivalence schema identifier.
pub const DERIVED_ARTIFACT_SCHEMA: &str = "auslander-derived-v1";

pub use errors::ArtifactError;
pub use model::{ArtifactMutation, ArtifactParseLimits, ArtifactVerifyLimits, DerivedArtifact};
pub use verification::{
    ArtifactVerificationCut, ArtifactVerificationOutcome, VerifiedDerivedArtifact,
    verify_derived_artifact,
};

#[cfg(test)]
#[path = "derived_artifact_parts/tests.rs"]
mod tests;

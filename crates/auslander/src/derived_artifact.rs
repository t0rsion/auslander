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
///
/// Replay reduces each mutation cone to a minimal complex.
pub const DERIVED_ARTIFACT_SCHEMA: &str = "auslander-derived-v2";

/// The schema whose replay kept unreduced mutation cones. Its recipes can
/// replay to different complexes, so the parsers reject it.
pub(crate) const OBSOLETE_DERIVED_ARTIFACT_SCHEMA: &str = "auslander-derived-v1";

pub use errors::ArtifactError;
pub use model::{ArtifactMutation, ArtifactParseLimits, ArtifactVerifyLimits, DerivedArtifact};
pub(crate) use parser::read_mutation;
pub(crate) use serialization::push_mutation;
pub use verification::{
    ArtifactVerificationCut, ArtifactVerificationOutcome, VerifiedDerivedArtifact,
    verify_derived_artifact,
};
pub(crate) use verification::{declared_limits, exceeded, replay_recipe};

#[cfg(test)]
#[path = "derived_artifact_parts/tests.rs"]
mod tests;

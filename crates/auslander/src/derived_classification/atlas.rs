//! The portable `derived-atlas-v1` artifact of a derived classification.
//!
//! [`DerivedClassification::to_artifact`] writes the field, the member
//! certificates, every invariant reading, the classes with their merges,
//! the separations, the unresolved pairs, the limits, the walks, the status,
//! and a fingerprint. [`verify_derived_atlas_artifact`] replays all of it
//! without discovery and rebuilds the classification.
//!
//! A merge stores its recipe and the isomorphism coordinates, not the
//! recovered target: the verifier replays the recipe through
//! [`crate::derived_artifact`] and recovers the target itself. A walk
//! record is not replayed. It states why an unresolved pair stayed open,
//! and the verifier checks only that it matches the merges.
//!
//! [`DerivedClassification::to_artifact`]: super::DerivedClassification::to_artifact

mod errors;
mod model;
mod parse;
mod verify;
mod write;

/// The schema identifier, shared with the other computation artifacts.
pub const DERIVED_ATLAS_ARTIFACT_SCHEMA: &str = "auslander-computation-v1";
/// The payload kind of a derived atlas.
pub const DERIVED_ATLAS_ARTIFACT_KIND: &str = "derived-atlas-v1";
/// The engine that produced the classification.
pub const DERIVED_ATLAS_ARTIFACT_ENGINE: &str = "derived-classification-v1";

pub use errors::DerivedAtlasError;
pub use model::{
    AtlasClass, AtlasMerge, AtlasReading, AtlasSeparation, AtlasStop, DerivedAtlasArtifact,
    DerivedAtlasParseLimits, DerivedAtlasVerifyLimits,
};
pub use verify::{DerivedAtlasVerification, VerifiedDerivedAtlas, verify_derived_atlas_artifact};

#[cfg(test)]
mod tests;

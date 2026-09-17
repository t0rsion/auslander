//! Portable replay artifacts for catalog Ext tables and multiplicity results.

#[path = "atlas_artifact/errors.rs"]
mod errors;
#[path = "atlas_artifact/model.rs"]
mod model;
#[path = "atlas_artifact/parser.rs"]
mod parser;
#[path = "atlas_artifact/serialization.rs"]
mod serialization;
#[path = "atlas_artifact/verification.rs"]
mod verification;

pub const CATALOG_ATLAS_ARTIFACT_SCHEMA: &str = "auslander-computation-v1";
pub const CATALOG_ATLAS_ARTIFACT_KIND: &str = "catalog-atlas-v1";
pub const CATALOG_ATLAS_ARTIFACT_ENGINE: &str = "catalog-ext-multiplicity-v1";

pub use errors::CatalogAtlasArtifactError;
pub use model::{
    CatalogAtlasArtifact, CatalogAtlasArtifactExtRow, CatalogAtlasArtifactParseLimits,
    CatalogAtlasArtifactResultRow, CatalogAtlasArtifactStatus, CatalogAtlasArtifactVerifyLimits,
    VerifiedCatalogAtlasArtifact,
};
pub use verification::verify_catalog_atlas_artifact;

#[cfg(test)]
#[path = "atlas_artifact/tests.rs"]
mod tests;

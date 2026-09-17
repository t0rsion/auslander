use crate::algebra::AlgebraBuildError;
use crate::atlas::AtlasScoreError;
use crate::certificate::CertParseError;
use crate::ext::ExtError;
use crate::field::FieldError;
use crate::verify::VerifyError;

/// A portable atlas artifact failed parsing, replay, or a mathematical check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CatalogAtlasArtifactError {
    /// A parser byte, container, string, or integer limit was exceeded.
    ParseLimit {
        path: String,
        used: usize,
        limit: usize,
    },
    /// The bounded parser rejected one byte.
    Syntax { byte: usize, message: String },
    /// The top-level schema is unsupported.
    Schema { found: String },
    /// The payload kind is unsupported.
    Kind { found: String },
    /// The computation engine identifier is unsupported.
    Engine { found: String },
    /// The parsed bytes are valid but not canonical JSON.
    NonCanonical,
    /// The embedded completion certificate is malformed.
    Certificate(CertParseError),
    /// The embedded completion certificate failed verification.
    Verify(VerifyError),
    /// The verified completion could not rebuild an algebra.
    Algebra(AlgebraBuildError),
    /// The explicit field does not match the certificate field.
    FieldMismatch { certificate: u64, artifact: u64 },
    /// The explicit prime field is invalid.
    Field(FieldError),
    /// The catalog provenance string is unknown.
    Provenance { found: String },
    /// Rebuilding the catalog failed for the stored provenance.
    Catalog { message: String },
    /// The atlas engine rejected its stored limits or degree bound.
    Atlas(crate::atlas::CatalogAtlasError),
    /// The multiplicity engine rejected its stored target or limits.
    Multiplicity(crate::atlas::MultiplicityError),
    /// A cached self-Ext score request was invalid.
    Score(AtlasScoreError),
    /// A generic Ext cell could not be rebuilt.
    Ext(ExtError),
    /// A serialized field has the wrong shape or count.
    CountMismatch { field: String },
    /// The replay differs from one serialized claim.
    ReplayMismatch { field: String },
    /// A declared workload exceeds the verifier ceiling.
    VerificationLimit {
        field: &'static str,
        declared: usize,
        limit: usize,
    },
    /// A checked count has no representable product or sum.
    Overflow { field: &'static str },
}

display_error! { CatalogAtlasArtifactError {
    Self::ParseLimit { path, used, limit } => "atlas artifact field {path} needs {used} units, limit {limit}";
    Self::Syntax { byte, message } => "invalid atlas artifact JSON at byte {byte}: {message}";
    Self::Schema { found } => "unsupported atlas artifact schema {found:?}";
    Self::Kind { found } => "unsupported atlas artifact kind {found:?}";
    Self::Engine { found } => "unsupported atlas artifact engine {found:?}";
    Self::NonCanonical => "atlas artifact JSON is not canonical";
    Self::Certificate(error) => "embedded completion certificate rejected: {error}";
    Self::Verify(error) => "embedded completion certificate failed verification: {error}";
    Self::Algebra(error) => "verified completion could not rebuild an algebra: {error}";
    Self::FieldMismatch { certificate, artifact } => "certificate field F_{certificate} differs from artifact field F_{artifact}";
    Self::Field(error) => "artifact field is invalid: {error}";
    Self::Provenance { found } => "unsupported catalog provenance {found:?}";
    Self::Catalog { message } => "catalog reconstruction failed: {message}";
    Self::Atlas(error) => "catalog atlas replay failed: {error}";
    Self::Multiplicity(error) => "multiplicity replay failed: {error}";
    Self::Score(error) => "self-Ext score replay failed: {error}";
    Self::Ext(error) => "generic Ext replay failed: {error}";
    Self::CountMismatch { field } => "atlas artifact count field {field} is inconsistent";
    Self::ReplayMismatch { field } => "atlas artifact replay differs at {field}";
    Self::VerificationLimit { field, declared, limit } => "atlas artifact verification field {field} has {declared}, limit {limit}";
    Self::Overflow { field } => "atlas artifact count overflows while checking {field}";
} }

error_source! { CatalogAtlasArtifactError {
    Self::Certificate(error) => Some(error),
    Self::Verify(error) => Some(error),
    Self::Algebra(error) => Some(error),
    Self::Atlas(error) => Some(error),
    Self::Multiplicity(error) => Some(error),
    Self::Score(error) => Some(error),
    Self::Ext(error) => Some(error),
    Self::Field(error) => Some(error),
    _ => None,
} }

from_variants! { CatalogAtlasArtifactError {
    CertParseError => Certificate,
    VerifyError => Verify,
    AlgebraBuildError => Algebra,
    FieldError => Field,
    crate::atlas::CatalogAtlasError => Atlas,
    crate::atlas::MultiplicityError => Multiplicity,
    AtlasScoreError => Score,
    ExtError => Ext,
} }

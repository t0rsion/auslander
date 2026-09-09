use crate::algebra::AlgebraBuildError;
use crate::certificate::CertParseError;
use crate::complex_target::ComplexTargetError;
use crate::tilting_complex::TiltingComplexError;
use crate::verify::VerifyError;

/// An artifact failed parsing, reconstruction, or a mathematical check.
#[derive(Clone, Debug)]
pub enum ArtifactError {
    /// The source edge failed verification.
    InvalidEdge,
    /// An artifact generation chain did not start at the regular generator.
    Generation,
    /// A parser allocation limit rejected a container.
    ParseLimit {
        path: String,
        used: usize,
        limit: usize,
    },
    /// The bounded JSON parser rejected one byte.
    Syntax { byte: usize, message: String },
    /// An embedded completion certificate was malformed.
    Certificate { path: String, message: String },
    /// The schema identifier was not supported.
    Schema { found: String },
    /// The fingerprint field was not 16 lowercase hexadecimal digits.
    FingerprintShape,
    /// The fingerprint did not match the canonical preceding fields.
    FingerprintMismatch,
    /// A completion certificate failed independent verification.
    Verify(VerifyError),
    /// A verified completion could not rebuild an algebra.
    Algebra(AlgebraBuildError),
    /// A tilting mutation failed structurally.
    Tilting(TiltingComplexError),
    /// Complex target recovery failed structurally.
    Target(ComplexTargetError),
    /// A complete serialized mathematical claim did not recheck.
    Mathematical(String),
}

display_error! { ArtifactError {
    Self::InvalidEdge => "derived-equivalence edge does not verify";
    Self::Generation => "tilting generation does not reduce to regular mutations";
    Self::ParseLimit { path, used, limit } => "artifact field {path} needs {used} units, limit {limit}";
    Self::Syntax { byte, message } => "invalid artifact JSON at byte {byte}: {message}";
    Self::Certificate { path, message } => "invalid certificate in {path}: {message}";
    Self::Schema { found } => "unsupported artifact schema {found:?}";
    Self::FingerprintShape => "artifact fingerprint must contain 16 lowercase hexadecimal digits";
    Self::FingerprintMismatch => "artifact fingerprint does not match its canonical fields";
    Self::Verify(error) => "completion certificate rejected: {error}";
    Self::Algebra(error) => "verified source algebra rejected: {error}";
    Self::Tilting(error) => "artifact mutation failed: {error}";
    Self::Target(error) => "artifact target failed: {error}";
    Self::Mathematical(message) => "artifact claim rejected: {message}";
} }

error_source! { ArtifactError {
    Self::Verify(error) => Some(error),
    Self::Algebra(error) => Some(error),
    Self::Tilting(error) => Some(error),
    Self::Target(error) => Some(error),
    _ => None,
} }

impl From<VerifyError> for ArtifactError {
    fn from(error: VerifyError) -> Self {
        ArtifactError::Verify(error)
    }
}

impl From<AlgebraBuildError> for ArtifactError {
    fn from(error: AlgebraBuildError) -> Self {
        ArtifactError::Algebra(error)
    }
}

impl From<TiltingComplexError> for ArtifactError {
    fn from(error: TiltingComplexError) -> Self {
        ArtifactError::Tilting(error)
    }
}

impl From<ComplexTargetError> for ArtifactError {
    fn from(error: ComplexTargetError) -> Self {
        ArtifactError::Target(error)
    }
}

impl From<CertParseError> for ArtifactError {
    fn from(error: CertParseError) -> Self {
        ArtifactError::Certificate {
            path: "$".to_string(),
            message: error.to_string(),
        }
    }
}

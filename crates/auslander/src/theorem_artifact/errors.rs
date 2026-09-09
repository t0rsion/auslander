use crate::batch_stream::HomologicalStreamPortableError;
use crate::ext::ExtError;

/// A rejected self-Ext locus artifact or verification attempt.
#[derive(Clone, Debug)]
pub enum SelfExtLocusArtifactError {
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
    /// The parsed bytes are valid but not canonical JSON.
    NonCanonical,
    /// The fingerprint does not have its canonical shape.
    FingerprintShape,
    /// The fingerprint does not match the canonical preceding fields.
    FingerprintMismatch,
    /// The embedded homological checkpoint was rejected.
    Checkpoint(HomologicalStreamPortableError),
    /// The embedded homological checkpoint is not complete.
    CheckpointNotComplete,
    /// The first Ext degree is zero or exceeds the last degree.
    DegreeRange { first: usize, last: usize },
    /// The claimed last degree exceeds the checkpoint degree.
    DegreeOutsideCheckpoint { degree: usize, checkpoint: usize },
    /// A claimed representative index is repeated, unordered, or out of range.
    RepresentativeIndex { index: usize },
    /// A declared verification workload exceeds the caller's ceiling.
    VerificationLimit {
        field: &'static str,
        declared: usize,
        limit: usize,
    },
    /// A verification counter overflowed.
    CounterOverflow { field: &'static str },
    /// The generic Ext engine rejected a reconstructed representative.
    Ext(ExtError),
    /// Independent Ext calculation disagrees with the claimed locus.
    LocusMismatch { representative: usize },
}

display_error! { SelfExtLocusArtifactError {
    Self::ParseLimit { path, used, limit } => "theorem artifact field {path} needs {used} units, limit {limit}";
    Self::Syntax { byte, message } => "invalid theorem artifact JSON at byte {byte}: {message}";
    Self::Schema { found } => "unsupported theorem artifact schema {found:?}";
    Self::Kind { found } => "unsupported theorem artifact kind {found:?}";
    Self::NonCanonical => "theorem artifact JSON is not canonical";
    Self::FingerprintShape => "theorem artifact fingerprint must contain 16 lowercase hexadecimal digits";
    Self::FingerprintMismatch => "theorem artifact fingerprint does not match its canonical fields";
    Self::Checkpoint(error) => "embedded homological checkpoint rejected: {error}";
    Self::CheckpointNotComplete => "self-Ext locus needs a complete homological checkpoint";
    Self::DegreeRange { first, last } => "self-Ext degree range {first} through {last} must start above zero and be nonempty";
    Self::DegreeOutsideCheckpoint { degree, checkpoint } => "self-Ext degree {degree} exceeds checkpoint degree {checkpoint}";
    Self::RepresentativeIndex { index } => "self-Ext locus index {index} is unordered, repeated, or outside the census";
    Self::VerificationLimit { field, declared, limit } => "theorem verification field {field} has {declared}, limit {limit}";
    Self::CounterOverflow { field } => "theorem verification field {field} overflows usize";
    Self::Ext(error) => "independent self-Ext calculation failed: {error}";
    Self::LocusMismatch { representative } => "independent self-Ext calculation disagrees at representative {representative}";
} }

error_source! { SelfExtLocusArtifactError {
    Self::Checkpoint(error) => Some(error),
    Self::Ext(error) => Some(error),
    _ => None,
} }

impl From<HomologicalStreamPortableError> for SelfExtLocusArtifactError {
    fn from(error: HomologicalStreamPortableError) -> Self {
        Self::Checkpoint(error)
    }
}

impl From<ExtError> for SelfExtLocusArtifactError {
    fn from(error: ExtError) -> Self {
        Self::Ext(error)
    }
}

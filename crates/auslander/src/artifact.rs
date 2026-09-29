//! One dispatch over every portable artifact kind.
//!
//! [`read_kind`] reads the header of a portable document with the strict
//! portable cursor: `schema` first, then `kind` when the schema carries
//! payload kinds. [`inspect_artifact`] parses the selected format without
//! replay. [`verify_artifact`] runs the selected verifier and returns one
//! [`ArtifactVerification`]. Each kind keeps its own parser, verifier, and
//! error type. This module only selects them.
//!
//! Every kind registers in one place: [`ArtifactKind`] and the matches in
//! `artifact/kinds.rs`.

mod kinds;

use crate::control::ComputationControl;
use crate::derived_artifact::ArtifactVerificationCut;
use crate::portable::{Cursor, CursorLimits};

pub use kinds::{ArtifactKind, ArtifactLimits, VerifiedArtifactValue};

/// The longest `schema` or `kind` string the header reader accepts.
const HEADER_STRING_BYTES: usize = 256;

/// Headers that a current kind replaced: the schema, the payload kind when
/// the schema has payload kinds, and the current kind.
const OBSOLETE_KINDS: [(&str, Option<&str>, ArtifactKind); 2] = [
    (
        crate::batch_stream::HOMOLOGICAL_STREAM_PORTABLE_SCHEMA,
        Some("homological-self-pair-stream-v1"),
        ArtifactKind::HomologicalStream,
    ),
    (
        crate::derived_artifact::OBSOLETE_DERIVED_ARTIFACT_SCHEMA,
        None,
        ArtifactKind::DerivedEquivalence,
    ),
];

/// A header rejection, or a rejection from the verifier of one kind.
#[derive(Clone, Debug)]
pub enum PortableArtifactError {
    /// The header breaks the strict grammar at byte `byte`.
    Syntax { byte: usize, message: String },
    /// A header string at `path` needs `used` bytes against `limit`.
    ParseLimit {
        path: String,
        used: usize,
        limit: usize,
    },
    /// No registered kind uses the schema `found`.
    Schema { found: String },
    /// The schema is known, but no registered kind has the payload kind `found`.
    Kind { schema: String, found: String },
    /// `found` is a payload kind, or a schema without payload kinds, that
    /// `current` replaced.
    ObsoleteKind {
        found: String,
        current: ArtifactKind,
    },
    /// The derived-equivalence parser or verifier rejected the artifact.
    DerivedEquivalence(crate::derived_artifact::ArtifactError),
    /// The census parser or verifier rejected the value.
    Census(crate::census::CensusPortableError),
    /// The homological stream parser or verifier rejected the checkpoint.
    HomologicalStream(crate::batch_stream::HomologicalStreamPortableError),
    /// The catalog atlas parser or verifier rejected the artifact.
    CatalogAtlas(crate::atlas_artifact::CatalogAtlasArtifactError),
    /// The self-Ext locus parser or verifier rejected the artifact.
    SelfExtLocus(crate::theorem_artifact::SelfExtLocusArtifactError),
    /// The derived atlas parser or verifier rejected the artifact.
    DerivedAtlas(crate::derived_classification::DerivedAtlasError),
}

from_portable_error!(PortableArtifactError);

display_error! { error PortableArtifactError {
    Self::Syntax { byte, message } => "invalid portable value JSON at byte {byte}: {message}";
    Self::ParseLimit { path, used, limit } => "portable value field {path} needs {used} bytes, limit {limit}";
    Self::Schema { found } => "unsupported portable value schema {found:?}";
    Self::Kind { schema, found } => "unsupported portable value kind {found:?} for schema {schema:?}";
    Self::ObsoleteKind { found, current } => "obsolete portable value kind {found:?}, current kind {:?}", current.name();
    Self::DerivedEquivalence(error) => "{error}";
    Self::Census(error) => "{error}";
    Self::HomologicalStream(error) => "{error}";
    Self::CatalogAtlas(error) => "{error}";
    Self::SelfExtLocus(error) => "{error}";
    Self::DerivedAtlas(error) => "{error}";
} }

impl PortableArtifactError {
    /// The kind whose parser or verifier rejected the value, when the header
    /// selected one.
    pub fn kind(&self) -> Option<ArtifactKind> {
        match self {
            Self::DerivedEquivalence(_) => Some(ArtifactKind::DerivedEquivalence),
            Self::Census(_) => Some(ArtifactKind::Census),
            Self::HomologicalStream(_) => Some(ArtifactKind::HomologicalStream),
            Self::CatalogAtlas(_) => Some(ArtifactKind::CatalogAtlas),
            Self::SelfExtLocus(_) => Some(ArtifactKind::SelfExtLocus),
            Self::DerivedAtlas(_) => Some(ArtifactKind::DerivedAtlas),
            _ => None,
        }
    }
}

/// The display data of one parsed portable value.
///
/// `summary` holds short label and value pairs in a fixed order per kind.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArtifactReport {
    kind: ArtifactKind,
    fingerprint: String,
    canonical_json: String,
    summary: Vec<(&'static str, String)>,
    complete: bool,
}

impl ArtifactReport {
    accessor_methods! {
        /// The kind selected by the header.
        pub kind() -> ArtifactKind = |this| this.kind;
        /// The stored fingerprint.
        pub fingerprint() -> &str = |this| &this.fingerprint;
        /// The canonical JSON rebuilt from the parsed fields.
        pub canonical_json() -> &str = |this| &this.canonical_json;
        /// Label and value pairs for display.
        pub summary() -> &[(&'static str, String)] = |this| &this.summary;
        /// Whether the value claims a complete result, not a cut or active prefix.
        pub is_complete() -> bool = |this| this.complete;
    }
}

/// Whether a verified value claims a complete result or a prefix.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ArtifactStatus {
    /// Every claim replayed, and the value claims a complete result.
    Verified,
    /// Every stored claim replayed, and the value is a cut or active prefix.
    VerifiedCut,
}

impl ArtifactStatus {
    /// `"verified"` or `"verified-cut"`.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Verified => "verified",
            Self::VerifiedCut => "verified-cut",
        }
    }
}

/// A portable value accepted by the verifier of its kind.
#[derive(Clone, Debug)]
pub struct VerifiedArtifact {
    report: ArtifactReport,
    value: VerifiedArtifactValue,
}

impl VerifiedArtifact {
    accessor_methods! {
        /// The kind, fingerprint, canonical JSON, and summary.
        pub report() -> &ArtifactReport = |this| &this.report;
        /// The verified value with its rebuilt live data.
        pub value() -> &VerifiedArtifactValue = |this| &this.value;
    }

    /// [`ArtifactStatus::Verified`] for a complete claim, otherwise
    /// [`ArtifactStatus::VerifiedCut`].
    pub fn status(&self) -> ArtifactStatus {
        if self.report.complete {
            ArtifactStatus::Verified
        } else {
            ArtifactStatus::VerifiedCut
        }
    }
}

/// A verified value, or a typed stop before the verifier decided.
#[derive(Clone, Debug)]
pub enum ArtifactVerification {
    /// The verifier accepted the value.
    Verified(Box<VerifiedArtifact>),
    /// Cancellation or a verifier ceiling stopped the run. The value is
    /// neither accepted nor rejected. Only derived-equivalence and derived
    /// atlas replay stop.
    Stopped {
        kind: ArtifactKind,
        cut: ArtifactVerificationCut,
    },
}

/// Reads the header of `text` and returns the registered kind it names.
///
/// The header is the object's first member `schema`, then `kind` when the
/// schema carries payload kinds. Nothing after the header is read.
pub fn read_kind(text: &str) -> Result<ArtifactKind, PortableArtifactError> {
    let limits = CursorLimits {
        string_bytes: HEADER_STRING_BYTES,
        ..CursorLimits::NONE
    };
    let mut c = Cursor::new(text, limits)?;
    c.token(b'{')?;
    c.key("schema")?;
    let schema = c.string("$.schema")?;
    let matching: Vec<ArtifactKind> = ArtifactKind::ALL
        .into_iter()
        .filter(|kind| kind.schema() == schema)
        .collect();
    match matching.as_slice() {
        [] => Err(unknown_kind(schema, None)),
        [kind] if kind.payload_kind().is_none() => Ok(*kind),
        _ => read_payload_kind(&mut c, schema, &matching),
    }
}

fn read_payload_kind(
    c: &mut Cursor,
    schema: String,
    matching: &[ArtifactKind],
) -> Result<ArtifactKind, PortableArtifactError> {
    let found = c.next("kind", |c| c.string("$.kind"))?;
    let kind = matching
        .iter()
        .find(|kind| kind.payload_kind() == Some(found.as_str()));
    kind.copied()
        .ok_or_else(|| unknown_kind(schema, Some(found)))
}

/// The obsolete-kind error for a replaced header, or the unknown schema or
/// payload kind error.
fn unknown_kind(schema: String, found: Option<String>) -> PortableArtifactError {
    let obsolete = OBSOLETE_KINDS
        .iter()
        .find(|(old_schema, old_kind, _)| *old_schema == schema && *old_kind == found.as_deref());
    match (obsolete, found) {
        (Some(&(_, _, current)), found) => PortableArtifactError::ObsoleteKind {
            found: found.unwrap_or(schema),
            current,
        },
        (None, Some(found)) => PortableArtifactError::Kind { schema, found },
        (None, None) => PortableArtifactError::Schema { found: schema },
    }
}

/// Parses one portable value of any registered kind without replay.
///
/// The parser of the selected kind applies its parse limits from `limits`.
/// The report carries the stored fingerprint, which is not checked here.
pub fn inspect_artifact(
    text: &str,
    limits: &ArtifactLimits,
) -> Result<ArtifactReport, PortableArtifactError> {
    kinds::inspect(read_kind(text)?, text, limits)
}

/// Parses and verifies one portable value of any registered kind.
///
/// The verifier of the selected kind applies its limits from `limits`.
/// Only derived-equivalence and derived atlas replay observe `control`. A
/// derived artifact or atlas whose declared limits exceed the verifier
/// ceilings, or whose replay is cancelled, returns
/// [`ArtifactVerification::Stopped`].
pub fn verify_artifact(
    text: &str,
    limits: &ArtifactLimits,
    control: &ComputationControl,
) -> Result<ArtifactVerification, PortableArtifactError> {
    kinds::verify(read_kind(text)?, text, limits, control)
}

#[cfg(test)]
mod tests;

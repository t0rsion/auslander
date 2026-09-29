use crate::algebra::AlgebraBuildError;
use crate::certificate::CertParseError;
use crate::derived_invariant::DerivedInvariantKind;
use crate::field::FieldError;
use crate::hochschild::HochschildError;
use crate::verify::VerifyError;

/// An atlas failed to serialize, parse, or verify.
#[derive(Clone, Debug)]
pub enum DerivedAtlasError {
    /// A parser limit rejected the field at `path`.
    ParseLimit {
        path: String,
        used: usize,
        limit: usize,
    },
    /// The strict parser rejected the byte at `byte`.
    Syntax { byte: usize, message: String },
    /// The schema identifier is not `auslander-computation-v1`.
    Schema { found: String },
    /// The payload kind is not `derived-atlas-v1`.
    Kind { found: String },
    /// The engine identifier is not `derived-classification-v1`.
    Engine { found: String },
    /// The parsed value does not serialize back to the input bytes.
    NonCanonical,
    /// The fingerprint does not match the preceding canonical fields.
    FingerprintMismatch,
    /// The family has no member, so it names no field.
    EmptyFamily,
    /// The stored field is not a prime below `2^31`.
    Field(FieldError),
    /// A member certificate is malformed.
    Certificate {
        member: usize,
        error: CertParseError,
    },
    /// A member certificate names another field than the atlas.
    FieldMismatch { member: usize, found: u64 },
    /// A member certificate failed independent verification.
    Verify { member: usize, error: VerifyError },
    /// A verified member certificate did not rebuild an algebra.
    Algebra {
        member: usize,
        error: AlgebraBuildError,
    },
    /// The invariant rows do not have one row per member.
    RowCount { rows: usize, members: usize },
    /// A reading of `member` was cancelled, so no replay can reproduce it.
    CancelledReading { member: usize },
    /// The bar computation of `member` failed, an internal defect.
    Invariant {
        member: usize,
        error: HochschildError,
    },
    /// The recomputed reading of `kind` for `member` differs from the
    /// stored one.
    ReadingMismatch {
        member: usize,
        kind: DerivedInvariantKind,
    },
    /// The classes do not partition the family in representative order.
    Partition,
    /// The merges of `class` do not form a spanning tree of its members.
    SpanningTree { class: usize },
    /// The separated and unresolved pairs do not cover each pair of classes
    /// exactly once in pair order.
    PairCoverage,
    /// The walk list of an unresolved pair is not every walk from a member
    /// of either class.
    UnresolvedWalks { classes: (usize, usize) },
    /// The walks are not in member order, or their merge counts differ
    /// from the stored merges.
    Walks,
    /// The status is not `complete` exactly when no pair is unresolved.
    Status,
    /// A separation names members outside its classes, or its kind does not
    /// separate the recomputed readings, or its values differ from them.
    Separation { classes: (usize, usize) },
    /// The recipe of a merge does not replay to a certified target.
    Replay { source: usize, member: usize },
    /// The isomorphism of a merge does not verify.
    Isomorphism { source: usize, member: usize },
}

from_portable_error!(DerivedAtlasError, header);

display_error! { DerivedAtlasError {
    Self::ParseLimit { path, used, limit } => "atlas field {path} needs {used} units, limit {limit}";
    Self::Syntax { byte, message } => "invalid atlas JSON at byte {byte}: {message}";
    Self::Schema { found } => "unsupported atlas schema {found:?}";
    Self::Kind { found } => "unsupported atlas kind {found:?}";
    Self::Engine { found } => "unsupported atlas engine {found:?}";
    Self::NonCanonical => "atlas JSON is not canonical";
    Self::FingerprintMismatch => "atlas fingerprint does not match its canonical fields";
    Self::EmptyFamily => "the atlas family has no member";
    Self::Field(error) => "atlas field is invalid: {error}";
    Self::Certificate { member, error } => "certificate of member {member} is malformed: {error}";
    Self::FieldMismatch { member, found } => "member {member} lives over GF({found})";
    Self::Verify { member, error } => "certificate of member {member} failed verification: {error}";
    Self::Algebra { member, error } => "member {member} did not rebuild: {error}";
    Self::RowCount { rows, members } => "the atlas has {rows} invariant rows for {members} members";
    Self::CancelledReading { member } => "a reading of member {member} was cancelled";
    Self::Invariant { member, error } => "invariants of member {member} failed: {error}";
    Self::ReadingMismatch { member, kind } => "the reading {kind:?} of member {member} differs from its recomputation";
    Self::Partition => "the classes do not partition the family in representative order";
    Self::SpanningTree { class } => "the merges of class {class} do not form a spanning tree";
    Self::PairCoverage => "the pairs of classes are not each separated or unresolved exactly once";
    Self::UnresolvedWalks { classes } => "the walks of unresolved classes {} and {} are not the walks from their members", classes.0, classes.1;
    Self::Walks => "the walk records do not match the merges";
    Self::Status => "the status does not match the unresolved pairs";
    Self::Separation { classes } => "the separation of classes {} and {} does not hold", classes.0, classes.1;
    Self::Replay { source, member } => "the recipe of the merge from member {source} to member {member} does not replay";
    Self::Isomorphism { source, member } => "the isomorphism of the merge from member {source} to member {member} does not verify";
} }

error_source! { DerivedAtlasError {
    Self::Field(error) => Some(error),
    Self::Certificate { error, .. } => Some(error),
    Self::Verify { error, .. } => Some(error),
    Self::Algebra { error, .. } => Some(error),
    Self::Invariant { error, .. } => Some(error),
    _ => None,
} }

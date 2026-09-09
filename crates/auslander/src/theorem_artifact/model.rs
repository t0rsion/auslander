use crate::batch_stream::{
    HomologicalStreamParseLimits, HomologicalStreamPortable, HomologicalStreamPortableStatus,
    HomologicalStreamVerifyLimits, VerifiedHomologicalStream,
};

use super::errors::SelfExtLocusArtifactError;

/// The schema for portable finite computation claims.
pub const SELF_EXT_LOCUS_ARTIFACT_SCHEMA: &str = "auslander-theorem-v1";

/// The payload kind for one fixed-dimension self-Ext vanishing locus.
pub const SELF_EXT_LOCUS_ARTIFACT_KIND: &str = "fixed-dimension-self-ext-locus-v1";

/// Limits applied before the theorem artifact parser allocates containers.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SelfExtLocusParseLimits {
    /// The greatest byte count of the complete artifact.
    pub max_input_bytes: usize,
    /// Limits applied to the embedded homological checkpoint.
    pub checkpoint: HomologicalStreamParseLimits,
    /// The greatest number of claimed representative indices.
    pub max_vanishing_indices: usize,
    /// The greatest digit count in one unsigned integer.
    pub max_integer_digits: usize,
    /// The greatest byte count of a theorem artifact string.
    pub max_string_bytes: usize,
}

impl Default for SelfExtLocusParseLimits {
    fn default() -> Self {
        Self {
            max_input_bytes: 1 << 30,
            checkpoint: HomologicalStreamParseLimits::default(),
            max_vanishing_indices: 1_000_000,
            max_integer_digits: 39,
            max_string_bytes: 4096,
        }
    }
}

/// Limits applied during independent self-Ext locus verification.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SelfExtLocusVerifyLimits {
    /// Limits applied by the theorem artifact parser.
    pub parse: SelfExtLocusParseLimits,
    /// Limits applied while replaying the embedded checkpoint.
    pub checkpoint: HomologicalStreamVerifyLimits,
    /// The greatest number of representatives checked independently.
    pub max_representatives: usize,
    /// The greatest number of Ext degrees checked per representative.
    pub max_degree_span: usize,
    /// The greatest number of generic Ext spaces constructed.
    pub max_ext_spaces: usize,
}

impl Default for SelfExtLocusVerifyLimits {
    fn default() -> Self {
        Self {
            parse: SelfExtLocusParseLimits::default(),
            checkpoint: HomologicalStreamVerifyLimits::default(),
            max_representatives: 1_000_000,
            max_degree_span: 4096,
            max_ext_spaces: 10_000_000,
        }
    }
}

/// A complete fixed-dimension census claim about self-Ext vanishing.
#[derive(Clone, Debug)]
pub struct SelfExtLocusArtifact {
    pub(super) checkpoint: HomologicalStreamPortable,
    pub(super) first_degree: usize,
    pub(super) last_degree: usize,
    pub(super) vanishing_indices: Vec<usize>,
    pub(super) fingerprint: String,
}

impl SelfExtLocusArtifact {
    /// Builds a claim from one replay-verified complete checkpoint.
    pub fn from_verified_checkpoint(
        verified: &VerifiedHomologicalStream,
        first_degree: usize,
        last_degree: usize,
    ) -> Result<Self, SelfExtLocusArtifactError> {
        let checkpoint = verified.portable();
        check_degree_range(first_degree, last_degree, checkpoint.max_degree())?;
        if !matches!(
            checkpoint.status(),
            HomologicalStreamPortableStatus::Complete
        ) {
            return Err(SelfExtLocusArtifactError::CheckpointNotComplete);
        }
        let vanishing_indices = checkpoint
            .rows()
            .iter()
            .enumerate()
            .filter_map(|(index, row)| {
                row.ext_dimensions()[first_degree..=last_degree]
                    .iter()
                    .all(|&dimension| dimension == 0)
                    .then_some(index)
            })
            .collect();
        let mut artifact = Self {
            checkpoint: checkpoint.clone(),
            first_degree,
            last_degree,
            vanishing_indices,
            fingerprint: String::new(),
        };
        artifact.fingerprint = fingerprint(&artifact.canonical_without_fingerprint());
        Ok(artifact)
    }

    accessor_methods! {
        /// The embedded complete homological checkpoint.
        pub checkpoint() -> &HomologicalStreamPortable = |this| &this.checkpoint;
        /// The first positive Ext degree in the claim.
        pub first_degree() -> usize = |this| this.first_degree;
        /// The last Ext degree in the claim.
        pub last_degree() -> usize = |this| this.last_degree;
        /// Representative indices whose Ext groups vanish throughout the range.
        pub vanishing_indices() -> &[usize] = |this| &this.vanishing_indices;
        /// The canonical FNV-1a fingerprint of the preceding fields.
        pub fingerprint() -> &str = |this| &this.fingerprint;
    }

    /// Serializes the artifact to byte-exact canonical JSON.
    pub fn to_canonical_json(&self) -> String {
        let mut output = self.canonical_without_fingerprint();
        output.push_str(",\"fingerprint\":\"");
        output.push_str(&self.fingerprint);
        output.push_str("\"}");
        output
    }

    /// Parses one canonical theorem artifact under explicit limits.
    pub fn from_json(
        text: &str,
        limits: SelfExtLocusParseLimits,
    ) -> Result<Self, SelfExtLocusArtifactError> {
        let raw = super::parser::parse(text, limits)?;
        let checkpoint = HomologicalStreamPortable::from_json(&raw.checkpoint, limits.checkpoint)?;
        let artifact = Self {
            checkpoint,
            first_degree: raw.first_degree,
            last_degree: raw.last_degree,
            vanishing_indices: raw.vanishing_indices,
            fingerprint: raw.fingerprint,
        };
        if artifact.to_canonical_json() != text {
            return Err(SelfExtLocusArtifactError::NonCanonical);
        }
        if !artifact.has_valid_fingerprint() {
            return Err(SelfExtLocusArtifactError::FingerprintMismatch);
        }
        Ok(artifact)
    }

    /// Whether the fingerprint matches every preceding canonical field.
    pub fn has_valid_fingerprint(&self) -> bool {
        self.fingerprint == fingerprint(&self.canonical_without_fingerprint())
    }

    pub(super) fn canonical_without_fingerprint(&self) -> String {
        let mut output = String::new();
        output.push_str("{\"schema\":\"");
        output.push_str(SELF_EXT_LOCUS_ARTIFACT_SCHEMA);
        output.push_str("\",\"kind\":\"");
        output.push_str(SELF_EXT_LOCUS_ARTIFACT_KIND);
        output.push_str("\",\"checkpoint\":");
        output.push_str(&self.checkpoint.to_canonical_json());
        output.push_str(",\"first_degree\":");
        output.push_str(&self.first_degree.to_string());
        output.push_str(",\"last_degree\":");
        output.push_str(&self.last_degree.to_string());
        output.push_str(",\"vanishing_indices\":[");
        for (position, index) in self.vanishing_indices.iter().enumerate() {
            if position != 0 {
                output.push(',');
            }
            output.push_str(&index.to_string());
        }
        output.push(']');
        output
    }
}

pub(super) fn check_degree_range(
    first: usize,
    last: usize,
    checkpoint: usize,
) -> Result<(), SelfExtLocusArtifactError> {
    if first == 0 || first > last {
        return Err(SelfExtLocusArtifactError::DegreeRange { first, last });
    }
    if last > checkpoint {
        return Err(SelfExtLocusArtifactError::DegreeOutsideCheckpoint {
            degree: last,
            checkpoint,
        });
    }
    Ok(())
}

pub(super) fn fingerprint(text: &str) -> String {
    let mut value = 0xcbf29ce484222325u64;
    for byte in text.bytes() {
        value ^= u64::from(byte);
        value = value.wrapping_mul(0x100000001b3);
    }
    format!("{value:016x}")
}

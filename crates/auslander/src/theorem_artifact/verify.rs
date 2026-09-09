use crate::batch_stream::{HomologicalStreamPortableStatus, VerifiedHomologicalStream};
use crate::census::CensusOutcome;
use crate::ext::ExtSpace;

use super::errors::SelfExtLocusArtifactError;
use super::model::{
    SelfExtLocusArtifact, SelfExtLocusVerifyLimits, check_degree_range, fingerprint,
};

/// A self-Ext locus accepted by checkpoint replay and generic Ext calculation.
#[derive(Clone, Debug)]
pub struct VerifiedSelfExtLocusArtifact {
    artifact: SelfExtLocusArtifact,
    checkpoint: VerifiedHomologicalStream,
}

impl VerifiedSelfExtLocusArtifact {
    accessor_methods! {
        /// The canonical finite-census claim.
        pub artifact() -> &SelfExtLocusArtifact = |this| &this.artifact;
        /// The independently replayed homological checkpoint.
        pub checkpoint() -> &VerifiedHomologicalStream = |this| &this.checkpoint;
    }
}

impl SelfExtLocusArtifact {
    /// Replays the checkpoint and recomputes the claimed locus through `ExtSpace`.
    pub fn verify(
        &self,
        limits: SelfExtLocusVerifyLimits,
    ) -> Result<VerifiedSelfExtLocusArtifact, SelfExtLocusArtifactError> {
        if self.fingerprint != fingerprint(&self.canonical_without_fingerprint()) {
            return Err(SelfExtLocusArtifactError::FingerprintMismatch);
        }
        check_degree_range(
            self.first_degree,
            self.last_degree,
            self.checkpoint.max_degree(),
        )?;
        if !matches!(
            self.checkpoint.status(),
            HomologicalStreamPortableStatus::Complete
        ) {
            return Err(SelfExtLocusArtifactError::CheckpointNotComplete);
        }
        let verified_checkpoint = self.checkpoint.verify(limits.checkpoint)?;
        let CensusOutcome::Complete(result) = verified_checkpoint.census().outcome() else {
            return Err(SelfExtLocusArtifactError::CheckpointNotComplete);
        };
        let representatives = result.representatives();
        check_work_limits(self, representatives.len(), limits)?;
        check_indices(&self.vanishing_indices, representatives.len())?;
        verify_locus(self, representatives)?;
        Ok(VerifiedSelfExtLocusArtifact {
            artifact: self.clone(),
            checkpoint: verified_checkpoint,
        })
    }
}

fn check_work_limits(
    artifact: &SelfExtLocusArtifact,
    representatives: usize,
    limits: SelfExtLocusVerifyLimits,
) -> Result<(), SelfExtLocusArtifactError> {
    check_limit(
        "representatives",
        representatives,
        limits.max_representatives,
    )?;
    let span = artifact
        .last_degree
        .checked_sub(artifact.first_degree)
        .and_then(|value| value.checked_add(1))
        .ok_or(SelfExtLocusArtifactError::CounterOverflow {
            field: "degree span",
        })?;
    check_limit("degree_span", span, limits.max_degree_span)?;
    let ext_spaces =
        representatives
            .checked_mul(span)
            .ok_or(SelfExtLocusArtifactError::CounterOverflow {
                field: "Ext spaces",
            })?;
    check_limit("ext_spaces", ext_spaces, limits.max_ext_spaces)
}

fn check_limit(
    field: &'static str,
    declared: usize,
    limit: usize,
) -> Result<(), SelfExtLocusArtifactError> {
    if declared > limit {
        Err(SelfExtLocusArtifactError::VerificationLimit {
            field,
            declared,
            limit,
        })
    } else {
        Ok(())
    }
}

fn check_indices(
    indices: &[usize],
    representatives: usize,
) -> Result<(), SelfExtLocusArtifactError> {
    let mut previous = None;
    for &index in indices {
        if index >= representatives || previous.is_some_and(|value| index <= value) {
            return Err(SelfExtLocusArtifactError::RepresentativeIndex { index });
        }
        previous = Some(index);
    }
    Ok(())
}

fn verify_locus(
    artifact: &SelfExtLocusArtifact,
    representatives: &[crate::census::CensusRepresentative],
) -> Result<(), SelfExtLocusArtifactError> {
    let mut claimed_position = 0usize;
    for (index, representative) in representatives.iter().enumerate() {
        let claimed = artifact.vanishing_indices.get(claimed_position) == Some(&index);
        let actual = ext_range_vanishes(
            representative.module(),
            artifact.first_degree,
            artifact.last_degree,
        )?;
        if claimed != actual {
            return Err(SelfExtLocusArtifactError::LocusMismatch {
                representative: index,
            });
        }
        if claimed {
            claimed_position += 1;
        }
    }
    Ok(())
}

fn ext_range_vanishes(
    module: &crate::module::Module,
    first_degree: usize,
    last_degree: usize,
) -> Result<bool, SelfExtLocusArtifactError> {
    for degree in first_degree..=last_degree {
        if ExtSpace::new(module, module, degree)?.dim() != 0 {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Parses and independently verifies one untrusted self-Ext locus artifact.
pub fn verify_self_ext_locus_artifact(
    text: &str,
    limits: SelfExtLocusVerifyLimits,
) -> Result<VerifiedSelfExtLocusArtifact, SelfExtLocusArtifactError> {
    SelfExtLocusArtifact::from_json(text, limits.parse)?.verify(limits)
}

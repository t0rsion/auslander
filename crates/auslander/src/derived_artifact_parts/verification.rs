use std::sync::Arc;

use crate::algebra::Algebra;
use crate::complex_target::{ComplexTargetOutcome, present_complex_target};
use crate::control::{ComputationControl, ProgressStage};
use crate::tilting_complex::{
    ApproximationDirection, CertifiedTiltingComplex, TiltingComplexLimits, TiltingComplexResult,
    TiltingMutationOutcome, left_tilting_mutation, regular_tilting_complex, right_tilting_mutation,
};
use crate::verify::verify;

use super::errors::ArtifactError;
use super::model::{ArtifactMutation, ArtifactVerifyLimits, DerivedArtifact};

/// A verified artifact and its rebuilt live values.
#[derive(Clone, Debug)]
pub struct VerifiedDerivedArtifact {
    pub(super) artifact: DerivedArtifact,
    pub(super) source: Arc<Algebra>,
    pub(super) tilting: CertifiedTiltingComplex,
}

impl VerifiedDerivedArtifact {
    accessor_methods! {
        /// The canonical parsed artifact.
        pub artifact() -> &DerivedArtifact = |this| &this.artifact;
        /// The rebuilt source algebra.
        pub source() -> &Arc<Algebra> = |this| &this.source;
        /// The rebuilt certified tilting complex.
        pub tilting() -> &CertifiedTiltingComplex = |this| &this.tilting;
    }
}

/// Why independent verification stopped without accepting the artifact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArtifactVerificationCut {
    /// The caller requested cancellation before the named mutation.
    Cancelled { completed_mutations: usize },
    /// A declared limit exceeds the verifier ceiling.
    DeclaredLimit {
        field: &'static str,
        declared: usize,
        limit: usize,
    },
    /// The verifier work budget stopped before the next mutation.
    WorkLimit { completed: usize, limit: usize },
}

/// A complete verified value or a typed verifier cut.
#[derive(Clone, Debug)]
pub enum ArtifactVerificationOutcome {
    /// Every serialized and mathematical obligation passed.
    Verified(Box<VerifiedDerivedArtifact>),
    /// Cancellation or a verifier ceiling stopped the run.
    Cut(ArtifactVerificationCut),
}

enum MutationReplay {
    Complete(Box<CertifiedTiltingComplex>),
    Cut(ArtifactVerificationCut),
}

fn artifact_cut(
    artifact: &DerivedArtifact,
    limits: ArtifactVerifyLimits,
) -> Result<Option<ArtifactVerificationCut>, ArtifactError> {
    if !artifact.has_valid_fingerprint() {
        return Err(ArtifactError::FingerprintMismatch);
    }
    for (field, declared, limit) in [
        (
            "max_hom_spaces",
            artifact.tilting_limits.max_hom_spaces,
            limits.max_hom_spaces,
        ),
        (
            "max_endo_dimension",
            artifact.target_limits.max_endo_dimension,
            limits.max_endo_dimension,
        ),
        (
            "max_radical_products",
            artifact.target_limits.max_radical_products,
            limits.max_radical_products,
        ),
        (
            "max_paths",
            artifact.target_limits.max_paths,
            limits.max_paths,
        ),
        (
            "max_relation_terms",
            artifact.target_limits.max_relation_terms,
            limits.max_relation_terms,
        ),
        (
            "completion.max_steps",
            artifact.target_limits.completion.max_steps,
            limits.max_completion_steps,
        ),
    ] {
        if declared > limit {
            return Ok(Some(ArtifactVerificationCut::DeclaredLimit {
                field,
                declared,
                limit,
            }));
        }
    }
    Ok(None)
}

fn source_and_regular(
    artifact: &DerivedArtifact,
) -> Result<(Arc<Algebra>, CertifiedTiltingComplex), ArtifactError> {
    let source_text = artifact.source.to_canonical_json();
    let source_verified = verify(&source_text)?;
    let source =
        Algebra::from_verified_with_limits(source_verified, &artifact.target_limits.completion)?;
    let TiltingComplexResult::Tilting(value) =
        regular_tilting_complex(&source, artifact.tilting_limits)?
    else {
        return Err(ArtifactError::Mathematical(
            "regular tilting check was incomplete".into(),
        ));
    };
    Ok((source, *value))
}

fn mutated_tilting(
    tilting: &CertifiedTiltingComplex,
    mutation: &ArtifactMutation,
    limits: TiltingComplexLimits,
    completed: usize,
) -> Result<CertifiedTiltingComplex, ArtifactError> {
    let outcome = match mutation.direction {
        ApproximationDirection::Left => left_tilting_mutation(tilting, mutation.summand, limits)?,
        ApproximationDirection::Right => right_tilting_mutation(tilting, mutation.summand, limits)?,
    };
    let TiltingMutationOutcome::Tilting(next) = outcome else {
        return Err(ArtifactError::Mathematical(format!(
            "mutation {completed} did not produce a tilting complex"
        )));
    };
    Ok(*next)
}

fn replay_mutations(
    mut tilting: CertifiedTiltingComplex,
    artifact: &DerivedArtifact,
    limit: usize,
    control: &ComputationControl,
) -> Result<MutationReplay, ArtifactError> {
    for (completed, mutation) in artifact.mutations.iter().enumerate() {
        if control.is_cancelled() {
            return Ok(MutationReplay::Cut(ArtifactVerificationCut::Cancelled {
                completed_mutations: completed,
            }));
        }
        if completed == limit {
            return Ok(MutationReplay::Cut(ArtifactVerificationCut::WorkLimit {
                completed,
                limit,
            }));
        }
        control.update(ProgressStage::ArtifactVerify, completed, completed + 1);
        tilting = mutated_tilting(&tilting, mutation, artifact.tilting_limits, completed)?;
        control.update(ProgressStage::ArtifactVerify, completed + 1, completed + 1);
    }
    Ok(MutationReplay::Complete(Box::new(tilting)))
}

fn finish_artifact_verification(
    artifact: DerivedArtifact,
    source: Arc<Algebra>,
    tilting: Box<CertifiedTiltingComplex>,
    control: &ComputationControl,
) -> Result<ArtifactVerificationOutcome, ArtifactError> {
    let target_text = artifact.target.to_canonical_json();
    verify(&target_text)?;
    let ComplexTargetOutcome::Presented(target) =
        present_complex_target(&tilting, &artifact.target_limits)?
    else {
        return Err(ArtifactError::Mathematical(
            "stored target limits cut target recovery".to_string(),
        ));
    };
    if target.completion_certificate() != &artifact.target || target.work() != artifact.work {
        return Err(ArtifactError::Mathematical(
            "rebuilt target or exact work differs from the artifact".to_string(),
        ));
    }
    control.update(
        ProgressStage::Complete,
        artifact.mutations.len(),
        artifact.mutations.len(),
    );
    Ok(ArtifactVerificationOutcome::Verified(Box::new(
        VerifiedDerivedArtifact {
            artifact,
            source,
            tilting: *tilting,
        },
    )))
}

fn verify_parsed_artifact(
    artifact: DerivedArtifact,
    limits: ArtifactVerifyLimits,
    control: &ComputationControl,
) -> Result<ArtifactVerificationOutcome, ArtifactError> {
    let (source, tilting) = source_and_regular(&artifact)?;
    match replay_mutations(tilting, &artifact, limits.max_work_units, control)? {
        MutationReplay::Complete(tilting) => {
            finish_artifact_verification(artifact, source, tilting, control)
        }
        MutationReplay::Cut(cut) => Ok(ArtifactVerificationOutcome::Cut(cut)),
    }
}

/// Parses and independently verifies one untrusted artifact string.
pub fn verify_derived_artifact(
    text: &str,
    limits: ArtifactVerifyLimits,
    control: &ComputationControl,
) -> Result<ArtifactVerificationOutcome, ArtifactError> {
    control.update(ProgressStage::ArtifactVerify, 0, 0);
    let artifact = DerivedArtifact::from_json(text, limits.parse)?;
    if let Some(cut) = artifact_cut(&artifact, limits)? {
        return Ok(ArtifactVerificationOutcome::Cut(cut));
    }
    verify_parsed_artifact(artifact, limits, control)
}

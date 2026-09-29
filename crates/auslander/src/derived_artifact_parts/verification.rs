use std::sync::Arc;

use crate::algebra::Algebra;
use crate::complex_target::{ComplexTargetOutcome, present_complex_target};
use crate::control::{ComputationControl, ProgressStage};
use crate::target::TargetLimits;
use crate::tilting_complex::{
    CertifiedSiltingComplex, CertifiedTiltingComplex, OrthogonalityGoal, TiltingComplexLimits,
    TiltingComplexResult, TiltingMutationOutcome, regular_tilting_complex, silting_mutation,
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
    /// A declared limit, or the dimension of a stored algebra, exceeds the
    /// verifier ceiling.
    DeclaredLimit {
        field: &'static str,
        declared: u64,
        limit: u64,
    },
    /// The verifier work budget stopped before the next mutation.
    WorkLimit { completed: usize, limit: usize },
}

/// A complete verified value, or a typed stop before the verifier decided.
#[derive(Clone, Debug)]
pub enum ArtifactVerificationOutcome {
    /// Every serialized and mathematical obligation passed.
    Verified(Box<VerifiedDerivedArtifact>),
    /// Cancellation or a verifier ceiling stopped the run.
    Stopped(ArtifactVerificationCut),
}

enum MutationReplay {
    Complete(Box<CertifiedTiltingComplex>),
    Stopped(ArtifactVerificationCut),
}

fn artifact_cut(
    artifact: &DerivedArtifact,
    limits: ArtifactVerifyLimits,
) -> Result<Option<ArtifactVerificationCut>, ArtifactError> {
    if !artifact.has_valid_fingerprint() {
        return Err(ArtifactError::FingerprintMismatch);
    }
    let declared = declared_limits(artifact.tilting_limits, &artifact.target_limits, &limits);
    // The source is the endomorphism algebra of its regular complex.
    let source = artifact.source.declared_dimension();
    let source = ("source_dimension", source, limits.max_endo_dimension);
    Ok(exceeded(declared.into_iter().chain([source])))
}

/// The first `(field, declared, limit)` entry whose declared value exceeds
/// its limit, as an [`ArtifactVerificationCut::DeclaredLimit`].
pub(crate) fn exceeded(
    entries: impl IntoIterator<Item = (&'static str, u64, u64)>,
) -> Option<ArtifactVerificationCut> {
    let mut entries = entries.into_iter();
    let (field, declared, limit) = entries.find(|&(_, declared, limit)| declared > limit)?;
    Some(ArtifactVerificationCut::DeclaredLimit {
        field,
        declared,
        limit,
    })
}

/// Every declared tilting and target limit with its verifier ceiling in
/// `ceiling`, for [`exceeded`].
pub(crate) fn declared_limits(
    tilting: TiltingComplexLimits,
    target: &TargetLimits,
    ceiling: &ArtifactVerifyLimits,
) -> [(&'static str, u64, u64); 10] {
    let completion = &target.completion;
    [
        (
            "max_hom_spaces",
            tilting.max_hom_spaces,
            ceiling.max_hom_spaces,
        ),
        (
            "max_endo_dimension",
            target.max_endo_dimension,
            ceiling.max_endo_dimension,
        ),
        (
            "max_radical_products",
            target.max_radical_products,
            ceiling.max_radical_products,
        ),
        ("max_paths", target.max_paths, ceiling.max_paths),
        (
            "max_relation_terms",
            target.max_relation_terms,
            ceiling.max_relation_terms,
        ),
        (
            "completion.max_steps",
            completion.max_steps,
            ceiling.max_completion_steps,
        ),
        (
            "completion.max_basis",
            completion.max_basis,
            ceiling.max_completion_basis,
        ),
        (
            "completion.max_word_len",
            completion.max_word_len,
            ceiling.max_completion_word_len,
        ),
        (
            "completion.max_origin_terms",
            completion.max_origin_terms,
            ceiling.max_completion_origin_terms,
        ),
        (
            "completion.max_ambiguities",
            completion.max_ambiguities,
            ceiling.max_completion_ambiguities,
        ),
    ]
}

fn source_and_regular(
    artifact: &DerivedArtifact,
) -> Result<(Arc<Algebra>, CertifiedSiltingComplex), ArtifactError> {
    let source_text = artifact.source.to_canonical_json();
    let source_verified = verify(&source_text)?;
    let source =
        Algebra::from_verified_with_limits(source_verified, &artifact.target_limits.completion)?;
    let regular = regular_complex(&source, artifact.tilting_limits)?;
    Ok((source, regular.into_silting()))
}

fn regular_complex(
    source: &Arc<Algebra>,
    limits: TiltingComplexLimits,
) -> Result<CertifiedTiltingComplex, ArtifactError> {
    let TiltingComplexResult::Tilting(value) = regular_tilting_complex(source, limits)? else {
        return Err(ArtifactError::Mathematical(
            "regular tilting check was incomplete".into(),
        ));
    };
    Ok(*value)
}

/// Rebuilds the tilting complex that `recipe` reaches from the regular
/// complex of `source`, with no budget beyond `limits`.
///
/// Each step is an irreducible silting mutation, so a step can pass through a
/// silting complex that is not tilting, unless `goal` is `Tilting`. The last
/// complex must be tilting.
pub(crate) fn replay_recipe(
    source: &Arc<Algebra>,
    recipe: &[ArtifactMutation],
    limits: TiltingComplexLimits,
    goal: OrthogonalityGoal,
) -> Result<CertifiedTiltingComplex, ArtifactError> {
    let regular = regular_complex(source, limits)?.into_silting();
    let end = recipe
        .iter()
        .enumerate()
        .try_fold(regular, |complex, (completed, mutation)| {
            let next = mutated(&complex, mutation, limits, completed)?;
            if goal == OrthogonalityGoal::Tilting && next.negative_class().is_some() {
                return Err(ArtifactError::Mathematical(format!(
                    "mutation {completed} leaves a walk without through_silting"
                )));
            }
            Ok(next)
        })?;
    tilting_end(&end)
}

fn mutated(
    complex: &CertifiedSiltingComplex,
    mutation: &ArtifactMutation,
    limits: TiltingComplexLimits,
    completed: usize,
) -> Result<CertifiedSiltingComplex, ArtifactError> {
    match silting_mutation(complex, mutation.summand, mutation.direction, limits)? {
        TiltingMutationOutcome::Tilting(next) => Ok(next.into_silting()),
        TiltingMutationOutcome::Silting(next) => Ok(*next),
        _ => Err(ArtifactError::Mathematical(format!(
            "mutation {completed} did not produce a silting complex"
        ))),
    }
}

fn tilting_end(end: &CertifiedSiltingComplex) -> Result<CertifiedTiltingComplex, ArtifactError> {
    end.to_tilting().ok_or_else(|| {
        ArtifactError::Mathematical("the recipe ends at a complex that is not tilting".into())
    })
}

fn replay_mutations(
    mut complex: CertifiedSiltingComplex,
    artifact: &DerivedArtifact,
    limit: usize,
    control: &ComputationControl,
) -> Result<MutationReplay, ArtifactError> {
    for (completed, mutation) in artifact.mutations.iter().enumerate() {
        if control.is_cancelled() {
            return Ok(MutationReplay::Stopped(
                ArtifactVerificationCut::Cancelled {
                    completed_mutations: completed,
                },
            ));
        }
        if completed == limit {
            return Ok(MutationReplay::Stopped(
                ArtifactVerificationCut::WorkLimit { completed, limit },
            ));
        }
        control.update(ProgressStage::ArtifactVerify, completed, completed + 1);
        complex = mutated(&complex, mutation, artifact.tilting_limits, completed)?;
        control.update(ProgressStage::ArtifactVerify, completed + 1, completed + 1);
    }
    Ok(MutationReplay::Complete(Box::new(tilting_end(&complex)?)))
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
        MutationReplay::Stopped(cut) => Ok(ArtifactVerificationOutcome::Stopped(cut)),
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
        return Ok(ArtifactVerificationOutcome::Stopped(cut));
    }
    verify_parsed_artifact(artifact, limits, control)
}

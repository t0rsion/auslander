//! Acceptance tests for portable derived-equivalence artifacts.

mod common;

use auslander::algebra::linear_an;
use auslander::control::ComputationControl;
use auslander::derived_artifact::{
    ArtifactError, ArtifactParseLimits, ArtifactVerificationCut, ArtifactVerificationOutcome,
    ArtifactVerifyLimits, DerivedArtifact, verify_derived_artifact,
};
use auslander::equivalence_edge::{DerivedEquivalenceEdge, DerivedEquivalenceEdgeOutcome};
use auslander::field::PrimeField;
use auslander::target::TargetLimits;
use auslander::tilting_complex::{
    ApproximationDirection, TiltingComplexLimits, TiltingMutationOutcome, left_tilting_mutation,
    right_tilting_mutation,
};

fn artifact(field: u64) -> DerivedArtifact {
    artifact_with(field, ApproximationDirection::Left)
}

fn artifact_with(field: u64, direction: ApproximationDirection) -> DerivedArtifact {
    let algebra = linear_an(2, PrimeField::new(field).unwrap());
    let regular = common::certified_regular(&algebra);
    let mutation = (0..2)
        .find_map(|summand| {
            let outcome = match direction {
                ApproximationDirection::Left => {
                    left_tilting_mutation(&regular, summand, TiltingComplexLimits::default())
                }
                ApproximationDirection::Right => {
                    right_tilting_mutation(&regular, summand, TiltingComplexLimits::default())
                }
            }
            .unwrap();
            match outcome {
                TiltingMutationOutcome::Tilting(value)
                    if value
                        .candidate()
                        .summands()
                        .iter()
                        .any(|part| part.complex().len() > 1) =>
                {
                    Some(*value)
                }
                _ => None,
            }
        })
        .unwrap();
    let edge = match DerivedEquivalenceEdge::recover(mutation, &TargetLimits::default()).unwrap() {
        DerivedEquivalenceEdgeOutcome::Certified(value) => value,
        DerivedEquivalenceEdgeOutcome::Cut(_) => panic!("the A2 target was cut"),
    };
    DerivedArtifact::from_edge(&edge).unwrap()
}

#[test]
fn left_and_right_recipe_families_verify_over_f2_and_f5() {
    for field in [2, 5] {
        for direction in [ApproximationDirection::Left, ApproximationDirection::Right] {
            let artifact = artifact_with(field, direction);
            assert_eq!(artifact.mutations()[0].direction(), direction);
            assert!(matches!(
                verify_derived_artifact(
                    &artifact.to_canonical_json(),
                    ArtifactVerifyLimits::default(),
                    &ComputationControl::new(),
                ),
                Ok(ArtifactVerificationOutcome::Verified(_))
            ));
        }
    }
}

#[test]
fn multi_degree_artifacts_round_trip_and_verify_over_f2_and_f5() {
    for field in [2, 5] {
        let artifact = artifact(field);
        let text = artifact.to_canonical_json();
        let parsed = DerivedArtifact::from_json(&text, ArtifactParseLimits::default()).unwrap();
        assert_eq!(parsed, artifact);
        assert_eq!(parsed.to_canonical_json(), text);
        assert!(parsed.has_valid_fingerprint());
        let control = ComputationControl::new();
        let outcome =
            verify_derived_artifact(&text, ArtifactVerifyLimits::default(), &control).unwrap();
        let ArtifactVerificationOutcome::Verified(verified) = outcome else {
            panic!("the artifact was cut")
        };
        assert_eq!(verified.artifact(), &artifact);
        assert!(verified.tilting().verify());
        assert_eq!(control.progress().completed_work(), 1);
        assert_eq!(control.progress().reserved_work(), 1);
    }
}

#[test]
fn fingerprint_schema_and_input_limits_reject_tampering() {
    let text = artifact(5).to_canonical_json();
    let fingerprint = text
        .rfind(|character: char| character.is_ascii_hexdigit())
        .unwrap();
    let mut changed = text.clone();
    changed.replace_range(fingerprint..=fingerprint, "0");
    if changed == text {
        changed.replace_range(fingerprint..=fingerprint, "1");
    }
    assert!(matches!(
        verify_derived_artifact(
            &changed,
            ArtifactVerifyLimits::default(),
            &ComputationControl::new(),
        ),
        Err(ArtifactError::FingerprintMismatch)
    ));
    let wrong_key = text.replacen("\"source\"", "\"unknown\"", 1);
    assert!(matches!(
        DerivedArtifact::from_json(&wrong_key, ArtifactParseLimits::default()),
        Err(ArtifactError::Syntax { .. })
    ));
    assert!(matches!(
        DerivedArtifact::from_json(
            &text,
            ArtifactParseLimits {
                max_input_bytes: text.len() - 1,
                ..ArtifactParseLimits::default()
            },
        ),
        Err(ArtifactError::ParseLimit { .. })
    ));
}

#[test]
fn cancellation_returns_a_typed_unverified_cut() {
    let text = artifact(5).to_canonical_json();
    let control = ComputationControl::new();
    control.cancel();
    let outcome =
        verify_derived_artifact(&text, ArtifactVerifyLimits::default(), &control).unwrap();
    assert!(matches!(
        outcome,
        ArtifactVerificationOutcome::Cut(ArtifactVerificationCut::Cancelled {
            completed_mutations: 0
        })
    ));
}

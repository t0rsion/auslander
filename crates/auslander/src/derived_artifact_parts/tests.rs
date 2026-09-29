use super::serialization::fingerprint;
use super::*;
use crate::algebra::linear_an;
use crate::completion::CompletionLimits;
use crate::control::ComputationControl;
use crate::equivalence_edge::{DerivedEquivalenceEdge, DerivedEquivalenceEdgeOutcome};
use crate::field::PrimeField;
use crate::target::TargetLimits;
use crate::tilting_complex::{
    ApproximationDirection, TiltingComplexLimits, TiltingComplexResult, TiltingMutationOutcome,
    left_tilting_mutation, regular_tilting_complex, silting_mutation,
};

fn artifact() -> DerivedArtifact {
    let algebra = linear_an(2, PrimeField::new(5).unwrap());
    let TiltingComplexResult::Tilting(regular) =
        regular_tilting_complex(&algebra, TiltingComplexLimits::default()).unwrap()
    else {
        panic!("the regular generator certifies")
    };
    let mutation = (0..2)
        .find_map(|summand| {
            let outcome =
                left_tilting_mutation(&regular, summand, TiltingComplexLimits::default()).unwrap();
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
        .expect("A2 has a multi-degree left mutation");
    let edge = match DerivedEquivalenceEdge::recover(mutation, &TargetLimits::default()).unwrap() {
        DerivedEquivalenceEdgeOutcome::Certified(value) => value,
        DerivedEquivalenceEdgeOutcome::Cut(_) => panic!("the A2 target completes"),
    };
    DerivedArtifact::from_edge(&edge).unwrap()
}

fn resign(artifact: &mut DerivedArtifact) {
    artifact.fingerprint = fingerprint(&artifact.canonical_without_fingerprint());
}

fn rejects(artifact: &DerivedArtifact) -> bool {
    verify_derived_artifact(
        &artifact.to_canonical_json(),
        ArtifactVerifyLimits::default(),
        &ComputationControl::new(),
    )
    .is_err()
}

/// In `A_2`, left mutation at `P_0` gives a silting complex with a nonzero
/// class in shift `-1`. Left mutation at the other summand returns to a
/// tilting complex. The artifact of that complex replays both steps, and the
/// recipe without its last step ends at a complex that is not tilting.
#[test]
fn a_recipe_through_a_silting_complex_verifies() {
    let limits = TiltingComplexLimits::default();
    let left = ApproximationDirection::Left;
    let algebra = linear_an(2, PrimeField::new(5).unwrap());
    let TiltingComplexResult::Tilting(regular) = regular_tilting_complex(&algebra, limits).unwrap()
    else {
        panic!("the regular generator certifies")
    };
    assert!(matches!(
        left_tilting_mutation(&regular, 0, limits).unwrap(),
        TiltingMutationOutcome::SiltingOnly(_)
    ));
    let TiltingMutationOutcome::Silting(middle) =
        silting_mutation(&regular, 0, left, limits).unwrap()
    else {
        panic!("the mutation at P_0 is silting")
    };
    assert!(middle.verify() && middle.to_tilting().is_none());
    assert_eq!(
        middle.negative_class().map(|class| class.degree()),
        Some(-1)
    );
    let TiltingMutationOutcome::Tilting(end) = silting_mutation(&middle, 1, left, limits).unwrap()
    else {
        panic!("the second mutation is tilting")
    };
    assert!(end.verify());
    let DerivedEquivalenceEdgeOutcome::Certified(edge) =
        DerivedEquivalenceEdge::recover(*end, &TargetLimits::default()).unwrap()
    else {
        panic!("the A2 target completes")
    };
    let artifact = DerivedArtifact::from_edge(&edge).unwrap();
    let steps = [
        ArtifactMutation::new(left, 0),
        ArtifactMutation::new(left, 1),
    ];
    assert_eq!(artifact.mutations, steps);
    assert!(matches!(
        verify_derived_artifact(
            &artifact.to_canonical_json(),
            ArtifactVerifyLimits::default(),
            &ComputationControl::new(),
        ),
        Ok(ArtifactVerificationOutcome::Verified(_))
    ));
    let mut short = artifact;
    short.mutations.pop();
    resign(&mut short);
    assert!(rejects(&short));
}

#[test]
fn verifier_rejects_resigned_tampering_in_each_claim_family() {
    let original = artifact();

    let mut source = original.clone();
    source.source.field = 7;
    resign(&mut source);
    assert!(rejects(&source));

    let mut mutation = original.clone();
    mutation.mutations[0].summand = usize::MAX;
    resign(&mut mutation);
    assert!(rejects(&mutation));

    let mut target = original.clone();
    target.target.field = 7;
    resign(&mut target);
    assert!(rejects(&target));

    let mut limits = original.clone();
    limits.tilting_limits.max_hom_spaces = 0;
    resign(&mut limits);
    assert!(rejects(&limits));

    let mut work = original;
    work.work.endo_dimension += 1;
    resign(&mut work);
    assert!(rejects(&work));
}

/// The source dimension is checked before the source algebra is built. The
/// source of `A_2` has dimension 3.
#[test]
fn a_source_above_the_endomorphism_ceiling_stops_replay() {
    let mut artifact = artifact();
    artifact.target_limits.max_endo_dimension = 2;
    resign(&mut artifact);
    let limits = ArtifactVerifyLimits {
        max_endo_dimension: 2,
        ..Default::default()
    };
    let outcome = verify_derived_artifact(
        &artifact.to_canonical_json(),
        limits,
        &ComputationControl::new(),
    );
    assert!(matches!(
        outcome,
        Ok(ArtifactVerificationOutcome::Stopped(
            ArtifactVerificationCut::DeclaredLimit {
                field: "source_dimension",
                declared: 3,
                limit: 2,
            }
        ))
    ));
}

/// Each completion limit bounds work that `max_steps` does not, so each one
/// declared above its ceiling stops replay before any mutation.
#[test]
fn every_declared_completion_limit_has_a_ceiling() {
    type Raise = fn(&mut CompletionLimits);
    let raises: [(&str, Raise); 5] = [
        ("completion.max_steps", |c| c.max_steps = u64::MAX),
        ("completion.max_basis", |c| c.max_basis = u64::MAX),
        ("completion.max_word_len", |c| c.max_word_len = u64::MAX),
        ("completion.max_origin_terms", |c| {
            c.max_origin_terms = u64::MAX
        }),
        ("completion.max_ambiguities", |c| {
            c.max_ambiguities = u64::MAX
        }),
    ];
    for (name, raise) in raises {
        let mut artifact = artifact();
        raise(&mut artifact.target_limits.completion);
        resign(&mut artifact);
        let outcome = verify_derived_artifact(
            &artifact.to_canonical_json(),
            ArtifactVerifyLimits::default(),
            &ComputationControl::new(),
        );
        assert!(
            matches!(
                &outcome,
                Ok(ArtifactVerificationOutcome::Stopped(ArtifactVerificationCut::DeclaredLimit {
                    field,
                    declared: u64::MAX,
                    ..
                })) if *field == name
            ),
            "{name}: {outcome:?}"
        );
    }
}

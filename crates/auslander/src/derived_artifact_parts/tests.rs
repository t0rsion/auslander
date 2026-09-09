use super::serialization::fingerprint;
use super::*;
use crate::algebra::linear_an;
use crate::control::ComputationControl;
use crate::equivalence_edge::{DerivedEquivalenceEdge, DerivedEquivalenceEdgeOutcome};
use crate::field::PrimeField;
use crate::target::TargetLimits;
use crate::tilting_complex::{
    TiltingComplexLimits, TiltingComplexResult, TiltingMutationOutcome, left_tilting_mutation,
    regular_tilting_complex,
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

use super::*;
use crate::algebra::linear_an;
use crate::batch_stream::{
    HomologicalBatchStreamLimits, HomologicalStreamBudget, HomologicalStreamConfig,
    HomologicalStreamStep, homological_stream_from_census,
};
use crate::census::{Census, CensusLimits, CensusPortable, CensusVerifyLimits};
use crate::field::PrimeField;

fn verified_checkpoint(max_degree: usize) -> crate::batch_stream::VerifiedHomologicalStream {
    let algebra = linear_an(2, PrimeField::new(5).unwrap());
    let census = Census::new(&algebra, vec![1, 1]).unwrap();
    let outcome = census.run_with(
        CensusLimits {
            max_candidates: 100,
            max_representatives: 100,
            max_assignments: 100,
            max_isomorphism_checks: 100,
            max_work_units: 1_000,
            ..CensusLimits::default()
        },
        None,
    );
    let verified_census = CensusPortable::from_outcome(&outcome)
        .unwrap()
        .verify(CensusVerifyLimits::default())
        .unwrap();
    let mut stream = homological_stream_from_census(
        &verified_census,
        max_degree,
        HomologicalStreamConfig {
            chunk_limits: HomologicalBatchStreamLimits {
                max_live_sources: 1,
                max_pairs: 100,
                max_ext_cells: 500,
            },
            budget: HomologicalStreamBudget::default(),
        },
        None,
    )
    .unwrap();
    loop {
        match stream.next_chunk() {
            HomologicalStreamStep::Chunk(chunk) => assert!(chunk.verify()),
            HomologicalStreamStep::Complete { .. } => {
                return stream
                    .checkpoint()
                    .verify(crate::batch_stream::HomologicalStreamVerifyLimits::default())
                    .unwrap();
            }
            HomologicalStreamStep::Cut { reason, .. } => panic!("unexpected cut: {reason}"),
            HomologicalStreamStep::Failed { error, .. } => {
                panic!("unexpected failure: {error}")
            }
        }
    }
}

#[test]
fn complete_fixed_dimension_locus_round_trips_and_rechecks() {
    let checkpoint = verified_checkpoint(2);
    let artifact = SelfExtLocusArtifact::from_verified_checkpoint(&checkpoint, 1, 2).unwrap();
    assert_eq!(artifact.vanishing_indices().len(), 1);
    let text = artifact.to_canonical_json();
    let parsed =
        SelfExtLocusArtifact::from_json(&text, SelfExtLocusParseLimits::default()).unwrap();
    let verified = parsed.verify(SelfExtLocusVerifyLimits::default()).unwrap();
    assert_eq!(verified.artifact().to_canonical_json(), text);
    assert_eq!(
        verified.checkpoint().portable().fingerprint(),
        artifact.checkpoint().fingerprint()
    );
}

#[test]
fn independent_ext_recheck_rejects_a_resigned_wrong_locus() {
    let checkpoint = verified_checkpoint(2);
    let mut artifact = SelfExtLocusArtifact::from_verified_checkpoint(&checkpoint, 1, 2).unwrap();
    artifact.vanishing_indices.clear();
    artifact.fingerprint = super::model::fingerprint(&artifact.canonical_without_fingerprint());
    assert!(matches!(
        artifact.verify(SelfExtLocusVerifyLimits::default()),
        Err(SelfExtLocusArtifactError::LocusMismatch { .. })
    ));
}

#[test]
fn degree_and_parser_limits_are_typed() {
    let checkpoint = verified_checkpoint(2);
    assert!(matches!(
        SelfExtLocusArtifact::from_verified_checkpoint(&checkpoint, 0, 2),
        Err(SelfExtLocusArtifactError::DegreeRange { .. })
    ));
    assert!(matches!(
        SelfExtLocusArtifact::from_verified_checkpoint(&checkpoint, 1, 3),
        Err(SelfExtLocusArtifactError::DegreeOutsideCheckpoint { .. })
    ));
    let artifact = SelfExtLocusArtifact::from_verified_checkpoint(&checkpoint, 1, 2).unwrap();
    let text = artifact.to_canonical_json();
    let limits = SelfExtLocusParseLimits {
        max_input_bytes: text.len() - 1,
        ..SelfExtLocusParseLimits::default()
    };
    assert!(matches!(
        SelfExtLocusArtifact::from_json(&text, limits),
        Err(SelfExtLocusArtifactError::ParseLimit { path, .. }) if path == "$"
    ));
}

#[test]
fn fingerprint_and_claim_shape_reject_tampering() {
    let checkpoint = verified_checkpoint(2);
    let artifact = SelfExtLocusArtifact::from_verified_checkpoint(&checkpoint, 1, 2).unwrap();
    let text = artifact.to_canonical_json();
    let changed = text.replacen("\"first_degree\":1", "\"first_degree\":2", 1);
    assert!(matches!(
        SelfExtLocusArtifact::from_json(&changed, SelfExtLocusParseLimits::default()),
        Err(SelfExtLocusArtifactError::FingerprintMismatch)
    ));
    let unknown = text.replacen("\"kind\":", "\"unknown\":0,\"kind\":", 1);
    assert!(matches!(
        SelfExtLocusArtifact::from_json(&unknown, SelfExtLocusParseLimits::default()),
        Err(SelfExtLocusArtifactError::Syntax { .. })
    ));
}

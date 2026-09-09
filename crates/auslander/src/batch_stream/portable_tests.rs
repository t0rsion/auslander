use super::*;
use crate::algebra::linear_an;
use crate::census::{Census, CensusLimits, CensusPortable, CensusVerifyLimits, VerifiedCensus};
use crate::control::ComputationControl;
use crate::field::PrimeField;

fn verified_census() -> VerifiedCensus {
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
    let portable = CensusPortable::from_outcome(&outcome).unwrap();
    portable.verify(CensusVerifyLimits::default()).unwrap()
}

fn config(chunk_size: usize, budget: HomologicalStreamBudget) -> HomologicalStreamConfig {
    HomologicalStreamConfig {
        chunk_limits: HomologicalBatchStreamLimits {
            max_live_sources: chunk_size,
            max_pairs: 100,
            max_ext_cells: 500,
        },
        budget,
    }
}

fn finish(stream: &mut HomologicalSelfPairCheckpointStream) -> HomologicalStreamPortable {
    loop {
        match stream.next_chunk() {
            HomologicalStreamStep::Chunk(chunk) => assert!(chunk.verify()),
            HomologicalStreamStep::Complete { .. } => return stream.checkpoint(),
            HomologicalStreamStep::Cut { reason, .. } => panic!("unexpected cut: {reason}"),
            HomologicalStreamStep::Failed { error, .. } => panic!("unexpected failure: {error}"),
        }
    }
}

#[test]
fn checkpoint_round_trip_replays_rows_and_work() {
    let census = verified_census();
    let mut stream = homological_stream_from_census(
        &census,
        2,
        config(1, HomologicalStreamBudget::default()),
        None,
    )
    .unwrap();
    let initial = stream.checkpoint();
    let parsed = HomologicalStreamPortable::from_json(
        &initial.to_canonical_json(),
        HomologicalStreamParseLimits::default(),
    )
    .unwrap();
    parsed
        .verify(HomologicalStreamVerifyLimits::default())
        .unwrap();
    let complete = finish(&mut stream);
    assert!(matches!(
        complete.status(),
        HomologicalStreamPortableStatus::Complete
    ));
    let parsed = HomologicalStreamPortable::from_json(
        &complete.to_canonical_json(),
        HomologicalStreamParseLimits::default(),
    )
    .unwrap();
    let verified = parsed
        .verify(HomologicalStreamVerifyLimits::default())
        .unwrap();
    assert_eq!(verified.portable().rows(), complete.rows());
    assert_eq!(verified.portable().work(), complete.work());
}

#[test]
fn verified_cut_resumes_from_the_first_unfinished_representative() {
    let census = verified_census();
    let mut first = homological_stream_from_census(
        &census,
        2,
        config(
            1,
            HomologicalStreamBudget {
                max_sources: 1,
                max_work_units: usize::MAX,
            },
        ),
        None,
    )
    .unwrap();
    assert!(matches!(
        first.next_chunk(),
        HomologicalStreamStep::Chunk(_)
    ));
    let cut = first.checkpoint();
    assert!(matches!(
        cut.status(),
        HomologicalStreamPortableStatus::Cut(HomologicalStreamCutReason::SourceLimit { limit: 1 })
    ));
    let verified = cut
        .verify(HomologicalStreamVerifyLimits::default())
        .unwrap();
    let mut resumed = verified
        .resume(HomologicalStreamBudget::default(), None)
        .unwrap();
    assert_eq!(resumed.next_source(), 1);
    let resumed = finish(&mut resumed);
    assert!(matches!(
        resumed.status(),
        HomologicalStreamPortableStatus::Complete
    ));
    assert_eq!(resumed.rows().len(), resumed.next_source());
}

#[test]
fn resumed_checkpoint_replays_partial_source_budget_chunk() {
    let census = verified_census();
    let mut first = homological_stream_from_census(
        &census,
        2,
        config(
            2,
            HomologicalStreamBudget {
                max_sources: 1,
                max_work_units: usize::MAX,
            },
        ),
        None,
    )
    .unwrap();
    assert!(matches!(
        first.next_chunk(),
        HomologicalStreamStep::Chunk(_)
    ));
    let verified = first
        .checkpoint()
        .verify(HomologicalStreamVerifyLimits::default())
        .unwrap();
    let mut resumed = verified
        .resume(HomologicalStreamBudget::default(), None)
        .unwrap();
    let complete = finish(&mut resumed);
    complete
        .verify(HomologicalStreamVerifyLimits::default())
        .unwrap();
    assert_eq!(complete.chunk_sizes().len(), complete.work().chunks);
}

#[test]
fn resume_rejects_ceilings_below_committed_work() {
    let census = verified_census();
    let mut first = homological_stream_from_census(
        &census,
        2,
        config(
            1,
            HomologicalStreamBudget {
                max_sources: 1,
                max_work_units: usize::MAX,
            },
        ),
        None,
    )
    .unwrap();
    assert!(matches!(
        first.next_chunk(),
        HomologicalStreamStep::Chunk(_)
    ));
    let verified = first
        .checkpoint()
        .verify(HomologicalStreamVerifyLimits::default())
        .unwrap();
    assert!(matches!(
        verified.resume(
            HomologicalStreamBudget {
                max_sources: 0,
                max_work_units: usize::MAX,
            },
            None,
        ),
        Err(HomologicalStreamPortableError::ResumeBudget {
            field: "max_sources",
            committed: 1,
            limit: 0,
        })
    ));

    let committed_work = super::portable::primitive_work_units(verified.portable().work()).unwrap();
    assert!(committed_work > 0);
    assert!(matches!(
        verified.resume(
            HomologicalStreamBudget {
                max_sources: usize::MAX,
                max_work_units: committed_work - 1,
            },
            None,
        ),
        Err(HomologicalStreamPortableError::ResumeBudget {
            field: "max_work_units",
            committed,
            limit,
        }) if committed == committed_work && limit == committed_work - 1
    ));
}

#[test]
fn work_ceiling_cuts_without_committing_an_incomplete_chunk() {
    let census = verified_census();
    let mut stream = homological_stream_from_census(
        &census,
        2,
        config(
            1,
            HomologicalStreamBudget {
                max_sources: usize::MAX,
                max_work_units: 1,
            },
        ),
        None,
    )
    .unwrap();
    let HomologicalStreamStep::Cut {
        next_source,
        reason: HomologicalStreamCutReason::WorkLimit { limit: 1 },
        work,
    } = stream.next_chunk()
    else {
        panic!("the first chunk exceeds the work ceiling");
    };
    assert_eq!(next_source, 0);
    assert_eq!(work, HomologicalBatchStreamWork::default());
    let checkpoint = stream.checkpoint();
    checkpoint
        .verify(HomologicalStreamVerifyLimits::default())
        .unwrap();
}

#[test]
fn cancellation_is_observed_between_chunks() {
    let census = verified_census();
    let control = ComputationControl::new();
    let mut stream = homological_stream_from_census(
        &census,
        2,
        config(1, HomologicalStreamBudget::default()),
        Some(&control),
    )
    .unwrap();
    assert!(matches!(
        stream.next_chunk(),
        HomologicalStreamStep::Chunk(_)
    ));
    control.cancel();
    let HomologicalStreamStep::Cut {
        reason: HomologicalStreamCutReason::Cancelled,
        next_source,
        ..
    } = stream.next_chunk()
    else {
        panic!("cancellation must stop at the next boundary");
    };
    assert_eq!(next_source, 1);
    stream
        .checkpoint()
        .verify(HomologicalStreamVerifyLimits::default())
        .unwrap();
}

#[test]
fn rows_do_not_depend_on_chunk_size() {
    let census = verified_census();
    let mut singleton = homological_stream_from_census(
        &census,
        2,
        config(1, HomologicalStreamBudget::default()),
        None,
    )
    .unwrap();
    let mut grouped = homological_stream_from_census(
        &census,
        2,
        config(8, HomologicalStreamBudget::default()),
        None,
    )
    .unwrap();
    let singleton = finish(&mut singleton);
    let grouped = finish(&mut grouped);
    assert_eq!(singleton.rows(), grouped.rows());
    assert_eq!(singleton.work().resolutions, grouped.work().resolutions);
    assert_ne!(singleton.work().chunks, grouped.work().chunks);
}

#[test]
fn fingerprints_and_unknown_keys_are_rejected() {
    let census = verified_census();
    let stream = homological_stream_from_census(
        &census,
        1,
        config(1, HomologicalStreamBudget::default()),
        None,
    )
    .unwrap();
    let text = stream.checkpoint().to_canonical_json();
    let corrupted = text.replacen("\"max_degree\":1", "\"max_degree\":2", 1);
    assert!(matches!(
        HomologicalStreamPortable::from_json(&corrupted, HomologicalStreamParseLimits::default()),
        Err(HomologicalStreamPortableError::FingerprintMismatch)
    ));
    let unknown = text.replacen("\"census\":", "\"unknown\":0,\"census\":", 1);
    assert!(matches!(
        HomologicalStreamPortable::from_json(&unknown, HomologicalStreamParseLimits::default()),
        Err(HomologicalStreamPortableError::Syntax { .. })
    ));
    let old_kind = text.replacen(
        "homological-self-pair-stream-v2",
        "homological-self-pair-stream-v1",
        1,
    );
    assert!(matches!(
        HomologicalStreamPortable::from_json(
            &old_kind,
            HomologicalStreamParseLimits::default()
        ),
        Err(HomologicalStreamPortableError::Kind { found })
            if found == "homological-self-pair-stream-v1"
    ));
}

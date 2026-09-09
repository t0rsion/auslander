use auslander::algebra::{commutative_square, linear_an};
use auslander::batch_stream::{
    HomologicalBatchStreamLimits, HomologicalStreamBudget, HomologicalStreamConfig,
    HomologicalStreamCutReason, HomologicalStreamParseLimits, HomologicalStreamPortable,
    HomologicalStreamPortableError, HomologicalStreamPortableStatus, HomologicalStreamStep,
    HomologicalStreamVerifyLimits, homological_stream_from_census,
};
use auslander::census::{
    Census, CensusLimits, CensusPortable, CensusRetention, CensusVerifyLimits, VerifiedCensus,
};
use auslander::field::PrimeField;
use auslander::theorem_artifact::{
    SelfExtLocusArtifactError, SelfExtLocusVerifyLimits, verify_self_ext_locus_artifact,
};

const FLAGSHIP_ARTIFACT: &str =
    include_str!("../artifacts/research/commutative-square-f2-d2112-self-ext-1-3.json");

fn verified_flagship_census() -> VerifiedCensus {
    let algebra = commutative_square(PrimeField::new(2).unwrap());
    let census = Census::new(&algebra, vec![2, 1, 1, 2]).unwrap();
    let outcome = census.run_with(
        CensusLimits {
            retention: CensusRetention::RepresentativesOnly,
            max_candidates: 256,
            max_representatives: 100,
            max_assignments: 0,
            max_isomorphism_checks: 10_000,
            max_work_units: 10_000,
        },
        None,
    );
    CensusPortable::from_outcome(&outcome)
        .unwrap()
        .verify(CensusVerifyLimits::default())
        .unwrap()
}

fn verified_boundary_census() -> VerifiedCensus {
    let field = PrimeField::new(5).unwrap();
    let algebra = linear_an(2, field);
    let census = Census::new(&algebra, vec![1, 1]).unwrap();
    let outcome = census.run_with(
        CensusLimits {
            retention: CensusRetention::RepresentativesOnly,
            max_candidates: 100,
            max_representatives: 100,
            max_assignments: 0,
            max_isomorphism_checks: 100,
            max_work_units: 1_000,
        },
        None,
    );
    CensusPortable::from_outcome(&outcome)
        .unwrap()
        .verify(CensusVerifyLimits::default())
        .unwrap()
}

fn flagship_config(budget: HomologicalStreamBudget) -> HomologicalStreamConfig {
    HomologicalStreamConfig {
        chunk_limits: HomologicalBatchStreamLimits {
            max_live_sources: 2,
            max_pairs: 100,
            max_ext_cells: 1_000,
        },
        budget,
    }
}

fn finish_stream(
    stream: &mut auslander::batch_stream::HomologicalSelfPairCheckpointStream,
) -> HomologicalStreamPortable {
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
fn flagship_cut_checkpoint_resumes_to_the_direct_checkpoint() {
    let census = verified_flagship_census();
    let full_budget = HomologicalStreamBudget {
        max_sources: 100,
        max_work_units: 100_000,
    };
    let mut direct =
        homological_stream_from_census(&census, 3, flagship_config(full_budget), None).unwrap();
    let direct_checkpoint = finish_stream(&mut direct);

    let cut_budget = HomologicalStreamBudget {
        max_sources: 4,
        ..full_budget
    };
    let mut cut_stream =
        homological_stream_from_census(&census, 3, flagship_config(cut_budget), None).unwrap();
    for _ in 0..2 {
        let HomologicalStreamStep::Chunk(chunk) = cut_stream.next_chunk() else {
            panic!("the first two chunks should complete")
        };
        assert!(chunk.verify());
    }
    let HomologicalStreamStep::Cut {
        next_source,
        reason: HomologicalStreamCutReason::SourceLimit { limit },
        work,
    } = cut_stream.next_chunk()
    else {
        panic!("the source budget should cut at a chunk boundary")
    };
    assert_eq!(next_source, 4);
    assert_eq!(limit, 4);
    assert_eq!(work.sources, 4);

    let cut_checkpoint = cut_stream.checkpoint();
    assert!(matches!(
        cut_checkpoint.status(),
        HomologicalStreamPortableStatus::Cut(HomologicalStreamCutReason::SourceLimit { limit: 4 })
    ));
    let verified_cut = cut_checkpoint
        .verify(HomologicalStreamVerifyLimits::default())
        .unwrap();
    assert_eq!(verified_cut.portable().next_source(), 4);

    let mut resumed = verified_cut.resume(full_budget, None).unwrap();
    let resumed_checkpoint = finish_stream(&mut resumed);
    assert_eq!(
        resumed_checkpoint.to_canonical_json(),
        direct_checkpoint.to_canonical_json()
    );
}

#[test]
fn flagship_artifact_rejects_a_resigned_wrong_locus() {
    let changed = FLAGSHIP_ARTIFACT.replacen(
        "\"vanishing_indices\":[5,10]",
        "\"vanishing_indices\":[5]",
        1,
    );
    let resigned = resign_fingerprint(&changed);
    assert!(matches!(
        verify_self_ext_locus_artifact(&resigned, SelfExtLocusVerifyLimits::default()),
        Err(SelfExtLocusArtifactError::LocusMismatch { representative: 10 })
    ));
}

#[test]
fn flagship_artifact_rejects_an_unsigned_domain_mutation() {
    let changed = FLAGSHIP_ARTIFACT.replacen(
        "\\\"dimensions\\\":[2,1,1,2]",
        "\\\"dimensions\\\":[2,1,2,2]",
        1,
    );
    assert_ne!(changed, FLAGSHIP_ARTIFACT);
    let error = verify_self_ext_locus_artifact(&changed, SelfExtLocusVerifyLimits::default())
        .expect_err("the unsigned domain mutation must fail");
    assert!(matches!(
        error,
        SelfExtLocusArtifactError::Checkpoint(
            auslander::batch_stream::HomologicalStreamPortableError::FingerprintMismatch
        )
    ));
}

#[test]
fn resigned_work_limit_rejects_committed_work_above_limit() {
    let census = verified_boundary_census();
    let mut stream = homological_stream_from_census(
        &census,
        3,
        HomologicalStreamConfig {
            chunk_limits: HomologicalBatchStreamLimits {
                max_live_sources: 1,
                max_pairs: 100,
                max_ext_cells: 1_000,
            },
            budget: HomologicalStreamBudget {
                max_sources: 100,
                max_work_units: 5,
            },
        },
        None,
    )
    .unwrap();
    assert!(matches!(
        stream.next_chunk(),
        HomologicalStreamStep::Chunk(_)
    ));
    let checkpoint = stream.checkpoint();
    let changed = checkpoint
        .to_canonical_json()
        .replacen("\"max_work_units\":5", "\"max_work_units\":4", 1)
        .replacen("\"limit\":5", "\"limit\":4", 1);
    assert_ne!(changed, checkpoint.to_canonical_json());
    let resigned = resign_fingerprint(&changed);
    let parsed =
        HomologicalStreamPortable::from_json(&resigned, HomologicalStreamParseLimits::default())
            .unwrap();
    assert!(parsed.has_valid_fingerprint());
    assert!(matches!(
        parsed.verify(HomologicalStreamVerifyLimits::default()),
        Err(HomologicalStreamPortableError::CountMismatch { field })
            if field == "work-limit committed work"
    ));
}

#[test]
fn resigned_work_limit_rejects_a_complete_prefix() {
    let census = verified_boundary_census();
    let mut stream = homological_stream_from_census(
        &census,
        3,
        flagship_config(HomologicalStreamBudget {
            max_sources: 100,
            max_work_units: 100_000,
        }),
        None,
    )
    .unwrap();
    let checkpoint = finish_stream(&mut stream);
    let work = checkpoint.work();
    let units = work.resolutions
        + work.target_covers
        + work.hom_spaces
        + work.projective_factor_spaces
        + work.ext_tables;
    let changed = checkpoint
        .to_canonical_json()
        .replacen(
            "\"max_work_units\":100000",
            &format!("\"max_work_units\":{units}"),
            1,
        )
        .replacen(
            "\"status\":{\"kind\":\"complete\"}",
            &format!(
                "\"status\":{{\"kind\":\"cut\",\"reason\":{{\"kind\":\"work_limit\",\"limit\":{units}}}}}"
            ),
            1,
        );
    assert_ne!(changed, checkpoint.to_canonical_json());
    let resigned = resign_fingerprint(&changed);
    let parsed =
        HomologicalStreamPortable::from_json(&resigned, HomologicalStreamParseLimits::default())
            .unwrap();
    assert!(parsed.has_valid_fingerprint());
    assert!(matches!(
        parsed.verify(HomologicalStreamVerifyLimits::default()),
        Err(HomologicalStreamPortableError::CountMismatch { field })
            if field == "work-limit complete prefix"
    ));
}

#[test]
fn resigned_source_limit_must_match_the_stored_budget() {
    let census = verified_boundary_census();
    let mut stream = homological_stream_from_census(
        &census,
        3,
        HomologicalStreamConfig {
            chunk_limits: HomologicalBatchStreamLimits {
                max_live_sources: 1,
                max_pairs: 100,
                max_ext_cells: 1_000,
            },
            budget: HomologicalStreamBudget {
                max_sources: 1,
                max_work_units: 100_000,
            },
        },
        None,
    )
    .unwrap();
    assert!(matches!(
        stream.next_chunk(),
        HomologicalStreamStep::Chunk(_)
    ));
    let checkpoint = stream.checkpoint();
    let changed = checkpoint
        .to_canonical_json()
        .replacen("\"limit\":1", "\"limit\":2", 1);
    assert_ne!(changed, checkpoint.to_canonical_json());
    let resigned = resign_fingerprint(&changed);
    let parsed =
        HomologicalStreamPortable::from_json(&resigned, HomologicalStreamParseLimits::default())
            .unwrap();
    assert!(matches!(
        parsed.verify(HomologicalStreamVerifyLimits::default()),
        Err(HomologicalStreamPortableError::CountMismatch { field })
            if field == "source-limit reason and budget"
    ));
}

#[test]
fn work_limit_probe_observes_the_remaining_source_budget() {
    let census = verified_flagship_census();
    let mut singleton = homological_stream_from_census(
        &census,
        3,
        HomologicalStreamConfig {
            chunk_limits: HomologicalBatchStreamLimits {
                max_live_sources: 1,
                max_pairs: 100,
                max_ext_cells: 1_000,
            },
            budget: HomologicalStreamBudget::default(),
        },
        None,
    )
    .unwrap();
    assert!(matches!(
        singleton.next_chunk(),
        HomologicalStreamStep::Chunk(_)
    ));
    let work = singleton.work();
    let limit = work.resolutions
        + work.target_covers
        + work.hom_spaces
        + work.projective_factor_spaces
        + work.ext_tables;
    let stream = homological_stream_from_census(
        &census,
        3,
        HomologicalStreamConfig {
            chunk_limits: HomologicalBatchStreamLimits {
                max_live_sources: 2,
                max_pairs: 100,
                max_ext_cells: 1_000,
            },
            budget: HomologicalStreamBudget {
                max_sources: 1,
                max_work_units: limit,
            },
        },
        None,
    )
    .unwrap();
    let checkpoint = stream.checkpoint();
    let changed = checkpoint.to_canonical_json().replacen(
        "\"status\":{\"kind\":\"active\"}",
        &format!(
            "\"status\":{{\"kind\":\"cut\",\"reason\":{{\"kind\":\"work_limit\",\"limit\":{limit}}}}}"
        ),
        1,
    );
    assert_ne!(changed, checkpoint.to_canonical_json());
    let resigned = resign_fingerprint(&changed);
    let parsed =
        HomologicalStreamPortable::from_json(&resigned, HomologicalStreamParseLimits::default())
            .unwrap();
    assert!(matches!(
        parsed.verify(HomologicalStreamVerifyLimits::default()),
        Err(HomologicalStreamPortableError::CountMismatch { field })
            if field == "work-limit boundary"
    ));
}

#[test]
fn resigned_chunk_sizes_reject_invalid_history() {
    let census = verified_flagship_census();
    let mut stream = homological_stream_from_census(
        &census,
        3,
        flagship_config(HomologicalStreamBudget::default()),
        None,
    )
    .unwrap();
    assert!(matches!(
        stream.next_chunk(),
        HomologicalStreamStep::Chunk(_)
    ));
    let checkpoint = stream.checkpoint();
    let text = checkpoint.to_canonical_json();
    for (sizes, expected) in [
        ("[0]", "chunk size 0 is zero"),
        ("[3]", "chunk size 0 exceeds capacity"),
        ("[1]", "chunk sizes and next_source"),
        ("[2,1]", "chunk sizes and work.chunks"),
    ] {
        let changed = text.replacen(
            "\"chunk_sizes\":[2]",
            &format!("\"chunk_sizes\":{sizes}"),
            1,
        );
        assert_ne!(changed, text);
        let resigned = resign_fingerprint(&changed);
        let parsed = HomologicalStreamPortable::from_json(
            &resigned,
            HomologicalStreamParseLimits::default(),
        )
        .unwrap();
        assert!(parsed.has_valid_fingerprint());
        assert!(matches!(
            parsed.verify(HomologicalStreamVerifyLimits::default()),
            Err(HomologicalStreamPortableError::CountMismatch { field })
                if field == expected
        ));
    }
}

fn resign_fingerprint(text: &str) -> String {
    let marker = ",\"fingerprint\":\"";
    let position = text
        .rfind(marker)
        .expect("artifact has an outer fingerprint");
    let prefix = &text[..position];
    format!("{prefix}{marker}{:016x}\"}}", fnv1a(prefix.as_bytes()))
}

fn fnv1a(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf29ce484222325u64, |value, byte| {
        (value ^ u64::from(*byte)).wrapping_mul(0x100000001b3)
    })
}

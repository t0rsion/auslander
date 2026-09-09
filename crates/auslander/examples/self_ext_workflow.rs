use auslander::algebra::commutative_square;
use auslander::batch_stream::{
    HomologicalBatchStreamLimits, HomologicalSelfPairCheckpointStream, HomologicalStreamBudget,
    HomologicalStreamConfig, HomologicalStreamCutReason, HomologicalStreamStep,
    HomologicalStreamVerifyLimits, VerifiedHomologicalStream, homological_stream_from_census,
};
use auslander::census::{
    Census, CensusLimits, CensusPortable, CensusRetention, CensusVerifyLimits, VerifiedCensus,
};
use auslander::field::PrimeField;
use auslander::iso::{IsoOutcome, is_isomorphic};
use auslander::module::{Module, direct_sum};
use auslander::theorem_artifact::{
    SelfExtLocusArtifact, SelfExtLocusVerifyLimits, VerifiedSelfExtLocusArtifact,
    verify_self_ext_locus_artifact,
};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};

const ARTIFACT: &str =
    include_str!("../artifacts/research/commutative-square-f2-d1111-self-ext-1-3.json");
const FLAGSHIP_ARTIFACT: &str =
    include_str!("../artifacts/research/commutative-square-f2-d2112-self-ext-1-3.json");
const STARTER_ARTIFACT_FILE: &str = "commutative-square-f2-d1111-self-ext-1-3.json";
const FLAGSHIP_ARTIFACT_FILE: &str = "commutative-square-f2-d2112-self-ext-1-3.json";

struct PreparedArtifact {
    text: String,
    verified: VerifiedSelfExtLocusArtifact,
}

fn export_directory() -> Option<PathBuf> {
    let arguments: Vec<String> = env::args().skip(1).collect();
    match arguments.as_slice() {
        [] => None,
        [flag, directory] if flag == "--export-directory" => {
            Some(PathBuf::from(directory.as_str()))
        }
        _ => panic!("usage: self_ext_workflow [--export-directory DIR]"),
    }
}

fn prepare_artifact(
    checkpoint: &VerifiedHomologicalStream,
    first_degree: usize,
    last_degree: usize,
) -> PreparedArtifact {
    let artifact =
        SelfExtLocusArtifact::from_verified_checkpoint(checkpoint, first_degree, last_degree)
            .unwrap();
    let text = artifact.to_canonical_json();
    let verified =
        verify_self_ext_locus_artifact(&text, SelfExtLocusVerifyLimits::default()).unwrap();
    PreparedArtifact { text, verified }
}

fn publish_artifact(
    prepared: &PreparedArtifact,
    committed: &str,
    directory: Option<&Path>,
    file_name: &str,
) {
    if let Some(directory) = directory {
        let path = directory.join(file_name);
        fs::write(&path, &prepared.text)
            .unwrap_or_else(|error| panic!("failed to write {}: {error}", path.display()));
    } else {
        assert_eq!(prepared.text, committed);
    }
}

fn complete_census(
    dimensions: Vec<usize>,
    max_candidates: usize,
    max_assignments: usize,
) -> VerifiedCensus {
    let algebra = commutative_square(PrimeField::new(2).unwrap());
    let census = Census::new(&algebra, dimensions).unwrap();
    let outcome = census.run_with(
        CensusLimits {
            retention: CensusRetention::RepresentativesOnly,
            max_candidates,
            max_representatives: 100,
            max_assignments,
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

fn stream_config(budget: HomologicalStreamBudget) -> HomologicalStreamConfig {
    HomologicalStreamConfig {
        chunk_limits: HomologicalBatchStreamLimits {
            max_live_sources: 2,
            max_pairs: 100,
            max_ext_cells: 1_000,
        },
        budget,
    }
}

fn finish(stream: &mut HomologicalSelfPairCheckpointStream) {
    loop {
        match stream.next_chunk() {
            HomologicalStreamStep::Chunk(chunk) => assert!(chunk.verify()),
            HomologicalStreamStep::Complete { .. } => return,
            HomologicalStreamStep::Cut { reason, .. } => panic!("unexpected cut: {reason}"),
            HomologicalStreamStep::Failed { error, .. } => {
                panic!("unexpected failure: {error}")
            }
        }
    }
}

fn complete_stream(
    census: &VerifiedCensus,
    budget: HomologicalStreamBudget,
) -> VerifiedHomologicalStream {
    let mut stream =
        homological_stream_from_census(census, 3, stream_config(budget), None).unwrap();
    finish(&mut stream);
    stream
        .checkpoint()
        .verify(HomologicalStreamVerifyLimits::default())
        .unwrap()
}

fn cut_and_resume(
    census: &VerifiedCensus,
    full_budget: HomologicalStreamBudget,
) -> VerifiedHomologicalStream {
    let cut_budget = HomologicalStreamBudget {
        max_sources: 4,
        ..full_budget
    };
    let mut stream =
        homological_stream_from_census(census, 3, stream_config(cut_budget), None).unwrap();
    for _ in 0..2 {
        let HomologicalStreamStep::Chunk(chunk) = stream.next_chunk() else {
            panic!("the first two chunks should complete")
        };
        assert!(chunk.verify());
    }
    let HomologicalStreamStep::Cut {
        reason: HomologicalStreamCutReason::SourceLimit { limit: 4 },
        ..
    } = stream.next_chunk()
    else {
        panic!("the source budget should cut at a chunk boundary")
    };
    let verified_cut = stream
        .checkpoint()
        .verify(HomologicalStreamVerifyLimits::default())
        .unwrap();
    let mut resumed = verified_cut.resume(full_budget, None).unwrap();
    finish(&mut resumed);
    resumed
        .checkpoint()
        .verify(HomologicalStreamVerifyLimits::default())
        .unwrap()
}

fn main() {
    let export_directory = export_directory();
    let full_budget = HomologicalStreamBudget {
        max_sources: 100,
        max_work_units: 100_000,
    };
    let starter_census = complete_census(vec![1, 1, 1, 1], 100, 100);
    let starter_checkpoint = complete_stream(&starter_census, full_budget);
    let starter = prepare_artifact(&starter_checkpoint, 1, 3);

    let flagship_census = complete_census(vec![2, 1, 1, 2], 256, 0);
    let flagship_checkpoint = complete_stream(&flagship_census, full_budget);
    let flagship = prepare_artifact(&flagship_checkpoint, 1, 3);
    let starter_verified = &starter.verified;
    let flagship_verified = &flagship.verified;
    assert_eq!(starter_verified.artifact().vanishing_indices(), &[9]);
    let flagship_degree_one =
        SelfExtLocusArtifact::from_verified_checkpoint(&flagship_checkpoint, 1, 1).unwrap();
    assert_eq!(flagship_degree_one.vanishing_indices(), &[5, 10, 11]);
    let resumed_checkpoint = cut_and_resume(&flagship_census, full_budget);
    assert_eq!(
        resumed_checkpoint.portable().to_canonical_json(),
        flagship_checkpoint.portable().to_canonical_json()
    );
    assert_eq!(flagship_verified.artifact().vanishing_indices(), &[5, 10]);
    assert_eq!(
        flagship_verified.checkpoint().portable().rows()[11].ext_dimensions(),
        &[5, 0, 1, 0]
    );
    let representative = flagship_verified
        .checkpoint()
        .census()
        .outcome()
        .complete()
        .unwrap()
        .representatives()[11]
        .module();
    let algebra = representative.algebra();
    let p0 = Module::projective(algebra, 0);
    let s0 = Module::simple(algebra, 0);
    let s3 = Module::simple(algebra, 3);
    let (decomposition, _, _) = direct_sum(&[&p0, &s0, &s3]);
    let IsoOutcome::Isomorphic(witness) = is_isomorphic(representative, &decomposition).unwrap()
    else {
        panic!("representative 11 must be isomorphic to P_0 ⊕ S_0 ⊕ S_3")
    };
    assert!(witness.is_isomorphism());
    if let Some(directory) = export_directory.as_deref() {
        fs::create_dir_all(directory)
            .unwrap_or_else(|error| panic!("failed to create {}: {error}", directory.display()));
    }
    publish_artifact(
        &starter,
        ARTIFACT,
        export_directory.as_deref(),
        STARTER_ARTIFACT_FILE,
    );
    publish_artifact(
        &flagship,
        FLAGSHIP_ARTIFACT,
        export_directory.as_deref(),
        FLAGSHIP_ARTIFACT_FILE,
    );

    println!(
        "starter dims={:?}; raw={}; classes={}; self-ext-free={:?}",
        starter_verified
            .checkpoint()
            .census()
            .portable()
            .dimensions(),
        starter_verified
            .checkpoint()
            .census()
            .portable()
            .raw_space_size(),
        starter_verified
            .checkpoint()
            .census()
            .portable()
            .representatives()
            .len(),
        starter_verified.artifact().vanishing_indices(),
    );
    println!(
        "flagship field=F2; dims={:?}; raw={}; accepted={}; classes={}; ext1-free={:?}; ext1-3-free={:?}; rep11=P0⊕S0⊕S3; rep11-ext={:?}; cut-resume=equal",
        flagship_verified
            .checkpoint()
            .census()
            .portable()
            .dimensions(),
        flagship_verified
            .checkpoint()
            .census()
            .portable()
            .raw_space_size(),
        flagship_verified
            .checkpoint()
            .census()
            .outcome()
            .complete()
            .unwrap()
            .accepted_modules(),
        flagship_verified
            .checkpoint()
            .census()
            .portable()
            .representatives()
            .len(),
        flagship_degree_one.vanishing_indices(),
        flagship_verified.artifact().vanishing_indices(),
        flagship_verified.checkpoint().portable().rows()[11].ext_dimensions(),
    );
}

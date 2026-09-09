//! Fresh-process tests for the portable command-line program.

use std::process::Command;

use auslander::algebra::linear_an;
use auslander::batch_stream::{
    HomologicalBatchStreamLimits, HomologicalStreamBudget, HomologicalStreamConfig,
    HomologicalStreamPortable, HomologicalStreamStep, homological_stream_from_census,
};
use auslander::census::{Census, CensusLimits, CensusOutcome, CensusPortable, CensusRetention};
use auslander::derived_artifact::DerivedArtifact;
use auslander::equivalence_edge::{DerivedEquivalenceEdge, DerivedEquivalenceEdgeOutcome};
use auslander::field::PrimeField;
use auslander::target::TargetLimits;
use auslander::tilting_complex::{
    TiltingComplexLimits, TiltingComplexResult, TiltingMutationOutcome, left_tilting_mutation,
    regular_tilting_complex,
};

fn artifact() -> DerivedArtifact {
    let algebra = linear_an(2, PrimeField::new(5).unwrap());
    let regular = match regular_tilting_complex(&algebra, TiltingComplexLimits::default()).unwrap()
    {
        TiltingComplexResult::Tilting(value) => *value,
        outcome => panic!("regular generator did not certify: {outcome:?}"),
    };
    let mutation = (0..2)
        .find_map(|summand| {
            match left_tilting_mutation(&regular, summand, TiltingComplexLimits::default()).unwrap()
            {
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
        DerivedEquivalenceEdgeOutcome::Cut(_) => panic!("the target was cut"),
    };
    DerivedArtifact::from_edge(&edge).unwrap()
}

fn census() -> CensusPortable {
    let algebra = linear_an(2, PrimeField::new(5).unwrap());
    let outcome = Census::new(&algebra, vec![1, 1]).unwrap().run();
    assert!(matches!(outcome, CensusOutcome::Complete(_)));
    CensusPortable::from_outcome(&outcome).unwrap()
}

fn compact_census() -> CensusPortable {
    let algebra = linear_an(2, PrimeField::new(5).unwrap());
    let limits = CensusLimits {
        retention: CensusRetention::RepresentativesOnly,
        max_assignments: 0,
        ..CensusLimits::default()
    };
    let outcome = Census::new(&algebra, vec![1, 1])
        .unwrap()
        .run_with(limits, None);
    assert!(matches!(outcome, CensusOutcome::Complete(_)));
    let portable = CensusPortable::from_outcome(&outcome).unwrap();
    assert!(portable.assignments().is_empty());
    portable
}

fn homological_stream() -> HomologicalStreamPortable {
    let verified = census()
        .verify(Default::default())
        .expect("census fixture must verify");
    let config = HomologicalStreamConfig {
        chunk_limits: HomologicalBatchStreamLimits {
            max_live_sources: 1,
            max_pairs: 100,
            max_ext_cells: 500,
        },
        budget: HomologicalStreamBudget::default(),
    };
    let mut stream = homological_stream_from_census(&verified, 2, config, None)
        .expect("homological stream fixture must start");
    loop {
        match stream.next_chunk() {
            HomologicalStreamStep::Chunk(chunk) => assert!(chunk.verify()),
            HomologicalStreamStep::Complete { .. } => return stream.checkpoint(),
            HomologicalStreamStep::Cut { .. } | HomologicalStreamStep::Failed { .. } => {
                panic!("homological stream fixture must complete")
            }
        }
    }
}

fn command(binary: &str, command: &str, path: &std::path::Path) -> std::process::Output {
    let output = Command::new(binary)
        .arg(command)
        .arg(path)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{command}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stderr.is_empty());
    output
}

fn check_commands(path: &std::path::Path, text: &str, fingerprint: &str) {
    let binary = env!("CARGO_BIN_EXE_auslander");
    for name in ["inspect", "verify", "canonicalize", "fingerprint"] {
        command(binary, name, path);
    }
    let canonical = command(binary, "canonicalize", path);
    assert_eq!(String::from_utf8(canonical.stdout).unwrap().trim(), text);
    let actual_fingerprint = command(binary, "fingerprint", path);
    assert_eq!(
        String::from_utf8(actual_fingerprint.stdout).unwrap().trim(),
        fingerprint
    );
}

#[test]
fn every_artifact_command_runs_in_a_fresh_process() {
    let artifact = artifact();
    let text = artifact.to_canonical_json();
    let path = std::env::temp_dir().join(format!(
        "auslander-artifact-cli-{}.json",
        std::process::id()
    ));
    std::fs::write(&path, &text).unwrap();
    check_commands(&path, &text, artifact.fingerprint());
    std::fs::remove_file(path).unwrap();
}

#[test]
fn every_census_command_replays_in_a_fresh_process() {
    let census = census();
    let text = census.to_canonical_json();
    let path =
        std::env::temp_dir().join(format!("auslander-census-cli-{}.json", std::process::id()));
    std::fs::write(&path, &text).unwrap();
    check_commands(&path, &text, census.fingerprint());
    std::fs::remove_file(path).unwrap();
}

#[test]
fn every_compact_census_command_replays_in_a_fresh_process() {
    let census = compact_census();
    let text = census.to_canonical_json();
    let path = std::env::temp_dir().join(format!(
        "auslander-compact-census-cli-{}.json",
        std::process::id()
    ));
    std::fs::write(&path, &text).unwrap();
    check_commands(&path, &text, census.fingerprint());
    std::fs::remove_file(path).unwrap();
}

#[test]
fn every_homological_stream_command_replays_in_a_fresh_process() {
    let stream = homological_stream();
    let text = stream.to_canonical_json();
    let path = std::env::temp_dir().join(format!(
        "auslander-homological-stream-cli-{}.json",
        std::process::id()
    ));
    std::fs::write(&path, &text).unwrap();
    check_commands(&path, &text, stream.fingerprint());
    std::fs::remove_file(path).unwrap();
}

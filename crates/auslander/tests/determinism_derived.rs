//! Fresh-process determinism tests for derived computations.

mod common;

use std::env;
use std::fmt::Write;
use std::time::Duration;

use auslander::algebra::{an_with_relations, linear_an};
use auslander::control::ComputationControl;
use auslander::derived_artifact::DerivedArtifact;
use auslander::derived_hom::{DerivedHomLimits, DerivedHomOutcome, derived_hom};
use auslander::equivalence_discovery::{DiscoveryLimits, discover_equivalences};
use auslander::equivalence_edge::{DerivedEquivalenceEdge, DerivedEquivalenceEdgeOutcome};
use auslander::field::PrimeField;
use auslander::homotopy::BoundedComplex;
use auslander::module::Module;
use auslander::perfect::{ReplacementLimits, ReplacementOutcome, replace_perfect};
use auslander::quiver::ArrowId;
use auslander::target::TargetLimits;

const CHILD_ENV: &str = "AUSLANDER_DERIVED_DETERMINISM_CHILD";
const MARKER: &str = "derived-fingerprint:";
const CHILD_TIMEOUT: Duration = Duration::from_secs(20);

fn complex_text(complex: &BoundedComplex) -> String {
    let mut output = format!("{}..{}", complex.lower(), complex.upper());
    let arrows = complex.terms()[0].algebra().quiver().num_arrows();
    let vertices = complex.terms()[0].algebra().quiver().num_vertices();
    for term in complex.terms() {
        write!(output, ";t={:?}", term.dim_vector()).unwrap();
        for arrow in 0..arrows {
            write!(
                output,
                ":a={:?}",
                term.map(ArrowId(arrow as u32)).entries_u64()
            )
            .unwrap();
        }
    }
    for differential in complex.differentials() {
        for vertex in 0..vertices {
            write!(output, ";d={:?}", differential.map_at(vertex).entries_u64()).unwrap();
        }
    }
    output
}

fn artifact(field: PrimeField) -> DerivedArtifact {
    let algebra = linear_an(2, field);
    let regular = common::certified_regular(&algebra);
    let mutation = common::genuine_left_mutation(&regular);
    let edge = match DerivedEquivalenceEdge::recover(mutation, &TargetLimits::default()).unwrap() {
        DerivedEquivalenceEdgeOutcome::Certified(value) => value,
        DerivedEquivalenceEdgeOutcome::Cut(_) => panic!("the A2 target completes"),
    };
    DerivedArtifact::from_edge(&edge).unwrap()
}

fn determinism_payload() -> String {
    let mut output = String::new();
    for field in [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()] {
        let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
        let source = common::one_term(&Module::simple(&algebra, 0));
        let target = common::one_term(&Module::simple(&algebra, 2));
        let ReplacementOutcome::Replaced(replacement) =
            replace_perfect(&source, ReplacementLimits::default(), None).unwrap()
        else {
            panic!("the pd2 replacement completes")
        };
        let DerivedHomOutcome::Complete(hom) =
            derived_hom(&source, &target, DerivedHomLimits::default(), None).unwrap()
        else {
            panic!("the pd2 derived Hom completes")
        };
        write!(
            output,
            "field={};replacement={};hom={:?};",
            field.modulus(),
            complex_text(replacement.projective().complex()),
            hom.work()
        )
        .unwrap();
        for space in hom.spaces() {
            write!(
                output,
                "q={}:n={:?}:c={:?};",
                space.degree(),
                space.null_homotopic_basis().entries_u64(),
                space.complement_basis().entries_u64()
            )
            .unwrap();
        }
        let mutation_algebra = linear_an(2, field);
        let graph = discover_equivalences(
            &mutation_algebra,
            DiscoveryLimits {
                max_vertices: 3,
                max_directed_mutations: 16,
                max_total_terms: 64,
                max_matrix_entries: 1_024,
                max_work_units: 16,
                ..DiscoveryLimits::default()
            },
            &ComputationControl::new(),
        )
        .unwrap();
        write!(
            output,
            "keys={:?};edges={:?};blocked={:?};stop={:?};artifact={};",
            graph
                .keys()
                .iter()
                .map(|key| key.as_str())
                .collect::<Vec<_>>(),
            graph.edges(),
            graph.blocked(),
            graph.stop(),
            artifact(field).to_canonical_json()
        )
        .unwrap();
    }
    output
}

#[test]
fn derived_determinism_child_prints_fingerprint() {
    if env::var(CHILD_ENV).is_err() {
        return;
    }
    println!("{}", common::fingerprint(MARKER, &determinism_payload()));
}

fn child_fingerprint() -> String {
    let stdout = common::child_test_stdout(
        "derived_determinism_child_prints_fingerprint",
        CHILD_ENV,
        CHILD_TIMEOUT,
    );
    common::marked_line(&stdout, MARKER)
}

#[test]
fn derived_values_are_deterministic_across_fresh_processes() {
    let payload = determinism_payload();
    assert_eq!(payload, determinism_payload());
    let first = child_fingerprint();
    let second = child_fingerprint();
    assert_eq!(first, second, "fresh processes disagree on derived data");
    assert_eq!(first, common::fingerprint(MARKER, &payload));
}

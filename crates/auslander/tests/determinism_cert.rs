//! Certificate determinism gate: identical input produces identical
//! certificate bytes, within one process and across two fresh processes.
//!
//! The fresh-process check spawns the current test binary twice on a child
//! test gated by an environment variable. That child builds the commutative
//! square and prints a hash of its certificate bytes. The two child outputs
//! must agree with each other and with the hash computed in this process.

use std::env;
use std::sync::Arc;
use std::time::Duration;

use auslander::algebra::Algebra;
use auslander::completion::CompletionLimits;
use auslander::field::PrimeField;
use auslander::quiver::{ArrowId, Quiver};
use auslander::relation::{Presentation, Relation};

mod common;

/// Builds the commutative square `kQ/(ab - cd)` over F_5 from a freshly
/// constructed presentation on every call.
fn square_algebra() -> Arc<Algebra> {
    let field = PrimeField::new(5).unwrap();
    let quiver = Quiver::new(4, &[(0, 1), (1, 3), (0, 2), (2, 3)]).unwrap();
    let relation = Relation::new(
        &quiver,
        field,
        vec![
            (field.one(), vec![ArrowId(0), ArrowId(1)]),
            (field.elem(-1), vec![ArrowId(2), ArrowId(3)]),
        ],
    )
    .unwrap();
    let presentation = Presentation::new(quiver, field, vec![relation]).unwrap();
    Algebra::new(presentation, &CompletionLimits::default()).unwrap()
}

fn certificate_bytes() -> String {
    square_algebra().certificate().to_canonical_json()
}

const CHILD_ENV: &str = "AUSLANDER_DETERMINISM_CHILD";
const MARKER: &str = "certificate-fingerprint:";
/// The child builds one dimension-9 algebra, which takes milliseconds here.
/// The bound exists to turn a hang into a test failure.
const CHILD_TIMEOUT: Duration = Duration::from_secs(60);

fn fingerprint(bytes: &str) -> String {
    common::fingerprint(MARKER, bytes)
}

#[test]
fn certificate_bytes_identical_across_two_in_process_constructions() {
    let first = certificate_bytes();
    let second = certificate_bytes();
    assert_eq!(first, second);
    assert!(!first.is_empty());
}

/// Runs only when spawned by the fresh-process gate below; a plain test run
/// passes it vacuously.
#[test]
fn determinism_child_prints_certificate_fingerprint() {
    if env::var(CHILD_ENV).is_err() {
        return;
    }
    println!("{}", fingerprint(&certificate_bytes()));
}

/// Spawns the current test binary on the child test alone and returns the
/// fingerprint line it printed.
fn child_fingerprint() -> String {
    let stdout = common::child_test_stdout(
        "determinism_child_prints_certificate_fingerprint",
        CHILD_ENV,
        CHILD_TIMEOUT,
    );
    common::marked_line(&stdout, MARKER)
}

#[test]
fn certificate_bytes_identical_across_two_fresh_processes() {
    let first = child_fingerprint();
    let second = child_fingerprint();
    assert_eq!(first, second, "fresh processes disagree on the certificate");
    assert_eq!(
        first,
        fingerprint(&certificate_bytes()),
        "child processes disagree with this process"
    );
}

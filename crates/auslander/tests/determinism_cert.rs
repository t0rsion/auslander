//! Certificate determinism gate: identical input produces identical
//! certificate bytes, within one process and across two fresh processes.
//!
//! The fresh-process check spawns the current test binary twice on a child
//! test gated by an environment variable. That child builds the commutative
//! square and prints a hash of its certificate bytes. The two child outputs
//! must agree with each other and with the hash computed in this process.

use std::env;
use std::io::Read;
use std::process::{Command, Stdio};
use std::sync::Arc;

use auslander::algebra::Algebra;
use auslander::completion::CompletionLimits;
use auslander::field::PrimeField;
use auslander::quiver::{ArrowId, Quiver};
use auslander::relation::{Presentation, Relation};

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

/// FNV-1a, 64 bit. Written out here so the fingerprint does not depend on
/// any hasher with unspecified cross-process behavior.
fn fnv1a(bytes: &[u8]) -> u64 {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for &byte in bytes {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    hash
}

const CHILD_ENV: &str = "AUSLANDER_DETERMINISM_CHILD";
const MARKER: &str = "certificate-fingerprint:";

fn fingerprint(bytes: &str) -> String {
    format!(
        "{MARKER}{:016x}:len:{}",
        fnv1a(bytes.as_bytes()),
        bytes.len()
    )
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
    let exe = env::current_exe().expect("path of the running test binary");
    let mut child = Command::new(exe)
        .args([
            "--exact",
            "determinism_child_prints_certificate_fingerprint",
            "--nocapture",
        ])
        .env(CHILD_ENV, "1")
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("spawn the child test process");
    let mut stdout = String::new();
    child
        .stdout
        .take()
        .expect("stdout was piped")
        .read_to_string(&mut stdout)
        .expect("read child output");
    let status = child.wait().expect("wait for the child test process");
    assert!(status.success(), "child test failed:\n{stdout}");
    assert!(
        stdout.contains("1 passed"),
        "child ran zero tests; was determinism_child_prints_certificate_fingerprint renamed?\n{stdout}"
    );
    stdout
        .lines()
        .find(|line| line.starts_with(MARKER))
        .unwrap_or_else(|| panic!("child printed no fingerprint line:\n{stdout}"))
        .to_string()
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

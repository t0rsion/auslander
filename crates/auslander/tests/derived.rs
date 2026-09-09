//! Public acceptance and fresh-process gates for strict derived transport.

use std::env;
use std::time::Duration;

mod common;

#[path = "derived/fingerprint.rs"]
mod fingerprint;
#[path = "derived/fixtures.rs"]
mod fixtures;
#[path = "derived/homotopy.rs"]
mod homotopy;

use fingerprint::{compare_one_term_hom, determinism_payload};
use fixtures::certificate;
use homotopy::compare_two_term_homotopy;

const CHILD_ENV: &str = "AUSLANDER_DERIVED_DETERMINISM_CHILD";
const MARKER: &str = "derived-fingerprint:";
const CHILD_TIMEOUT: Duration = Duration::from_secs(60);

#[test]
fn pd2_certificates_and_strict_transport_agree_over_f2_and_f5() {
    for field in [common::f2(), common::f5()] {
        let certificate = certificate(field);
        assert!(certificate.verify());
        assert_eq!(
            certificate
                .graded_homotopy()
                .iter()
                .map(|space| space.degree())
                .collect::<Vec<_>>(),
            vec![-2, -1, 0, 1, 2]
        );
        assert!(
            certificate
                .graded_homotopy()
                .iter()
                .filter(|space| space.degree() != 0)
                .all(|space| space.quotient().dim() == 0)
        );
        assert_eq!(
            certificate
                .graded_homotopy()
                .iter()
                .find(|space| space.degree() == 0)
                .unwrap()
                .quotient()
                .dim(),
            certificate.target().endo().dim()
        );
        compare_one_term_hom(&certificate, &mut String::new());
    }
}

#[test]
fn nontrivial_two_term_homotopy_transport_preserves_all_finite_support_data() {
    for field in [common::f2(), common::f5()] {
        compare_two_term_homotopy(&certificate(field));
    }
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
fn derived_data_is_deterministic_across_fresh_processes() {
    let payload = determinism_payload();
    assert_eq!(payload, determinism_payload());
    let first = child_fingerprint();
    let second = child_fingerprint();
    assert_eq!(first, second, "fresh processes disagree on derived data");
    assert_eq!(
        first,
        common::fingerprint(MARKER, &payload),
        "child processes disagree with this process"
    );
}

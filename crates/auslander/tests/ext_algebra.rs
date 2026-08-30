//! Acceptance checks for bounded graded self-Ext algebras.

use std::env;
use std::time::Duration;

use auslander::algebra::{linear_an, truncated_poly};
use auslander::extalgebra::{ExtAlgebra, ExtAlgebraOutcome};
use auslander::field::PrimeField;
use auslander::module::Module;

mod common;

const CHILD_ENV: &str = "AUSLANDER_EXT_ALGEBRA_DETERMINISM_CHILD";
const MARKER: &str = "ext-algebra-fingerprint:";
const CHILD_TIMEOUT: Duration = Duration::from_secs(30);

fn fields() -> [PrimeField; 2] {
    [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()]
}

fn finite(outcome: &ExtAlgebraOutcome) -> &ExtAlgebra {
    outcome
        .complete()
        .expect("the hereditary fixture has a finite resolution")
}

fn bounded(outcome: &ExtAlgebraOutcome) -> &ExtAlgebra {
    match outcome {
        ExtAlgebraOutcome::Complete(algebra) => algebra,
        ExtAlgebraOutcome::Cut(cut) => cut.algebra(),
    }
}

#[test]
fn finite_and_cut_outcomes_keep_their_mathematical_meanings() {
    for field in fields() {
        let hereditary = linear_an(3, field);
        let simple = Module::simple(&hereditary, 0);
        let complete = ExtAlgebraOutcome::compute(&simple, 4).unwrap();
        assert!(complete.is_complete());
        assert_eq!(finite(&complete).spaces().len(), 5);
        assert!(
            finite(&complete).spaces()[2..]
                .iter()
                .all(|space| space.dim() == 0)
        );
        assert!(complete.verify());

        let periodic = truncated_poly(3, field).unwrap();
        let simple = Module::simple(&periodic, 0);
        let cut = ExtAlgebraOutcome::compute(&simple, 4).unwrap();
        assert!(!cut.is_complete());
        let cut = cut.cut().unwrap();
        assert_eq!(cut.first_omitted_degree(), 5);
        assert_eq!(cut.algebra().spaces().len(), 5);
        assert!(cut.algebra().spaces().iter().all(|space| space.dim() == 1));
        assert!(cut.verify());
    }
}

#[test]
fn every_stored_basis_product_rechecks_through_the_ext_layer() {
    for field in fields() {
        let algebra = truncated_poly(3, field).unwrap();
        let simple = Module::simple(&algebra, 0);
        let outcome = ExtAlgebraOutcome::compute(&simple, 4).unwrap();
        let ext = bounded(&outcome);
        for record in ext.product_records() {
            let left = &ext.basis(record.left_degree()).unwrap()[record.left_basis()];
            let right = &ext.basis(record.right_degree()).unwrap()[record.right_basis()];
            let (product, witness) = left.then_with_witness(right).unwrap();
            assert_eq!(product.coordinates(), record.coordinates());
            assert!(product.equals(record.class()).unwrap());
            assert!(witness.verify(left, right, &product));
            assert!(record.witness().verify(left, right, record.class()));
        }
    }
}

#[test]
fn the_truncated_cubic_simple_has_the_expected_low_degree_products() {
    for field in fields() {
        let algebra = truncated_poly(3, field).unwrap();
        let simple = Module::simple(&algebra, 0);
        let outcome = ExtAlgebraOutcome::compute(&simple, 4).unwrap();
        let ext = bounded(&outcome);
        let y = &ext.basis(1).unwrap()[0];
        let z = &ext.basis(2).unwrap()[0];
        assert!(ext.multiply(y, y).unwrap().is_zero());
        assert!(!ext.multiply(y, z).unwrap().is_zero());
        assert!(!ext.multiply(z, y).unwrap().is_zero());
        assert!(!ext.multiply(z, z).unwrap().is_zero());
        assert!(ext.verify());
    }
}

fn fingerprint(ext: &ExtAlgebra) -> Vec<String> {
    let mut rows: Vec<String> = ext
        .spaces()
        .iter()
        .map(|space| format!("{:?}", space.complement_basis().entries_u64()))
        .collect();
    rows.extend(
        ext.product_records()
            .map(|record| format!("{:?}", record.coordinates())),
    );
    rows
}

#[test]
fn separate_builds_have_identical_bases_and_product_tensors() {
    for field in fields() {
        let build = || {
            let algebra = truncated_poly(3, field).unwrap();
            let simple = Module::simple(&algebra, 0);
            ExtAlgebraOutcome::compute(&simple, 4).unwrap()
        };
        let first = build();
        let second = build();
        assert_eq!(fingerprint(bounded(&first)), fingerprint(bounded(&second)));
    }
}

fn determinism_payload() -> String {
    let mut rows = Vec::new();
    for field in fields() {
        let algebra = truncated_poly(3, field).unwrap();
        let simple = Module::simple(&algebra, 0);
        let outcome = ExtAlgebraOutcome::compute(&simple, 4).unwrap();
        rows.push(format!(
            "field={};{:?}",
            field.modulus(),
            fingerprint(bounded(&outcome))
        ));
    }
    rows.join("\n")
}

#[test]
fn ext_algebra_determinism_child_prints_fingerprint() {
    if env::var(CHILD_ENV).is_err() {
        return;
    }
    println!("{}", common::fingerprint(MARKER, &determinism_payload()));
}

fn child_fingerprint() -> String {
    let stdout = common::child_test_stdout(
        "ext_algebra_determinism_child_prints_fingerprint",
        CHILD_ENV,
        CHILD_TIMEOUT,
    );
    common::marked_line(&stdout, MARKER)
}

#[test]
fn bases_and_product_tensors_are_stable_across_fresh_processes() {
    let payload = determinism_payload();
    assert_eq!(payload, determinism_payload());
    let first = child_fingerprint();
    let second = child_fingerprint();
    assert_eq!(
        first, second,
        "fresh processes disagree on Ext algebra data"
    );
    assert_eq!(
        first,
        common::fingerprint(MARKER, &payload),
        "child processes disagree with this process"
    );
}

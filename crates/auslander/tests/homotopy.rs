//! Acceptance and fresh-process determinism tests for bounded homotopy.

use std::env;
use std::fmt::Write as _;
use std::sync::Arc;
use std::time::Duration;

use auslander::algebra::{Algebra, linear_an};
use auslander::field::PrimeField;
use auslander::hom::{Morphism, identity};
use auslander::homotopy::{BoundedComplex, ChainMap, ChainMapError, DegreeRange, HomotopyHom};
use auslander::linalg::DenseMat;
use auslander::module::Module;

mod common;

const CHILD_ENV: &str = "AUSLANDER_HOMOTOPY_DETERMINISM_CHILD";
const MARKER: &str = "homotopy-fingerprint:";
const CHILD_TIMEOUT: Duration = Duration::from_secs(30);

fn fixture(modulus: u64) -> (Arc<Algebra>, BoundedComplex) {
    let field = PrimeField::new(modulus).unwrap();
    let algebra = linear_an(1, field);
    let simple = Module::simple(&algebra, 0);
    let complex = BoundedComplex::new(
        0,
        vec![simple.clone(), simple.clone()],
        vec![identity(&simple)],
    )
    .unwrap();
    (algebra, complex)
}

fn matrix_text(matrix: &DenseMat) -> String {
    format!(
        "{}x{}:{:?}",
        matrix.rows(),
        matrix.cols(),
        matrix.entries_u64()
    )
}

fn morphism_text(morphism: &Morphism) -> String {
    let mut text = String::new();
    for vertex in 0..morphism.source().algebra().quiver().num_vertices() {
        if vertex != 0 {
            text.push('|');
        }
        text.push_str(&matrix_text(morphism.map_at(vertex)));
    }
    text
}

fn complex_text(complex: &BoundedComplex) -> String {
    let mut text = format!("range={}..{};", complex.lower(), complex.upper());
    for (index, term) in complex.terms().iter().enumerate() {
        write!(text, "t{index}:{:?};", term.dim_vector()).unwrap();
    }
    for (index, differential) in complex.differentials().iter().enumerate() {
        write!(text, "d{index}:{};", morphism_text(differential)).unwrap();
    }
    text
}

fn map_text(map: &ChainMap) -> String {
    let mut text = format!("range={}..{};", map.range().lower(), map.range().upper());
    for (index, component) in map.components().iter().enumerate() {
        write!(text, "f{index}:{};", morphism_text(component)).unwrap();
    }
    text
}

fn hom_text(hom: &HomotopyHom) -> String {
    let quotient = hom.quotient().unwrap();
    let mut text = format!(
        "q={};dim={};target={};cycles={:?};null={:?};complement={:?};",
        hom.degree(),
        hom.dim(),
        complex_text(hom.shifted_target()),
        hom.basis_rows().entries_u64(),
        quotient.null_homotopic_basis().entries_u64(),
        quotient.complement_basis().entries_u64(),
    );
    for (index, basis) in hom.basis_iter().enumerate() {
        let coordinates = hom.coords(&basis).unwrap();
        let rebuilt = hom.morphism(&coordinates);
        let (quotient_coordinates, remainder) = quotient.reduce(&basis).unwrap();
        let reconstructed = quotient
            .representative(&quotient_coordinates)
            .add(&remainder)
            .unwrap();
        write!(
            text,
            "b{index}:{}:coords={coordinates:?}:roundtrip={}:reduce={quotient_coordinates:?}:remainder={}:reconstruct={};",
            map_text(&basis),
            rebuilt.agrees_with(&basis),
            map_text(&remainder),
            reconstructed.agrees_with(&basis),
        )
        .unwrap();
    }
    text
}

fn determinism_payload() -> String {
    let mut payload = String::new();
    for modulus in [2, 5] {
        let (_algebra, complex) = fixture(modulus);
        let shifted = complex.shift(1).unwrap();
        let cone = ChainMap::identity(&complex).mapping_cone().unwrap();
        write!(
            payload,
            "field={modulus};complex={};shift={};cone={};",
            complex_text(&complex),
            complex_text(&shifted),
            complex_text(&cone),
        )
        .unwrap();
        for degree in [-1, 0, 1] {
            let hom = HomotopyHom::new(&complex, &complex, degree).unwrap();
            write!(payload, "hom={};", hom_text(&hom)).unwrap();
        }
    }
    payload
}

#[test]
fn bounded_homotopy_acceptance_over_f2_and_f5() {
    for modulus in [2, 5] {
        let (_algebra, complex) = fixture(modulus);
        assert_eq!(complex.range(), DegreeRange::new(0, 1).unwrap());
        assert!(complex.verify());
        assert_eq!(complex.terms()[0].dim_vector(), &[1]);
        assert_eq!(complex.terms()[1].dim_vector(), &[1]);

        let shifted = complex.shift(1).unwrap();
        assert_eq!(shifted.range(), DegreeRange::new(1, 2).unwrap());
        let expected_sign = if modulus == 2 { 1 } else { 4 };
        assert_eq!(
            shifted.differential(2).unwrap().map_at(0).get(0, 0),
            PrimeField::new(modulus).unwrap().elem(expected_sign)
        );

        let cone = ChainMap::identity(&complex).mapping_cone().unwrap();
        assert_eq!(cone.range(), DegreeRange::new(0, 2).unwrap());
        assert_eq!(
            cone.terms()
                .iter()
                .map(|term| term.total_dim())
                .collect::<Vec<_>>(),
            vec![1, 2, 1]
        );
        assert!(cone.verify());
        assert!(!cone.differential(1).unwrap().is_zero());

        for degree in [-1, 0, 1] {
            let hom = HomotopyHom::new(&complex, &complex, degree).unwrap();
            assert_eq!(hom.degree(), degree);
            assert!(hom.verify());
            let quotient = hom.quotient().unwrap();
            assert!(quotient.verify());
            if degree == 0 {
                assert_eq!(hom.dim(), 1);
                assert_eq!(quotient.null_homotopic_basis().rows(), 1);
                assert_eq!(quotient.dim(), 0);
            }
            for basis in hom.basis_iter() {
                let coordinates = hom.coords(&basis).unwrap();
                assert!(hom.morphism(&coordinates).agrees_with(&basis));
                let (quotient_coordinates, remainder) = quotient.reduce(&basis).unwrap();
                let rebuilt = quotient
                    .representative(&quotient_coordinates)
                    .add(&remainder)
                    .unwrap();
                assert!(rebuilt.agrees_with(&basis));
            }
        }
        assert_eq!(
            HomotopyHom::new(&complex, &complex, i32::MAX).unwrap_err(),
            ChainMapError::DegreeOverflow {
                degree: 1,
                shift: i32::MAX,
            }
        );
    }
}

#[test]
fn homotopy_determinism_child_prints_fingerprint() {
    if env::var(CHILD_ENV).is_err() {
        return;
    }
    println!("{}", common::fingerprint(MARKER, &determinism_payload()));
}

fn child_fingerprint() -> String {
    let stdout = common::child_test_stdout(
        "homotopy_determinism_child_prints_fingerprint",
        CHILD_ENV,
        CHILD_TIMEOUT,
    );
    common::marked_line(&stdout, MARKER)
}

#[test]
fn homotopy_determinism_is_stable_across_fresh_processes() {
    let first = determinism_payload();
    let second = determinism_payload();
    assert_eq!(first, second);
    let child_first = child_fingerprint();
    let child_second = child_fingerprint();
    assert_eq!(child_first, child_second);
    assert_eq!(
        child_first,
        common::fingerprint(MARKER, &first),
        "fresh processes disagree with this process"
    );
}

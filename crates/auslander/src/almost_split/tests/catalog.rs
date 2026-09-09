use crate::algebra::{linear_an, truncated_poly};
use crate::arquiver::IndecomposableCatalog;
use crate::hom::HomError;
use crate::module::Module;
use crate::quiver::ArrowId;

use super::super::{AlmostSplitError, almost_split_via_catalog};
use super::support::*;

// tau is deterministic, so the two routes compute translate modules
// with identical vertex and arrow matrices, and class coordinates
// transport verbatim between their identically computed Ext bases. The
// transport below is checked entry by entry before equals() runs.
#[test]
fn via_catalog_agrees_with_the_ar_duality_route() {
    let x3 = truncated_poly(3, f2()).unwrap();
    let x3_catalog = IndecomposableCatalog::nakayama(&x3).unwrap();
    let a3 = linear_an(3, f5());
    let a3_catalog = IndecomposableCatalog::dynkin(&a3).unwrap();
    let cases = [
        (indec(&Module::simple(&x3, 0)), x3_catalog),
        (indec(&Module::simple(&a3, 1)), a3_catalog),
    ];
    for (m, catalog) in &cases {
        let duality = sequence_of(m);
        let through_catalog = catalog_sequence_of(m, catalog);
        assert_eq!(
            duality.sequence().middle().dim_vector(),
            through_catalog.sequence().middle().dim_vector()
        );
        let left = duality.sequence().sub();
        let right = through_catalog.sequence().sub();
        assert_eq!(left.dim_vector(), right.dim_vector());
        for a in 0..left.algebra().quiver().num_arrows() {
            let arrow = ArrowId(a as u32);
            assert_eq!(
                left.map(arrow).entries_u64(),
                right.map(arrow).entries_u64()
            );
        }
        let transported = duality
            .chosen_ar_class()
            .space()
            .class_from_coordinates(through_catalog.chosen_ar_class().coordinates())
            .unwrap();
        assert!(transported.equals(duality.chosen_ar_class()).unwrap());
        let witness = catalog_witness(&through_catalog);
        assert!(witness.verify(
            m,
            catalog,
            through_catalog.sequence(),
            through_catalog.chosen_ar_class()
        ));
    }
}

#[test]
fn via_catalog_rejects_a_catalog_over_another_algebra() {
    let x3 = truncated_poly(3, f2()).unwrap();
    let m = indec(&Module::simple(&x3, 0));
    let a3 = linear_an(3, f5());
    let catalog = IndecomposableCatalog::dynkin(&a3).unwrap();
    assert!(matches!(
        almost_split_via_catalog(&m, &catalog),
        Err(AlmostSplitError::Hom(HomError::DifferentAlgebras))
    ));
}

#[test]
fn a_tampered_catalog_factorization_coordinate_fails_verification() {
    let field = f2();
    let algebra = truncated_poly(3, field).unwrap();
    let catalog = IndecomposableCatalog::nakayama(&algebra).unwrap();
    let m = indec(&Module::simple(&algebra, 0));
    let sequence = catalog_sequence_of(&m, &catalog);
    let witness = catalog_witness(&sequence);
    assert!(witness.verify(
        &m,
        &catalog,
        sequence.sequence(),
        sequence.chosen_ar_class()
    ));
    let entry = witness
        .entries
        .iter()
        .position(|check| {
            check
                .right_factorizations
                .first()
                .is_some_and(|row| !row.is_empty())
        })
        .expect("some catalog entry has a nonzero radical into M");
    let mut bad = witness.clone();
    let old = bad.entries[entry].right_factorizations[0][0];
    bad.entries[entry].right_factorizations[0][0] = field.add(old, field.one());
    assert!(!bad.verify(
        &m,
        &catalog,
        sequence.sequence(),
        sequence.chosen_ar_class()
    ));
    let mut missing = witness.clone();
    missing.entries[entry].right_factorizations.pop();
    assert!(!missing.verify(
        &m,
        &catalog,
        sequence.sequence(),
        sequence.chosen_ar_class()
    ));
}

// The catalog witness stores no class coordinates, so realizing the
// class is the sequence-recovery gate's job: a scaled nonzero class
// shares the space and every endpoint but is not the class the
// sequence realizes.
#[test]
fn a_scaled_class_fails_catalog_verification() {
    let field = f5();
    let algebra = truncated_poly(3, field).unwrap();
    let catalog = IndecomposableCatalog::nakayama(&algebra).unwrap();
    let m = indec(&Module::simple(&algebra, 0));
    let sequence = catalog_sequence_of(&m, &catalog);
    let witness = catalog_witness(&sequence);
    assert!(witness.verify(
        &m,
        &catalog,
        sequence.sequence(),
        sequence.chosen_ar_class()
    ));
    let scaled = sequence.chosen_ar_class().scale(field.elem(2));
    assert!(!scaled.is_zero());
    assert!(!witness.verify(&m, &catalog, sequence.sequence(), &scaled));
}

// Both catalog domains of this release contain only modules of residue
// degree 1, so the socle-dimension gate forces a one-dimensional socle
// on every non-projective entry.
#[test]
fn catalog_domains_have_one_dimensional_socles() {
    let x3 = truncated_poly(3, f2()).unwrap();
    let a3 = linear_an(3, f5());
    let catalogs = [
        IndecomposableCatalog::nakayama(&x3).unwrap(),
        IndecomposableCatalog::dynkin(&a3).unwrap(),
    ];
    for catalog in &catalogs {
        for entry in catalog.entries() {
            assert_eq!(entry.residue_degree(), 1);
            if entry.is_projective() {
                continue;
            }
            let sequence = sequence_of(entry);
            let witness = duality_witness(&sequence);
            assert_eq!(witness.socle_dim(), 1);
            assert_eq!(witness.residue_degree(), 1);
        }
    }
}

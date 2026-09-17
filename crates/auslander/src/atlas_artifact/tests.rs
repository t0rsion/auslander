use std::sync::Arc;

use super::*;
use crate::algebra::path_algebra;
use crate::arquiver::IndecomposableCatalog;
use crate::atlas::{CatalogAtlas, CatalogAtlasLimits, MultiplicityLimits};
use crate::field::PrimeField;
use crate::quiver::Quiver;

fn zero_catalog_artifact() -> CatalogAtlasArtifact {
    let algebra = path_algebra(Quiver::new(0, &[]).unwrap(), PrimeField::new(5).unwrap()).unwrap();
    let catalog = Arc::new(IndecomposableCatalog::nakayama(&algebra).unwrap());
    let atlas = CatalogAtlas::compute(catalog, 0, CatalogAtlasLimits::default()).unwrap();
    CatalogAtlasArtifact::from_verified(&atlas, &[], MultiplicityLimits::default()).unwrap()
}

fn one_entry_artifact() -> CatalogAtlasArtifact {
    let algebra = path_algebra(Quiver::new(1, &[]).unwrap(), PrimeField::new(5).unwrap()).unwrap();
    let catalog = Arc::new(IndecomposableCatalog::dynkin(&algebra).unwrap());
    let atlas = CatalogAtlas::compute(catalog, 0, CatalogAtlasLimits::default()).unwrap();
    CatalogAtlasArtifact::from_verified(&atlas, &[1], MultiplicityLimits::default()).unwrap()
}

fn resign(text: &str) -> String {
    let marker = ",\"fingerprint\":\"";
    let key = text.rfind(marker).unwrap();
    let mut hash = 0xcbf29ce484222325u64;
    for byte in text[..key].bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    let fingerprint = format!("{hash:016x}");
    let start = key + marker.len();
    let mut output = text.to_owned();
    output.replace_range(start..start + 16, &fingerprint);
    output
}

#[test]
fn empty_nakayama_catalog_round_trips() {
    let artifact = zero_catalog_artifact();
    assert!(artifact.catalog_ids().is_empty());
    assert_eq!(artifact.result_rows().len(), 1);
    let text = artifact.to_canonical_json();
    let parsed = CatalogAtlasArtifact::from_json(&text, Default::default()).unwrap();
    assert_eq!(parsed, artifact);
    let verified = verify_catalog_atlas_artifact(&text, Default::default()).unwrap();
    assert!(verified.catalog().is_empty());
    assert_eq!(verified.artifact().target_dimensions(), &[]);
}

#[test]
fn verification_budget_rejects_catalog_before_rebuild() {
    let artifact = one_entry_artifact();
    let limits = CatalogAtlasArtifactVerifyLimits {
        max_catalog_entries: 0,
        ..Default::default()
    };
    assert!(matches!(
        artifact.verify(limits),
        Err(CatalogAtlasArtifactError::VerificationLimit {
            field: "catalog_entries",
            declared: 1,
            limit: 0,
        })
    ));
}

#[test]
fn parser_rejects_certificate_over_limit() {
    let artifact = zero_catalog_artifact();
    let text = artifact.to_canonical_json();
    let limits = CatalogAtlasArtifactParseLimits {
        max_certificate_bytes: artifact.certificate().to_canonical_json().len() - 1,
        ..Default::default()
    };
    let error = CatalogAtlasArtifact::from_json(&text, limits).unwrap_err();
    assert!(matches!(
        error,
        CatalogAtlasArtifactError::ParseLimit { .. }
    ));
}

#[test]
fn fingerprint_resealing_does_not_hide_shape_tampering() {
    let artifact = zero_catalog_artifact();
    let text = artifact.to_canonical_json();
    let tampered = resign(&text.replace("\"target_dimensions\":[]", "\"target_dimensions\":[0]"));
    let error = verify_catalog_atlas_artifact(&tampered, Default::default()).unwrap_err();
    assert!(matches!(
        error,
        CatalogAtlasArtifactError::CountMismatch { ref field }
            if field == "target_dimensions"
    ));
}

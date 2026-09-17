use std::sync::Arc;

use auslander::algebra::linear_an;
use auslander::arquiver::IndecomposableCatalog;
use auslander::atlas::{CatalogAtlas, CatalogAtlasLimits, MultiplicityLimits};
use auslander::atlas_artifact::{
    CatalogAtlasArtifact, CatalogAtlasArtifactError, CatalogAtlasArtifactParseLimits,
    CatalogAtlasArtifactVerifyLimits, verify_catalog_atlas_artifact,
};
use auslander::ext::ext_table;
use auslander::field::PrimeField;

fn artifact(max_solutions: usize) -> CatalogAtlasArtifact {
    let algebra = linear_an(2, PrimeField::new(5).unwrap());
    let catalog = Arc::new(IndecomposableCatalog::dynkin(&algebra).unwrap());
    let atlas = CatalogAtlas::compute(catalog, 2, CatalogAtlasLimits::default()).unwrap();
    CatalogAtlasArtifact::from_verified(
        &atlas,
        &[1, 1],
        MultiplicityLimits {
            max_solutions,
            ..MultiplicityLimits::default()
        },
    )
    .unwrap()
}

// Tampering tests recompute the public corruption checksum. Replay must reject
// false claims even when their bytes carry a matching checksum.
fn resign(text: &str) -> String {
    let (payload, _) = text.rsplit_once(",\"fingerprint\":\"").unwrap();
    let hash = payload.bytes().fold(0xcbf29ce484222325u64, |value, byte| {
        (value ^ u64::from(byte)).wrapping_mul(0x100000001b3)
    });
    format!("{payload},\"fingerprint\":\"{hash:016x}\"}}")
}

fn replace_rows(text: &str, transform: impl FnOnce(&str) -> String) -> String {
    let (prefix, tail) = text.split_once("\"result_rows\":[").unwrap();
    let (rows, suffix) = tail.split_once("],\"status\":").unwrap();
    resign(&format!(
        "{prefix}\"result_rows\":[{}],\"status\":{suffix}",
        transform(rows)
    ))
}

fn assert_replay_rejects(text: &str) {
    let parsed = CatalogAtlasArtifact::from_json(text, CatalogAtlasArtifactParseLimits::default())
        .expect("the modified claim remains canonical and has a valid checksum");
    assert!(matches!(
        parsed.verify(CatalogAtlasArtifactVerifyLimits::default()),
        Err(CatalogAtlasArtifactError::ReplayMismatch { .. })
            | Err(CatalogAtlasArtifactError::CountMismatch { .. })
    ));
}

#[test]
fn complete_artifact_roundtrips_through_public_parser_and_replay() {
    let original = artifact(10);
    let text = original.to_canonical_json();
    let rebuilt =
        verify_catalog_atlas_artifact(&text, CatalogAtlasArtifactVerifyLimits::default()).unwrap();
    assert_eq!(rebuilt.artifact().to_canonical_json(), text);
    assert!(rebuilt.artifact().status().is_complete());
    assert_eq!(rebuilt.artifact().result_rows().len(), 2);
}

#[test]
fn replayed_rows_match_generic_ext_on_materialized_modules() {
    let rebuilt = artifact(10)
        .verify(CatalogAtlasArtifactVerifyLimits::default())
        .unwrap();
    for row in rebuilt.artifact().result_rows() {
        let module = rebuilt.atlas().materialize(row.multiplicities()).unwrap();
        assert_eq!(row.self_ext(), ext_table(&module, &module, 2).unwrap());
    }
}

#[test]
fn replay_preserves_the_exact_cut_prefix() {
    let original = artifact(1);
    let text = original.to_canonical_json();
    let rebuilt =
        verify_catalog_atlas_artifact(&text, CatalogAtlasArtifactVerifyLimits::default()).unwrap();
    assert_eq!(rebuilt.artifact().status(), original.status());
    assert!(rebuilt.artifact().status().is_cut());
    assert_eq!(rebuilt.artifact().result_rows(), original.result_rows());
}

#[test]
fn omitted_valid_rows_do_not_pass_as_complete() {
    let text = replace_rows(&artifact(10).to_canonical_json(), |_| String::new());
    assert_replay_rejects(&text);
}

#[test]
fn duplicate_valid_rows_do_not_pass_as_complete() {
    let text = replace_rows(&artifact(10).to_canonical_json(), |rows| {
        let boundary = rows.find("},{").unwrap();
        let first = &rows[..boundary + 1];
        format!("{first},{first}")
    });
    assert_replay_rejects(&text);
}

#[test]
fn reordered_valid_rows_do_not_pass_replay() {
    let text = replace_rows(&artifact(10).to_canonical_json(), |rows| {
        let boundary = rows.find("},{").unwrap();
        format!("{},{}", &rows[boundary + 2..], &rows[..boundary + 1])
    });
    assert_replay_rejects(&text);
}

#[test]
fn a_cut_cannot_be_upgraded_to_complete() {
    let original = artifact(1).to_canonical_json();
    let (prefix, tail) = original.split_once("\"status\":").unwrap();
    let (_, suffix) = tail.split_once(",\"fingerprint\":").unwrap();
    let changed = format!("{prefix}\"status\":{{\"kind\":\"complete\"}},\"fingerprint\":{suffix}");
    assert_replay_rejects(&resign(&changed));
}

#[test]
fn modified_ext_cell_fails_even_with_a_recomputed_checksum() {
    let original = artifact(10).to_canonical_json();
    let changed = original.replacen("\"dimensions\":[1,0,0]", "\"dimensions\":[2,0,0]", 1);
    assert_ne!(original, changed);
    assert_replay_rejects(&resign(&changed));
}

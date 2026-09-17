"""Test catalog atlas artifact parsing, replay, and cut preservation."""

import pytest

import auslander


def _artifact(limits=None):
    algebra = auslander.Algebra.truncated_poly(3, field=auslander.PrimeField(5))
    atlas = algebra.catalog().atlas(3)
    return atlas, atlas.export([4], limits)


def test_atlas_artifact_exposes_identifiers():
    _, artifact = _artifact()

    assert artifact.schema == "auslander-computation-v1"
    assert artifact.kind == "catalog-atlas-v1"
    assert artifact.engine == "catalog-ext-multiplicity-v1"
    assert (artifact.field, artifact.provenance) == (5, "nakayama")


def test_atlas_artifact_exposes_scope():
    _, artifact = _artifact()

    assert artifact.catalog_ids == [0, 1, 2]
    assert artifact.target_dimensions == [4]
    assert artifact.catalog_len == 3
    assert artifact.max_degree == 3


def test_atlas_artifact_exposes_unverified_state():
    _, artifact = _artifact()

    assert artifact.status == "complete"
    assert artifact.enumeration_status.kind == "complete"
    assert artifact.cut_reason is None
    assert artifact.verification == "unverified"
    assert artifact.has_valid_fingerprint


def test_atlas_artifact_exposes_deterministic_rows():
    _, artifact = _artifact()

    assert [row.multiplicities for row in artifact.result_rows] == [
        [0, 2, 0],
        [1, 0, 1],
        [2, 1, 0],
        [4, 0, 0],
    ]
    assert len(artifact.ext_rows) == 9
    assert artifact.canonical_json.endswith(f'"fingerprint":"{artifact.fingerprint}"}}')


def test_atlas_artifact_parse_preserves_scope():
    _, artifact = _artifact()
    parsed = auslander.CatalogAtlasArtifact(artifact.canonical_json)

    assert parsed.canonical_json == artifact.canonical_json
    assert parsed.catalog_ids == artifact.catalog_ids
    assert parsed.target_dimensions == artifact.target_dimensions


def test_atlas_artifact_replay_preserves_rows():
    _, artifact = _artifact()
    verified = auslander.verify_catalog_atlas_artifact(artifact.canonical_json)

    assert verified.verification == "replayed"
    assert verified.status == "complete"
    assert verified.catalog.field.p == artifact.field
    assert [row.multiplicities for row in verified.result_rows] == [
        row.multiplicities for row in artifact.result_rows
    ]
    assert verified.atlas.verify()


def test_cut_artifact_keeps_typed_reason_before_and_after_replay():
    limits = auslander.MultiplicityLimits(max_solutions=1)
    _, artifact = _artifact(limits)
    parsed = auslander.CatalogAtlasArtifact(artifact.canonical_json)
    verified = auslander.verify_catalog_atlas_artifact(artifact.canonical_json)

    for value in (artifact, parsed, verified):
        assert value.status == "cut"
        assert value.enumeration_status.kind == "cut"
        assert value.cut_reason.kind == "solution_limit"
        assert value.cut_reason.limit == 1
        assert len(value.result_rows) == 1
    assert verified.verification == "replayed"


def test_artifact_parser_limits_and_fingerprint_reject_untrusted_input():
    _, artifact = _artifact()
    parse_limits = auslander.CatalogAtlasArtifactParseLimits(max_input_bytes=1)
    verify_limits = auslander.CatalogAtlasArtifactVerifyLimits(parse=parse_limits)

    with pytest.raises(auslander.BudgetExhaustedError) as limited:
        auslander.CatalogAtlasArtifact(artifact.canonical_json, verify_limits)
    assert limited.value.limit == 1

    corrupted = artifact.canonical_json.replace(artifact.fingerprint, "0" * 16)
    with pytest.raises(ValueError, match="fingerprint"):
        auslander.CatalogAtlasArtifact(corrupted)

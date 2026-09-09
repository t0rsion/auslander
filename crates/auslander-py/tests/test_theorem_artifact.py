"""Finite self-Ext locus artifacts and their fresh-process command-line path."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import auslander
import pytest


def _verified_census() -> auslander.VerifiedCensusCheckpoint:
    field = auslander.PrimeField(5)
    checkpoint = auslander.run_census(
        auslander.Algebra.linear_an(2),
        [1, 1],
        field,
        auslander.CensusLimits(
            max_candidates=100,
            max_representatives=100,
            max_assignments=100,
            max_isomorphism_checks=100,
            max_work_units=10_000,
        ),
    )
    assert checkpoint.status == "complete"
    return checkpoint.verify()


def _checkpoint(path: Path) -> auslander.HomologicalCheckpoint:
    stream = auslander.start_homological_stream(
        _verified_census(),
        2,
        auslander.HomologicalStreamConfig(
            max_live_sources=1,
            max_pairs=100,
            max_ext_cells=500,
            max_sources=100,
            max_work_units=10_000,
        ),
    )
    checkpoint = auslander.run_homological_stream(path, stream)
    assert checkpoint.status == "complete"
    return checkpoint


def test_self_ext_locus_roundtrips_and_verifies_independently(tmp_path: Path):
    checkpoint_path = tmp_path / "homology.aus.json"
    checkpoint = _checkpoint(checkpoint_path)
    artifact = auslander.build_self_ext_locus_artifact(
        checkpoint.verify(),
        1,
        2,
    )
    assert artifact.schema == "auslander-theorem-v1"
    assert artifact.kind == "fixed-dimension-self-ext-locus-v1"
    assert artifact.checkpoint.fingerprint == checkpoint.fingerprint
    assert artifact.vanishing_count == len(artifact.vanishing_indices)

    parsed = auslander.SelfExtLocusArtifact(artifact.canonical_json)
    verified = parsed.verify()
    assert verified.fingerprint == artifact.fingerprint
    assert verified.checkpoint.fingerprint == checkpoint.fingerprint
    assert verified.vanishing_indices == artifact.vanishing_indices


def test_self_ext_locus_file_helpers_are_atomic_and_bounded(tmp_path: Path):
    checkpoint_path = tmp_path / "homology.aus.json"
    _checkpoint(checkpoint_path)
    artifact_path = tmp_path / "locus.aus.json"
    artifact = auslander.build_self_ext_locus_artifact_file(
        checkpoint_path,
        artifact_path,
        1,
        2,
    )
    assert artifact_path.read_text(encoding="utf-8") == artifact.canonical_json
    loaded = auslander.load_self_ext_locus_artifact(artifact_path)
    verified = auslander.verify_self_ext_locus_artifact_file(artifact_path)
    assert loaded.fingerprint == verified.fingerprint

    with pytest.raises(ValueError, match="max_input_bytes"):
        auslander.load_self_ext_locus_artifact(
            artifact_path,
            auslander.SelfExtLocusVerifyLimits(max_input_bytes=4),
        )
    corrupted = artifact.canonical_json.replace(artifact.fingerprint, "0" * 16)
    artifact_path.write_text(corrupted, encoding="utf-8")
    with pytest.raises(ValueError, match="fingerprint"):
        auslander.verify_self_ext_locus_artifact_file(artifact_path)


def test_self_ext_locus_rejects_cut_checkpoint(tmp_path: Path):
    stream = auslander.start_homological_stream(
        _verified_census(),
        2,
        auslander.HomologicalStreamConfig(
            max_live_sources=1,
            max_pairs=100,
            max_ext_cells=500,
            max_sources=1,
            max_work_units=10_000,
        ),
    )
    checkpoint = stream.advance()
    assert checkpoint.status == "cut"
    with pytest.raises(ValueError, match="complete homological checkpoint"):
        auslander.build_self_ext_locus_artifact(checkpoint.verify(), 1, 2)


def _run_cli(*arguments: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, "-m", "auslander", *arguments],
        check=False,
        capture_output=True,
        text=True,
    )


def test_self_ext_locus_cli_builds_inspects_and_verifies(tmp_path: Path):
    checkpoint_path = tmp_path / "homology.aus.json"
    _checkpoint(checkpoint_path)
    artifact_path = tmp_path / "locus.aus.json"

    built = _run_cli(
        "theorem",
        "self-ext-locus",
        str(checkpoint_path),
        "1",
        "2",
        str(artifact_path),
    )
    assert built.returncode == 0, built.stderr
    assert "schema auslander-theorem-v1" in built.stdout
    assert "written " in built.stdout

    inspected = _run_cli("theorem", "inspect", str(artifact_path))
    assert inspected.returncode == 0, inspected.stderr
    assert "kind fixed-dimension-self-ext-locus-v1" in inspected.stdout

    verified = _run_cli("theorem", "verify", str(artifact_path))
    assert verified.returncode == 0, verified.stderr
    assert verified.stdout.startswith("verified ")

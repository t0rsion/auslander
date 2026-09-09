"""Durable homological streams and their fresh-process command-line path."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import auslander
import pytest


def _census() -> auslander.VerifiedCensusCheckpoint:
    field = auslander.PrimeField(5)
    algebra = auslander.Algebra.linear_an(2)
    checkpoint = auslander.run_census(
        algebra,
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


def _cut_stream() -> auslander.HomologicalCheckpointStream:
    return auslander.start_homological_stream(
        _census(),
        2,
        auslander.HomologicalStreamConfig(
            max_live_sources=1,
            max_pairs=100,
            max_ext_cells=500,
            max_sources=1,
            max_work_units=10_000,
        ),
    )


def _assert_cut_checkpoint(path: Path, checkpoint: auslander.HomologicalCheckpoint):
    assert checkpoint.status == "cut"
    assert checkpoint.cut_reason.kind == "source_limit"
    assert checkpoint.next_source == checkpoint.row_count == 1
    assert checkpoint.work.sources == 1
    assert checkpoint.work.peak_live_sources == 1
    assert path.read_text(encoding="utf-8") == checkpoint.canonical_json


def _assert_complete_checkpoint(
    path: Path,
    checkpoint: auslander.HomologicalCheckpoint,
    cut: auslander.HomologicalCheckpoint,
):
    assert checkpoint.status == "complete"
    assert checkpoint.next_source == checkpoint.row_count
    assert checkpoint.next_source > cut.next_source
    assert path.read_text(encoding="utf-8") == checkpoint.canonical_json
    assert checkpoint.verify().status == "complete"


def test_homological_checkpoint_persists_each_chunk_and_resumes(tmp_path: Path):
    first = tmp_path / "first.aus.json"
    cut = auslander.run_homological_stream(first, _cut_stream())
    _assert_cut_checkpoint(first, cut)

    loaded = auslander.load_homological_checkpoint(first)
    verified = auslander.verify_homological_checkpoint_file(first)
    assert loaded.canonical_json == cut.canonical_json
    assert verified.fingerprint == cut.fingerprint

    second = tmp_path / "second.aus.json"
    complete = auslander.resume_homological_checkpoint(
        first,
        second,
        auslander.HomologicalStreamBudget(
            max_sources=100,
            max_work_units=10_000,
        ),
    )
    _assert_complete_checkpoint(second, complete, cut)


def test_homological_checkpoint_rejects_corruption_and_small_limits(tmp_path: Path):
    path = tmp_path / "stream.aus.json"
    checkpoint = auslander.run_homological_stream(path, _cut_stream())
    corrupted = checkpoint.canonical_json.replace(checkpoint.fingerprint, "0" * 16)
    with pytest.raises(ValueError, match="fingerprint"):
        auslander.HomologicalCheckpoint(corrupted)
    with pytest.raises(ValueError, match="max_input_bytes"):
        auslander.load_homological_checkpoint(
            path,
            auslander.HomologicalStreamVerifyLimits(max_input_bytes=4),
        )


def test_homological_limits_and_resume_budget_are_visible():
    census_limits = auslander.CensusVerifyLimits(max_candidates=20_000)
    limits = auslander.HomologicalStreamVerifyLimits(
        census=census_limits,
        max_ext_dimensions=3,
        max_numeric_values=4,
        max_array_elements=5,
        max_integer_digits=6,
        max_string_bytes=7,
    )
    assert limits.max_ext_dimensions == 3
    assert limits.max_numeric_values == 4
    assert limits.max_array_elements == 5
    assert limits.max_integer_digits == 6
    assert limits.max_string_bytes == 7
    assert limits.census.max_candidates == 20_000
    assert repr(limits).startswith("HomologicalStreamVerifyLimits(")

    verified = _cut_stream().advance().verify()
    with pytest.raises(ValueError, match="below committed value"):
        verified.resume(auslander.HomologicalStreamBudget(max_sources=0))


def _run_cli(*arguments: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, "-m", "auslander", *arguments],
        check=False,
        capture_output=True,
        text=True,
    )


def test_homological_cli_starts_verifies_inspects_and_resumes(tmp_path: Path):
    census = tmp_path / "census.aus.json"
    auslander.write_checkpoint(census, _census())
    first = tmp_path / "first.aus.json"
    second = tmp_path / "second.aus.json"

    started = _run_cli(
        "homological",
        "start",
        str(census),
        "2",
        str(first),
        "--max-live-sources",
        "1",
        "--max-pairs",
        "100",
        "--max-ext-cells",
        "500",
        "--max-sources",
        "1",
        "--max-work-units",
        "10000",
    )
    assert started.returncode == 0, started.stderr
    assert "status cut" in started.stdout

    inspected = _run_cli("homological", "inspect", str(first))
    assert inspected.returncode == 0, inspected.stderr
    assert "kind homological-self-pair-stream-v2" in inspected.stdout
    verified = _run_cli("homological", "verify", str(first))
    assert verified.returncode == 0, verified.stderr
    assert verified.stdout.startswith("verified ")

    resumed = _run_cli(
        "homological",
        "resume",
        str(first),
        str(second),
        "--max-sources",
        "100",
        "--max-work-units",
        "10000",
    )
    assert resumed.returncode == 0, resumed.stderr
    assert "status complete" in resumed.stdout
    assert auslander.load_homological_checkpoint(second).status == "complete"

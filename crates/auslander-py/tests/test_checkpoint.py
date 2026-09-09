"""Portable census checkpoints, atomic writes, and command-line workflows."""

from __future__ import annotations

from pathlib import Path
import subprocess
import sys

import pytest

import auslander


def _certificate() -> str:
    field = auslander.PrimeField(5)
    return auslander.Algebra.linear_an(2).certificate_json(field)


def _cut(retention: str | None = None) -> auslander.CensusCheckpoint:
    field = auslander.PrimeField(5)
    algebra = auslander.Algebra.linear_an(2)
    return auslander.run_census(
        algebra,
        [1, 1],
        field,
        auslander.CensusLimits(
            max_candidates=2,
            max_work_units=100,
            retention=retention,
        ),
    )


def _assert_cut_checkpoint(checkpoint: auslander.CensusCheckpoint) -> None:
    assert isinstance(checkpoint, auslander.CensusCheckpoint)
    assert checkpoint.status == "cut"
    assert checkpoint.cut_reason.kind == "candidate_limit"
    assert checkpoint.cut_reason.limit == 2
    assert checkpoint.cursor == checkpoint.candidates == 2
    assert checkpoint.raw_space_size == 5
    assert checkpoint.counts["work_units"] == checkpoint.work_units
    assert checkpoint.canonical_json.endswith(f'"fingerprint":"{checkpoint.fingerprint}"}}')


def _assert_verified_checkpoint(
    checkpoint: auslander.CensusCheckpoint,
) -> auslander.VerifiedCensusCheckpoint:
    verified = checkpoint.verify()
    assert isinstance(verified, auslander.VerifiedCensusCheckpoint)
    assert verified.fingerprint == checkpoint.fingerprint
    assert [item.coordinates for item in verified.representatives] == [
        item.coordinates for item in checkpoint.representatives
    ]
    return verified


def _assert_complete_checkpoint(verified: auslander.VerifiedCensusCheckpoint) -> None:
    complete = verified.resume(
        auslander.CensusLimits(max_candidates=100, max_work_units=10_000)
    )
    assert complete.status == "complete"
    assert complete.cursor == complete.raw_space_size == 5
    assert complete.cut_reason is None
    assert complete.verify().status == "complete"


def test_census_checkpoint_exposes_typed_cut_and_resume_state():
    checkpoint = _cut()
    _assert_cut_checkpoint(checkpoint)
    _assert_complete_checkpoint(_assert_verified_checkpoint(checkpoint))


def test_compact_retention_survives_verification_and_default_resume():
    checkpoint = _cut("representatives_only")
    assert checkpoint.limits.retention == "representatives_only"
    assert checkpoint.assignment_count == 0
    verified = checkpoint.verify()
    complete = verified.resume()
    assert complete.status == "complete"
    assert complete.limits.retention == "representatives_only"
    with pytest.raises(ValueError, match="retention"):
        verified.resume(
            auslander.CensusLimits(
                max_candidates=100,
                max_work_units=10_000,
                retention="all_assignments",
            )
        )


def test_census_checkpoint_rejects_corruption():
    checkpoint = _cut()
    corrupted = checkpoint.canonical_json.replace(checkpoint.fingerprint, "0" * 16)
    with pytest.raises(ValueError, match="fingerprint"):
        auslander.CensusCheckpoint(corrupted)
    with pytest.raises(ValueError, match="fingerprint"):
        auslander.verify_census_checkpoint(corrupted)


def test_checkpoint_parser_and_replay_limits_are_caller_owned():
    checkpoint = _cut()
    text = checkpoint.canonical_json
    limits = auslander.CensusVerifyLimits(
        max_input_bytes=len(text),
        max_candidates=2,
        max_representatives=checkpoint.limits.max_representatives,
        max_assignments=checkpoint.limits.max_assignments,
    )
    parsed = auslander.CensusCheckpoint(text, limits)
    assert parsed.canonical_json == text
    assert parsed.verify(limits).cursor == checkpoint.cursor

    with pytest.raises(ValueError, match="cursor"):
        auslander.verify_census_checkpoint(
            text,
            auslander.CensusVerifyLimits(max_candidates=1),
        )


def test_checkpoint_write_is_atomic_and_cleans_failed_temporary_file(tmp_path, monkeypatch):
    checkpoint = _cut()
    path = tmp_path / "census.aus.json"
    path.write_text("old", encoding="utf-8")

    auslander.write_checkpoint(path, checkpoint)
    assert path.read_text(encoding="utf-8") == checkpoint.canonical_json
    assert list(tmp_path.glob(f".{path.name}.*.tmp")) == []

    path.write_text("old", encoding="utf-8")

    def fail_replace(_source: str, _target: Path) -> None:
        raise OSError("replace failed")

    from importlib import import_module

    checkpoint_module = import_module("auslander.checkpoint")
    monkeypatch.setattr(checkpoint_module.os, "replace", fail_replace)
    with pytest.raises(OSError, match="replace failed"):
        auslander.write_checkpoint(path, checkpoint)
    assert path.read_text(encoding="utf-8") == "old"
    assert list(tmp_path.glob(f".{path.name}.*.tmp")) == []


def test_checkpoint_load_and_verify_helpers(tmp_path):
    checkpoint = _cut()
    path = tmp_path / "census.aus.json"
    auslander.write_checkpoint(path, checkpoint)
    loaded = auslander.load_checkpoint(path)
    verified = auslander.verify_checkpoint(path)
    assert loaded.canonical_json == checkpoint.canonical_json
    assert verified.canonical_json == checkpoint.canonical_json


def test_checkpoint_file_reader_honors_input_and_utf8_limits(tmp_path):
    oversized = tmp_path / "oversized.aus.json"
    oversized.write_bytes(b"{}" * 8)
    with pytest.raises(ValueError, match="max_input_bytes=4"):
        auslander.load_checkpoint(
            oversized,
            auslander.CensusVerifyLimits(max_input_bytes=4),
        )

    invalid = tmp_path / "invalid.aus.json"
    invalid.write_bytes(b"\xff")
    with pytest.raises(ValueError, match="valid UTF-8"):
        auslander.load_checkpoint(invalid)


def _run_cli(*arguments: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, "-m", "auslander", *arguments],
        check=False,
        capture_output=True,
        text=True,
    )


def _start_cli(
    certificate: Path, output: Path, retention: str | None = None
) -> None:
    arguments = [
        "census",
        "start",
        str(certificate),
        "[1,1]",
        str(output),
        "--max-candidates",
        "2",
        "--max-work-units",
        "100",
    ]
    if retention is not None:
        arguments.extend(["--retention", retention])
    started = _run_cli(*arguments)
    assert started.returncode == 0, started.stderr
    assert "status cut" in started.stdout


def _inspect_cli(path: Path) -> None:
    inspected = _run_cli("census", "inspect", str(path))
    assert inspected.returncode == 0, inspected.stderr
    assert "kind census-v1" in inspected.stdout
    assert "cut_reason candidate_limit" in inspected.stdout


def _verify_cli(path: Path) -> None:
    verified = _run_cli("census", "verify", str(path))
    assert verified.returncode == 0, verified.stderr
    assert verified.stdout.startswith("verified ")


def _resume_cli(source: Path, output: Path) -> None:
    resumed = _run_cli(
        "census",
        "resume",
        str(source),
        str(output),
        "--max-candidates",
        "100",
        "--max-work-units",
        "10000",
    )
    assert resumed.returncode == 0, resumed.stderr
    assert "status complete" in resumed.stdout


def test_census_cli_starts_verifies_inspects_and_resumes_in_fresh_processes(tmp_path):
    certificate = tmp_path / "algebra.json"
    certificate.write_text(_certificate(), encoding="utf-8")
    first = tmp_path / "first.aus.json"
    second = tmp_path / "second.aus.json"

    _start_cli(certificate, first)
    _inspect_cli(first)
    _verify_cli(first)
    _resume_cli(first, second)
    assert auslander.CensusCheckpoint(second.read_text(encoding="utf-8")).status == "complete"


def test_census_cli_resume_preserves_compact_retention_when_omitted(tmp_path):
    certificate = tmp_path / "algebra.json"
    certificate.write_text(_certificate(), encoding="utf-8")
    first = tmp_path / "first.aus.json"
    second = tmp_path / "second.aus.json"

    _start_cli(certificate, first, "representatives_only")
    _resume_cli(first, second)
    resumed = auslander.CensusCheckpoint(second.read_text(encoding="utf-8"))
    assert resumed.status == "complete"
    assert resumed.limits.retention == "representatives_only"


def test_census_cli_does_not_replace_output_on_bad_resume(tmp_path):
    certificate = tmp_path / "algebra.json"
    certificate.write_text(_certificate(), encoding="utf-8")
    source = tmp_path / "source.aus.json"
    output = tmp_path / "output.aus.json"
    output.write_text("keep", encoding="utf-8")

    started = _run_cli(
        "census",
        "start",
        str(certificate),
        "[1,1]",
        str(source),
        "--max-candidates",
        "2",
        "--max-work-units",
        "100",
    )
    assert started.returncode == 0, started.stderr
    source.write_text(source.read_text(encoding="utf-8").replace("0", "1", 1), encoding="utf-8")
    resumed = _run_cli(
        "census",
        "resume",
        str(source),
        str(output),
        "--max-candidates",
        "100",
        "--max-work-units",
        "10000",
    )
    assert resumed.returncode == 2
    assert output.read_text(encoding="utf-8") == "keep"

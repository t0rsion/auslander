"""Exercise atlas replay and reports through the installed command line."""

import csv
import io
import json
import subprocess
import sys

import auslander as au
import pytest


@pytest.fixture(params=[("complete", 10), ("cut", 1)])
def atlas_file(request, tmp_path):
    status, max_solutions = request.param
    algebra = au.Algebra.linear_an(2, field=au.PrimeField(2))
    atlas = algebra.catalog().atlas(1)
    artifact = atlas.export([1, 1], au.MultiplicityLimits(max_solutions=max_solutions))
    path = tmp_path / "atlas.json"
    au.checkpoint(artifact, path)
    return path, status


def _cli(*arguments):
    return subprocess.run(
        [sys.executable, "-m", "auslander", "workflow", *map(str, arguments)],
        capture_output=True,
        text=True,
        check=True,
    ).stdout


def test_atlas_cli_inspects_and_verifies_the_same_status(atlas_file):
    path, status = atlas_file
    inspection = _cli("inspect", path)
    replay = _cli("verify", path)
    assert f"status: {status}" in inspection
    assert "verification: unverified" in inspection
    assert "provenance: dynkin_zero_ideal" in inspection
    assert f"status {status}" in replay


def test_atlas_markdown_reports_replayed_scope(atlas_file):
    path, status = atlas_file
    report = _cli("export", path, "--verify")
    assert f"status: {status}" in report
    assert "verification: replayed" in report
    assert "| index | multiplicities | Ext^0 | Ext^1 |" in report


def test_atlas_csv_keeps_metadata_separate_from_rows(atlas_file):
    path, status = atlas_file
    report = au.export(path, format="csv", verify_value=True)
    metadata, *rows = list(csv.DictReader(io.StringIO(report)))
    assert (metadata["record_type"], metadata["status"]) == ("metadata", status)
    assert metadata["verification"] == "replayed"
    assert json.loads(metadata["dimensions"]) == [1, 1]
    assert rows[0]["multiplicities"]


def test_atlas_inspection_scope_is_json_serializable(atlas_file):
    path, status = atlas_file
    inspection = au.inspect(au.verify(path))
    restored = json.loads(json.dumps(inspection.as_dict()))
    assert restored["status"] == status
    assert restored["scope"]["kind"] == "catalog_multiplicities"

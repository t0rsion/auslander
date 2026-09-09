"""Canonical JSON compute requests."""

import io
import json
import struct
import subprocess
import sys
from pathlib import Path

import pytest

import auslander
from auslander.__main__ import main


LINEAR = "field 5\nvertices 0 1\narrows a:0->1\n"


def request(module, operations):
    return {
        "schema": "auslander-compute-v1",
        "algebra": {"presentation": LINEAR},
        "modules": {"M": module},
        "operations": operations,
    }


def test_compute_json_is_canonical_and_runs_the_first_release_operations():
    document = request(
        {"dims": [1, 1], "maps": [[[1]]]},
        [
            {"op": "algebra_summary"},
            {"op": "hom_dim", "source": "M", "target": "M"},
            {"op": "stable_hom_dim", "source": "M", "target": "M"},
            {"op": "ext_table", "source": "M", "target": "M", "max_degree": 1},
            {"op": "tau", "module": "M"},
            {"op": "resolve", "module": "M", "steps": 1},
            {"op": "decompose", "module": "M"},
        ],
    )
    text = json.dumps(document, sort_keys=False)
    first = auslander.compute_json(text)
    second = auslander.compute_json(json.dumps(document, separators=(",", ":")))

    assert first == second
    result = json.loads(first)
    assert result["schema"] == "auslander-compute-result-v1"
    assert result["algebra"]["dimension"] == 3
    assert result["algebra"]["certificate"]["schema"] == "auslander-completion-certificate-v1"
    assert [item["op"] for item in result["results"]] == [
        "algebra_summary",
        "hom_dim",
        "stable_hom_dim",
        "ext_table",
        "tau",
        "resolve",
        "decompose",
    ]


def test_compute_json_rejects_unknown_fields_operations_and_names():
    base = request({"dims": [1, 1], "maps": [[[1]]]}, [])
    unknown = dict(base, extra=True)
    with pytest.raises(ValueError, match="unknown fields"):
        auslander.compute_request(unknown)

    alias = request({"dims": [1, 1], "maps_sparse": [[[0, 0, 1]]]}, [])
    with pytest.raises(ValueError, match="unknown fields"):
        auslander.compute_request(alias)

    bad_operation = request(
        {"dims": [1, 1], "maps": [[[1]]]}, [{"op": "not_supported"}]
    )
    with pytest.raises(ValueError, match="unknown operation"):
        auslander.compute_request(bad_operation)

    bad_name = request(
        {"dims": [1, 1], "maps": [[[1]]]},
        [{"op": "hom_dim", "source": "MISSING", "target": "M"}],
    )
    with pytest.raises(ValueError, match="unknown module name"):
        auslander.compute_request(bad_name)


def test_compute_json_dense_and_sparse_module_input_have_equal_results():
    operations = [{"op": "hom_dim", "source": "M", "target": "M"}]
    dense = request({"dims": [1, 1], "maps": [[[1]]]}, operations)
    sparse = request({"dims": [1, 1], "sparse_maps": [[[0, 0, 1]]]}, operations)

    assert auslander.compute_json(json.dumps(dense)) == auslander.compute_json(
        json.dumps(sparse)
    )


def test_compute_json_keeps_cut_resolution_typed():
    document = {
        "schema": "auslander-compute-v1",
        "algebra": {
            "presentation": "field 5\nvertices 0\narrows x:0->0\nrelations x*x = 0\n"
        },
        "modules": {"S": {"dims": [1], "maps": [[[0]]]}},
        "operations": [{"op": "resolve", "module": "S", "steps": 0}],
    }

    value = json.loads(auslander.compute_json(json.dumps(document)))["results"][0]["value"]
    assert value["status"] == {"kind": "cut", "at": 0}
    assert value["projective_dimension"] == {"kind": "at_least", "value": 1}
    assert "infinite" not in json.dumps(value)


def test_compute_json_returns_module_hom_and_stable_hom_bases():
    document = {
        "schema": "auslander-compute-v1",
        "algebra": {
            "presentation": "field 5\nvertices 0\narrows x:0->0\nrelations x*x = 0\n"
        },
        "modules": {"S": {"dims": [1], "maps": [[[0]]]}},
        "operations": [
            {"op": "hom", "source": "S", "target": "S"},
            {"op": "stable_hom", "source": "S", "target": "S"},
        ],
    }

    result = json.loads(auslander.compute_json(json.dumps(document)))
    assert result["modules"]["S"]["maps"] == [[[0]]]
    assert result["results"][0]["value"]["basis"] == [[[[1]]]]
    stable = result["results"][1]["value"]
    assert stable["dimension"] == 1
    assert stable["projective_factor_dimension"] == 0
    assert stable["basis"] == [[[[1]]]]
    assert stable["projective_factor_basis"] == []


def test_compute_json_returns_batch_names_indices_work_and_statuses():
    document = {
        "schema": "auslander-compute-v1",
        "algebra": {"presentation": LINEAR},
        "modules": {
            "P": {"dims": [1, 1], "maps": [[[1]]]},
            "S": {"dims": [0, 1], "maps": [[]]},
        },
        "operations": [
            {
                "op": "homological_batch",
                "modules": ["P", "S"],
                "max_degree": 1,
                "pairs": [["P", "S"], [1, 1]],
                "max_pairs": 2,
                "max_ext_cells": 4,
            },
            {
                "op": "homological_batch",
                "modules": ["P", "S"],
                "max_degree": 0,
                "all_pairs": True,
            },
        ],
    }

    values = json.loads(auslander.compute_json(json.dumps(document)))
    selected = values["results"][0]["value"]
    assert selected["selected_pairs"] == [
        {"source": "P", "target": "S", "source_index": 0, "target_index": 1},
        {"source": "S", "target": "S", "source_index": 1, "target_index": 1},
    ]
    assert selected["pairs"][0]["hom_dim"] == 0
    assert selected["pairs"][0]["stable_hom_dim"] == 0
    assert selected["pairs"][0]["ext_dimensions"] == [0, 0]
    assert selected["work"] == {
        "resolutions": 2,
        "target_covers": 1,
        "hom_spaces": 2,
        "projective_factor_spaces": 2,
        "ext_tables": 2,
    }
    assert all(item["status"] == {"kind": "finite"} for item in selected["resolutions"])
    assert len(values["results"][1]["value"]["pairs"]) == 4


def test_compute_cli_rejects_repl_argument_and_runtime_errors_without_traceback(
    monkeypatch, capsys
):
    with pytest.raises(SystemExit) as error:
        main(["repl", "unexpected.json"])
    assert error.value.code == 2
    assert "auslander" in capsys.readouterr().err

    def fail(_text):
        raise RuntimeError("budget exhausted")

    monkeypatch.setattr("auslander.__main__.compute_json", fail)
    monkeypatch.setattr(sys, "stdin", io.StringIO("{}"))
    assert main(["compute"]) == 2
    captured = capsys.readouterr()
    assert "budget exhausted" in captured.err
    assert "Traceback" not in captured.err


@pytest.mark.parametrize("operation", ["resolve", "ext_table"])
def test_compute_cli_reports_python_integers_that_do_not_fit_rust_usize(
    operation, monkeypatch, capsys
):
    too_large = 1 << (8 * struct.calcsize("P"))
    payload = (
        {"op": "resolve", "module": "M", "steps": too_large}
        if operation == "resolve"
        else {
            "op": "ext_table",
            "source": "M",
            "target": "M",
            "max_degree": too_large,
        }
    )
    document = request(
        {"dims": [1, 1], "maps": [[[1]]]},
        [payload],
    )
    monkeypatch.setattr(sys, "stdin", io.StringIO(json.dumps(document)))

    assert main(["compute"]) == 2
    captured = capsys.readouterr()
    assert "auslander: error:" in captured.err
    assert "Rust usize" in captured.err
    assert "Traceback" not in captured.err


def test_compute_json_rejects_oversized_nonnegative_ffi_values():
    too_large = 1 << (8 * struct.calcsize("P"))
    document = request(
        {"dims": [1, 1], "maps": [[[1]]]},
        [{"op": "ext_table", "source": "M", "target": "M", "max_degree": too_large}],
    )

    with pytest.raises(ValueError, match="Rust usize"):
        auslander.compute_request(document)


def test_compute_cli_has_subcommand_help_version_and_explicit_stdin(
    monkeypatch, capsys
):
    with pytest.raises(SystemExit) as version:
        main(["--version"])
    assert version.value.code == 0
    assert capsys.readouterr().out == f"auslander {auslander.__version__}\n"

    with pytest.raises(SystemExit) as help_exit:
        main(["compute", "--help"])
    assert help_exit.value.code == 0
    help_text = capsys.readouterr().out
    assert "REQUEST.json" in help_text
    assert "standard input" in help_text

    document = request({"dims": [1, 1], "maps": [[[1]]]}, [])
    monkeypatch.setattr(sys, "stdin", io.StringIO(json.dumps(document)))
    assert main(["compute", "-"]) == 0
    assert json.loads(capsys.readouterr().out)["schema"] == "auslander-compute-result-v1"


def test_compute_cli_matches_the_api_in_fresh_processes(tmp_path: Path):
    document = request(
        {"dims": [1, 1], "sparse_maps": [[[0, 0, 1]]]},
        [
            {"op": "hom", "source": "M", "target": "M"},
            {"op": "resolve", "module": "M", "steps": 1},
        ],
    )
    text = json.dumps(document)
    expected = auslander.compute_json(text) + "\n"
    from_stdin = subprocess.run(
        [sys.executable, "-m", "auslander", "compute"],
        input=text,
        check=True,
        capture_output=True,
        text=True,
    )
    path = tmp_path / "request.json"
    path.write_text(text, encoding="utf-8")
    from_path = subprocess.run(
        [sys.executable, "-m", "auslander", "compute", str(path)],
        check=True,
        capture_output=True,
        text=True,
    )
    assert from_stdin.stdout == from_path.stdout == expected
    assert from_stdin.stderr == from_path.stderr == ""

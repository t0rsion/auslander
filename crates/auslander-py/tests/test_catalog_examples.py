"""Execute the v0.9 catalog atlas example from the installed package."""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import nbformat
from nbclient import NotebookClient

EXAMPLES = Path(__file__).parents[1] / "examples"
NOTEBOOK = EXAMPLES / "catalog_workflow.ipynb"
SCRIPT = EXAMPLES / "catalog_workflow.py"
EXPECTED_RAW_ROWS = [
    "row: scalars=[0, 0, 0], self_ext=[4, 3, 1, 0]",
    "row: scalars=[0, 0, 1], self_ext=[3, 2, 1, 0]",
    "row: scalars=[0, 1, 0], self_ext=[3, 1, 0, 0]",
    "row: scalars=[0, 1, 1], self_ext=[2, 0, 0, 0]",
    "row: scalars=[1, 0, 0], self_ext=[3, 1, 0, 0]",
    "row: scalars=[1, 0, 1], self_ext=[2, 0, 0, 0]",
]
EXPECTED_ATLAS_ROWS = [
    "atlas row: multiplicities=[0, 1, 0, 0, 0, 0, 1, 0], self_ext=[2, 0, 0, 0]",
    "atlas row: multiplicities=[0, 1, 0, 0, 0, 1, 0, 1], self_ext=[3, 1, 0, 0]",
    "atlas row: multiplicities=[1, 0, 0, 0, 1, 0, 0, 0], self_ext=[2, 0, 0, 0]",
    "atlas row: multiplicities=[1, 0, 0, 1, 0, 0, 0, 1], self_ext=[3, 1, 0, 0]",
    "atlas row: multiplicities=[1, 0, 1, 0, 0, 0, 1, 0], self_ext=[3, 2, 1, 0]",
    "atlas row: multiplicities=[1, 0, 1, 0, 0, 1, 0, 1], self_ext=[4, 3, 1, 0]",
]


def _current_kernel(tmp_path: Path, monkeypatch) -> str:
    """Expose the test interpreter through a temporary kernelspec."""
    kernels = tmp_path / "kernels"
    spec = kernels / "auslander-current"
    spec.mkdir(parents=True)
    (spec / "kernel.json").write_text(
        json.dumps(
            {
                "argv": [
                    sys.executable,
                    "-m",
                    "ipykernel_launcher",
                    "-f",
                    "{connection_file}",
                ],
                "display_name": "Auslander current test interpreter",
                "language": "python",
            }
        ),
        encoding="utf-8",
    )
    monkeypatch.setenv("JUPYTER_PATH", str(tmp_path))
    return "auslander-current"


def _notebook_output(notebook) -> str:
    """Collect text output from all executed notebook cells."""
    return "\n".join(
        output.get("text", "")
        for cell in notebook.cells
        if cell.cell_type == "code"
        for output in cell.get("outputs", [])
        if output.output_type == "stream"
    )


def _assert_rows(output: str, rows: list[str]) -> None:
    for row in rows:
        assert output.count(row) == 2


def _assert_notebook_scope(output: str) -> None:
    assert "catalog provenance=gentle_tree" in output
    assert "atlas enumeration: status=complete, verification=computed" in output
    assert "atlas artifact: status=complete, verification=unverified" in output
    assert "replayed status=complete, verification=replayed" in output
    assert "cut: status=cut, verification=computed; artifact status=cut, replayed status=cut" in output
    assert "separated simples self_ext=[2, 0, 1, 0]" in output
    _assert_rows(output, EXPECTED_RAW_ROWS)
    _assert_rows(output, EXPECTED_ATLAS_ROWS)


def _assert_script_artifacts(output: str, directory: Path) -> None:
    assert "atlas artifact: status=complete" in output
    _assert_rows(output, EXPECTED_RAW_ROWS)
    _assert_rows(output, EXPECTED_ATLAS_ROWS)
    for field in (2, 5):
        artifact = directory / f"gentle-f{field}-atlas.json"
        report = directory / f"gentle-f{field}-atlas-report.md"
        assert artifact.is_file()
        assert report.is_file()
        document = json.loads(artifact.read_text(encoding="utf-8"))
        assert document["kind"] == "catalog-atlas-v1"
        assert "verification: replayed" in report.read_text(encoding="utf-8")


def test_catalog_notebook_executes_with_the_current_interpreter(
    tmp_path: Path,
    monkeypatch,
) -> None:
    """The committed notebook runs without repository import paths."""
    notebook = nbformat.read(NOTEBOOK, as_version=4)
    client = NotebookClient(
        notebook,
        timeout=180,
        kernel_name=_current_kernel(tmp_path, monkeypatch),
        resources={"metadata": {"path": str(EXAMPLES)}},
    )
    client.execute()
    _assert_notebook_scope(_notebook_output(notebook))


def test_catalog_script_writes_replayed_atlas_artifacts_from_the_installed_package(
    tmp_path: Path,
) -> None:
    """The script writes one canonical atlas report and artifact per field."""
    environment = os.environ.copy()
    environment.pop("PYTHONPATH", None)
    completed = subprocess.run(
        [sys.executable, str(SCRIPT), str(tmp_path)],
        cwd=tmp_path,
        env=environment,
        check=True,
        capture_output=True,
        text=True,
    )

    _assert_script_artifacts(completed.stdout, tmp_path)

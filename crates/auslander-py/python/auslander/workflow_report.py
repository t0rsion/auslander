"""Inspect and export workflow values."""

from __future__ import annotations

import csv
import io
import json
from pathlib import Path
from typing import Any

from ._core import CensusCheckpoint
from .workflow import (
    VerifiedWorkflowResult,
    WorkflowDefinition,
    WorkflowInspection,
    WorkflowResult,
    _homological_data,
    _row_record,
)
from .workflow_io import _load_value, _portable_kind


def inspect(source: Any, limits: Any | None = None) -> WorkflowInspection:
    """Inspect a definition or portable checkpoint without replaying it."""
    kind, value, verification = _load_value(source, limits)
    if kind == "definition":
        return WorkflowInspection(
            kind,
            "declared",
            verification,
            value.scope.as_dict(),
            None,
            value,
        )
    if kind == "workflow":
        return _workflow_inspection(value)
    return _portable_inspection(kind, value, verification)


def _workflow_inspection(
    value: WorkflowResult | VerifiedWorkflowResult,
) -> WorkflowInspection:
    return WorkflowInspection(
        "workflow",
        value.status,
        "replayed" if isinstance(value, VerifiedWorkflowResult) else "computed",
        value.scope,
        value.fingerprint,
        value,
    )


def _portable_inspection(kind: str, value: Any, verification: str) -> WorkflowInspection:
    if kind == "census":
        scope = _census_scope(value)
    elif kind == "homological":
        data = _homological_data(value)
        scope = _homological_scope(data, _census_from_homology(data))
    else:
        checkpoint = value.checkpoint
        data = _homological_data(checkpoint)
        scope = _homological_scope(data, _census_from_homology(data))
        scope.update(
            {
                "first_degree": value.first_degree,
                "last_degree": value.last_degree,
                "vanishing_indices": value.vanishing_indices,
            }
        )
    status = _homological_data(value.checkpoint).status if kind == "theorem" else value.status
    return WorkflowInspection(
        kind,
        status,
        verification,
        scope,
        value.fingerprint,
        value,
    )


def _census_scope(value: Any) -> dict[str, Any]:
    return {
        "field": value.field,
        "dimensions": value.dimensions,
        "first_degree": None,
        "last_degree": None,
        "kind": "finite_raw_matrix_domain",
        "raw_space_size": value.raw_space_size,
        "census_cursor": value.cursor,
        "census_candidates": value.candidates,
        "accepted_modules": value.accepted_modules,
        "representatives": value.representative_count,
    }


def _census_from_homology(value: Any) -> CensusCheckpoint:
    return CensusCheckpoint(_homological_data(value).census_json)


def _homological_scope(value: Any, census: Any) -> dict[str, Any]:
    return {
        "field": census.field,
        "dimensions": census.dimensions,
        "first_degree": 1,
        "last_degree": value.max_degree,
        "kind": "finite_raw_matrix_domain",
        "raw_space_size": census.raw_space_size,
        "census_cursor": census.cursor,
        "census_candidates": census.candidates,
        "accepted_modules": census.accepted_modules,
        "representatives": census.representative_count,
        "homological_cursor": value.next_source,
        "rows": value.row_count,
        "max_degree": value.max_degree,
        "chunks": value.work.chunks,
        "chunk_sizes": value.chunk_sizes,
    }


def inspection_text(inspection: WorkflowInspection) -> str:
    """Render one inspection as line-oriented text."""
    lines = [
        f"kind: {inspection.kind}",
        f"status: {inspection.status}",
        f"verification: {inspection.verification}",
        f"accepted: {'yes' if inspection.accepted else 'no'}",
    ]
    lines.extend(f"{key}: {value}" for key, value in inspection.scope.items())
    if inspection.fingerprint is not None:
        lines.append(f"fingerprint: {inspection.fingerprint}")
    return "\n".join(lines)


def export(
    source: Any,
    output: str | Path | None = None,
    *,
    format: str = "markdown",
    verify_value: bool = False,
) -> str:
    """Export a bounded Ext table and scope report as Markdown or CSV."""
    value = _verified_source(source) if verify_value else source
    inspection = inspect(value)
    text = _export_text(inspection, format)
    if output is not None:
        Path(output).write_text(text, encoding="utf-8", newline="\n")
    return text


def _verified_source(source: Any) -> Any:
    from .workflow_io import verify

    return verify(source)


def _export_text(inspection: WorkflowInspection, format: str) -> str:
    if format == "markdown":
        return _markdown_report(inspection)
    if format == "csv":
        return _csv_report(inspection)
    raise ValueError("format must be 'markdown' or 'csv'")


def _report_rows(inspection: WorkflowInspection) -> list[dict[str, Any]]:
    value = inspection.value
    if isinstance(value, (WorkflowResult, VerifiedWorkflowResult)):
        return value.rows()
    kind = _portable_kind(value)
    if kind == "homological":
        data = _homological_data(value)
        census = _census_from_homology(data)
        representatives = census.representatives
        return [_row_record(row, representatives) for row in data.rows]
    if kind == "theorem":
        checkpoint = _homological_data(value.checkpoint)
        census = _census_from_homology(checkpoint)
        representatives = census.representatives
        return [_row_record(row, representatives) for row in checkpoint.rows]
    return []


def _ext_headers(rows: list[dict[str, Any]], scope: dict[str, Any]) -> list[str]:
    degree = scope.get("max_degree")
    if degree is None:
        degree = max((len(row["ext_dimensions"]) - 1 for row in rows), default=-1)
    return [f"Ext^{index}" for index in range(degree + 1)]


def _markdown_report(inspection: WorkflowInspection) -> str:
    scope = inspection.scope
    lines = [
        "# Auslander computation report",
        "",
        f"kind: {inspection.kind}",
        f"status: {inspection.status}",
        f"verification: {inspection.verification}",
        f"scope: {scope.get('kind', 'finite_raw_matrix_domain')}",
        f"field: F_{scope.get('field')}",
        f"dimensions: {scope.get('dimensions')}",
        f"raw_space_size: {scope.get('raw_space_size')}",
        f"representatives: {scope.get('representatives')}",
        f"census_cursor: {scope.get('census_cursor')}",
    ]
    if "homological_cursor" in scope:
        lines.append(f"next_source: {scope['homological_cursor']}")
        lines.append(f"rows: {scope['rows']}")
    if scope.get("first_degree") is not None:
        lines.append(f"degrees: {scope['first_degree']}..{scope['last_degree']}")
    if inspection.fingerprint is not None:
        lines.append(f"fingerprint: {inspection.fingerprint}")
    claim = _claim(inspection)
    lines.append(f"claim: {claim}")
    rows = _report_rows(inspection)
    if rows:
        headers = ["index", "coordinates"] + _ext_headers(rows, scope)
        lines.extend(["", "| " + " | ".join(headers) + " |"])
        lines.append("| " + " | ".join("---" for _ in headers) + " |")
        for row in rows:
            cells = [str(row["index"]), str(row["coordinates"])]
            cells.extend(str(value) for value in row["ext_dimensions"])
            lines.append("| " + " | ".join(cells) + " |")
    artifact = _artifact_value(inspection.value)
    if artifact is not None:
        lines.extend(
            [
                "",
                f"vanishing_indices: {artifact.vanishing_indices}",
                f"vanishing_count: {artifact.vanishing_count}",
            ]
        )
    return "\n".join(lines) + "\n"


def _csv_report(inspection: WorkflowInspection) -> str:
    rows = _report_rows(inspection)
    ext_headers = _ext_headers(rows, inspection.scope)
    headers = [
        "record_type",
        "status",
        "verification",
        "field",
        "dimensions",
        "first_degree",
        "last_degree",
        "raw_space_size",
        "total_representatives",
        "census_cursor",
        "next_source",
        "rows",
        "index",
        "coordinates",
        *ext_headers,
    ]
    output = io.StringIO(newline="")
    writer = csv.writer(output, lineterminator="\n")
    writer.writerow(headers)
    scope = inspection.scope
    writer.writerow(
        [
            "metadata",
            inspection.status,
            inspection.verification,
            scope.get("field"),
            json.dumps(scope.get("dimensions"), separators=(",", ":")),
            scope.get("first_degree"),
            scope.get("last_degree"),
            scope.get("raw_space_size"),
            scope.get("representatives"),
            scope.get("census_cursor"),
            scope.get("homological_cursor"),
            scope.get("rows", 0),
            "",
            "",
            *([""] * len(ext_headers)),
        ]
    )
    for row in rows:
        writer.writerow(
            [
                "row",
                "",
                "",
                "",
                "",
                "",
                "",
                "",
                "",
                "",
                "",
                "",
                row["index"],
                json.dumps(row["coordinates"], separators=(",", ":")),
            ]
            + row["ext_dimensions"]
        )
    return output.getvalue()


def _claim(inspection: WorkflowInspection) -> str:
    if not inspection.accepted:
        return "declared by the portable value"
    if inspection.status == "complete":
        return "replay verified within the finite scope"
    return "replay verified prefix"


def _artifact_value(value: Any) -> Any | None:
    if isinstance(value, (WorkflowResult, VerifiedWorkflowResult)):
        return value.artifact
    return value if _portable_kind(value) == "theorem" else None

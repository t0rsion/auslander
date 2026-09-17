"""Inspect catalog atlas scope and export multiplicity scores."""

from __future__ import annotations

import csv
import io
import json
from typing import Any

from .workflow import WorkflowInspection


def atlas_inspection(value: Any, verification: str) -> WorkflowInspection:
    """Describe a parsed or replayed atlas without changing its status."""
    scope = {
        "kind": "catalog_multiplicities",
        "field": value.field,
        "provenance": value.provenance,
        "catalog_entries": len(value.catalog_ids),
        "dimensions": value.target_dimensions,
        "first_degree": 0,
        "last_degree": value.max_degree,
        "rows": len(value.result_rows),
        "cut_reason": _cut_reason(value),
    }
    return WorkflowInspection(
        "atlas", value.status, verification, scope, value.fingerprint, value
    )


def _cut_reason(value: Any) -> dict[str, Any] | None:
    reason = value.cut_reason
    if reason is None:
        return None
    return {"kind": reason.kind, "limit": reason.limit}


def atlas_report(inspection: WorkflowInspection, format: str) -> str:
    """Render atlas multiplicities with their finite scope and replay state."""
    if format == "markdown":
        return _markdown(inspection)
    if format == "csv":
        return _csv(inspection)
    raise ValueError("format must be 'markdown' or 'csv'")


def _claim(inspection: WorkflowInspection) -> str:
    if not inspection.accepted:
        return "stored claim, awaiting replay"
    if inspection.status == "complete":
        return "complete multiplicity enumeration, replayed within the stated scope"
    return "exact multiplicity prefix, replayed through the recorded cut"


def _ext_headers(inspection: WorkflowInspection) -> list[str]:
    return [f"Ext^{degree}" for degree in range(inspection.value.max_degree + 1)]


def _markdown(inspection: WorkflowInspection) -> str:
    lines = [
        "# Catalog atlas report",
        "",
        f"status: {inspection.status}",
        f"verification: {inspection.verification}",
    ]
    lines.extend(f"{key}: {value}" for key, value in inspection.scope.items())
    lines.extend([
        f"fingerprint: {inspection.fingerprint}",
        f"claim: {_claim(inspection)}",
        "",
        "Multiplicities follow the stored catalog order. Ext rows are self-pairs.",
        "",
    ])
    headers = ["index", "multiplicities", *_ext_headers(inspection)]
    lines.append("| " + " | ".join(headers) + " |")
    lines.append("| " + " | ".join("---" for _ in headers) + " |")
    for index, row in enumerate(inspection.value.result_rows):
        cells = [str(index), str(row.multiplicities), *map(str, row.self_ext)]
        lines.append("| " + " | ".join(cells) + " |")
    return "\n".join(lines) + "\n"


def _csv(inspection: WorkflowInspection) -> str:
    metadata = {
        "status": inspection.status,
        "verification": inspection.verification,
        **inspection.scope,
        "fingerprint": inspection.fingerprint,
    }
    output = io.StringIO(newline="")
    headers = [
        "record_type", *metadata, "index", "multiplicities", *_ext_headers(inspection)
    ]
    writer = csv.DictWriter(output, fieldnames=headers, lineterminator="\n")
    writer.writeheader()
    writer.writerow({"record_type": "metadata", **_csv_metadata(metadata)})
    for index, row in enumerate(inspection.value.result_rows):
        record = {
            "record_type": "row",
            "index": index,
            "multiplicities": json.dumps(row.multiplicities, separators=(",", ":")),
        }
        record.update(zip(_ext_headers(inspection), row.self_ext))
        writer.writerow(record)
    return output.getvalue()


def _csv_metadata(metadata: dict[str, Any]) -> dict[str, Any]:
    return {
        key: json.dumps(value, separators=(",", ":"))
        if isinstance(value, (list, dict)) else value
        for key, value in metadata.items()
    }

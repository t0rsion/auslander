"""Run the v0.9 gentle-tree catalog and atlas workflow."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import auslander

PRESENTATION = """
field {field}
vertices 0 1 2 3
arrows a:0->1 b:1->2 c:3->2
relations a*b = 0
"""
FIELDS = (2, 5)
TARGET_DIMENSIONS = [1, 1, 1, 1]
DEGREE_BOUND = 3


def build_algebra(field: int) -> auslander.Algebra:
    """Build the field-bound gentle-tree algebra for one prime field."""
    parsed = auslander.parse_presentation(PRESENTATION.format(field=field))
    algebra = parsed.build()
    if algebra.field is None or algebra.field.p != field:
        raise RuntimeError("the parsed presentation did not produce a field-bound algebra")
    return algebra


def _module_from_scalars(algebra: auslander.Algebra, scalars: list[int]) -> Any:
    """Build a thin module from the three arrow scalars."""
    if len(scalars) != algebra.num_arrows:
        raise ValueError("the gentle example has one scalar for each arrow")
    maps = [[[scalar]] for scalar in scalars]
    return algebra.module(TARGET_DIMENSIONS, maps)


def _raw_records(algebra: auslander.Algebra, checkpoint: Any) -> list[dict[str, Any]]:
    """Compute self-Ext rows for the retained raw census representatives."""
    records = []
    for representative in checkpoint.representatives:
        scalars = representative.coordinates
        module = _module_from_scalars(algebra, scalars)
        records.append(
            {
                "arrow_scalars": scalars,
                "self_ext": module.ext_table(module, DEGREE_BOUND),
            }
        )
    return records


def _raw_scope(verified: Any) -> dict[str, Any]:
    """Select stable scope fields for the independent raw census."""
    inspection = auslander.inspect(verified)
    names = (
        "field",
        "dimensions",
        "first_degree",
        "last_degree",
        "raw_space_size",
        "representatives",
    )
    return {name: inspection.scope.get(name) for name in names}


def _atlas_scope(atlas: Any) -> dict[str, Any]:
    """Select stable scope fields for the cached catalog atlas."""
    return {
        "field": atlas.field,
        "provenance": atlas.provenance,
        "catalog_entries": len(atlas),
        "dimensions": TARGET_DIMENSIONS,
        "first_degree": 0,
        "last_degree": atlas.max_degree,
        "pairs": atlas.work.pairs,
        "ext_cells": atlas.work.ext_cells,
    }


def _atlas_rows(atlas: Any, enumeration: Any) -> list[dict[str, Any]]:
    """Compute cached self-Ext scores and materialized dimensions per solution."""
    rows = []
    for multiplicities in enumeration.solutions:
        module = atlas.materialize(multiplicities)
        rows.append(
            {
                "multiplicities": multiplicities,
                "self_ext": atlas.self_ext_scores(multiplicities),
                "materialized_dimensions": module.dims,
            }
        )
    return rows


def _atlas_report(verified: Any) -> str:
    """Render one replayed atlas artifact as a short Markdown report."""
    artifact = verified.artifact
    lines = [
        "# Catalog atlas report",
        "",
        f"field: F_{artifact.field}",
        f"provenance: {artifact.provenance}",
        f"status: {verified.status}",
        f"verification: {verified.verification}",
        f"target dimensions: {artifact.target_dimensions}",
        f"max degree: {artifact.max_degree}",
        f"catalog entries: {artifact.catalog_len}",
        f"fingerprint: {artifact.fingerprint}",
        "",
        "| index | multiplicities | self-Ext |",
        "| ---: | --- | --- |",
    ]
    lines.extend(
        f"| {index} | {row.multiplicities} | {row.self_ext} |"
        for index, row in enumerate(artifact.result_rows)
    )
    return "\n".join(lines) + "\n"


def _complete_run(field: int, output_dir: Path) -> dict[str, Any]:
    """Build, enumerate, materialize, export, and replay one complete atlas."""
    algebra = build_algebra(field)
    catalog = auslander.catalog(algebra)
    atlas = catalog.atlas(DEGREE_BOUND)
    enumeration = atlas.enumerate(TARGET_DIMENSIONS)
    if enumeration.status != "complete":
        raise RuntimeError("the gentle-tree atlas enumeration did not complete")
    atlas_rows = _atlas_rows(atlas, enumeration)

    artifact = atlas.export(TARGET_DIMENSIONS)
    artifact_text = artifact.canonical_json
    parsed_artifact = auslander.CatalogAtlasArtifact(artifact_text)
    replayed_artifact = auslander.verify_catalog_atlas_artifact(artifact_text)
    if parsed_artifact.status != "complete" or replayed_artifact.status != "complete":
        raise RuntimeError("the complete atlas artifact changed status during replay")

    artifact_path = output_dir / f"gentle-f{field}-atlas.json"
    report_path = output_dir / f"gentle-f{field}-atlas-report.md"
    artifact_path.write_text(artifact_text, encoding="utf-8")
    report_path.write_text(_atlas_report(replayed_artifact), encoding="utf-8")

    definition = auslander.define(
        PRESENTATION.format(field=field),
        TARGET_DIMENSIONS,
        last_degree=DEGREE_BOUND,
    )
    raw_result = auslander.compute(
        definition,
        census_limits=auslander.CensusLimits(
            retention="all_assignments",
            max_assignments=256,
        ),
        stream_config=auslander.HomologicalStreamConfig(max_live_sources=2),
    )
    if raw_result.status != "complete" or raw_result.homological is None:
        raise RuntimeError("the independent raw census did not complete")
    raw_verified = auslander.verify(raw_result)
    raw_records = _raw_records(algebra, raw_result.census)

    return {
        "field": field,
        "algebra": algebra,
        "catalog": catalog,
        "atlas": atlas,
        "enumeration": enumeration,
        "atlas_rows": atlas_rows,
        "atlas_scope": _atlas_scope(atlas),
        "artifact": parsed_artifact,
        "replayed_artifact": replayed_artifact,
        "artifact_path": artifact_path,
        "report_path": report_path,
        "definition": definition,
        "result": raw_result,
        "verified": raw_verified,
        "raw_records": raw_records,
        "records": raw_records,
        "scope": _raw_scope(raw_verified),
    }


def _cut_run(field: int) -> dict[str, Any]:
    """Export and replay a cut atlas while preserving its cut status."""
    algebra = build_algebra(field)
    catalog = auslander.catalog(algebra)
    atlas = catalog.atlas(DEGREE_BOUND)
    limits = auslander.MultiplicityLimits(max_solutions=1)
    cut = atlas.enumerate(TARGET_DIMENSIONS, limits)
    if cut.status != "cut":
        raise RuntimeError("the bounded atlas enumeration did not produce a cut")
    artifact = atlas.export(TARGET_DIMENSIONS, limits)
    parsed_artifact = auslander.CatalogAtlasArtifact(artifact.canonical_json)
    replayed = auslander.verify_catalog_atlas_artifact(artifact.canonical_json)
    if parsed_artifact.status != "cut" or replayed.status != "cut":
        raise RuntimeError("atlas replay upgraded a cut enumeration")
    return {
        "field": field,
        "atlas": atlas,
        "cut": cut,
        "artifact": parsed_artifact,
        "replayed": replayed,
    }


def _obstruction(algebra: auslander.Algebra) -> list[int]:
    """Compute the degree-two obstruction for the separated simples."""
    module = algebra.module([1, 0, 1, 0], [[[]], [], []])
    return module.ext_table(module, DEGREE_BOUND)


def run(output_dir: str | Path = "catalog-workflow-output") -> dict[str, Any]:
    """Run both fields, write replayable atlas artifacts, and return the results."""
    output = Path(output_dir)
    output.mkdir(parents=True, exist_ok=True)
    fields = [_complete_run(field, output) for field in FIELDS]
    cut = _cut_run(FIELDS[0])
    obstruction = _obstruction(fields[0]["algebra"])
    return {"fields": fields, "cut": cut, "obstruction": obstruction}


def render(summary: dict[str, Any]) -> None:
    """Print catalog scope, atlas rows, raw witnesses, replay states, and obstruction."""
    for item in summary["fields"]:
        catalog = item["catalog"]
        atlas = item["atlas"]
        enumeration = item["enumeration"]
        artifact = item["artifact"]
        replayed_artifact = item["replayed_artifact"]
        print(
            f"field F_{item['field']}: catalog provenance={catalog.provenance}, "
            f"entries={len(catalog)}"
        )
        print(f"atlas scope: {json.dumps(item['atlas_scope'], sort_keys=True)}")
        print(
            f"atlas enumeration: status={enumeration.status}, "
            f"verification={enumeration.verification}, solutions={len(enumeration)}"
        )
        print(
            f"atlas cache: pairs={atlas.work.pairs}, ext_cells={atlas.work.ext_cells}, "
            f"max_degree={atlas.max_degree}"
        )
        for row in item["atlas_rows"]:
            print(
                f"atlas row: multiplicities={row['multiplicities']}, "
                f"self_ext={row['self_ext']}, "
                f"materialized_dims={row['materialized_dimensions']}"
            )
        print(
            f"atlas artifact: status={artifact.status}, verification={artifact.verification}; "
            f"replayed status={replayed_artifact.status}, "
            f"verification={replayed_artifact.verification}, "
            f"report={item['report_path'].name}"
        )

        verified = item["verified"]
        print(f"raw census scope: {json.dumps(item['scope'], sort_keys=True)}")
        print(f"raw census: status={verified.status}, verification={verified.verification}")
        representative = item["result"].census.representatives[0]
        module = _module_from_scalars(item["algebra"], representative.coordinates)
        print(f"raw witness representative: {representative.coordinates}")
        print(str(auslander.show(module)))
        assignments = item["result"].census.assignments
        if assignments:
            assignment = assignments[0]
            print(
                "raw witness isomorphism: "
                f"coordinates={assignment.coordinates}, "
                f"representative={assignment.representative}, "
                f"maps={assignment.witness}"
            )
        for record in item["raw_records"]:
            print(
                f"row: scalars={record['arrow_scalars']}, "
                f"self_ext={record['self_ext']}"
            )

    cut = summary["cut"]
    print(
        f"cut: status={cut['cut'].status}, verification={cut['cut'].verification}; "
        f"artifact status={cut['artifact'].status}, "
        f"replayed status={cut['replayed'].status}, "
        f"verification={cut['replayed'].verification}"
    )
    print(f"separated simples self_ext={summary['obstruction']}")


def main() -> None:
    """Run the example and print its finite-scope evidence."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "directory",
        nargs="?",
        type=Path,
        default=Path("catalog-workflow-output"),
    )
    render(run(parser.parse_args().directory))


if __name__ == "__main__":
    main()

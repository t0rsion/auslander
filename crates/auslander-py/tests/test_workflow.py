"""End-to-end tests for the finite definition and self-Ext workflow."""

import csv
import io
from pathlib import Path

import pytest

import auslander


PRESENTATION = """
field 2
vertices 0 1
arrows a:0->1
"""

OTHER_PRESENTATION = """
field 2
vertices 0 1
arrows b:1->0
"""


def _definition() -> auslander.WorkflowDefinition:
    return auslander.define(PRESENTATION, [1, 1], last_degree=2)


def _stream_config() -> auslander.HomologicalStreamConfig:
    return auslander.HomologicalStreamConfig(max_live_sources=1)


def _complete_workflow() -> tuple[
    auslander.WorkflowResult,
    auslander.VerifiedWorkflowResult,
]:
    result = auslander.compute(
        _definition(),
        census_limits=auslander.CensusLimits(retention="representatives_only"),
        stream_config=_stream_config(),
    )
    return result, auslander.verify(result)


def test_definition_normalizes_mutable_constructor_values() -> None:
    dimensions = [1, 1]
    definition = auslander.WorkflowDefinition(PRESENTATION, 2, dimensions)
    dimensions.append(9)

    assert definition.field == 2
    assert definition.dimensions == (1, 1)
    assert definition.scope.dimensions == (1, 1)


def test_workflow_cut_and_checkpoint_scope(tmp_path: Path) -> None:
    definition = _definition()
    retained = "representatives_only"
    cut = auslander.compute(
        definition,
        census_limits=auslander.CensusLimits(
            max_candidates=1,
            retention=retained,
        ),
        stream_config=_stream_config(),
    )

    assert cut.status == "cut"
    assert cut.homological is None
    assert cut.scope["raw_space_size"] == 2
    cut_path = tmp_path / "cut.json"
    auslander.checkpoint(cut, cut_path)
    parsed = auslander.inspect(cut_path)
    assert parsed.kind == "census"
    assert parsed.status == "cut"
    assert parsed.verification == "unverified"
    assert not parsed.accepted


def test_workflow_resume_completes_all_stages() -> None:
    definition = _definition()
    retained = "representatives_only"
    cut = auslander.compute(
        definition,
        census_limits=auslander.CensusLimits(
            max_candidates=1,
            retention=retained,
        ),
        stream_config=_stream_config(),
    )
    resumed = auslander.resume(
        cut,
        census_limits=auslander.CensusLimits(
            max_candidates=2,
            retention=retained,
        ),
    )
    assert isinstance(resumed, auslander.WorkflowResult)
    assert resumed.status == "complete"
    assert resumed.homological is not None
    assert resumed.artifact is not None
    assert resumed.scope["representatives"] == 2


def test_workflow_verification_preserves_scope_and_rows() -> None:
    resumed, verified = _complete_workflow()
    assert isinstance(verified, auslander.VerifiedWorkflowResult)
    assert verified.status == "complete"
    assert resumed.verification == "computed"
    assert verified.verification == "replayed"
    assert verified.scope == resumed.scope
    assert verified.rows() == resumed.rows()


def test_workflow_rejects_limits_for_in_memory_values() -> None:
    resumed, verified = _complete_workflow()
    with pytest.raises(TypeError):
        auslander.verify(resumed, auslander.CensusVerifyLimits())
    with pytest.raises(TypeError):
        auslander.verify(verified, auslander.CensusVerifyLimits())
    with pytest.raises(TypeError):
        auslander.inspect(resumed, auslander.CensusVerifyLimits())
    with pytest.raises(TypeError):
        auslander.inspect(verified, auslander.CensusVerifyLimits())


def test_workflow_constructors_enforce_cross_stage_bindings() -> None:
    result, verified = _complete_workflow()
    other_definition = auslander.define(OTHER_PRESENTATION, [1, 1], last_degree=2)

    with pytest.raises(ValueError, match="presentation"):
        auslander.WorkflowResult(other_definition, result.census)

    alternate = auslander.compute(
        _definition(),
        census_limits=auslander.CensusLimits(retention="all_assignments"),
        stream_config=_stream_config(),
    )
    assert alternate.homological is not None
    assert alternate.artifact is not None
    with pytest.raises(ValueError, match="census fingerprint"):
        auslander.WorkflowResult(_definition(), result.census, alternate.homological)

    with pytest.raises(TypeError, match="VerifiedCensusCheckpoint"):
        auslander.VerifiedWorkflowResult(
            result,
            result.census,
            verified.homological,
            verified.artifact,
        )

    alternate_verified = auslander.verify(alternate)
    with pytest.raises(ValueError, match="verified census stage"):
        auslander.VerifiedWorkflowResult(
            result,
            alternate_verified.census,
            alternate_verified.homological,
            alternate_verified.artifact,
        )


def test_workflow_repeated_compute_preserves_rows() -> None:
    resumed, _ = _complete_workflow()
    direct = auslander.compute(
        _definition(),
        census_limits=auslander.CensusLimits(retention="representatives_only"),
        stream_config=_stream_config(),
    )
    assert direct.rows() == resumed.rows()


def test_workflow_checkpoint_stages_preserve_kinds(tmp_path: Path) -> None:
    resumed, verified = _complete_workflow()
    homological_path = tmp_path / "homological.json"
    auslander.checkpoint(resumed, homological_path, stage="homological")
    assert auslander.inspect(homological_path).kind == "homological"
    artifact_path = tmp_path / "artifact.json"
    auslander.checkpoint(verified, artifact_path, stage="artifact")
    artifact_inspection = auslander.inspect(artifact_path)
    assert artifact_inspection.kind == "theorem"
    assert artifact_inspection.verification == "unverified"


def test_workflow_markdown_export_reports_verified_scope() -> None:
    _, verified = _complete_workflow()
    report = auslander.export(verified, format="markdown")
    assert "claim: replay verified within the finite scope" in report
    assert "Ext^2" in report


def test_workflow_csv_export_has_metadata_record() -> None:
    _, verified = _complete_workflow()
    csv_report = auslander.export(verified, format="csv")
    assert csv_report.splitlines()[0] == (
        "record_type,status,verification,field,dimensions,first_degree,last_degree,"
        "raw_space_size,total_representatives,census_cursor,next_source,rows,index,"
        "coordinates,Ext^0,Ext^1,Ext^2"
    )
    records = list(csv.DictReader(io.StringIO(csv_report)))
    assert records[0]["record_type"] == "metadata"
    assert records[0]["status"] == "complete"
    assert records[0]["verification"] == "replayed"


def test_workflow_csv_export_metadata_describes_scope() -> None:
    _, verified = _complete_workflow()
    csv_report = auslander.export(verified, format="csv")
    records = list(csv.DictReader(io.StringIO(csv_report)))
    assert records[0]["dimensions"] == "[1,1]"
    assert records[0]["first_degree"] == "1"
    assert records[0]["last_degree"] == "2"
    assert records[0]["total_representatives"] == "2"
    assert records[0]["next_source"] == "2"
    assert records[0]["rows"] == "2"
    assert records[1]["record_type"] == "row"


def test_workflow_rejects_tampered_homological_checkpoint(tmp_path: Path) -> None:
    resumed, _ = _complete_workflow()
    tampered = tmp_path / "tampered.json"
    homological_path = tmp_path / "homological.json"
    auslander.checkpoint(resumed, homological_path, stage="homological")
    text = homological_path.read_text(encoding="utf-8")
    tampered.write_text(
        text.replace(resumed.homological.fingerprint, "0" * 16, 1),
        encoding="utf-8",
    )
    with pytest.raises(ValueError):
        auslander.verify(tampered)


def test_homological_partial_chunk_resume_replays(tmp_path: Path) -> None:
    definition = _definition()
    cut = auslander.compute(
        definition,
        census_limits=auslander.CensusLimits(retention="representatives_only"),
        stream_config=auslander.HomologicalStreamConfig(
            max_live_sources=2,
            max_sources=1,
        ),
    )

    assert cut.status == "cut"
    assert cut.homological is not None
    assert cut.homological.next_source == 1
    assert cut.homological.chunk_sizes == [1]
    resumed = auslander.resume(
        cut,
        output=tmp_path / "resumed.json",
        budget=auslander.HomologicalStreamBudget(max_sources=2),
    )
    assert isinstance(resumed, auslander.WorkflowResult)
    assert resumed.status == "complete"
    assert resumed.homological is not None
    assert resumed.homological.chunk_sizes == [1, 1]
    verified = auslander.verify(resumed)
    assert verified.rows() == resumed.rows()


def test_workflow_cli_defines_and_inspects_a_definition(tmp_path: Path, capsys) -> None:
    from auslander.__main__ import main

    presentation = tmp_path / "presentation.txt"
    presentation.write_text(PRESENTATION, encoding="utf-8")
    definition = tmp_path / "definition.json"
    assert main(
        [
            "workflow",
            "define",
            str(presentation),
            "[1,1]",
            str(definition),
        ]
    ) == 0
    assert main(["workflow", "inspect", str(definition)]) == 0
    output = capsys.readouterr().out
    assert "kind: definition" in output
    assert "first_degree: 1" in output

    checkpoint = tmp_path / "checkpoint.json"
    assert main(
        [
            "workflow",
            "compute",
            str(definition),
            str(checkpoint),
            "--retention",
            "representatives_only",
            "--max-live-sources",
            "1",
        ]
    ) == 0
    cli_output = capsys.readouterr().out
    written = auslander.inspect(checkpoint)
    assert f"fingerprint {written.fingerprint}" in cli_output

"""Read, verify, resume, and write portable workflow values."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from ._core import (
    CensusCheckpoint,
    CensusVerifyLimits,
    HomologicalCheckpoint,
    HomologicalStreamBudget,
    HomologicalStreamVerifyLimits,
    SelfExtLocusArtifact,
    SelfExtLocusVerifyLimits,
    VerifiedCensusCheckpoint,
    VerifiedHomologicalCheckpoint,
    VerifiedSelfExtLocusArtifact,
)
from .checkpoint import (
    _read_utf8_bounded,
    _write_canonical_json,
    write_checkpoint,
)
from .theorem import write_theorem_artifact
from .workflow import (
    DEFINITION_KIND,
    DEFINITION_SCHEMA,
    VerifiedWorkflowResult,
    WorkflowDefinition,
    WorkflowResult,
    _artifact_for,
    _drain_stream,
    _start_stream,
    _stream_config,
)


def _portable_kind(value: Any) -> str | None:
    kinds = (
        ("census", (CensusCheckpoint, VerifiedCensusCheckpoint)),
        ("homological", (HomologicalCheckpoint, VerifiedHomologicalCheckpoint)),
        ("theorem", (SelfExtLocusArtifact, VerifiedSelfExtLocusArtifact)),
    )
    for kind, classes in kinds:
        if isinstance(value, classes):
            return kind
    return None


def _text_value(source: str | Path) -> str:
    return _read_utf8_bounded(source, _default_input_bytes(), "portable value")


def _default_input_bytes() -> int:
    return max(
        CensusVerifyLimits().max_input_bytes,
        HomologicalStreamVerifyLimits().max_input_bytes,
        SelfExtLocusVerifyLimits().max_input_bytes,
    )


def _bounded_text(source: str | Path, limits: Any | None) -> str:
    _validate_limit_type(limits)
    maximum = _default_input_bytes()
    if limits is not None:
        maximum = getattr(limits, "max_input_bytes", maximum)
    if isinstance(maximum, bool) or not isinstance(maximum, int) or maximum < 0:
        raise TypeError("limits.max_input_bytes must be a nonnegative integer")
    return _read_utf8_bounded(source, maximum, "portable value")


def _validate_limit_type(limits: Any | None) -> None:
    if limits is None or isinstance(
        limits,
        (CensusVerifyLimits, HomologicalStreamVerifyLimits, SelfExtLocusVerifyLimits),
    ):
        return
    raise TypeError(
        "limits must be a CensusVerifyLimits, HomologicalStreamVerifyLimits, "
        "or SelfExtLocusVerifyLimits"
    )


def _validate_kind_limits(kind: str, limits: Any | None) -> None:
    if limits is None:
        return
    expected = {
        "census": CensusVerifyLimits,
        "homological": HomologicalStreamVerifyLimits,
        "theorem": SelfExtLocusVerifyLimits,
    }.get(kind)
    if expected is not None and not isinstance(limits, expected):
        raise TypeError(f"limits must be a {expected.__name__} for a {kind}")


def _json_kind(text: str) -> str:
    try:
        value = json.loads(text)
    except json.JSONDecodeError as error:
        raise ValueError(
            f"invalid portable JSON at line {error.lineno}, column {error.colno}"
        ) from None
    if not isinstance(value, dict):
        raise ValueError("portable value must be an object")
    return _schema_kind(value.get("schema"), value.get("kind"))


def _schema_kind(schema: Any, kind: Any) -> str:
    kinds = {
        (DEFINITION_SCHEMA, DEFINITION_KIND): "definition",
        ("auslander-computation-v1", "census-v1"): "census",
        (
            "auslander-computation-v1",
            "homological-self-pair-stream-v2",
        ): "homological",
        (
            "auslander-theorem-v1",
            "fixed-dimension-self-ext-locus-v1",
        ): "theorem",
    }
    result = kinds.get((schema, kind))
    if result is None:
        raise ValueError("unsupported portable value schema")
    return result


def _load_value(source: Any, limits: Any | None = None) -> tuple[str, Any, str]:
    if isinstance(source, WorkflowDefinition):
        return _in_memory_definition(source, limits)
    if isinstance(source, (WorkflowResult, VerifiedWorkflowResult)):
        return _in_memory_workflow(source, limits)
    kind = _portable_kind(source)
    if kind is not None:
        return _in_memory_portable(kind, source, limits)
    if not isinstance(source, (str, Path)):
        raise TypeError("source must be a workflow value or path")
    return _load_path(source, limits)


def _in_memory_definition(
    source: WorkflowDefinition,
    limits: Any | None,
) -> tuple[str, WorkflowDefinition, str]:
    if limits is not None:
        raise TypeError("limits do not apply to a workflow definition")
    return "definition", source, "unverified"


def _in_memory_workflow(
    source: WorkflowResult | VerifiedWorkflowResult,
    limits: Any | None,
) -> tuple[str, WorkflowResult | VerifiedWorkflowResult, str]:
    if limits is not None:
        raise TypeError("limits do not apply to an in-memory workflow")
    return "workflow", source, _workflow_verification(source)


def _in_memory_portable(
    kind: str,
    source: Any,
    limits: Any | None,
) -> tuple[str, Any, str]:
    _validate_kind_limits(kind, limits)
    return kind, source, _portable_verification(source)


def _load_path(
    source: str | Path,
    limits: Any | None,
) -> tuple[str, Any, str]:
    text = _bounded_text(source, limits)
    kind = _json_kind(text)
    if kind == "definition":
        if limits is not None:
            raise TypeError("limits do not apply to a workflow definition")
        return kind, WorkflowDefinition.from_json(text), "unverified"
    return _load_portable(kind, text, limits)


def _load_portable(
    kind: str,
    text: str,
    limits: Any | None,
) -> tuple[str, Any, str]:
    _validate_kind_limits(kind, limits)
    constructors = {
        "census": CensusCheckpoint,
        "homological": HomologicalCheckpoint,
        "theorem": SelfExtLocusArtifact,
    }
    constructor = constructors[kind]
    return kind, constructor(text, limits), "unverified"


def _portable_verification(value: Any) -> str:
    verified = (
        VerifiedCensusCheckpoint,
        VerifiedHomologicalCheckpoint,
        VerifiedSelfExtLocusArtifact,
    )
    return "replayed" if isinstance(value, verified) else "unverified"


def _workflow_verification(value: WorkflowResult | VerifiedWorkflowResult) -> str:
    if isinstance(value, VerifiedWorkflowResult):
        return "replayed"
    return "computed"


def checkpoint(
    value: Any,
    path: str | Path,
    *,
    stage: str = "latest",
) -> Path:
    """Write the selected portable value from a workflow atomically."""
    if stage not in {"latest", "census", "homological", "artifact"}:
        raise ValueError("stage must be 'latest', 'census', 'homological', or 'artifact'")
    if isinstance(value, WorkflowResult):
        value = _workflow_stage(value, stage)
    elif isinstance(value, VerifiedWorkflowResult):
        value = _workflow_stage(value, stage)
    elif stage != "latest":
        raise ValueError("stage applies only to a WorkflowResult")
    if isinstance(value, WorkflowDefinition):
        return _write_canonical_json(path, value.canonical_json)
    kind = _portable_kind(value)
    if kind is None:
        raise TypeError("value must be a workflow or portable checkpoint")
    if kind == "theorem":
        return write_theorem_artifact(path, value)
    return write_checkpoint(path, value)


def _workflow_stage(
    value: WorkflowResult | VerifiedWorkflowResult,
    stage: str,
) -> Any:
    if stage == "census":
        return value.census
    if stage in {"homological", "latest"} and value.homological is not None:
        return value.homological
    if stage == "artifact" and value.artifact is not None:
        return value.artifact
    if stage == "latest":
        return value.census
    raise ValueError(f"workflow has no {stage} checkpoint")


def verify(source: Any, limits: Any | None = None) -> Any:
    """Replay-verify a definition, checkpoint, theorem artifact, or workflow."""
    if isinstance(source, VerifiedWorkflowResult):
        if limits is not None:
            raise TypeError("limits cannot be applied to a verified workflow")
        return source
    if isinstance(source, WorkflowResult):
        if limits is not None:
            raise TypeError("limits cannot be applied to an in-memory workflow")
        return source.verify()
    kind, value, _ = _load_value(source, limits)
    if _portable_verification(value) == "replayed":
        if limits is not None:
            raise TypeError("limits cannot be applied to an already verified value")
        return value
    if kind == "definition":
        value.build()
        return value
    return value.verify(limits)


def resume(
    source: Any,
    output: str | Path | None = None,
    *,
    census_limits: Any | None = None,
    budget: Any | None = None,
    control: Any | None = None,
) -> Any:
    """Verify and resume a cut census, stream, or composed workflow."""
    if isinstance(source, VerifiedWorkflowResult):
        source = source.result
    if isinstance(source, WorkflowResult):
        result = _resume_workflow(source, census_limits, budget, control)
        if output is not None:
            checkpoint(result, output)
        return result
    kind, value, _ = _load_value(source)
    if kind == "census":
        if budget is not None:
            raise TypeError("budget applies only to a homological checkpoint")
        resumed = _resume_census(value, census_limits, control)
    elif kind == "homological":
        if census_limits is not None:
            raise TypeError("census_limits applies only to a census checkpoint")
        resumed = _resume_homological(value, budget, control)
    else:
        raise ValueError("only a cut census or homological checkpoint can resume")
    if output is not None:
        checkpoint(resumed, output)
    return resumed


def _resume_census(
    value: CensusCheckpoint | VerifiedCensusCheckpoint,
    limits: Any,
    control: Any,
) -> Any:
    verified = value if isinstance(value, VerifiedCensusCheckpoint) else value.verify()
    if limits is None:
        limits = _census_limits_for_resume(value)
    elif not isinstance(limits, type(verified.limits)):
        raise TypeError("census_limits must be a CensusLimits")
    return verified.resume(limits, control=control)


def _census_limits_for_resume(value: Any) -> Any:
    from ._core import CensusLimits

    return CensusLimits(retention=value.limits.retention)


def _resume_homological(
    value: HomologicalCheckpoint | VerifiedHomologicalCheckpoint,
    budget: HomologicalStreamBudget | None,
    control: Any,
) -> Any:
    if value.status != "cut":
        raise ValueError("only a cut homological checkpoint can resume")
    verified = value if isinstance(value, VerifiedHomologicalCheckpoint) else value.verify()
    stream = verified.resume(
        HomologicalStreamBudget() if budget is None else budget,
        control=control,
    )
    return _drain_stream(stream)


def _resume_workflow(
    source: WorkflowResult,
    census_limits: Any | None,
    budget: Any | None,
    control: Any,
) -> WorkflowResult:
    if source.homological is not None:
        if census_limits is not None:
            raise TypeError("census_limits applies only to a census checkpoint")
        homological = _resume_homological(source.homological, budget, control)
        return WorkflowResult(
            source.definition,
            source.census,
            homological,
            _artifact_for(source.definition, homological),
            source.stream_config,
        )
    if budget is not None:
        raise TypeError("budget applies only to a homological checkpoint")
    census = _resume_census(source.census, census_limits, control)
    if census.status != "complete":
        return WorkflowResult(source.definition, census, None, None, source.stream_config)
    config = _stream_config(source.stream_config)
    stream = _start_stream(source.definition, census.verify(), config, control)
    homological = _drain_stream(stream)
    return WorkflowResult(
        source.definition,
        census,
        homological,
        _artifact_for(source.definition, homological),
        config,
    )


def write_definition(path: str | Path, definition: WorkflowDefinition) -> Path:
    """Write one canonical workflow definition atomically."""
    if not isinstance(definition, WorkflowDefinition):
        raise TypeError("definition must be a WorkflowDefinition")
    return _write_canonical_json(path, definition.canonical_json)


def load_definition(path: str | Path) -> WorkflowDefinition:
    """Load one canonical workflow definition."""
    return WorkflowDefinition.from_json(_text_value(path))

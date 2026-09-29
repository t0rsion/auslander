"""Read, verify, resume, and write portable workflow values."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from ._core import (
    CatalogAtlasArtifact,
    CatalogAtlasArtifactVerifyLimits,
    CensusCheckpoint,
    CensusVerifyLimits,
    DerivedAtlasArtifact,
    HomologicalCheckpoint,
    HomologicalStreamBudget,
    HomologicalStreamVerifyLimits,
    SelfExtLocusArtifact,
    SelfExtLocusVerifyLimits,
    VerifiedCatalogAtlasArtifact,
    VerifiedCensusCheckpoint,
    VerifiedDerivedArtifact,
    VerifiedHomologicalCheckpoint,
    VerifiedSelfExtLocusArtifact,
    _header_kind,
    verify_catalog_atlas_artifact,
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

_KIND_LIMIT_TYPES = (
    ("census", CensusVerifyLimits),
    ("homological", HomologicalStreamVerifyLimits),
    ("theorem", SelfExtLocusVerifyLimits),
    ("atlas", CatalogAtlasArtifactVerifyLimits),
)
_PORTABLE_LOADERS = (
    ("census", CensusCheckpoint),
    ("homological", HomologicalCheckpoint),
    ("theorem", SelfExtLocusArtifact),
    ("atlas", CatalogAtlasArtifact),
    ("derived_atlas", lambda text, _limits: DerivedAtlasArtifact(text)),
)


def _portable_kind(value: Any) -> str | None:
    kinds = (
        ("census", (CensusCheckpoint, VerifiedCensusCheckpoint)),
        ("homological", (HomologicalCheckpoint, VerifiedHomologicalCheckpoint)),
        ("theorem", (SelfExtLocusArtifact, VerifiedSelfExtLocusArtifact)),
        ("atlas", (CatalogAtlasArtifact, VerifiedCatalogAtlasArtifact)),
        ("derived_atlas", (DerivedAtlasArtifact,)),
    )
    for kind, classes in kinds:
        if isinstance(value, classes):
            return kind
    if isinstance(value, VerifiedDerivedArtifact):
        return "derived"
    return None


def _text_value(source: str | Path) -> str:
    return _read_utf8_bounded(source, _default_input_bytes(), "portable value")


def _default_input_bytes() -> int:
    defaults = [
        CensusVerifyLimits().max_input_bytes,
        HomologicalStreamVerifyLimits().max_input_bytes,
        SelfExtLocusVerifyLimits().max_input_bytes,
    ]
    defaults.append(CatalogAtlasArtifactVerifyLimits().parse.max_input_bytes)
    defaults.append(DerivedAtlasArtifact.max_input_bytes)
    return max(defaults)


def _bounded_text(source: str | Path, limits: Any | None) -> str:
    _validate_limit_type(limits)
    maximum = _input_limit(limits)
    return _read_utf8_bounded(source, maximum, "portable value")


def _input_limit(limits: Any | None) -> int:
    maximum = _default_input_bytes()
    if isinstance(limits, CatalogAtlasArtifactVerifyLimits):
        maximum = limits.parse.max_input_bytes
    elif limits is not None:
        maximum = limits.max_input_bytes
    if isinstance(maximum, bool) or not isinstance(maximum, int) or maximum < 0:
        raise TypeError("limits.max_input_bytes must be a nonnegative integer")
    return maximum


def _validate_limit_type(limits: Any | None) -> None:
    types = (
        CensusVerifyLimits,
        HomologicalStreamVerifyLimits,
        SelfExtLocusVerifyLimits,
    )
    types += (CatalogAtlasArtifactVerifyLimits,)
    if limits is None or isinstance(limits, types):
        return
    raise TypeError(
        "limits must be a CensusVerifyLimits, HomologicalStreamVerifyLimits, "
        "SelfExtLocusVerifyLimits, or CatalogAtlasArtifactVerifyLimits"
    )


def _validate_kind_limits(kind: str, limits: Any | None) -> None:
    if limits is None:
        return
    if kind == "derived_atlas":
        raise TypeError("limits do not apply to a derived atlas")
    expected = _dispatch(_KIND_LIMIT_TYPES, kind)
    if expected is None:
        return
    if not isinstance(limits, expected):
        raise TypeError(f"limits must be a {expected.__name__} for a {kind}")


def _json_kind(text: str) -> str:
    try:
        return _header_kind(text)
    except ValueError:
        if _is_definition(text):
            return "definition"
        raise


def _is_definition(text: str) -> bool:
    # A definition has sorted keys, so its schema is not the first member
    # that the Rust header reader requires.
    try:
        value = json.loads(text)
    except ValueError:
        return False
    return (
        isinstance(value, dict)
        and value.get("schema") == DEFINITION_SCHEMA
        and value.get("kind") == DEFINITION_KIND
    )


def _dispatch(table: tuple[tuple[Any, Any], ...], key: Any) -> Any:
    return next((value for candidate, value in table if candidate == key), None)


def _verify_definition(text: str, limits: Any | None) -> WorkflowDefinition:
    if limits is not None:
        raise TypeError("limits do not apply to a workflow definition")
    return WorkflowDefinition.from_json(text)


def _verify_census(text: str, limits: Any | None) -> Any:
    _validate_kind_limits("census", limits)
    effective = CensusVerifyLimits() if limits is None else limits
    from ._core import verify_census_checkpoint

    return verify_census_checkpoint(text, effective)


def _verify_homological(text: str, limits: Any | None) -> Any:
    _validate_kind_limits("homological", limits)
    effective = HomologicalStreamVerifyLimits() if limits is None else limits
    from ._core import verify_homological_checkpoint

    return verify_homological_checkpoint(text, effective)


def _verify_theorem(text: str, limits: Any | None) -> Any:
    _validate_kind_limits("theorem", limits)
    effective = SelfExtLocusVerifyLimits() if limits is None else limits
    from ._core import verify_self_ext_locus_artifact

    return verify_self_ext_locus_artifact(text, effective)


def _verify_derived(text: str, limits: Any | None) -> Any:
    if limits is not None:
        raise TypeError("limits do not apply to a derived artifact")
    from ._core import verify_derived_artifact

    return verify_derived_artifact(text)


def _verify_atlas(text: str, limits: Any | None) -> Any:
    _validate_kind_limits("atlas", limits)
    effective = CatalogAtlasArtifactVerifyLimits() if limits is None else limits

    return verify_catalog_atlas_artifact(text, effective)


def _verify_derived_atlas(text: str, limits: Any | None) -> Any:
    _validate_kind_limits("derived_atlas", limits)
    from .derived_atlas import verify_derived_atlas

    return verify_derived_atlas(text)


_VERIFY_HANDLERS = (
    ("definition", _verify_definition),
    ("census", _verify_census),
    ("homological", _verify_homological),
    ("theorem", _verify_theorem),
    ("derived", _verify_derived),
    ("atlas", _verify_atlas),
    ("derived_atlas", _verify_derived_atlas),
)


def _verify_dispatched(kind: str, text: str, limits: Any | None) -> Any:
    verifier = _dispatch(_VERIFY_HANDLERS, kind)
    if verifier is None:
        raise ValueError(f"unsupported portable value kind {kind!r}")
    return verifier(text, limits)


def verify_file_text(text: str, limits: Any | None = None) -> Any:
    """Verify one portable value selected by its schema and payload kind."""
    if not isinstance(text, str):
        raise TypeError("portable value must be text")
    _validate_limit_type(limits)
    maximum = _input_limit(limits)
    if len(text.encode("utf-8")) > maximum:
        raise ValueError(f"portable value exceeds max_input_bytes={maximum}")
    kind = _json_kind(text)
    return _verify_dispatched(kind, text, limits)


def verify_file(path: str | Path, limits: Any | None = None) -> Any:
    """Read and verify one portable value with a bounded input reader."""
    text = _bounded_text(path, limits)
    return verify_file_text(text, limits)


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
    if kind == "derived":
        return kind, _verify_derived(text, limits), "replayed"
    constructor = _dispatch(_PORTABLE_LOADERS, kind)
    if constructor is None:
        raise ValueError(f"unsupported portable value kind {kind!r}")
    return kind, constructor(text, limits), "unverified"


def _portable_verification(value: Any) -> str:
    verified = (
        VerifiedCensusCheckpoint,
        VerifiedHomologicalCheckpoint,
        VerifiedSelfExtLocusArtifact,
    )
    if isinstance(value, verified):
        return "replayed"
    if isinstance(value, VerifiedCatalogAtlasArtifact):
        return "replayed"
    return "replayed" if isinstance(value, VerifiedDerivedArtifact) else "unverified"


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
        raise ValueError(
            "stage must be 'latest', 'census', 'homological', or 'artifact'"
        )
    return _write_checkpoint_value(_checkpoint_stage(value, stage), path)


def _checkpoint_stage(value: Any, stage: str) -> Any:
    if isinstance(value, (WorkflowResult, VerifiedWorkflowResult)):
        return _workflow_stage(value, stage)
    if stage != "latest":
        raise ValueError("stage applies only to a WorkflowResult")
    return value


def _write_checkpoint_value(value: Any, path: str | Path) -> Path:
    if isinstance(value, WorkflowDefinition):
        return _write_canonical_json(path, value.canonical_json)
    kind = _portable_kind(value)
    if kind is None:
        raise TypeError("value must be a workflow or portable checkpoint")
    if kind == "theorem":
        return write_theorem_artifact(path, value)
    if kind in {"atlas", "derived", "derived_atlas"}:
        return _write_canonical_json(path, value.canonical_json)
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
    """Replay-verify a checkpoint, theorem artifact, or composed workflow."""
    if isinstance(source, VerifiedWorkflowResult):
        return _verify_verified_workflow(source, limits)
    if isinstance(source, WorkflowResult):
        return _verify_workflow(source, limits)
    return _verify_loaded(source, limits)


def _verify_verified_workflow(
    source: VerifiedWorkflowResult,
    limits: Any | None,
) -> VerifiedWorkflowResult:
    if limits is not None:
        raise TypeError("limits cannot be applied to a verified workflow")
    return source


def _verify_workflow(source: WorkflowResult, limits: Any | None) -> Any:
    if limits is not None:
        raise TypeError("limits cannot be applied to an in-memory workflow")
    return source.verify()


def _verify_loaded(source: Any, limits: Any | None) -> Any:
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
    verified = (
        value if isinstance(value, VerifiedHomologicalCheckpoint) else value.verify()
    )
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
        return WorkflowResult(
            source.definition, census, None, None, source.stream_config
        )
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

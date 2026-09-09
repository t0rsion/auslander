"""Compose the finite census, homological stream, and theorem artifact APIs."""

from __future__ import annotations

from dataclasses import dataclass, field
import json
from pathlib import Path
from typing import Any

from ._core import (
    CensusCheckpoint,
    CensusLimits,
    HomologicalCheckpoint,
    HomologicalStreamConfig,
    PrimeField,
    SelfExtLocusArtifact,
    VerifiedCensusCheckpoint,
    VerifiedHomologicalCheckpoint,
    VerifiedSelfExtLocusArtifact,
    build_self_ext_locus_artifact,
    run_census,
    start_homological_stream,
)
from .parser import parse_presentation


DEFINITION_SCHEMA = "auslander-workflow-definition-v1"
DEFINITION_KIND = "finite-self-ext-workflow-v1"
_CENSUS_TYPES = (CensusCheckpoint, VerifiedCensusCheckpoint)
_HOMOLOGICAL_TYPES = (HomologicalCheckpoint, VerifiedHomologicalCheckpoint)
_ARTIFACT_TYPES = (SelfExtLocusArtifact, VerifiedSelfExtLocusArtifact)


def _integer(value: Any, label: str, *, positive: bool = False) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValueError(f"{label} must be an integer")
    if value < (1 if positive else 0):
        bound = "positive" if positive else "nonnegative"
        raise ValueError(f"{label} must be {bound}")
    return value


def _dimensions(value: Any) -> tuple[int, ...]:
    if not isinstance(value, (list, tuple)) or not value:
        raise ValueError("dimensions must be a nonempty array")
    result = tuple(_integer(item, f"dimensions[{index}]") for index, item in enumerate(value))
    return result


def _field_value(value: Any) -> int:
    if hasattr(value, "p"):
        value = value.p
    return _integer(value, "field", positive=True)


def _pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate definition field {key!r}")
        result[key] = value
    return result


def _definition_document(definition: "WorkflowDefinition") -> dict[str, Any]:
    return {
        "schema": DEFINITION_SCHEMA,
        "kind": DEFINITION_KIND,
        "field": definition.field,
        "presentation": definition.presentation,
        "dimensions": list(definition.dimensions),
        "first_degree": definition.first_degree,
        "last_degree": definition.last_degree,
    }


@dataclass(frozen=True)
class WorkflowScope:
    """The finite field, dimension, and positive-degree scope of one run."""

    field: int
    dimensions: tuple[int, ...]
    first_degree: int
    last_degree: int

    def as_dict(self) -> dict[str, Any]:
        """Return scope data in the report and inspection shape."""
        return {
            "field": self.field,
            "dimensions": list(self.dimensions),
            "first_degree": self.first_degree,
            "last_degree": self.last_degree,
            "kind": "finite_raw_matrix_domain",
        }


@dataclass(frozen=True)
class WorkflowDefinition:
    """A parsed presentation and finite self-Ext degree interval."""

    presentation: str
    field: int
    dimensions: tuple[int, ...]
    first_degree: int = 1
    last_degree: int = 3

    def __post_init__(self) -> None:
        if not isinstance(self.presentation, str) or not self.presentation.strip():
            raise ValueError("presentation must be nonempty text")
        field = _field_value(self.field)
        dimensions = _dimensions(self.dimensions)
        first = _integer(self.first_degree, "first_degree", positive=True)
        last = _integer(self.last_degree, "last_degree", positive=True)
        if first > last:
            raise ValueError("first_degree must not exceed last_degree")
        parsed = parse_presentation(self.presentation)
        if parsed.field != field:
            raise ValueError(
                f"field {field} does not match presentation field {parsed.field}"
            )
        if len(dimensions) != len(parsed.vertices):
            raise ValueError(
                "dimensions must have one entry for each presentation vertex"
            )
        object.__setattr__(self, "field", field)
        object.__setattr__(self, "dimensions", dimensions)
        object.__setattr__(self, "first_degree", first)
        object.__setattr__(self, "last_degree", last)

    @property
    def scope(self) -> WorkflowScope:
        """Return the exact finite scope declared by the definition."""
        return WorkflowScope(
            self.field,
            self.dimensions,
            self.first_degree,
            self.last_degree,
        )

    @property
    def canonical_json(self) -> str:
        """Return the canonical definition JSON."""
        return json.dumps(
            _definition_document(self),
            ensure_ascii=True,
            allow_nan=False,
            sort_keys=True,
            separators=(",", ":"),
        )

    def build(self) -> Any:
        """Build the checked algebra named by the presentation."""
        return parse_presentation(self.presentation).build()

    @classmethod
    def from_json(cls, text: str) -> "WorkflowDefinition":
        """Parse one canonical workflow definition."""
        if not isinstance(text, str):
            raise TypeError("definition must be text")
        try:
            value = json.loads(text, object_pairs_hook=_pairs)
        except json.JSONDecodeError as error:
            raise ValueError(
                f"invalid definition JSON at line {error.lineno}, column {error.colno}"
            ) from None
        if not isinstance(value, dict):
            raise ValueError("definition must be an object")
        expected = {
            "schema",
            "kind",
            "field",
            "presentation",
            "dimensions",
            "first_degree",
            "last_degree",
        }
        if set(value) != expected:
            raise ValueError("definition has missing or unknown fields")
        if value["schema"] != DEFINITION_SCHEMA or value["kind"] != DEFINITION_KIND:
            raise ValueError("unsupported workflow definition schema")
        definition = cls(
            value["presentation"],
            _field_value(value["field"]),
            _dimensions(value["dimensions"]),
            _integer(value["first_degree"], "first_degree", positive=True),
            _integer(value["last_degree"], "last_degree", positive=True),
        )
        if definition.canonical_json != text:
            raise ValueError("definition is not canonical JSON")
        return definition

    def __repr__(self) -> str:
        return (
            "WorkflowDefinition("
            f"field={self.field}, dimensions={list(self.dimensions)!r}, "
            f"degrees={self.first_degree}..{self.last_degree})"
        )


def define(
    presentation: str,
    dimensions: list[int] | tuple[int, ...],
    *,
    field: int | Any | None = None,
    first_degree: int = 1,
    last_degree: int = 3,
) -> WorkflowDefinition:
    """Validate presentation syntax and return a finite workflow definition."""
    parsed = parse_presentation(presentation)
    chosen_field = parsed.field if field is None else _field_value(field)
    return WorkflowDefinition(
        presentation,
        chosen_field,
        _dimensions(dimensions),
        first_degree,
        last_degree,
    )


def _stream_config(value: Any | None) -> Any:
    if value is None:
        return HomologicalStreamConfig(max_live_sources=2)
    if not isinstance(value, HomologicalStreamConfig):
        raise TypeError("stream_config must be a HomologicalStreamConfig")
    return value


def _census_limits(value: Any | None) -> Any | None:
    if value is None:
        return None
    if not isinstance(value, CensusLimits):
        raise TypeError("census_limits must be a CensusLimits")
    return value


def _drain_stream(stream: Any) -> Any:
    checkpoint = stream.checkpoint
    while checkpoint.status == "active":
        checkpoint = stream.advance()
    return checkpoint


def _artifact_for(definition: WorkflowDefinition, checkpoint: Any) -> Any | None:
    if checkpoint.status != "complete":
        return None
    return _build_artifact(checkpoint, definition.first_degree, definition.last_degree)


def _build_artifact(checkpoint: Any, first_degree: int, last_degree: int) -> Any:
    return build_self_ext_locus_artifact(
        checkpoint.verify(),
        first_degree,
        last_degree,
    )


def _validate_census_binding(
    definition: WorkflowDefinition,
    census: Any,
) -> None:
    if not isinstance(census, _CENSUS_TYPES):
        raise TypeError("census must be a CensusCheckpoint")
    if census.field != definition.field:
        raise ValueError("workflow field does not match the census")
    if tuple(census.dimensions) != definition.dimensions:
        raise ValueError("workflow dimensions do not match the census")
    expected = definition.build().certificate_json(PrimeField(definition.field))
    if census.certificate_json != expected:
        raise ValueError("workflow presentation does not match the census")


def _validate_homological_binding(
    definition: WorkflowDefinition,
    census: Any,
    homological: Any,
) -> Any:
    if not isinstance(homological, _HOMOLOGICAL_TYPES):
        raise TypeError("homological must be a HomologicalCheckpoint")
    homological_data = _homological_data(homological)
    if homological_data.census_fingerprint != census.fingerprint:
        raise ValueError("homological checkpoint does not match the census fingerprint")
    if homological_data.census_json != census.canonical_json:
        raise ValueError("homological checkpoint does not embed this census")
    if homological_data.max_degree != definition.last_degree:
        raise ValueError("homological degree does not match the workflow definition")
    return homological_data


def _validate_artifact_binding(
    definition: WorkflowDefinition,
    homological_data: Any,
    artifact: Any | None,
) -> None:
    if artifact is None:
        return
    if not isinstance(artifact, _ARTIFACT_TYPES):
        raise TypeError("artifact must be a SelfExtLocusArtifact")
    artifact_checkpoint = _homological_data(artifact.checkpoint)
    if artifact_checkpoint.fingerprint != homological_data.fingerprint:
        raise ValueError("theorem artifact does not match the homological checkpoint")
    if artifact_checkpoint.canonical_json != homological_data.canonical_json:
        raise ValueError("theorem artifact does not embed this homological checkpoint")
    if (
        artifact.first_degree != definition.first_degree
        or artifact.last_degree != definition.last_degree
    ):
        raise ValueError("theorem degree interval does not match the workflow definition")


def _validate_bindings(
    definition: WorkflowDefinition,
    census: Any,
    homological: Any | None,
    artifact: Any | None,
) -> None:
    """Check that every composed value names the same finite computation."""
    _validate_census_binding(definition, census)
    if homological is None:
        if artifact is not None:
            raise ValueError("a theorem artifact requires a homological checkpoint")
        return
    homological_data = _validate_homological_binding(
        definition,
        census,
        homological,
    )
    _validate_artifact_binding(definition, homological_data, artifact)


def _homological_data(value: Any) -> Any:
    if isinstance(value, VerifiedHomologicalCheckpoint):
        return value.checkpoint
    return value


def _validate_verified_stage(
    verified: Any | None,
    result: Any | None,
    label: str,
) -> None:
    if (verified is None) != (result is None):
        raise ValueError(f"verified {label} stage does not match the workflow result")
    if verified is not None and verified.canonical_json != result.canonical_json:
        raise ValueError(f"verified {label} stage does not match the workflow result")


@dataclass(frozen=True)
class WorkflowResult:
    """The latest census, homological prefix, and optional theorem artifact."""

    definition: WorkflowDefinition
    census: Any
    homological: Any | None = None
    artifact: Any | None = None
    stream_config: Any | None = field(default=None, repr=False)

    def __post_init__(self) -> None:
        if not isinstance(self.definition, WorkflowDefinition):
            raise TypeError("definition must be a WorkflowDefinition")
        if not isinstance(self.census, CensusCheckpoint):
            raise TypeError("census must be a CensusCheckpoint")
        if self.homological is not None and not isinstance(self.homological, HomologicalCheckpoint):
            raise TypeError("homological must be a HomologicalCheckpoint")
        if self.artifact is not None and not isinstance(self.artifact, SelfExtLocusArtifact):
            raise TypeError("artifact must be a SelfExtLocusArtifact")
        _validate_bindings(
            self.definition,
            self.census,
            self.homological,
            self.artifact,
        )

    @property
    def verification(self) -> str:
        """Return the trust state of an un-replayed workflow result."""
        return "computed"

    @property
    def status(self) -> str:
        """Return the latest typed status in the workflow."""
        if self.homological is not None:
            return self.homological.status
        return self.census.status

    @property
    def scope(self) -> dict[str, Any]:
        """Return declared scope and exact counters available in the result."""
        value = self.definition.scope.as_dict()
        value.update(
            {
                "raw_space_size": self.census.raw_space_size,
                "census_cursor": self.census.cursor,
                "census_candidates": self.census.candidates,
                "accepted_modules": self.census.accepted_modules,
                "representatives": self.census.representative_count,
            }
        )
        if self.homological is not None:
            value.update(
                {
                    "homological_cursor": self.homological.next_source,
                    "rows": self.homological.row_count,
                    "max_degree": self.homological.max_degree,
                    "chunks": self.homological.work.chunks,
                    "chunk_sizes": self.homological.chunk_sizes,
                }
            )
        return value

    @property
    def fingerprint(self) -> str:
        """Return the fingerprint of the latest portable value."""
        if self.artifact is not None:
            return self.artifact.fingerprint
        if self.homological is not None:
            return self.homological.fingerprint
        return self.census.fingerprint

    def rows(self) -> list[dict[str, Any]]:
        """Return stored self-pair rows joined with representative coordinates."""
        if self.homological is None:
            return []
        representatives = self.census.representatives
        return [_row_record(row, representatives) for row in self.homological.rows]

    def verify(self) -> "VerifiedWorkflowResult":
        """Replay every portable value and return a verified workflow."""
        census = self.census.verify()
        homological = (
            None if self.homological is None else self.homological.verify()
        )
        artifact = None if self.artifact is None else self.artifact.verify()
        return VerifiedWorkflowResult(
            self,
            census,
            homological,
            artifact,
        )


@dataclass(frozen=True)
class VerifiedWorkflowResult:
    """A workflow whose stored census, stream, and artifact passed replay."""

    result: WorkflowResult
    census: VerifiedCensusCheckpoint
    homological: VerifiedHomologicalCheckpoint | None
    artifact: VerifiedSelfExtLocusArtifact | None

    def __post_init__(self) -> None:
        if not isinstance(self.result, WorkflowResult):
            raise TypeError("result must be a WorkflowResult")
        if not isinstance(self.census, VerifiedCensusCheckpoint):
            raise TypeError("census must be a VerifiedCensusCheckpoint")
        if self.homological is not None and not isinstance(self.homological, VerifiedHomologicalCheckpoint):
            raise TypeError("homological must be a VerifiedHomologicalCheckpoint")
        if self.artifact is not None and not isinstance(self.artifact, VerifiedSelfExtLocusArtifact):
            raise TypeError("artifact must be a VerifiedSelfExtLocusArtifact")
        _validate_bindings(
            self.definition,
            self.census,
            self.homological,
            self.artifact,
        )
        _validate_verified_stage(self.census, self.result.census, "census")
        _validate_verified_stage(
            self.homological,
            self.result.homological,
            "homological",
        )
        _validate_verified_stage(self.artifact, self.result.artifact, "artifact")

    @property
    def definition(self) -> WorkflowDefinition:
        """Return the workflow definition."""
        return self.result.definition

    @property
    def verification(self) -> str:
        """Return the replay trust state."""
        return "replayed"

    @property
    def status(self) -> str:
        """Return the replayed typed status."""
        if self.homological is not None:
            return self.homological.status
        return self.census.status

    @property
    def scope(self) -> dict[str, Any]:
        """Return finite scope and exact replayed counters."""
        return self.result.scope

    @property
    def fingerprint(self) -> str:
        """Return the replayed latest fingerprint."""
        if self.artifact is not None:
            return self.artifact.fingerprint
        if self.homological is not None:
            return self.homological.fingerprint
        return self.census.fingerprint

    def rows(self) -> list[dict[str, Any]]:
        """Return replayed rows joined with representative coordinates."""
        if self.homological is None:
            return []
        rows = _homological_data(self.homological).rows
        representatives = self.census.representatives
        return [_row_record(row, representatives) for row in rows]


def compute(
    definition: WorkflowDefinition,
    *,
    census_limits: Any | None = None,
    stream_config: Any | None = None,
    control: Any | None = None,
    output: str | Path | None = None,
) -> WorkflowResult:
    """Run a finite census and bounded self-pair stream from a definition."""
    if not isinstance(definition, WorkflowDefinition):
        raise TypeError("definition must be a WorkflowDefinition")
    limits = _census_limits(census_limits)
    config = _stream_config(stream_config)
    census = _run_census(definition, limits, control)
    homological = None
    artifact = None
    if census.status == "complete":
        verified = census.verify()
        stream = _start_stream(definition, verified, config, control)
        homological = _drain_stream(stream)
        artifact = _artifact_for(definition, homological)
    result = WorkflowResult(definition, census, homological, artifact, config)
    if output is not None:
        checkpoint(result, output)
    return result


def _run_census(definition: WorkflowDefinition, limits: Any | None, control: Any) -> Any:
    return run_census(
        definition.build(),
        list(definition.dimensions),
        PrimeField(definition.field),
        limits=limits,
        control=control,
    )


def _start_stream(definition: WorkflowDefinition, census: Any, config: Any, control: Any) -> Any:
    return start_homological_stream(
        census,
        definition.last_degree,
        config,
        control=control,
    )


def _row_record(row: Any, representatives: list[Any]) -> dict[str, Any]:
    source = row.source
    coordinates = representatives[source].coordinates if source < len(representatives) else None
    return {
        "index": source,
        "target": row.target,
        "coordinates": coordinates,
        "hom_dim": row.hom_dim,
        "stable_hom_dim": row.stable_hom_dim,
        "ext_dimensions": row.ext_dimensions,
        "resolution_status": row.resolution_status,
        "resolution_cut_at": row.resolution_cut_at,
    }


@dataclass(frozen=True)
class WorkflowInspection:
    """A bounded inspection with explicit declared or replayed trust state."""

    kind: str
    status: str
    verification: str
    scope: dict[str, Any]
    fingerprint: str | None
    value: Any = field(repr=False)

    @property
    def accepted(self) -> bool:
        """Return whether a replay verifier accepted the inspected value."""
        return self.verification == "replayed"

    def as_dict(self) -> dict[str, Any]:
        """Return inspection metadata without the core value object."""
        return {
            "kind": self.kind,
            "status": self.status,
            "verification": self.verification,
            "accepted": self.accepted,
            "scope": self.scope,
            "fingerprint": self.fingerprint,
        }

    def __str__(self) -> str:
        from .workflow_report import inspection_text

        return inspection_text(self)


def inspect(source: Any, limits: Any | None = None) -> WorkflowInspection:
    """Inspect a definition or portable checkpoint without replaying it."""
    from .workflow_report import inspect as _inspect

    return _inspect(source, limits)


def checkpoint(value: Any, path: str | Path, *, stage: str = "latest") -> Path:
    """Write the selected portable value from a workflow atomically."""
    from .workflow_io import checkpoint as _checkpoint

    return _checkpoint(value, path, stage=stage)


def verify(source: Any, limits: Any | None = None) -> Any:
    """Replay-verify a definition, checkpoint, theorem artifact, or workflow."""
    from .workflow_io import verify as _verify

    return _verify(source, limits)


def resume(
    source: Any,
    output: str | Path | None = None,
    *,
    census_limits: Any | None = None,
    budget: Any | None = None,
    control: Any | None = None,
) -> Any:
    """Verify and resume a cut census, stream, or composed workflow."""
    from .workflow_io import resume as _resume

    return _resume(
        source,
        output,
        census_limits=census_limits,
        budget=budget,
        control=control,
    )


def export(
    source: Any,
    output: str | Path | None = None,
    *,
    format: str = "markdown",
    verify_value: bool = False,
) -> str:
    """Export a bounded Ext table and scope report as Markdown or CSV."""
    from .workflow_report import export as _export

    return _export(source, output, format=format, verify_value=verify_value)


def write_definition(path: str | Path, definition: WorkflowDefinition) -> Path:
    """Write one canonical workflow definition atomically."""
    from .workflow_io import write_definition as _write_definition

    return _write_definition(path, definition)


def load_definition(path: str | Path) -> WorkflowDefinition:
    """Load one canonical workflow definition."""
    from .workflow_io import load_definition as _load_definition

    return _load_definition(path)

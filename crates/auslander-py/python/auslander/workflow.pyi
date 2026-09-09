from dataclasses import dataclass
from pathlib import Path
from typing import Any

from ._core import (
    Algebra,
    CensusCheckpoint,
    CensusLimits,
    ComputationControl,
    HomologicalCheckpoint,
    HomologicalStreamBudget,
    HomologicalStreamConfig,
    PrimeField,
    SelfExtLocusArtifact,
    VerifiedCensusCheckpoint,
    VerifiedHomologicalCheckpoint,
    VerifiedSelfExtLocusArtifact,
)

DEFINITION_SCHEMA: str
DEFINITION_KIND: str

@dataclass(frozen=True)
class WorkflowScope:
    field: int
    dimensions: tuple[int, ...]
    first_degree: int
    last_degree: int
    def as_dict(self) -> dict[str, Any]: ...

@dataclass(frozen=True)
class WorkflowDefinition:
    def __init__(
        self,
        presentation: str,
        field: int | PrimeField,
        dimensions: list[int] | tuple[int, ...],
        first_degree: int = ...,
        last_degree: int = ...,
    ) -> None: ...
    presentation: str
    field: int
    dimensions: tuple[int, ...]
    first_degree: int
    last_degree: int
    @property
    def scope(self) -> WorkflowScope: ...
    @property
    def canonical_json(self) -> str: ...
    def build(self) -> Algebra: ...
    @classmethod
    def from_json(cls, text: str) -> WorkflowDefinition: ...

@dataclass(frozen=True)
class WorkflowResult:
    definition: WorkflowDefinition
    census: CensusCheckpoint
    homological: HomologicalCheckpoint | None = ...
    artifact: SelfExtLocusArtifact | None = ...
    stream_config: HomologicalStreamConfig | None = ...
    @property
    def verification(self) -> str: ...
    @property
    def status(self) -> str: ...
    @property
    def scope(self) -> dict[str, Any]: ...
    @property
    def fingerprint(self) -> str: ...
    def rows(self) -> list[dict[str, Any]]: ...
    def verify(self) -> VerifiedWorkflowResult: ...

@dataclass(frozen=True)
class VerifiedWorkflowResult:
    result: WorkflowResult
    census: VerifiedCensusCheckpoint
    homological: VerifiedHomologicalCheckpoint | None
    artifact: VerifiedSelfExtLocusArtifact | None
    @property
    def definition(self) -> WorkflowDefinition: ...
    @property
    def verification(self) -> str: ...
    @property
    def status(self) -> str: ...
    @property
    def scope(self) -> dict[str, Any]: ...
    @property
    def fingerprint(self) -> str: ...
    def rows(self) -> list[dict[str, Any]]: ...

@dataclass(frozen=True)
class WorkflowInspection:
    kind: str
    status: str
    verification: str
    scope: dict[str, Any]
    fingerprint: str | None
    value: Any
    @property
    def accepted(self) -> bool: ...
    def as_dict(self) -> dict[str, Any]: ...

def define(
    presentation: str,
    dimensions: list[int] | tuple[int, ...],
    *,
    field: int | PrimeField | None = ...,
    first_degree: int = ...,
    last_degree: int = ...,
) -> WorkflowDefinition: ...
def compute(
    definition: WorkflowDefinition,
    *,
    census_limits: CensusLimits | None = ...,
    stream_config: HomologicalStreamConfig | None = ...,
    control: ComputationControl | None = ...,
    output: str | Path | None = ...,
) -> WorkflowResult: ...
def inspect(source: Any, limits: Any | None = ...) -> WorkflowInspection: ...
def checkpoint(value: Any, path: str | Path, *, stage: str = ...) -> Path: ...
def resume(
    source: Any,
    output: str | Path | None = ...,
    *,
    census_limits: CensusLimits | None = ...,
    budget: HomologicalStreamBudget | None = ...,
    control: ComputationControl | None = ...,
) -> Any: ...
def verify(source: Any, limits: Any | None = ...) -> Any: ...
def export(
    source: Any,
    output: str | Path | None = ...,
    *,
    format: str = ...,
    verify_value: bool = ...,
) -> str: ...
def write_definition(path: str | Path, definition: WorkflowDefinition) -> Path: ...
def load_definition(path: str | Path) -> WorkflowDefinition: ...

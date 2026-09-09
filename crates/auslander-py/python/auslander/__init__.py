"""Checked computations for finite-dimensional bound quiver algebras."""

from . import _core as _core

for _name in dir(_core):
    if not _name.startswith("_"):
        globals()[_name] = getattr(_core, _name)

from .checkpoint import (
    CensusCheckpointValue,
    CheckpointValue,
    HomologicalCheckpointValue,
    load_checkpoint,
    load_homological_checkpoint,
    resume_homological_checkpoint,
    run_homological_stream,
    verify_checkpoint,
    verify_homological_checkpoint_file,
    write_checkpoint,
)
from .compute import compute_json, compute_request
from .display import Explanation, Rendered, explain, show, to_dot, to_latex, to_networkx
from .parser import ParsedPresentation, PresentationSyntaxError, parse_presentation
from .session import Session, verify_file
from .theorem import (
    SelfExtLocusArtifactValue,
    build_self_ext_locus_artifact_file,
    load_self_ext_locus_artifact,
    verify_self_ext_locus_artifact_file,
    write_theorem_artifact,
)
from .workflow import (
    DEFINITION_KIND,
    DEFINITION_SCHEMA,
    VerifiedWorkflowResult,
    WorkflowDefinition,
    WorkflowInspection,
    WorkflowResult,
    WorkflowScope,
    checkpoint,
    compute,
    define,
    export,
    inspect,
    load_definition,
    resume,
    verify,
    write_definition,
)

__version__ = "0.8.0"

__all__ = [
    *[name for name in dir(_core) if not name.startswith("_")],
    "Explanation",
    "DEFINITION_KIND",
    "DEFINITION_SCHEMA",
    "ParsedPresentation",
    "PresentationSyntaxError",
    "Rendered",
    "Session",
    "VerifiedWorkflowResult",
    "WorkflowDefinition",
    "WorkflowInspection",
    "WorkflowResult",
    "WorkflowScope",
    "checkpoint",
    "compute",
    "compute_json",
    "compute_request",
    "CheckpointValue",
    "CensusCheckpointValue",
    "HomologicalCheckpointValue",
    "SelfExtLocusArtifactValue",
    "explain",
    "define",
    "export",
    "inspect",
    "load_definition",
    "parse_presentation",
    "build_self_ext_locus_artifact_file",
    "load_checkpoint",
    "load_homological_checkpoint",
    "load_self_ext_locus_artifact",
    "resume_homological_checkpoint",
    "run_homological_stream",
    "show",
    "to_dot",
    "to_latex",
    "to_networkx",
    "resume",
    "verify",
    "verify_checkpoint",
    "verify_homological_checkpoint_file",
    "verify_self_ext_locus_artifact_file",
    "verify_file",
    "write_checkpoint",
    "write_definition",
    "write_theorem_artifact",
]

"""Build, write, and verify finite theorem artifacts."""

from __future__ import annotations

import os
from pathlib import Path
from typing import TypeAlias

from ._core import (
    SelfExtLocusArtifact,
    SelfExtLocusVerifyLimits,
    VerifiedSelfExtLocusArtifact,
    build_self_ext_locus_artifact,
    verify_self_ext_locus_artifact,
)
from .checkpoint import (
    _read_utf8_bounded,
    _write_canonical_json,
    verify_homological_checkpoint_file,
)

SelfExtLocusArtifactValue: TypeAlias = (
    SelfExtLocusArtifact | VerifiedSelfExtLocusArtifact
)


def write_theorem_artifact(
    path: str | os.PathLike[str], artifact: SelfExtLocusArtifactValue
) -> Path:
    """Write one canonical theorem artifact with an atomic replace."""
    if not isinstance(
        artifact,
        (SelfExtLocusArtifact, VerifiedSelfExtLocusArtifact),
    ):
        raise TypeError("artifact must be a self-Ext locus artifact")
    return _write_canonical_json(path, artifact.canonical_json)


def load_self_ext_locus_artifact(
    path: str | os.PathLike[str],
    limits: SelfExtLocusVerifyLimits | None = None,
) -> SelfExtLocusArtifact:
    """Load one canonical self-Ext locus without independent verification."""
    limits = SelfExtLocusVerifyLimits() if limits is None else limits
    text = _read_utf8_bounded(path, limits.max_input_bytes, "theorem artifact")
    return SelfExtLocusArtifact(text, limits)


def verify_self_ext_locus_artifact_file(
    path: str | os.PathLike[str],
    limits: SelfExtLocusVerifyLimits | None = None,
) -> VerifiedSelfExtLocusArtifact:
    """Load and independently verify one self-Ext locus artifact."""
    limits = SelfExtLocusVerifyLimits() if limits is None else limits
    text = _read_utf8_bounded(path, limits.max_input_bytes, "theorem artifact")
    return verify_self_ext_locus_artifact(text, limits)


def build_self_ext_locus_artifact_file(
    checkpoint_path: str | os.PathLike[str],
    output: str | os.PathLike[str],
    first_degree: int,
    last_degree: int,
    limits: SelfExtLocusVerifyLimits | None = None,
) -> SelfExtLocusArtifact:
    """Verify a complete checkpoint, build its self-Ext locus, and write it."""
    limits = SelfExtLocusVerifyLimits() if limits is None else limits
    checkpoint = verify_homological_checkpoint_file(
        checkpoint_path,
        limits.checkpoint,
    )
    artifact = build_self_ext_locus_artifact(
        checkpoint,
        first_degree,
        last_degree,
    )
    write_theorem_artifact(output, artifact)
    return artifact

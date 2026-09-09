"""Write, verify, and resume portable computation checkpoints."""

from __future__ import annotations

import os
import tempfile
from pathlib import Path
from typing import TypeAlias

from ._core import (
    CensusCheckpoint,
    CensusVerifyLimits,
    ComputationControl,
    HomologicalCheckpoint,
    HomologicalCheckpointStream,
    HomologicalStreamBudget,
    HomologicalStreamVerifyLimits,
    VerifiedCensusCheckpoint,
    VerifiedHomologicalCheckpoint,
    verify_census_checkpoint,
    verify_homological_checkpoint,
)

CensusCheckpointValue: TypeAlias = CensusCheckpoint | VerifiedCensusCheckpoint
HomologicalCheckpointValue: TypeAlias = (
    HomologicalCheckpoint | VerifiedHomologicalCheckpoint
)
CheckpointValue: TypeAlias = CensusCheckpointValue | HomologicalCheckpointValue


def write_checkpoint(
    path: str | os.PathLike[str], checkpoint: CheckpointValue
) -> Path:
    """Write one canonical checkpoint with an atomic same-directory replace."""
    if not isinstance(
        checkpoint,
        (
            CensusCheckpoint,
            VerifiedCensusCheckpoint,
            HomologicalCheckpoint,
            VerifiedHomologicalCheckpoint,
        ),
    ):
        raise TypeError("checkpoint must be a portable checkpoint value")
    return _write_canonical_json(path, checkpoint.canonical_json)


def _write_canonical_json(path: str | os.PathLike[str], text: str) -> Path:
    """Write canonical JSON with an atomic same-directory replace."""
    target = Path(path)
    parent = target.parent
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{target.name}.",
        suffix=".tmp",
        dir=parent,
    )
    open_descriptor = descriptor
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as stream:
            open_descriptor = -1
            stream.write(text)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary_name, target)
        _sync_directory(parent)
    except BaseException:
        if open_descriptor >= 0:
            try:
                os.close(open_descriptor)
            except OSError:
                pass
        try:
            os.unlink(temporary_name)
        except OSError:
            pass
        raise
    return target


def load_checkpoint(
    path: str | os.PathLike[str], limits: CensusVerifyLimits | None = None
) -> CensusCheckpoint:
    """Load one canonical checkpoint without replay verification."""
    limits = _effective_limits(limits)
    text = _read_utf8_bounded(path, limits.max_input_bytes, "checkpoint")
    return CensusCheckpoint(text, limits)


def verify_checkpoint(
    path: str | os.PathLike[str], limits: CensusVerifyLimits | None = None
) -> VerifiedCensusCheckpoint:
    """Load and replay-verify one checkpoint against a rebuilt algebra."""
    limits = _effective_limits(limits)
    text = _read_utf8_bounded(path, limits.max_input_bytes, "checkpoint")
    return verify_census_checkpoint(text, limits)


def load_homological_checkpoint(
    path: str | os.PathLike[str],
    limits: HomologicalStreamVerifyLimits | None = None,
) -> HomologicalCheckpoint:
    """Load one homological checkpoint without replay verification."""
    limits = HomologicalStreamVerifyLimits() if limits is None else limits
    text = _read_utf8_bounded(path, limits.max_input_bytes, "homological checkpoint")
    return HomologicalCheckpoint(text, limits)


def verify_homological_checkpoint_file(
    path: str | os.PathLike[str],
    limits: HomologicalStreamVerifyLimits | None = None,
) -> VerifiedHomologicalCheckpoint:
    """Load and replay-verify one homological checkpoint."""
    limits = HomologicalStreamVerifyLimits() if limits is None else limits
    text = _read_utf8_bounded(path, limits.max_input_bytes, "homological checkpoint")
    return verify_homological_checkpoint(text, limits)


def run_homological_stream(
    path: str | os.PathLike[str], stream: HomologicalCheckpointStream
) -> HomologicalCheckpoint:
    """Advance a stream and atomically replace its checkpoint after each chunk."""
    if not isinstance(stream, HomologicalCheckpointStream):
        raise TypeError("stream must be a HomologicalCheckpointStream")
    checkpoint = stream.checkpoint
    write_checkpoint(path, checkpoint)
    while checkpoint.status == "active":
        checkpoint = stream.advance()
        write_checkpoint(path, checkpoint)
    return checkpoint


def resume_homological_checkpoint(
    source: str | os.PathLike[str],
    output: str | os.PathLike[str],
    budget: HomologicalStreamBudget | None = None,
    limits: HomologicalStreamVerifyLimits | None = None,
    control: ComputationControl | None = None,
) -> HomologicalCheckpoint:
    """Verify, resume, and atomically persist one homological checkpoint."""
    verified = verify_homological_checkpoint_file(source, limits)
    stream = verified.resume(budget, control)
    return run_homological_stream(output, stream)


def _effective_limits(limits: CensusVerifyLimits | None) -> CensusVerifyLimits:
    return CensusVerifyLimits() if limits is None else limits


def _read_utf8_bounded(
    path: str | os.PathLike[str],
    max_bytes: int,
    kind: str,
    limit_name: str = "max_input_bytes",
) -> str:
    with Path(path).open("rb") as stream:
        payload = stream.read(max_bytes + 1)
    if len(payload) > max_bytes:
        raise ValueError(f"{kind} exceeds {limit_name}={max_bytes}")
    try:
        return payload.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ValueError(f"{kind} is not valid UTF-8") from error


def _sync_directory(path: Path) -> None:
    """Flush the containing directory when the platform exposes directory fsync."""
    descriptor = -1
    try:
        descriptor = os.open(path, os.O_RDONLY)
        os.fsync(descriptor)
    except OSError:
        return
    finally:
        if descriptor >= 0:
            try:
                os.close(descriptor)
            except OSError:
                pass

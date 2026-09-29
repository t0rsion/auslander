"""Replay portable derived atlases."""

from __future__ import annotations

import os

from ._core import (
    ComputationControl,
    DerivedAtlasArtifact,
    DerivedClassification,
    IncompleteArtifactVerification,
    _verify_derived_atlas,
)
from .checkpoint import _read_utf8_bounded


def verify_derived_atlas(
    source: str | os.PathLike[str],
    control: ComputationControl | None = None,
) -> DerivedClassification | IncompleteArtifactVerification:
    """Replay one derived atlas and return the rebuilt classification.

    A `str` that starts with `{` is the atlas text. Any other `str` or path
    names a file, read up to `DerivedAtlasArtifact.max_input_bytes`. Returns
    a `DerivedClassification` with `verification == "replayed"`, or an
    `IncompleteArtifactVerification` when cancellation through `control` or
    a verifier ceiling stopped the replay. Raises ValueError when the atlas
    is malformed or a claim does not replay.
    """
    if isinstance(source, str) and source.startswith("{"):
        text = source
    else:
        text = _read_utf8_bounded(
            source, DerivedAtlasArtifact.max_input_bytes, "derived atlas"
        )
    return _verify_derived_atlas(text, control)

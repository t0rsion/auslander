"""Structured explanations for typed computation results."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, replace
from typing import Any

from ._core import (
    ResolutionKind,
    VerifiedCensusCheckpoint,
    VerifiedDerivedArtifact,
    VerifiedHomologicalCheckpoint,
    VerifiedSelfExtLocusArtifact,
)


@dataclass(frozen=True)
class Explanation:
    """Describe computation status separately from replay verification."""

    variant: str
    status: str
    verification: str
    completed: str
    unfinished: str | None = None
    next_action: str | None = None


_MISSING = object()
_Rule = Callable[[Any, str], Explanation | None]


def explain(value: Any) -> Explanation:
    """Describe a typed result without parsing exception or repr text."""
    variant = type(value).__name__
    for rule in _COMPUTATION_RULES:
        result = rule(value, variant)
        if result is not None:
            break
    else:
        result = _make(variant, "value", "construction")
    return replace(result, verification=_verification_status(value))


def _read(value: Any, name: str) -> Any:
    try:
        return getattr(value, name)
    except AttributeError:
        return _MISSING


def _first_present(*values: Any) -> Any:
    """Return the first value that is neither `_MISSING` nor `None`."""
    for value in values:
        if value is not _MISSING and value is not None:
            return value
    return _MISSING


def _make(
    variant: str,
    status: str,
    completed: str,
    unfinished: str | None = None,
    next_action: str | None = None,
) -> Explanation:
    return Explanation(
        variant, status, "unverified", completed, unfinished, next_action
    )


def _verification_status(value: Any) -> str:
    reported = _read(value, "verification")
    if isinstance(reported, str):
        return reported
    if isinstance(value, _REPLAYED_VALUES):
        return "replayed"
    return "unverified"


_REPLAYED_VALUES = (
    VerifiedCensusCheckpoint,
    VerifiedDerivedArtifact,
    VerifiedHomologicalCheckpoint,
    VerifiedSelfExtLocusArtifact,
)


def _status_rule(value: Any, variant: str) -> Explanation | None:
    status = _read(value, "status")
    if status is _MISSING:
        return None
    if isinstance(status, str):
        return _status_text(value, variant, status)
    return _resolution_end(value, variant, status)


def _typed_status_rule(value: Any, variant: str) -> Explanation | None:
    status = _read(value, "enumeration_status")
    if status is _MISSING:
        kind = _read(value, "kind")
        complete = _read(value, "is_complete")
        cut = _read(value, "is_cut")
        if not isinstance(kind, str) or not isinstance(complete, bool) or not isinstance(cut, bool):
            return None
        status = value
    kind = _read(status, "kind")
    if kind == "complete":
        return _make(variant, "complete", "stored result")
    if kind == "cut":
        return _cut_status(value, variant, status)
    return None


def _status_text(value: Any, variant: str, status: str) -> Explanation:
    if status == "cut":
        return _cut_status(value, variant)
    message = _STATUS_MESSAGES.get(status)
    if message is None:
        return _make(variant, status, "stored result")
    completed, unfinished, action = message
    return _make(variant, status, completed, unfinished, action)


_STATUS_MESSAGES = {
    "complete": ("stored result", None, None),
    "finite": ("finite resolution", None, None),
    "active": (
        "stored prefix",
        "next source chunk",
        "advance the stream within its limits",
    ),
    "incomplete": (
        "stored prefix",
        "completion",
        "raise the named limit or inspect the partial result",
    ),
}


def _cut_status(value: Any, variant: str, status: Any = _MISSING) -> Explanation:
    stored_status = _read(value, "status")
    reason = _first_present(
        _read(value, "cut_reason"),
        _read(value, "reason"),
        _read(status, "cut_reason"),
        _read(stored_status, "cut_reason"),
    )
    reason = _reason_label(reason)
    return _make(
        variant,
        "cut",
        "stored prefix",
        reason or "cut reason",
        "raise the named limit or inspect the cut reason",
    )


def _resolution_rule(value: Any, variant: str) -> Explanation | None:
    status = _read(value, "resolution_status")
    if status is _MISSING:
        return None
    if isinstance(status, str):
        return _status_text(value, variant, status)
    return _resolution_end(value, variant, status)


def _resolution_end(value: Any, variant: str, status: Any) -> Explanation:
    kind = _read(status, "kind")
    if kind == ResolutionKind.FINITE:
        return _make(variant, "finite", "finite resolution")
    if kind == ResolutionKind.CUT:
        return _resolution_cut(value, variant, _read(status, "at"))
    if isinstance(kind, str):
        return _status_text(value, variant, kind)
    return _make(variant, "unknown", "status object", "resolution end")


def _resolution_cut(value: Any, variant: str, at: Any) -> Explanation:
    if at is _MISSING:
        return _make(variant, "unknown", "status object", "resolution end")
    terms = _read(value, "terms")
    bound = _read(value, "bound")
    if terms is not _MISSING:
        completed = f"{len(terms)} stored terms"
    elif bound is not _MISSING:
        completed = f"exact degrees through {bound}"
    else:
        completed = f"resolution through differential {at}"
    return _make(
        variant,
        "cut",
        completed,
        f"next syzygy after differential {at}",
        "raise the resolution bound or inspect the next syzygy",
    )


_NESTED_STATUS = (
    ("checkpoint", "checkpoint"),
    ("resolution", "syzygy"),
    ("coresolution", "cosyzygy"),
)


def _nested_rule(value: Any, variant: str) -> Explanation | None:
    for name, label in _NESTED_STATUS:
        nested = _read(value, name)
        if nested is _MISSING:
            continue
        if nested is None:
            return _make(variant, "complete", f"degree-zero {label}")
        status = _read(nested, "status")
        if status is not _MISSING:
            return _status_rule_value(nested, variant, status)
    return None


def _status_rule_value(value: Any, variant: str, status: Any) -> Explanation:
    if isinstance(status, str):
        return _status_text(value, variant, status)
    return _resolution_end(value, variant, status)


def _bounded_rule(value: Any, variant: str) -> Explanation | None:
    exact = _read(value, "exact")
    lower = _read(value, "at_least")
    if exact is not _MISSING and exact is not None:
        return _make(variant, "exact", f"exact value {exact}")
    if lower is _MISSING or lower is None:
        return None
    return _make(
        variant,
        "at_least",
        f"lower bound {lower}",
        "the exact value",
        "raise the resolution bound",
    )


_DECISIONS = (
    ("is_pair", "support pair conditions", "pair condition"),
    ("is_tilting", "tilting obligations", "self-extension check"),
    ("is_tau_rigid", "tau-rigidity conditions", "nonzero Hom witness"),
    ("is_tau_tilting", "support tau-tilting obligations", "pair conditions"),
    ("isomorphic", "isomorphism check", "obstruction"),
)


def _decision_rule(value: Any, variant: str) -> Explanation | None:
    for name, completed, rejected in _DECISIONS:
        answer = _read(value, name)
        if answer is not _MISSING:
            return _boolean(value, variant, answer, completed, rejected)
    classes = _read(value, "classes")
    if classes is _MISSING:
        return None
    if classes is None:
        return _make(
            variant,
            "undetermined",
            "decomposition checks",
            _reason_label(_read(value, "reason")) or "Krull-Schmidt grouping",
            "inspect the decomposition reason",
        )
    return _make(variant, "complete", "Krull-Schmidt grouping")


def _boolean(
    value: Any,
    variant: str,
    answer: Any,
    completed: str,
    rejected: str,
) -> Explanation:
    if answer is True:
        return _make(variant, "complete", completed)
    if answer is False:
        return _make(variant, "rejected", rejected)
    for name in ("blocker", "reason", "obstruction"):
        detail = _reason_label(_read(value, name))
        if detail is not None:
            break
    else:
        detail = "classification"
    return _make(
        variant,
        "undetermined",
        "checked prefix",
        detail,
        "raise the named limit or inspect the blocker",
    )


def _stop_rule(value: Any, variant: str) -> Explanation | None:
    completed = _read(value, "completed_mutations")
    stop = _read(value, "stop")
    if completed is _MISSING or stop is _MISSING:
        return None
    return _make(
        variant,
        "incomplete",
        f"{completed} directed mutations",
        _reason_label(stop),
        "raise the named discovery limit or inspect blocked mutations",
    )


def _blocker_rule(value: Any, variant: str) -> Explanation | None:
    kind = _read(value, "kind")
    generation = _read(value, "generation_kind")
    bound = _read(value, "projective_dimension_bound")
    if kind is _MISSING and generation is _MISSING and bound is _MISSING:
        return None
    detail = _first_present(
        _reason_label(kind) or _MISSING,
        _reason_label(generation) or _MISSING,
        _reason_label(_read(value, "projective_dimension")) or _MISSING,
    )
    return _make(
        variant,
        "undetermined",
        "checked prefix",
        "classification" if detail is _MISSING else detail,
        "raise the named limit or inspect the blocker",
    )


def _has_accessors(value: Any, names: tuple[str, ...]) -> bool:
    return all(_read(value, name) is not _MISSING for name in names)


def _typed_cut_rule(value: Any, variant: str) -> Explanation | None:
    for names, handler in _CUT_RULES:
        if _has_accessors(value, names):
            return handler(value, variant)
    return None


def _replacement_cut(value: Any, variant: str) -> Explanation:
    kind = _read(value, "kind")
    status = _CUT_STATUS.get(kind, "cut")
    action = "raise the named resolution limit or inspect the next kernel"
    if kind == "cancelled":
        action = "rerun without cancellation or inspect the next kernel"
    return _make(
        variant,
        status,
        f"verified prefix length {_read(value, 'prefix_length')}",
        kind,
        action,
    )


def _derived_cut(value: Any, variant: str) -> Explanation:
    kind = _read(value, "kind")
    action = "raise the named limit or inspect the replacement cut"
    if kind in {"replacement_cancelled", "cancelled"}:
        action = "rerun without cancellation or inspect the next degree"
    elif _read(value, "next_degree") is not None:
        action = (
            f"raise the named limit or inspect degree {_read(value, 'next_degree')}"
        )
    return _make(
        variant,
        _CUT_STATUS.get(kind, "cut"),
        f"verified {len(_read(value, 'dimensions'))} graded dimensions",
        kind,
        action,
    )


def _target_cut(value: Any, variant: str) -> Explanation:
    return _make(
        variant,
        "cut",
        "verified target prefix",
        f"{_read(value, 'kind')}:{_read(value, 'stage')}",
        "raise the named target limit",
    )


def _hochschild_cut(value: Any, variant: str) -> Explanation:
    return _make(
        variant,
        "cut",
        f"verified {len(_read(value, 'completed_degrees'))} cohomology degrees",
        _read(value, "reason"),
        "raise the named bar limit",
    )


def _support_cut(value: Any, variant: str) -> Explanation:
    return _make(
        variant,
        "incomplete",
        f"{len(_read(value, 'vertices_found'))} vertices and {len(_read(value, 'verified_mutations'))} mutations",
        _read(value, "reason"),
        "raise the named discovery limit or inspect diagnostics",
    )


def _artifact_cut(value: Any, variant: str) -> Explanation:
    kind = _read(value, "kind")
    return _make(
        variant,
        _CUT_STATUS.get(kind, "cut"),
        "verified artifact prefix",
        kind,
        "raise the verification limit or inspect the cut",
    )


def _reason_label(reason: Any) -> str | None:
    if reason is _MISSING or reason is None:
        return None
    if isinstance(reason, str):
        return reason
    kind = _read(reason, "kind")
    return kind if isinstance(kind, str) else type(reason).__name__


_CUT_STATUS = {"cancelled": "cancelled"}
_CUT_RULES = (
    (("next_degree", "kind"), _derived_cut),
    (("prefix_length", "kind"), _replacement_cut),
    (("stage_kind", "stage"), _target_cut),
    (("completed_degrees", "reason"), _hochschild_cut),
    (("verify_parts", "reason"), _support_cut),
    (("completed", "field", "kind"), _artifact_cut),
)


_COMPUTATION_RULES = (
    _status_rule,
    _typed_status_rule,
    _resolution_rule,
    _nested_rule,
    _bounded_rule,
    _decision_rule,
    _stop_rule,
    _typed_cut_rule,
    _blocker_rule,
)

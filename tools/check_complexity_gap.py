"""Measure GAP function complexity from source tokens."""

from __future__ import annotations

from collections.abc import Callable, Sequence
from pathlib import Path
from typing import Any

try:
    from .check_complexity_source import Token, tokens
except ImportError:
    from check_complexity_source import Token, tokens


ScopeFactory = Callable[..., dict[str, Any]]
GAP_OPENERS = {
    "if": "fi",
    "for": "od",
    "while": "od",
    "repeat": "until",
    "case": "esac",
}
GAP_CLOSERS = frozenset({"fi", "od", "until", "esac", "end"})
GAP_DECISIONS = frozenset(
    {"if", "elif", "for", "while", "repeat", "case", "when", "and", "or"}
)
GAP_PUNCTUATION_OPENERS = frozenset({"(", "[", "{"})
GAP_PUNCTUATION_CLOSERS = {"}": "{", "]": "[", ")": "("}


def _gap_function_name(source_tokens: Sequence[Token], index: int) -> str:
    if index >= 2 and source_tokens[index - 1].text == ":=":
        return source_tokens[index - 2].text
    return "<anonymous>"


def _gap_is_case(source_tokens: Sequence[Token], index: int) -> bool:
    return source_tokens[index].text != "case" or (
        index + 1 < len(source_tokens) and source_tokens[index + 1].text == "of"
    )


def _gap_close(
    source_tokens: Sequence[Token],
    index: int,
    frame: dict[str, Any],
    active: list[dict[str, Any]],
    completed: list[dict[str, Any]],
) -> None:
    token = source_tokens[index]
    blocks = frame["blocks"]
    if token.text == "end":
        if blocks[-1] != "function":
            raise RuntimeError(
                f"GAP block {blocks[-1]} closes with end on line {token.line}"
            )
        completed.append({**frame, "end": index})
        active.pop()
        return
    expected = GAP_OPENERS.get(blocks[-1])
    if expected != token.text:
        raise RuntimeError(
            f"GAP block {blocks[-1]} closes with {token.text} on line {token.line}"
        )
    blocks.pop()


def _gap_frames(source_tokens: Sequence[Token]) -> list[dict[str, Any]]:
    active: list[dict[str, Any]] = []
    completed: list[dict[str, Any]] = []
    for index, token in enumerate(source_tokens):
        if token.text == "function":
            active.append(
                {
                    "name": _gap_function_name(source_tokens, index),
                    "start": index,
                    "blocks": ["function"],
                }
            )
            continue
        if not active:
            continue
        frame = active[-1]
        if token.text in GAP_OPENERS and _gap_is_case(source_tokens, index):
            frame["blocks"].append(token.text)
        elif token.text in GAP_CLOSERS:
            _gap_close(source_tokens, index, frame, active, completed)
    if active:
        frame = active[-1]
        raise RuntimeError(
            f"unterminated GAP function {frame['name']} on line {source_tokens[frame['start']].line}"
        )
    completed.sort(key=lambda frame: (frame["start"], frame["end"]))
    return completed


def _gap_decision(source_tokens: Sequence[Token], index: int) -> bool:
    token = source_tokens[index].text
    return token in GAP_DECISIONS and _gap_is_case(source_tokens, index)


def _gap_punctuation_depths(source_tokens: Sequence[Token]) -> list[int]:
    depth = 0
    depths: list[int] = []
    for token in source_tokens:
        depths.append(depth)
        if token.text in GAP_PUNCTUATION_OPENERS:
            depth += 1
        elif token.text in GAP_PUNCTUATION_CLOSERS:
            depth = max(depth - 1, 0)
    return depths


def _gap_lambda_end(source_tokens: Sequence[Token], start: int, base_depth: int) -> int:
    depth = base_depth
    for index in range(start + 1, len(source_tokens)):
        token = source_tokens[index].text
        if token in GAP_PUNCTUATION_OPENERS:
            depth += 1
        elif token in GAP_PUNCTUATION_CLOSERS:
            if depth == base_depth:
                return index
            depth -= 1
        elif depth == base_depth and (token in {",", ";"} or token in GAP_CLOSERS):
            return index
    return len(source_tokens)


def _gap_lambda_frames(source_tokens: Sequence[Token]) -> list[dict[str, Any]]:
    depths = _gap_punctuation_depths(source_tokens)
    return [
        {
            "name": "<lambda>",
            "start": index,
            "body_start": index + 1,
            "end": _gap_lambda_end(source_tokens, index, depths[index]),
            "kind": "closure",
        }
        for index, token in enumerate(source_tokens)
        if token.text == "->"
    ]


def _gap_raw_complexity(source_tokens: Sequence[Token], frame: dict[str, Any]) -> int:
    body = range(frame["body_start"], frame["end"])
    nested_bases = sum(
        source_tokens[index].text in {"function", "->"} for index in body
    )
    return 1 + nested_bases + sum(_gap_decision(source_tokens, index) for index in body)


def _gap_children(
    completed: Sequence[dict[str, Any]],
) -> dict[int, list[dict[str, Any]]]:
    children: dict[int, list[dict[str, Any]]] = {id(frame): [] for frame in completed}
    stack: list[dict[str, Any]] = []
    for frame in completed:
        while stack and frame["start"] > stack[-1]["end"]:
            stack.pop()
        if stack:
            children[id(stack[-1])].append(frame)
        stack.append(frame)
    return children


def _gap_scope_end_line(source_tokens: Sequence[Token], frame: dict[str, Any]) -> int:
    index = (
        frame["end"]
        if frame["kind"] == "function"
        else max(frame["start"], frame["end"] - 1)
    )
    return source_tokens[index].line


def gap_functions(
    path: Path, root: Path, scope_factory: ScopeFactory
) -> list[dict[str, Any]]:
    """Return direct complexity rows for every GAP function in a file."""

    source_tokens = tokens(path.read_text(encoding="utf-8"), "gap")
    completed = _gap_frames(source_tokens)
    for frame in completed:
        frame["body_start"] = frame["start"] + 1
        frame["kind"] = "function"
    completed.extend(_gap_lambda_frames(source_tokens))
    completed.sort(key=lambda frame: (frame["start"], frame["end"]))
    raw = {id(frame): _gap_raw_complexity(source_tokens, frame) for frame in completed}
    children = _gap_children(completed)
    scopes: list[dict[str, Any]] = []
    for frame in completed:
        total = raw[id(frame)]
        direct = total - sum(raw[id(child)] for child in children[id(frame)])
        if direct < 1:
            raise RuntimeError(
                f"GAP function {frame['name']} has direct complexity {direct}"
            )
        scopes.append(
            scope_factory(
                path=path.relative_to(root).as_posix(),
                language="gap",
                kind=frame["kind"],
                name=str(frame["name"]),
                start_line=source_tokens[frame["start"]].line,
                end_line=_gap_scope_end_line(source_tokens, frame),
                complexity=direct,
                raw_complexity=total,
                metric="gap-source-token-audit",
            )
        )
    return scopes

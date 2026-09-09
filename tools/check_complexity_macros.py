"""Measure Rust macro templates and count their source invocations."""

from __future__ import annotations

from collections.abc import Callable, Sequence
from pathlib import Path
from typing import Any

try:
    from .check_complexity_source import Token, tokens
except ImportError:
    from check_complexity_source import Token, tokens


ScopeFactory = Callable[..., dict[str, Any]]


def _matching_delimiter(tokens: Sequence[Token], start: int) -> int:
    pairs = {"{": "}", "[": "]", "(": ")"}
    closing = {value: key for key, value in pairs.items()}
    stack = [tokens[start].text]
    for index in range(start + 1, len(tokens)):
        token = tokens[index].text
        if token in pairs:
            stack.append(token)
        elif token in closing:
            if not stack or stack[-1] != closing[token]:
                raise RuntimeError(
                    f"unmatched Rust delimiter on line {tokens[index].line}"
                )
            stack.pop()
            if not stack:
                return index
    raise RuntimeError(f"unterminated Rust delimiter on line {tokens[start].line}")


def _macro_close(
    token: Token, delimiters: list[str], match_delimiters: list[int]
) -> None:
    expected = {"}": "{", "]": "[", ")": "("}[token.text]
    if not delimiters or delimiters[-1] != expected:
        raise RuntimeError(f"unmatched macro delimiter on line {token.line}")
    depth = len(delimiters)
    delimiters.pop()
    match_delimiters[:] = [value for value in match_delimiters if value != depth]


def _macro_delimiter(
    token: Token,
    delimiters: list[str],
    match_delimiters: list[int],
    pending_match: bool,
) -> bool:
    if token.text in {"{", "[", "("}:
        delimiters.append(token.text)
        if pending_match and token.text == "{":
            match_delimiters.append(len(delimiters))
            return False
    elif token.text in {"}", "]", ")"}:
        _macro_close(token, delimiters, match_delimiters)
    return pending_match


def macro_complexity(source_tokens: Sequence[Token]) -> int:
    """Count decisions in a Rust macro template before expansion."""

    complexity = 1
    delimiters: list[str] = []
    pending_match = False
    match_delimiters: list[int] = []
    for token in source_tokens:
        text = token.text
        if text in {"if", "for", "while", "loop", "&&", "||"}:
            complexity += 1
        if text == "match":
            pending_match = True
        else:
            pending_match = _macro_delimiter(
                token, delimiters, match_delimiters, pending_match
            )
            if text == "=>" and match_delimiters:
                complexity += 1
    return complexity


def rust_macros(
    path: Path, root: Path, scope_factory: ScopeFactory
) -> list[dict[str, Any]]:
    """Return source complexity rows for every macro_rules template in a file."""

    source_tokens = tokens(path.read_text(encoding="utf-8"), "rust")
    macros: list[dict[str, Any]] = []
    index = 0
    while index + 3 < len(source_tokens):
        if (
            source_tokens[index].text != "macro_rules"
            or source_tokens[index + 1].text != "!"
        ):
            index += 1
            continue
        name = source_tokens[index + 2].text
        opening = index + 3
        while opening < len(source_tokens) and source_tokens[opening].text not in {
            "{",
            "[",
            "(",
        }:
            opening += 1
        if opening == len(source_tokens):
            raise RuntimeError(
                f"macro {name} has no body on line {source_tokens[index].line}"
            )
        closing = _matching_delimiter(source_tokens, opening)
        macros.append(
            scope_factory(
                path=path.relative_to(root).as_posix(),
                language="rust",
                kind="macro",
                name=name,
                start_line=source_tokens[index].line,
                end_line=source_tokens[closing].line,
                complexity=macro_complexity(source_tokens[opening + 1 : closing]),
                metric="rust-source-macro-token-audit",
                extra={"expanded_complexity_measured": False, "invocations": 0},
            )
        )
        index = closing + 1
    return macros


def macro_invocations(files: Sequence[Path], names: set[str]) -> dict[str, int]:
    """Count tokenized Rust invocations for known macro names."""

    counts = {name: 0 for name in names}
    for path in files:
        source_tokens = tokens(path.read_text(encoding="utf-8"), "rust")
        for index, token in enumerate(source_tokens[:-1]):
            if token.text in counts and source_tokens[index + 1].text == "!":
                counts[token.text] += 1
    return counts

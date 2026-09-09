"""Tokenize maintained Rust and GAP source for source complexity audits."""

from __future__ import annotations

import re
from dataclasses import dataclass


_RUST_CHAR_LITERAL = re.compile(
    r"'(?:[^'\\\n\r]|\\(?:['\"\\nrt0]|x[0-9A-Fa-f]{2}|u\{[0-9A-Fa-f]+\}))'"
)


@dataclass(frozen=True)
class Token:
    """Store one source token and its one-based line number."""

    text: str
    line: int


def _comment_end(
    text: str, index: int, language: str, line: int
) -> tuple[int, int] | None:
    marker = "//" if language == "rust" else "#"
    if text.startswith(marker, index):
        newline = text.find("\n", index + len(marker))
        return (len(text), line) if newline < 0 else (newline, line)
    if language != "rust" or not text.startswith("/*", index):
        return None
    cursor, depth = index, 0
    while cursor < len(text):
        if text.startswith("/*", cursor):
            depth += 1
            cursor += 2
        elif text.startswith("*/", cursor):
            depth -= 1
            cursor += 2
            if depth == 0:
                return cursor, line + text[index:cursor].count("\n")
        else:
            cursor += 1
    raise RuntimeError("unterminated Rust block comment")


def _quoted_end(text: str, index: int, line: int, quote: str) -> tuple[int, int]:
    cursor = index + 1
    while cursor < len(text):
        if text[cursor] == "\\":
            cursor += 2
            continue
        line += text[cursor] == "\n"
        if text[cursor] == quote:
            return cursor + 1, line
        cursor += 1
    return cursor, line


def _raw_end(text: str, index: int, line: int) -> tuple[int, int] | None:
    raw = re.match(r"(?:br|r)(#+)?\"", text[index:])
    if not raw:
        return None
    hashes = raw.group(1) or ""
    opening = raw.group(0)
    closing = f'"{hashes}'
    end = text.find(closing, index + len(opening))
    if end < 0:
        raise RuntimeError("unterminated Rust raw string")
    fragment = text[index : end + len(closing)]
    return end + len(closing), line + fragment.count("\n")


def _rust_char_end(text: str, index: int) -> int | None:
    match = _RUST_CHAR_LITERAL.match(text, index)
    return match.end() if match else None


def _quoted_token(
    text: str, index: int, line: int, quote: str, prefix: int = 0
) -> tuple[Token | None, int, int]:
    end, next_line = _quoted_end(text, index + prefix, line, quote)
    return None, end, next_line


def _rust_literal(
    text: str, index: int, line: int
) -> tuple[Token | None, int, int] | None:
    character = text[index]
    if text.startswith('b"', index):
        return _quoted_token(text, index, line, '"', prefix=1)
    if text.startswith("b'", index):
        end = _rust_char_end(text, index + 1)
        if end is not None:
            return None, end, line
    raw = _raw_end(text, index, line)
    if raw:
        return None, *raw
    if character == "'":
        end = _rust_char_end(text, index)
        if end is not None:
            return None, end, line
        return Token("'", line), index + 1, line
    if character == '"':
        return _quoted_token(text, index, line, '"')
    return None


def _literal_token(
    text: str, index: int, line: int, language: str
) -> tuple[Token | None, int, int] | None:
    if language == "rust":
        return _rust_literal(text, index, line)
    if text[index] == '"':
        return _quoted_token(text, index, line, '"')
    return None


def _scan_token(
    text: str, index: int, line: int, language: str
) -> tuple[Token | None, int, int]:
    character = text[index]
    if character == "\n":
        return None, index + 1, line + 1
    if character.isspace():
        return None, index + 1, line
    comment = _comment_end(text, index, language, line)
    if comment:
        return None, *comment
    literal = _literal_token(text, index, line, language)
    if literal:
        return literal
    match = re.match(r"[A-Za-z_][A-Za-z0-9_]*", text[index:])
    if match:
        return Token(match.group(0), line), match.end() + index, line
    operators = (
        ("&&", "||", "=>", "::", "->")
        if language == "rust"
        else (":=", "<>", "<=", ">=", "->", "..")
    )
    operator = next(
        (value for value in operators if text.startswith(value, index)), None
    )
    if operator:
        return Token(operator, line), index + len(operator), line
    return Token(character, line), index + 1, line


def tokens(text: str, language: str) -> list[Token]:
    """Tokenize source while skipping comments and literals."""

    result: list[Token] = []
    index, line = 0, 1
    while index < len(text):
        token, index, line = _scan_token(text, index, line, language)
        if token:
            result.append(token)
    return result

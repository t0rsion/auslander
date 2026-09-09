"""Parser for short bound-quiver presentations."""

from __future__ import annotations

from dataclasses import dataclass
import re
from typing import Any


class PresentationSyntaxError(ValueError):
    """A presentation line has invalid syntax or incompatible paths."""


@dataclass(frozen=True)
class ParsedPresentation:
    """A checked text recipe before the core algebra constructor runs."""

    field: int
    vertices: tuple[int, ...]
    arrows: tuple[tuple[str, int, int], ...]
    relations: tuple[tuple[tuple[int, tuple[int, ...]], ...], ...]

    def build(self) -> Any:
        """Build the core algebra through its checked constructor."""
        from ._core import Algebra, PrimeField, Quiver

        field = PrimeField(self.field)
        quiver = Quiver(len(self.vertices), [(s, t) for _, s, t in self.arrows])
        relations = [
            [(coefficient, list(path)) for coefficient, path in relation]
            for relation in self.relations
        ]
        return Algebra.from_relations(quiver, relations, field)


_ARROW = re.compile(r"([A-Za-z][A-Za-z0-9_]*)\s*:\s*(\d+)\s*->\s*(\d+)")


def _lines(text: str) -> dict[str, str]:
    values: dict[str, str] = {}
    for number, raw in enumerate(text.splitlines(), 1):
        parsed = _parse_line(number, raw)
        if parsed is None:
            continue
        key, value = parsed
        if key in values:
            raise PresentationSyntaxError(f"line {number}: duplicate keyword {key!r}")
        values[key] = value
    missing = _missing_lines(values)
    if missing:
        raise PresentationSyntaxError(f"missing line for {missing[0]!r}")
    return values


def _parse_line(number: int, raw: str) -> tuple[str, str] | None:
    line = raw.split("#", 1)[0].strip()
    if not line:
        return None
    key, separator, value = line.partition(" ")
    if not separator:
        raise PresentationSyntaxError(f"line {number}: expected a keyword and value")
    if key not in {"field", "vertices", "arrows", "relations"}:
        raise PresentationSyntaxError(f"line {number}: unknown keyword {key!r}")
    return key, value.strip()


def _missing_lines(values: dict[str, str]) -> list[str]:
    return [key for key in ("field", "vertices", "arrows") if key not in values]


def _parse_relation_coefficient(factors: list[str]) -> tuple[int, list[str]]:
    coefficient = 1
    if factors[0] in {"-", ""}:
        coefficient = -1
        factors = factors[1:]
    elif re.fullmatch(r"[+-]?\d+", factors[0]):
        coefficient = int(factors.pop(0))
    elif factors[0].startswith("-"):
        coefficient = -1
        factors[0] = factors[0][1:].strip()
    return coefficient, factors


def _parse_relation_path(factors: list[str], names: dict[str, int]) -> tuple[int, ...]:
    if len(factors) < 2:
        raise PresentationSyntaxError("each relation path needs at least two arrows")
    try:
        return tuple(names[name] for name in factors)
    except KeyError as error:
        raise PresentationSyntaxError(f"unknown arrow {error.args[0]!r}") from None


def _validate_composed_path(path: tuple[int, ...], endpoints: tuple[tuple[int, int], ...]) -> None:
    for first, second in zip(path, path[1:]):
        if endpoints[first][1] != endpoints[second][0]:
            raise PresentationSyntaxError("relation path does not compose left to right")


def _relation_term(
    raw: str,
    names: dict[str, int],
    endpoints: tuple[tuple[int, int], ...],
) -> tuple[tuple[int, tuple[int, ...]], tuple[int, int]]:
    factors = [factor.strip() for factor in raw.split("*")]
    coefficient, factors = _parse_relation_coefficient(factors)
    if coefficient == 0:
        raise PresentationSyntaxError("a zero relation coefficient is not accepted")
    path = _parse_relation_path(factors, names)
    _validate_composed_path(path, endpoints)
    current = (endpoints[path[0]][0], endpoints[path[-1]][1])
    return (coefficient, path), current


def _merge_relation_endpoints(
    previous: tuple[int, int] | None,
    current: tuple[int, int],
) -> tuple[int, int]:
    if previous is not None and previous != current:
        raise PresentationSyntaxError("relation terms must have one source and target")
    return current if previous is None else previous


def _relation_expression(text: str) -> str:
    left, separator, right = text.partition("=")
    if not separator:
        raise PresentationSyntaxError("each relation must have the form expression = 0")
    if right.strip() != "0":
        raise PresentationSyntaxError("each relation must have the form expression = 0")
    return left.replace("-", "+-")


def _relation_terms(
    text: str,
    names: dict[str, int],
    endpoints: tuple[tuple[int, int], ...],
) -> tuple[tuple[int, tuple[int, ...]], ...]:
    expression = _relation_expression(text)
    terms: list[tuple[int, tuple[int, ...]]] = []
    relation_endpoints: tuple[int, int] | None = None
    for raw in expression.split("+"):
        raw = raw.strip()
        if not raw:
            continue
        term, current = _relation_term(raw, names, endpoints)
        relation_endpoints = _merge_relation_endpoints(relation_endpoints, current)
        terms.append(term)
    if not terms:
        raise PresentationSyntaxError("a relation needs one nonzero term")
    return tuple(terms)


def _parse_field(value: str) -> int:
    try:
        return int(value)
    except ValueError:
        raise PresentationSyntaxError("field must be an unsigned base-ten integer") from None


def _parse_vertices(value: str) -> tuple[int, ...]:
    try:
        vertices = tuple(int(item) for item in value.split())
    except ValueError:
        raise PresentationSyntaxError("vertices must be unsigned base-ten integers") from None
    if not vertices or vertices != tuple(range(len(vertices))):
        raise PresentationSyntaxError("vertices must be listed as 0 through n - 1")
    return vertices


def _read_arrows(text: str) -> list[tuple[str, int, int]]:
    arrows: list[tuple[str, int, int]] = []
    position = 0
    arrow_text = text
    while position < len(arrow_text):
        match = _ARROW.match(arrow_text, position)
        if match is None:
            raise PresentationSyntaxError(f"invalid arrow near {arrow_text[position:]!r}")
        name, source, target = match.groups()
        arrows.append((name, int(source), int(target)))
        position = match.end()
        while position < len(arrow_text) and arrow_text[position].isspace():
            position += 1
    return arrows


def _validate_arrows(arrows: list[tuple[str, int, int]], vertices: tuple[int, ...]) -> None:
    names = {name: index for index, (name, _, _) in enumerate(arrows)}
    if len(names) != len(arrows):
        raise PresentationSyntaxError("arrow names must be distinct")
    _validate_arrow_endpoints(arrows, vertices)


def _validate_arrow_endpoints(
    arrows: list[tuple[str, int, int]],
    vertices: tuple[int, ...],
) -> None:
    for _, source, target in arrows:
        if source not in vertices:
            raise PresentationSyntaxError("an arrow endpoint is outside the vertex list")
        if target not in vertices:
            raise PresentationSyntaxError("an arrow endpoint is outside the vertex list")


def _parse_arrows(text: str, vertices: tuple[int, ...]) -> tuple[tuple[str, int, int], ...]:
    arrows = _read_arrows(text)
    _validate_arrows(arrows, vertices)
    return tuple(arrows)


def _parse_relations(
    text: str,
    arrows: tuple[tuple[str, int, int], ...],
) -> tuple[tuple[tuple[int, tuple[int, ...]], ...], ...]:
    names = {name: index for index, (name, _, _) in enumerate(arrows)}
    endpoints = tuple((source, target) for _, source, target in arrows)
    return tuple(
        _relation_terms(raw.strip(), names, endpoints)
        for raw in text.split(";")
        if raw.strip()
    )


def parse_presentation(text: str) -> ParsedPresentation:
    """Parse the session presentation language without normalizing bad paths."""
    values = _lines(text)
    field = _parse_field(values["field"])
    vertices = _parse_vertices(values["vertices"])
    arrows = _parse_arrows(values["arrows"], vertices)
    relations = _parse_relations(values.get("relations", ""), arrows)
    return ParsedPresentation(field, vertices, tuple(arrows), relations)

"""Tables and explanations for derived invariants and classifications."""

from __future__ import annotations

from dataclasses import dataclass
from html import escape
from typing import Any

from ._core import DERIVED_INVARIANT_KINDS

MEMBER_LIMIT = 8
"""The number of members a class row lists before it counts the rest."""

_WALK_LIMITS = {
    "vertex_limit": "max_vertices",
    "mutation_limit": "max_directed_mutations",
    "term_limit": "max_total_terms",
    "matrix_limit": "max_matrix_entries",
}


def _monomial(coefficient: int, degree: int) -> str:
    size = abs(coefficient)
    power = "" if degree == 0 else "x" if degree == 1 else f"x^{degree}"
    if degree and size == 1:
        return power
    return f"{size}{power}"


def polynomial_text(coefficients: list[int]) -> str:
    """Write coefficients, constant term first, as a polynomial in `x`."""
    terms = [
        (coefficient, degree)
        for degree, coefficient in enumerate(coefficients)
        if coefficient
    ]
    if not terms:
        return "0"
    parts = []
    for coefficient, degree in reversed(terms):
        sign = "-" if coefficient < 0 else "+"
        parts.append(f"{sign} {_monomial(coefficient, degree)}")
    text = " ".join(parts)
    return text[2:] if text.startswith("+ ") else "-" + text[2:]


def cut_degree(reading: Any, degree: int) -> int | None:
    """Return the first Hochschild degree a bar cut left out, or None.

    A bar cut after `HH^0` keeps the finished prefix, and the reading stays
    `finished` with fewer than `degree + 1` dimensions. Two prefixes differ
    only at a degree present in both.
    """
    if reading.kind != "hochschild_dimensions" or reading.status != "finished":
        return None
    finished = len(reading.value)
    return finished if finished <= degree else None


def reading_text(reading: Any, degree: int) -> str:
    """Write one reading: its value, or why it has none.

    `degree` is the requested last Hochschild degree.
    """
    if reading.status == "finished":
        if reading.kind == "cartan_pencil":
            return polynomial_text(reading.value)
        if reading.kind == "winding_class":
            return reading.value
        cut = cut_degree(reading, degree)
        suffix = "" if cut is None else f", bar cut at HH^{cut}"
        return repr(reading.value) + suffix
    if reading.status == "stopped":
        return f"stopped ({reading.stop})"
    return "not applicable"


def _table(headers: list[str], rows: list[list[str]]) -> list[str]:
    widths = [
        max(len(cell) for cell in column) for column in zip(headers, *rows)
    ]
    return [
        "  " + "  ".join(cell.ljust(width) for cell, width in zip(row, widths)).rstrip()
        for row in [headers, *rows]
    ]


def _html_table(headers: list[str], rows: list[list[str]], omitted: int = 0) -> str:
    head = "".join(f"<th>{escape(cell)}</th>" for cell in headers)
    body = "".join(
        "<tr>" + "".join(f"<td>{escape(cell)}</td>" for cell in row) + "</tr>"
        for row in rows
    )
    if omitted:
        body += f'<tr><td colspan="{len(headers)}">... {omitted} rows omitted</td></tr>'
    return f"<table><thead><tr>{head}</tr></thead><tbody>{body}</tbody></table>"


def _field_text(algebra: Any) -> str:
    return f"F_{algebra.field.p}"


def _invariant_rows(value: Any) -> list[list[str]]:
    rows = []
    degree = value.limits.hochschild_degree
    for reading in value.readings:
        detail = reading_text(reading, degree)
        if reading.status != "finished":
            detail = f"{detail}: {reading.reason}"
        rows.append([reading.kind, reading.status, detail])
    return rows


def _invariants_header(value: Any) -> str:
    algebra = value.algebra
    return (
        f"DerivedInvariants: {algebra.num_vertices} vertices, dim {algebra.dim}, "
        f"field {_field_text(algebra)}, "
        f"Hochschild degrees 0..{value.limits.hochschild_degree}"
    )


_INVARIANTS_SCOPE = (
    "a finished value that differs separates two algebras; "
    "equal values never merge them"
)


def render_invariants(value: Any, _: int) -> tuple[list[str], str | None]:
    """Render one row per invariant kind in table order."""
    lines = [_invariants_header(value)]
    lines.extend(_table(["kind", "status", "value"], _invariant_rows(value)))
    lines.append(f"  {_INVARIANTS_SCOPE}")
    return lines, None


def invariants_html(value: Any, _: int) -> str:
    """Return the invariant table as notebook HTML."""
    table = _html_table(["kind", "status", "value"], _invariant_rows(value))
    header = escape(_invariants_header(value))
    return f"<div><p>{header}</p>{table}<p>{escape(_INVARIANTS_SCOPE)}</p></div>"


def _members_text(members: list[int]) -> str:
    shown = ", ".join(map(str, members[:MEMBER_LIMIT]))
    rest = len(members) - MEMBER_LIMIT
    return f"[{shown}, ... +{rest}]" if rest > 0 else f"[{shown}]"


def _short(reading: Any, degree: int) -> str:
    if reading.status == "finished":
        if reading.kind == "winding_class":
            return str(reading.value)
        cut = "" if cut_degree(reading, degree) is None else " cut"
        return repr(reading.value) + cut
    return "n/a" if reading.status == "not_applicable" else f"stopped ({reading.stop})"


@dataclass(frozen=True)
class _Snapshot:
    """The accessor lists of one classification, read once.

    Each accessor call builds new Python objects, so the renderers read
    every list once and share it.
    """

    value: Any
    classes: list[Any]
    invariants: list[Any]
    separations: list[Any]
    unresolved: list[Any]
    walks: list[Any]


def _snapshot(value: Any) -> _Snapshot:
    return _Snapshot(
        value,
        value.classes,
        value.invariants,
        value.separations,
        value.unresolved,
        value.walks,
    )


_SEPARATED = "every pair of classes is separated by a derived invariant"
_SUMMARY_KINDS = (
    "cartan_determinant",
    "aag_function",
    "winding_class",
    "hochschild_dimensions",
)
_CLASS_HEADERS = ["class", "rep", "members", "merges", "det C", "AAG", "winding", "HH"]
_SEPARATION_HEADERS = ["classes", "members", "invariant", "values"]


def _class_rows(view: _Snapshot, limit: int) -> tuple[list[list[str]], int]:
    rows = []
    degree = view.value.limits.invariants.hochschild_degree
    for index, derived_class in enumerate(view.classes[:limit]):
        record = view.invariants[derived_class.representative]
        rows.append([
            str(index),
            str(derived_class.representative),
            _members_text(derived_class.members),
            str(len(derived_class.merges)),
            *(_short(record.reading(kind), degree) for kind in _SUMMARY_KINDS),
        ])
    return rows, max(0, len(view.classes) - limit)


def separation_counts(value: Any) -> dict[str, int]:
    """Count the separations by witness kind, in table order, omitting zeros."""
    kinds = [separation.witness.kind for separation in value.separations]
    counts = {kind: kinds.count(kind) for kind in DERIVED_INVARIANT_KINDS}
    return {kind: count for kind, count in counts.items() if count}


def _plural(count: int, noun: str) -> str:
    if count == 1:
        return f"{count} {noun}"
    return f"{count} {noun}es" if noun.endswith(("s", "x")) else f"{count} {noun}s"


def _summary(view: _Snapshot) -> list[str]:
    value = view.value
    merges = sum(len(derived_class.merges) for derived_class in view.classes)
    counts = ", ".join(f"{kind} {count}" for kind, count in separation_counts(view).items())
    return [
        (
            f"DerivedClassification: {_plural(len(value.family), 'member')}, "
            f"{_plural(len(view.classes), 'class')}, status {value.status}, "
            f"verification {value.verification}"
        ),
        (
            f"  {_plural(merges, 'merge')} by tilting recipes, "
            f"{_plural(len(view.separations), 'separation')} by invariants, "
            f"{len(view.unresolved)} unresolved, {_plural(len(view.walks), 'walk')}"
        ),
        f"  separations by invariant: {counts or 'none'}",
    ]


def _separation_rows(view: _Snapshot, limit: int) -> tuple[list[list[str]], int]:
    rows = []
    for separation in view.separations[:limit]:
        witness = separation.witness
        rows.append([
            f"{separation.classes[0]} | {separation.classes[1]}",
            f"{separation.members[0]} | {separation.members[1]}",
            witness.kind,
            f"{witness.left_value!r} != {witness.right_value!r}",
        ])
    return rows, max(0, len(view.separations) - limit)


def render_classification(value: Any, max_items: int) -> tuple[list[str], str | None]:
    """Render the class table, the separation counts, and the unresolved pairs."""
    view = _snapshot(value)
    lines = _summary(view)
    rows, omitted = _class_rows(view, max_items)
    lines.extend(_table(_CLASS_HEADERS, rows))
    if omitted:
        lines.append(f"  ... {omitted} classes omitted")
    open_pairs = [f"  unresolved: {line}" for line, _ in _open_pairs(view)]
    lines.extend(open_pairs or [f"  {_SEPARATED}"])
    return lines, None


def classification_html(value: Any, max_items: int) -> str:
    """Return the classification tables as notebook HTML.

    The class and separation tables share `max_items` rows and count the
    rows they omit.
    """
    view = _snapshot(value)
    summary = "<br>".join(escape(line.strip()) for line in _summary(view))
    class_rows, omitted = _class_rows(view, max_items)
    classes = _html_table(_CLASS_HEADERS, class_rows, omitted)
    remaining = max_items - len(class_rows)
    separations = _html_table(_SEPARATION_HEADERS, *_separation_rows(view, remaining))
    parts = [
        f"<div><p>{summary}</p>{classes}",
        f"<details><summary>{len(view.separations)} separations</summary>",
        f"{separations}</details>",
    ]
    lines = [line for line, _ in _open_pairs(view)]
    if lines:
        items = "".join(f"<li>{escape(line)}</li>" for line in lines[:max_items])
        parts.append(f"<p>Unresolved pairs</p><ul>{items}</ul>")
    else:
        parts.append(f"<p>{escape(_SEPARATED)}</p>")
    parts.append("</div>")
    return "".join(parts)


def _walks_text(walks: list[Any], replayed: bool) -> str:
    """Write the stops of the walks of one pair, counted by stop.

    Replay does not rerun a walk, so a replayed result labels its stops as
    recorded.
    """
    if not walks:
        return "no walk ran"
    stops = [
        walk.stop if walk.stop_limit is None else f"{walk.stop} {walk.stop_limit}"
        for walk in walks
    ]
    counts = ", ".join(
        f"{stops.count(stop)} stopped on {stop}" for stop in dict.fromkeys(stops)
    )
    source = "recorded walks (not replayed)" if replayed else "walks"
    return f"{source} from members {_members_text([walk.member for walk in walks])}: {counts}"


def _walk_action(walk: Any) -> str | None:
    field = _WALK_LIMITS.get(walk.stop)
    if field is not None:
        return f"raise discovery.{field} above {walk.stop_limit}"
    if walk.stop == "cancelled":
        return "rerun without cancellation"
    if walk.target_cuts:
        return "raise the target limits"
    return None


def _reading_action(reading: Any, degree: int) -> str | None:
    if reading.stop == "bar_cut" or cut_degree(reading, degree) is not None:
        return "raise the invariants.bar limits"
    if reading.stop == "cancelled":
        return "rerun without cancellation"
    return None


_GENTLE_COMPLETE = ("aag_function", "winding_class")


def _gentle_complete(view: _Snapshot, members: list[int]) -> bool:
    """Return whether the complete gentle invariant finished for both classes.

    An unresolved pair has no separating finished value, so finished values
    are equal, and equal AAG functions and winding classes imply derived
    equivalence (Amiot, Plamondon, and Schroll). Only a merge can then
    settle the pair.
    """
    return all(
        view.invariants[member].reading(kind).status == "finished"
        for member in members
        for kind in _GENTLE_COMPLETE
    )


def _pair_actions(
    view: _Snapshot, members: list[int], walks: list[Any], complete: bool
) -> list[str]:
    degree = view.value.limits.invariants.hochschild_degree
    actions = [_walk_action(walk) for walk in walks]
    actions.extend(
        _reading_action(reading, degree)
        for member in members
        for reading in view.invariants[member].readings
    )
    if not complete:
        actions.append(f"raise invariants.hochschild_degree above {degree}")
    elif not view.value.limits.through_silting:
        actions.append("walk through silting complexes with through_silting=True")
    return list(dict.fromkeys(action for action in actions if action is not None))


def _open_pair(view: _Snapshot, pair: Any) -> tuple[str, list[str]]:
    left, right = (view.classes[index] for index in pair.classes)
    members = [*left.members, *right.members]
    walks = [view.walks[index] for index in pair.walks]
    complete = _gentle_complete(view, members)
    actions = _pair_actions(view, members, walks, complete)
    reason = (
        "their complete gentle invariants agree, which implies a derived "
        "equivalence by Amiot, Plamondon, and Schroll that no merge certifies yet"
        if complete
        else "no finished invariant separates them and no merge joins them"
    )
    stops = _walks_text(walks, view.value.verification == "replayed")
    line = (
        f"classes {pair.classes[0]} and {pair.classes[1]} "
        f"(members {_members_text(left.members)} and {_members_text(right.members)}): "
        f"{reason}; {stops}; next: {' or '.join(actions) or 'no limit applies'}"
    )
    return line, actions


def _open_pairs(view: _Snapshot) -> list[tuple[str, list[str]]]:
    return [_open_pair(view, pair) for pair in view.unresolved]


def classification_explanation(value: Any) -> dict[str, Any]:
    """Return the fields of an `Explanation` of a classification."""
    view = _snapshot(value)
    scope = f"{_plural(len(view.classes), 'class')} of {_plural(len(value.family), 'member')}"
    open_pairs = _open_pairs(view)
    if not open_pairs:
        return {"status": value.status, "completed": f"{scope}; {_SEPARATED}"}
    actions = [action for _, pair_actions in open_pairs for action in pair_actions]
    return {
        "status": value.status,
        "completed": f"{scope}, {_plural(len(view.separations), 'separated pair')}",
        "unfinished": _plural(len(open_pairs), "unresolved pair"),
        "next_action": " or ".join(dict.fromkeys(actions)),
        "details": tuple(line for line, _ in open_pairs),
    }


def _latex_value(reading: Any, degree: int) -> str:
    if reading.status != "finished":
        return "n/a" if reading.status == "not_applicable" else "stopped"
    if reading.kind == "aag_function":
        return "$" + ", ".join(f"({n}, {m})" for n, m in reading.value) + "$"
    if reading.kind == "hochschild_dimensions":
        cut = "" if cut_degree(reading, degree) is None else ", cut"
        return ", ".join(map(str, reading.value)) + cut
    return str(reading.value)


def _latex_comments(view: _Snapshot) -> list[str]:
    value = view.value
    lines = [f"% {line.strip()}" for line in _summary(view)]
    if value.fingerprint is not None:
        lines.append(f"% derived-atlas-v1 fingerprint {value.fingerprint}")
    lines.extend(
        f"% unresolved: classes {pair.classes[0]} and {pair.classes[1]}"
        for pair in view.unresolved
    )
    return lines


def classification_latex(value: Any) -> str:
    """Return a LaTeX `tabular` with one row per class and every member.

    Comment lines above the table carry the summary, the atlas fingerprint
    of a replayed result, and each unresolved pair. The invariant columns
    read the class representative. A Hochschild prefix that a bar cut
    shortened ends in `cut`.
    """
    view = _snapshot(value)
    degree = value.limits.invariants.hochschild_degree
    rows = []
    for index, derived_class in enumerate(view.classes):
        record = view.invariants[derived_class.representative]
        cells = [str(index), ", ".join(map(str, derived_class.members))]
        cells.extend(_latex_value(record.reading(kind), degree) for kind in _SUMMARY_KINDS)
        rows.append(" & ".join(cells) + r" \\")
    head = (
        r"Class & Members & $\det C$ & AAG function & Winding class & "
        rf"$\dim \mathrm{{HH}}^i$, $i \le {degree}$ \\"
    )
    return "\n".join([
        *_latex_comments(view),
        r"\begin{tabular}{rlrlll}",
        r"\hline",
        head,
        r"\hline",
        *rows,
        r"\hline",
        r"\end{tabular}",
    ]) + "\n"

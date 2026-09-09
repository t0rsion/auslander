"""Bounded deterministic renderings and structured explanations."""

from __future__ import annotations

from dataclasses import dataclass
from html import escape
import math
from typing import Any


@dataclass(frozen=True)
class Rendered:
    """Text with optional bounded notebook HTML and SVG."""

    text: str
    html: str
    svg: str | None = None
    omitted: int = 0

    def __str__(self) -> str:
        return self.text

    def _repr_html_(self) -> str:
        return self.html

    def _repr_svg_(self) -> str | None:
        return self.svg


@dataclass(frozen=True)
class Explanation:
    """The outcome variant, completed work, first open item, and next action."""

    variant: str
    status: str
    completed: str
    unfinished: str | None
    next_action: str | None


def _bounded(items: list[str], limit: int) -> tuple[list[str], int]:
    return items[:limit], max(0, len(items) - limit)


def _quiver_svg(quiver: Any, limit: int) -> str | None:
    count = quiver.num_vertices
    if count == 0 or count > limit:
        return None
    return _quiver_svg_body(count, quiver.arrows)


def _quiver_svg_body(count: int, arrows: list[tuple[int, int]]) -> str:
    width = 440
    height = 260
    radius = 90
    points = [
        (
            width / 2 + radius * math.cos(2 * math.pi * index / count),
            height / 2 + radius * math.sin(2 * math.pi * index / count),
        )
        for index in range(count)
    ]
    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" '
        f'viewBox="0 0 {width} {height}">',
        '<defs><marker id="a" markerWidth="8" markerHeight="8" refX="7" refY="3" '
        'orient="auto"><path d="M0,0 L0,6 L8,3 z" fill="#555"/></marker></defs>',
    ]
    for source, target in arrows:
        x1, y1 = points[source]
        x2, y2 = points[target]
        parts.append(
            f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" '
            'stroke="#555" marker-end="url(#a)"/>'
        )
    for index, (x, y) in enumerate(points):
        parts.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="17" fill="#fff" stroke="#222"/>')
        parts.append(f'<text x="{x:.1f}" y="{y + 5:.1f}" text-anchor="middle">{index}</text>')
    parts.append("</svg>")
    return "".join(parts)


def _quiver_lines(value: Any) -> list[str]:
    lines = [f"Quiver: {value.num_vertices} vertices, {value.num_arrows} arrows"]
    lines.extend(f"  {index}: {source} -> {target}" for index, (source, target) in enumerate(value.arrows))
    return lines


def _ar_quiver_parts(value: Any) -> tuple[list[Any], list[Any]]:
    return value.vertices(), value.arrows()


def _ar_quiver_svg(value: Any, limit: int) -> str | None:
    vertices, arrows = _ar_quiver_parts(value)
    if not vertices or len(vertices) > limit:
        return None
    endpoints = [(arrow.source, arrow.target) for arrow in arrows]
    return _quiver_svg_body(len(vertices), endpoints)


def _ar_quiver_lines(value: Any) -> list[str]:
    vertices, arrows = _ar_quiver_parts(value)
    lines = [f"ArQuiver: {len(vertices)} vertices, {len(arrows)} arrows"]
    lines.extend(f"  vertex {vertex.id}: {vertex.module.dims}" for vertex in vertices)
    lines.extend(
        f"  arrow {index}: {arrow.source} -> {arrow.target} (dim {arrow.base_field_dim})"
        for index, arrow in enumerate(arrows)
    )
    return lines


def _algebra_lines(value: Any, max_items: int) -> list[str]:
    return [
        f"Algebra: dim {value.dim}, field {value.field}",
        str(show(value.quiver, max_items=max_items)),
    ]


def _module_lines(value: Any) -> list[str]:
    lines = [f"Module: dimension vector {value.dims}"]
    lines.extend(f"  arrow {index}: {matrix}" for index, matrix in enumerate(value.maps))
    return lines


def _complex_lines(value: Any, kind: str) -> list[str]:
    lines = [f"{kind}: degrees {getattr(value, 'degree_range', 'display order')}"]
    lines.extend(f"  term {index}: {term.dims}" for index, term in enumerate(value.terms))
    return lines


def _resolution_lines(value: Any, kind: str) -> list[str]:
    lines = [f"{kind}: {len(value.terms)} stored terms"]
    lines.extend(f"  term {index}: {term.dims}" for index, term in enumerate(value.terms))
    return lines


def _render_perfect_replacement(value: Any, _: int) -> tuple[list[str], str | None]:
    return [
        f"PerfectReplacement: input {value.original.degree_range}",
        f"  projective model {value.projective.degree_range}",
    ], None


def _render_derived_hom(value: Any, _: int) -> tuple[list[str], str | None]:
    lines = [f"DerivedHom: support {value.support}"]
    lines.extend(
        f"  degree {degree}: {dimension}"
        for degree, dimension in zip(
            range(value.support[0], value.support[1] + 1), value.dimensions
        )
    )
    return lines, None


def _render_transport(value: Any, _: int) -> tuple[list[str], str | None]:
    return [
        f"DerivedTransportResult: {value.direction}",
        f"  input {value.input.degree_range}",
        f"  output {value.output.degree_range}",
    ], None


def _render_artifact(value: Any, _: int) -> tuple[list[str], str | None]:
    return [
        f"VerifiedDerivedArtifact: {value.mutation_count} mutations",
        f"  fields {value.source_field} -> {value.target_field}",
        f"  fingerprint {value.fingerprint}",
    ], None


def _render_graph(value: Any) -> tuple[list[str], str | None]:
    lines = [f"{type(value).__name__}: {value.vertex_count} vertices, {len(value.edges)} edges, stop {value.stop}"]
    lines.extend(
        f"  {source} -> {target} ({direction} {summand})"
        for source, target, direction, summand in value.edges
    )
    return lines, None


def _render_vertices(value: Any) -> tuple[list[str], str | None]:
    lines = [f"{type(value).__name__}: {len(value.vertices)} vertices, {len(value.edges)} edges"]
    lines.extend(str(edge) for edge in value.edges)
    return lines, None


def _support_pair_line(index: int, pair: Any) -> str:
    modules = [module.dims for module in pair.module_summands]
    return f"  vertex {index}: modules {modules}, projective support {pair.projective_support}"


def _support_mutation_line(mutation: Any) -> str:
    details = f"slot {mutation.slot}, {mutation.shape}"
    if mutation.exchanged_vertex is not None:
        details += f", exchanged {mutation.exchanged_vertex}"
    if mutation.multiplicity is not None:
        details += f", multiplicity {mutation.multiplicity}"
    return f"  {mutation.source_vertex} -> {mutation.target_vertex} ({details})"


def _support_graph_data(value: Any) -> tuple[list[Any], list[Any], str, int]:
    if type(value).__name__ == "ClosedSupportTauTiltingGraph":
        return value.pairs(), value.mutations(), "complete", value.work_units()
    return value.vertices_found, value.verified_mutations, value.reason, value.work_units()


def _render_support_graph(value: Any, _: int) -> tuple[list[str], str | None]:
    vertices, mutations, stop, work_units = _support_graph_data(value)
    lines = [
        f"{type(value).__name__}: {len(vertices)} vertices, {len(mutations)} edges, "
        f"stop {stop}, work {work_units}"
    ]
    lines.extend(_support_pair_line(index, pair) for index, pair in enumerate(vertices))
    lines.extend(_support_mutation_line(mutation) for mutation in mutations)
    if type(value).__name__ == "IncompleteSupportTauTiltingGraph":
        lines.append(f"  diagnostics: {value.diagnostics!r}")
    return lines, None


def _render_optional(value: Any) -> tuple[list[str], str | None] | None:
    if hasattr(value, "keys"):
        if hasattr(value, "edges"):
            return _render_graph(value)
    elif hasattr(value, "vertices"):
        if hasattr(value, "edges"):
            return _render_vertices(value)
    return None


def _render_quiver(value: Any, max_items: int) -> tuple[list[str], str | None]:
    return _quiver_lines(value), _quiver_svg(value, max_items)


def _render_ar_quiver(value: Any, max_items: int) -> tuple[list[str], str | None]:
    return _ar_quiver_lines(value), _ar_quiver_svg(value, max_items)


def _render_algebra(value: Any, max_items: int) -> tuple[list[str], str | None]:
    return _algebra_lines(value, max_items), _quiver_svg(value.quiver, max_items)


def _render_module(value: Any, _: int) -> tuple[list[str], str | None]:
    return _module_lines(value), None


def _render_complex(value: Any, _: int) -> tuple[list[str], str | None]:
    return _complex_lines(value, type(value).__name__), None


def _render_resolution(value: Any, _: int) -> tuple[list[str], str | None]:
    return _resolution_lines(value, type(value).__name__), None


_RENDERERS = {
    "Quiver": _render_quiver,
    "ArQuiver": _render_ar_quiver,
    "Algebra": _render_algebra,
    "Module": _render_module,
    "BoundedComplex": _render_complex,
    "CheckedComplex": _render_complex,
    "Resolution": _render_resolution,
    "InjectiveCoresolution": _render_resolution,
    "PerfectReplacement": _render_perfect_replacement,
    "DerivedHom": _render_derived_hom,
    "DerivedTransportResult": _render_transport,
    "VerifiedDerivedArtifact": _render_artifact,
    "ClosedSupportTauTiltingGraph": _render_support_graph,
    "IncompleteSupportTauTiltingGraph": _render_support_graph,
}


def _render_value(value: Any, max_items: int) -> tuple[list[str], str | None]:
    renderer = _RENDERERS.get(type(value).__name__)
    if renderer is not None:
        return renderer(value, max_items)
    optional = _render_optional(value)
    if optional is not None:
        return optional
    return [repr(value)], None


def show(value: Any, *, max_items: int = 200, max_chars: int = 12000) -> Rendered:
    """Render stored data without triggering a mathematical computation."""
    lines, svg = _render_value(value, max_items)
    lines, omitted = _bounded(lines, max_items)
    if omitted:
        lines.append(f"... {omitted} items omitted")
    text = "\n".join(lines)
    if len(text) > max_chars:
        omitted += len(text) - max_chars
        text = text[:max_chars] + f"\n... {len(text) - max_chars} characters omitted"
    html = f"<pre>{escape(text)}</pre>"
    return Rendered(text, html, svg, omitted)


def explain(value: Any) -> Explanation:
    """Describe a typed result without parsing exception or repr text."""
    variant = type(value).__name__
    if variant == "IncompletePerfectReplacement":
        return _explain_replacement_cut(value, variant)
    if variant == "IncompleteDerivedHom":
        return _explain_derived_hom_cut(value, variant)
    return _explain_standard(value, variant)


def _explain_standard(value: Any, variant: str) -> Explanation:
    if hasattr(value, "is_tilting"):
        return _explain_tilting(value, variant)
    if hasattr(value, "stop"):
        return _explain_stop(value, variant)
    if _is_cut_variant(variant):
        return _explain_cut(value, variant)
    if hasattr(value, "verify"):
        return Explanation(variant, "complete", "stored certificate", None, None)
    return Explanation(variant, "value", "construction", None, None)


def _explain_tilting(value: Any, variant: str) -> Explanation:
    answer = value.is_tilting
    if answer is True:
        return Explanation(variant, "complete", "tilting obligations", None, None)
    if answer is False:
        return Explanation(variant, "rejected", "self-extension check", None, None)
    blocker = type(value.blocker).__name__ if value.blocker is not None else "classification"
    return Explanation(variant, "undetermined", "checked prefix", blocker, "raise the named limit or inspect the blocker")


def _explain_stop(value: Any, variant: str) -> Explanation:
    return Explanation(
        variant,
        "incomplete",
        f"{value.completed_mutations} directed mutations",
        value.stop,
        "raise the named discovery limit or inspect blocked mutations",
    )


def _explain_replacement_cut(value: Any, variant: str) -> Explanation:
    action = "raise the named resolution limit or inspect the next kernel"
    if value.kind == "cancelled":
        action = "rerun without cancellation or inspect the next kernel"
    return Explanation(
        variant,
        "incomplete",
        f"verified prefix length {value.prefix_length}",
        value.kind,
        action,
    )


def _explain_derived_hom_cut(value: Any, variant: str) -> Explanation:
    next_degree = value.next_degree
    action = "raise the named limit or inspect the replacement cut"
    if value.kind in {"replacement_cancelled", "cancelled"}:
        action = "rerun without cancellation or inspect the next degree"
    elif next_degree is not None:
        action = f"raise the named limit or inspect degree {next_degree}"
    return Explanation(
        variant,
        "incomplete",
        f"verified {len(value.dimensions)} graded dimensions",
        value.kind,
        action,
    )


def _explain_cut(value: Any, variant: str) -> Explanation:
    kind = getattr(value, "kind", None)
    if kind is not None:
        unfinished = kind if isinstance(kind, str) else type(kind).__name__
        return Explanation(
            variant,
            "incomplete",
            "verified prefix",
            unfinished,
            "inspect the typed cut",
    )
    reason = getattr(value, "reason", None)
    unfinished = (
        reason
        if isinstance(reason, str)
        else type(reason).__name__
        if reason is not None
        else "incomplete"
    )
    return Explanation(variant, "incomplete", "verified prefix", unfinished, "inspect the typed cut")


def _is_cut_variant(variant: str) -> bool:
    if variant.startswith("Incomplete"):
        return True
    return variant.endswith("Cut")


def _graph_dot(value: Any, max_items: int) -> str:
    nodes, omitted_nodes = _bounded(
        [f'  {index} [label="{index}"];' for index in range(value.vertex_count)],
        max_items,
    )
    edges, omitted_edges = _bounded(
        [
            f'  {source} -> {target} [label="{direction} {summand}"];'
            for source, target, direction, summand in value.edges
        ],
        max_items,
    )
    omitted = omitted_nodes + omitted_edges
    if omitted:
        edges.append(f"  // {omitted} items omitted")
    return "digraph auslander {\n" + "\n".join(nodes + edges) + "\n}"


def _ar_quiver_dot(value: Any, max_items: int) -> str:
    vertices, arrows = _ar_quiver_parts(value)
    nodes, omitted_nodes = _bounded(
        [f'  {vertex.id} [label="{vertex.id}"];' for vertex in vertices],
        max_items,
    )
    edges, omitted_edges = _bounded(
        [
            f'  {arrow.source} -> {arrow.target} [label="dim {arrow.base_field_dim}"];'
            for arrow in arrows
        ],
        max_items,
    )
    omitted = omitted_nodes + omitted_edges
    if omitted:
        edges.append(f"  // {omitted} items omitted")
    return "digraph auslander {\n" + "\n".join(nodes + edges) + "\n}"


def _support_graph_dot(value: Any, max_items: int) -> str:
    vertices, mutations, _, _ = _support_graph_data(value)
    nodes, omitted_nodes = _bounded(
        [f'  {index} [label="{index}"];' for index in range(len(vertices))],
        max_items,
    )
    edges, omitted_edges = _bounded(
        [
            f'  {mutation.source_vertex} -> {mutation.target_vertex} '
            f'[label="slot {mutation.slot} {mutation.shape}"];'
            for mutation in mutations
        ],
        max_items,
    )
    omitted = omitted_nodes + omitted_edges
    if omitted:
        edges.append(f"  // {omitted} items omitted")
    return "digraph auslander {\n" + "\n".join(nodes + edges) + "\n}"


def _quiver_dot(value: Any, max_items: int) -> str:
    quiver = getattr(value, "quiver", value)
    if not hasattr(quiver, "arrows"):
        raise TypeError("to_dot expects a quiver or algebra")
    arrows = list(quiver.arrows)
    kept, omitted = _bounded([f"  {s} -> {t};" for s, t in arrows], max_items)
    if omitted:
        kept.append(f"  // {omitted} arrows omitted")
    return "digraph auslander {\n" + "\n".join(kept) + "\n}"


def to_dot(value: Any, *, max_items: int = 200) -> str:
    """Return bounded Graphviz DOT without importing a renderer."""
    name = type(value).__name__
    if name == "ArQuiver":
        return _ar_quiver_dot(value, max_items)
    if name in {"ClosedSupportTauTiltingGraph", "IncompleteSupportTauTiltingGraph"}:
        return _support_graph_dot(value, max_items)
    if hasattr(value, "keys") and hasattr(value, "edges"):
        return _graph_dot(value, max_items)
    return _quiver_dot(value, max_items)


def _module_latex(value: Any) -> str:
    return r"\operatorname{dim} M=" + str(tuple(value.dims))


def _graph_latex(value: Any) -> str:
    edges = ", ".join(
        f"{source}\\xrightarrow{{{direction[0]}_{summand}}}{target}"
        for source, target, direction, summand in value.edges
    )
    return r"\mathcal{G}=(" + edges + ")"


def _ar_quiver_latex(value: Any) -> str:
    _, arrows = _ar_quiver_parts(value)
    edges = ", ".join(
        f"{arrow.source}\\xrightarrow{{{arrow.base_field_dim}}}{arrow.target}"
        for arrow in arrows
    )
    return r"\mathcal{AR}(Q)=(" + edges + ")"


def _support_graph_latex(value: Any) -> str:
    _, mutations, _, _ = _support_graph_data(value)
    edges = ", ".join(
        f"{mutation.source_vertex}\\xrightarrow{{slot_{mutation.slot}}}"
        f"{mutation.target_vertex}"
        for mutation in mutations
    )
    return r"\mathcal{G}_{\tau}= (" + edges + ")"


def _quiver_latex(value: Any) -> str:
    quiver = getattr(value, "quiver", value)
    if hasattr(quiver, "arrows"):
        arrows = ", ".join(f"{source}\\to {target}" for source, target in quiver.arrows)
        return r"Q=(" + arrows + ")"
    return r"\texttt{" + escape(repr(value)) + "}"


def to_networkx(value: Any) -> Any:
    """Copy a supported quiver or graph into NetworkX when installed."""
    import networkx as nx

    name = type(value).__name__
    if name == "ArQuiver":
        return _ar_quiver_networkx(nx, value)
    if name in {"ClosedSupportTauTiltingGraph", "IncompleteSupportTauTiltingGraph"}:
        return _support_graph_networkx(nx, value)
    if _is_equivalence_graph(value):
        return _equivalence_graph_networkx(nx, value)
    return _quiver_networkx(nx, value)


def _ar_quiver_networkx(nx: Any, value: Any) -> Any:
    graph = nx.MultiDiGraph()
    vertices, arrows = _ar_quiver_parts(value)
    graph.add_nodes_from(vertex.id for vertex in vertices)
    for index, arrow in enumerate(arrows):
        graph.add_edge(
            arrow.source,
            arrow.target,
            key=index,
            base_field_dim=arrow.base_field_dim,
            dim_over_source_residue=arrow.dim_over_source_residue,
            dim_over_target_residue=arrow.dim_over_target_residue,
        )
    return graph


def _support_graph_networkx(nx: Any, value: Any) -> Any:
    graph = nx.MultiDiGraph()
    vertices, mutations, stop, _ = _support_graph_data(value)
    graph.graph["stop"] = stop
    graph.add_nodes_from(range(len(vertices)))
    for mutation in mutations:
        graph.add_edge(
            mutation.source_vertex,
            mutation.target_vertex,
            slot=mutation.slot,
            shape=mutation.shape,
            exchanged_vertex=mutation.exchanged_vertex,
            multiplicity=mutation.multiplicity,
        )
    return graph


def _is_equivalence_graph(value: Any) -> bool:
    return hasattr(value, "keys") and hasattr(value, "edges")


def _equivalence_graph_networkx(nx: Any, value: Any) -> Any:
    graph = nx.MultiDiGraph()
    graph.add_nodes_from(range(value.vertex_count))
    for source, target, direction, summand in value.edges:
        graph.add_edge(source, target, direction=direction, summand=summand)
    return graph


def _quiver_networkx(nx: Any, value: Any) -> Any:
    graph = nx.MultiDiGraph()
    quiver = getattr(value, "quiver", value)
    graph.add_nodes_from(range(quiver.num_vertices))
    for index, (source, target) in enumerate(quiver.arrows):
        graph.add_edge(source, target, key=index)
    return graph


def to_latex(value: Any) -> str:
    """Return a small LaTeX representation without importing a renderer."""
    name = type(value).__name__
    if name == "Module":
        return _module_latex(value)
    if name == "ArQuiver":
        return _ar_quiver_latex(value)
    if name in {"ClosedSupportTauTiltingGraph", "IncompleteSupportTauTiltingGraph"}:
        return _support_graph_latex(value)
    if _is_equivalence_graph(value):
        return _graph_latex(value)
    return _quiver_latex(value)

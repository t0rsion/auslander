"""Bounded deterministic renderings and structured explanations."""

from __future__ import annotations

import math
from dataclasses import dataclass
from html import escape
from typing import Any

from .explanation import Explanation, explain  # noqa: F401


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
        (
            f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" '
            f'viewBox="0 0 {width} {height}">'
        ),
        (
            '<defs><marker id="a" markerWidth="8" markerHeight="8" refX="7" refY="3" '
            'orient="auto"><path d="M0,0 L0,6 L8,3 z" fill="#555"/></marker></defs>'
        ),
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


def _field_text(value: Any) -> str:
    """Return the public prime-field label for a catalog value."""
    field = getattr(value, "p", value)
    return f"F_{field}"


def _render_catalog(value: Any, _: int) -> tuple[list[str], str | None]:
    """Render catalog provenance and certified entry dimensions."""
    entries = value.entries
    lines = [
        (
            f"IndecomposableCatalog: {len(entries)} entries, "
            f"provenance {value.provenance}, field {_field_text(value.field)}"
        )
    ]
    lines.extend(f"  {index}: {entry.dims}" for index, entry in enumerate(entries))
    return lines, None


def _render_higher_orthogonality(value: Any, _: int) -> tuple[list[str], str | None]:
    """Render higher Ext orthogonality rows and decisions."""
    lines = [
        (
            f"HigherOrthogonality: chosen={value.chosen}, max_degree={value.max_degree}, "
            f"left={value.left}, right={value.right}, rigid={value.is_rigid}"
        ),
        f"  two-sided maximal={value.is_two_sided_maximal}",
    ]
    lines.extend(
        f"  pair {pair.source} -> {pair.target}: {pair.dimensions}"
        for pair in value.pairs
    )
    return lines, None


def _render_ext_table(value: Any, _: int) -> tuple[list[str], str | None]:
    """Render an ordered catalog Ext table."""
    lines = [
        (
            f"CatalogExtTable: {value.catalog_len} entries, "
            f"degree bound {value.max_degree}, rows {len(value)}"
        )
    ]
    lines.extend(
        f"  {row.source} -> {row.target}: {row.dimensions}"
        for row in value.rows
    )
    return lines, None


def _render_atlas(value: Any, _: int) -> tuple[list[str], str | None]:
    """Render catalog atlas metadata and cached work counts."""
    work = value.work
    lines = [
        (
            f"CatalogAtlas: {len(value)} entries, provenance {value.provenance}, "
            f"field {_field_text(value.field)}, degree bound {value.max_degree}"
        ),
        (
            f"  pairs={work.pairs}, ext_cells={work.ext_cells}, "
            f"resolutions={work.resolutions}, ext_tables={work.ext_tables}"
        ),
    ]
    return lines, None


def _render_multiplicity(value: Any, _: int) -> tuple[list[str], str | None]:
    """Render multiplicity status, verification state, and retained rows."""
    lines = [
        (
            f"MultiplicityResult: status={value.status}, verification={value.verification}, "
            f"target={value.target_dimensions}, solutions={len(value)}"
        ),
        f"  nodes_visited={value.nodes_visited}",
    ]
    lines.extend(f"  {index}: {solution}" for index, solution in enumerate(value.solutions))
    return lines, None


def _render_catalog_atlas_artifact(value: Any, _: int) -> tuple[list[str], str | None]:
    """Render catalog atlas artifact metadata and multiplicity rows."""
    lines = [
        (
            f"{type(value).__name__}: status={value.status}, "
            f"verification={value.verification}, field=F_{value.field}, "
            f"provenance={value.provenance}"
        ),
        (
            f"  target={value.target_dimensions}, max_degree={value.max_degree}, "
            f"result_rows={len(value.result_rows)}"
        ),
        f"  fingerprint={value.fingerprint}",
    ]
    lines.extend(
        f"  {index}: {row.multiplicities} -> {row.self_ext}"
        for index, row in enumerate(value.result_rows)
    )
    return lines, None


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
    if hasattr(value, "pairs") and hasattr(value, "mutations"):
        return value.pairs(), value.mutations(), "complete", value.work_units()
    return value.vertices_found, value.verified_mutations, value.reason, value.work_units()


def _render_support_graph(value: Any, _: int) -> tuple[list[str], str | None]:
    vertices, mutations, stop, work_units = _support_graph_data(value)
    lines = [
        (
            f"{type(value).__name__}: {len(vertices)} vertices, {len(mutations)} edges, "
            f"stop {stop}, work {work_units}"
        )
    ]
    lines.extend(_support_pair_line(index, pair) for index, pair in enumerate(vertices))
    lines.extend(_support_mutation_line(mutation) for mutation in mutations)
    if hasattr(value, "diagnostics"):
        lines.append(f"  diagnostics: {value.diagnostics!r}")
    return lines, None


def _render_optional(value: Any) -> tuple[list[str], str | None] | None:
    if hasattr(value, "keys") and hasattr(value, "edges"):
        return _render_graph(value)
    if hasattr(value, "vertices") and hasattr(value, "edges"):
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
    "IndecomposableCatalog": _render_catalog,
    "HigherOrthogonality": _render_higher_orthogonality,
    "CatalogExtTable": _render_ext_table,
    "CatalogAtlas": _render_atlas,
    "MultiplicityResult": _render_multiplicity,
    "CatalogAtlasArtifact": _render_catalog_atlas_artifact,
    "VerifiedCatalogAtlasArtifact": _render_catalog_atlas_artifact,
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

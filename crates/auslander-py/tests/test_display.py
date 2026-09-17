"""Display adapters for complete and incomplete public values."""

import auslander
import pytest

FIELD = auslander.PrimeField(5)


def test_ar_quiver_renderers_use_method_accessors():
    ar_quiver = auslander.Algebra.linear_an(2).ar_quiver(FIELD)

    rendered = auslander.show(ar_quiver, max_items=100)
    assert "ArQuiver:" in str(rendered)
    assert "arrow" in str(rendered)
    assert rendered._repr_svg_().startswith("<svg")
    assert "0 ->" in auslander.to_dot(ar_quiver)
    assert "\\xrightarrow" in auslander.to_latex(ar_quiver)

    nx = pytest.importorskip("networkx")
    graph = auslander.to_networkx(ar_quiver)
    assert len(graph) == len(ar_quiver.vertices())
    assert graph.number_of_edges() == len(ar_quiver.arrows())
    assert nx.MultiDiGraph is type(graph)


def test_catalog_atlas_renderers_show_scope_and_multiplicity_status():
    quiver = auslander.Quiver(4, [(0, 1), (1, 2), (3, 2)])
    catalog = auslander.Algebra(quiver, [[0, 1]], FIELD).catalog()
    atlas = catalog.atlas(3)
    result = atlas.enumerate([1, 1, 1, 1])
    orthogonality = catalog.higher_orthogonality([0], 2)

    catalog_text = str(auslander.show(catalog))
    atlas_text = str(auslander.show(atlas))
    result_text = str(auslander.show(result))
    orthogonality_text = str(auslander.show(orthogonality))

    assert "provenance gentle_tree" in catalog_text
    assert "degree bound 3" in atlas_text
    assert "status=complete, verification=computed" in result_text
    assert "HigherOrthogonality:" in orthogonality_text


def test_support_tau_tilting_renderers_use_closed_graph_apis():
    graph = auslander.Algebra.linear_an(2).support_tau_tilting_graph(FIELD)

    text = str(auslander.show(graph, max_items=100))
    assert "ClosedSupportTauTiltingGraph:" in text
    assert "stop complete" in text
    assert "slot" in text
    assert "slot" in auslander.to_dot(graph)
    assert "\\xrightarrow" in auslander.to_latex(graph)

    nx_graph = auslander.to_networkx(graph)
    assert nx_graph.graph["stop"] == "complete"
    assert len(nx_graph) == len(graph.pairs())
    assert nx_graph.number_of_edges() == len(graph.mutations())


def test_support_tau_tilting_renderers_use_incomplete_graph_apis():
    graph = auslander.Algebra.kronecker(2).support_tau_tilting_graph(
        FIELD,
        limits=auslander.MutationGraphLimits(max_vertices=6),
    )

    text = str(auslander.show(graph, max_items=100))
    assert "IncompleteSupportTauTiltingGraph:" in text
    assert "stop budget_exhausted" in text
    assert "GraphBudgetDiagnostics" in text
    assert "slot" in auslander.to_dot(graph)
    assert "\\xrightarrow" in auslander.to_latex(graph)

    nx_graph = auslander.to_networkx(graph)
    assert nx_graph.graph["stop"] == "budget_exhausted"
    assert len(nx_graph) == len(graph.vertices_found)
    assert nx_graph.number_of_edges() == len(graph.verified_mutations)


def test_explain_incomplete_derived_values_uses_typed_cuts():
    algebra = auslander.Algebra.an_with_relations(3, [(0, 2)])
    source = auslander.BoundedComplex(0, [algebra.simple(0, field=FIELD)], [])
    target = auslander.BoundedComplex(0, [algebra.simple(2, field=FIELD)], [])

    replacement = source.perfect_replacement(
        auslander.ReplacementLimits(max_resolution_steps=0)
    )
    replacement_explanation = auslander.explain(replacement)
    assert replacement_explanation.unfinished == "cut"
    assert "prefix length" in replacement_explanation.completed

    derived = source.derived_hom(target, auslander.DerivedHomLimits(max_degrees=1))
    derived_explanation = auslander.explain(derived)
    assert derived_explanation.unfinished == "work_cut"
    assert "graded dimensions" in derived_explanation.completed


def test_explain_cancellation_does_not_suggest_raising_limits():
    algebra = auslander.Algebra.an_with_relations(3, [(0, 2)])
    source = auslander.BoundedComplex(0, [algebra.simple(0, field=FIELD)], [])
    target = auslander.BoundedComplex(0, [algebra.simple(2, field=FIELD)], [])

    replacement_control = auslander.ComputationControl()
    replacement_control.cancel()
    replacement = source.perfect_replacement(control=replacement_control)
    replacement_explanation = auslander.explain(replacement)
    assert replacement.kind == "cancelled"
    assert replacement_explanation.unfinished == "cancelled"
    assert "rerun without cancellation" in replacement_explanation.next_action
    assert "raise" not in replacement_explanation.next_action

    derived_control = auslander.ComputationControl()
    derived_control.cancel()
    derived = source.derived_hom(target, control=derived_control)
    derived_explanation = auslander.explain(derived)
    assert derived.kind == "replacement_cancelled"
    assert derived_explanation.unfinished == "replacement_cancelled"
    assert "rerun without cancellation" in derived_explanation.next_action
    assert "raise" not in derived_explanation.next_action

"""Package workbench, text input, persistence, display, and artifact entry."""

from pathlib import Path
import os
import subprocess
import sys

import pytest

import auslander
from auslander.__main__ import _namespace


PRESENTATION = """
field 5
vertices 0 1 2
arrows a:0->1 b:1->2
relations a*b = 0
"""


def test_text_presentation_builds_the_checked_pd2_fixture():
    parsed = auslander.parse_presentation(PRESENTATION)
    algebra = parsed.build()

    assert parsed.field == 5
    assert parsed.arrows == (("a", 0, 1), ("b", 1, 2))
    assert algebra.dim == 5
    assert algebra.quiver.arrows == [(0, 1), (1, 2)]


@pytest.mark.parametrize(
    "change, message",
    [
        ("arrows a:0->1 a:1->2", "distinct"),
        ("relations b*a = 0", "compose"),
        ("relations a*c = 0", "unknown arrow"),
        ("vertices 1 2 3", "0 through"),
    ],
)
def test_text_parser_rejects_bad_names_paths_and_vertices(change, message):
    lines = PRESENTATION.strip().splitlines()
    key = change.split(" ", 1)[0]
    text = "\n".join(change if line.startswith(key + " ") else line for line in lines)
    with pytest.raises(auslander.PresentationSyntaxError, match=message):
        auslander.parse_presentation(text)


def test_session_save_rebuilds_recipes_not_python_objects(tmp_path):
    session = auslander.Session(5)
    algebra = session.algebra("A", PRESENTATION)
    module = session.module("M", "A", [1, 1, 0], [[[1]], [[]]])
    session.display["max_items"] = 17
    path = tmp_path / "session.json"
    session.save(path)

    reloaded = auslander.Session.load(path)
    assert reloaded.names == ("A", "M")
    assert reloaded["A"].certificate_json() == algebra.certificate_json()
    assert reloaded["M"].dims == module.dims == [1, 1, 0]
    assert reloaded.display["max_items"] == 17
    assert "pickle" not in path.read_text(encoding="utf-8")


def test_bounded_display_and_optional_adapters_do_not_compute():
    algebra = auslander.parse_presentation(PRESENTATION).build()
    quiver = algebra.quiver
    rendered = auslander.show(quiver)

    assert "3 vertices" in str(rendered)
    assert rendered._repr_html_().startswith("<pre>")
    assert rendered._repr_svg_().startswith("<svg")
    assert "0 -> 1" in auslander.to_dot(quiver)
    assert "0\\to 1" in auslander.to_latex(quiver)
    explanation = auslander.explain(algebra)
    assert explanation.variant == "Algebra"
    assert explanation.status == "value"


def test_shell_namespace_and_typed_package_files_are_present():
    namespace = _namespace()
    assert {"session", "F", "algebra", "module", "show", "explain", "verify_file"} <= set(namespace)
    assert {"run_census", "write_checkpoint", "verify_checkpoint"} <= set(namespace)
    package = Path(auslander.__file__).parent
    assert (package / "py.typed").is_file()
    assert (package / "_core.pyi").is_file()
    assert auslander.__version__ == "0.8.0"


def test_stable_hom_exposes_projective_factors_and_reduction():
    field = auslander.PrimeField(5)
    algebra = auslander.Algebra.dual_numbers()
    simple = algebra.simple(field, 0)
    projective = algebra.projective(field, 0)

    stable_simple = simple.stable_hom(simple)
    assert stable_simple.dim == 1
    assert stable_simple.projective_factor_dim == 0
    assert len(stable_simple.basis) == 1

    stable_projective = projective.stable_hom(projective)
    assert stable_projective.dim == 0
    assert stable_projective.projective_factor_dim == projective.hom_dim(projective)
    morphism = projective.hom(projective)[0]
    coordinates, factor = stable_projective.reduce(morphism)
    assert coordinates == []
    assert stable_projective.is_projective_factor(factor)
    assert factor.maps == morphism.maps


def test_syzygy_and_cosyzygy_return_recheckable_prefixes():
    field = auslander.PrimeField(5)
    algebra = auslander.Algebra.dual_numbers()
    simple = algebra.simple(field, 0)

    omega = simple.syzygy()
    omega_inverse = simple.cosyzygy()
    assert omega.degree == omega_inverse.degree == 1
    assert omega.module.dims == omega_inverse.module.dims == simple.dims
    assert omega.resolution.status.kind == auslander.ResolutionKind.CUT
    assert omega_inverse.coresolution.status.kind == auslander.ResolutionKind.CUT
    assert omega.verify() and omega_inverse.verify()

    assert simple.syzygy(0).resolution is None
    assert simple.cosyzygy(0).coresolution is None


def test_homological_batch_reuses_sources_and_target_covers():
    field = auslander.PrimeField(5)
    algebra = auslander.Algebra.linear_an(3)
    modules = [algebra.simple(field, vertex) for vertex in range(3)]
    selected = [(0, 0), (0, 1), (2, 1)]
    batch = auslander.HomologicalBatch(modules, 2, selected)
    _assert_batch_work(batch, selected)
    _assert_batch_pairs(batch, modules)


def _assert_batch_work(batch, selected):

    assert batch.selected_pairs == selected
    assert batch.work.resolutions == 2
    assert batch.work.target_covers == 2
    assert batch.work.hom_spaces == len(selected)
    assert batch.work.ext_tables == len(selected)
    assert batch.resolution(1) is None
    assert batch.resolution(2).status.kind in {
        auslander.ResolutionKind.FINITE,
        auslander.ResolutionKind.CUT,
    }


def _assert_batch_pairs(batch, modules):
    for result in batch.pairs:
        source = modules[result.source]
        target = modules[result.target]
        assert result.hom_dim == source.hom_dim(target)
        assert result.stable_hom_dim == source.stable_hom_dim(target)
        assert result.ext_dimensions == source.ext_table(target, 2)
    assert batch.stable_hom(1).dim == batch.pairs[1].stable_hom_dim
    assert batch.verify()


def test_homological_batch_defaults_to_self_pairs_and_checks_size_first():
    field = auslander.PrimeField(5)
    algebra = auslander.Algebra.dual_numbers()
    modules = [algebra.simple(field, 0), algebra.projective(field, 0)]
    batch = auslander.HomologicalBatch(modules, 2)
    assert batch.selected_pairs == [(0, 0), (1, 1)]

    all_pairs = auslander.HomologicalBatch.all_pairs(modules, 1)
    assert all_pairs.selected_pairs == [(0, 0), (0, 1), (1, 0), (1, 1)]

    limits = auslander.HomologicalBatchLimits(max_ext_cells=1)
    with pytest.raises(auslander.BudgetExhaustedError, match="Ext cells"):
        auslander.HomologicalBatch(modules, 2, limits=limits)


def test_artifact_binding_rejects_untrusted_bad_json_as_value_error():
    with pytest.raises(ValueError, match="artifact JSON"):
        auslander.verify_derived_artifact("{}")


@pytest.mark.parametrize("prime", [2, 5])
def test_python_builds_and_independently_verifies_multi_degree_artifacts(prime):
    field = auslander.PrimeField(prime)
    algebra = auslander.Algebra.linear_an(2)
    text = auslander.build_derived_artifact(algebra, [("left", 1)], field)
    verified = auslander.verify_derived_artifact(text)

    assert isinstance(verified, auslander.VerifiedDerivedArtifact)
    assert verified.mutation_count == 1
    assert verified.source_field == verified.target_field == prime
    assert verified.canonical_json == text
    assert verified.verify()


def test_session_persists_only_canonical_verified_artifacts(tmp_path):
    field = auslander.PrimeField(5)
    algebra = auslander.Algebra.linear_an(2)
    text = auslander.build_derived_artifact(algebra, [("left", 1)], field)
    session = auslander.Session(5)
    session.add_artifact("edge", text)
    path = tmp_path / "artifacts.json"
    session.save(path)

    loaded = auslander.Session.load(path)
    assert loaded.artifacts == {"edge": text}


@pytest.mark.parametrize("prime", [2, 5])
def test_python_perfect_replacement_and_derived_hom_keep_typed_cuts(prime):
    field = auslander.PrimeField(prime)
    algebra = auslander.Algebra.an_with_relations(3, [(0, 2)])
    source = auslander.BoundedComplex(0, [algebra.simple(field, 0)], [])
    target = auslander.BoundedComplex(0, [algebra.simple(field, 2)], [])

    replacement = source.perfect_replacement()
    _assert_perfect_replacement(replacement)

    cut = source.perfect_replacement(auslander.ReplacementLimits(max_resolution_steps=0))
    _assert_replacement_cut(cut)

    hom = source.derived_hom(target)
    _assert_derived_hom(hom)

    hom_cut = source.derived_hom(target, auslander.DerivedHomLimits(max_degrees=1))
    _assert_derived_hom_cut(hom_cut)


def _assert_perfect_replacement(replacement):
    assert isinstance(replacement, auslander.PerfectReplacement)
    assert replacement.projective.degree_range == (0, 2)
    assert replacement.verify()


def _assert_replacement_cut(cut):
    assert isinstance(cut, auslander.IncompletePerfectReplacement)
    assert cut.kind == "cut"
    assert cut.verify()


def _assert_derived_hom(hom):
    assert isinstance(hom, auslander.DerivedHom)
    assert hom.dimension(2) == 1
    assert hom.verify()


def _assert_derived_hom_cut(hom_cut):
    assert isinstance(hom_cut, auslander.IncompleteDerivedHom)
    assert hom_cut.kind == "work_cut"
    assert hom_cut.next_degree is not None
    assert hom_cut.verify()


def test_python_control_returns_typed_cancellation_and_progress():
    field = auslander.PrimeField(5)
    algebra = auslander.Algebra.an_with_relations(3, [(0, 2)])
    source = auslander.BoundedComplex(0, [algebra.simple(field, 0)], [])
    control = auslander.ComputationControl()
    control.cancel()

    cancelled = source.perfect_replacement(control=control)
    assert isinstance(cancelled, auslander.IncompletePerfectReplacement)
    assert cancelled.kind == "cancelled"
    assert cancelled.verify()
    assert control.is_cancelled
    assert control.stage == "idle"

    text = auslander.build_derived_artifact(
        auslander.Algebra.linear_an(2), [("left", 1)], field
    )
    artifact = auslander.verify_derived_artifact(text, control)
    assert isinstance(artifact, auslander.IncompleteArtifactVerification)
    assert artifact.kind == "cancelled"
    assert control.stage == "artifact_verify"


@pytest.mark.parametrize("prime", [2, 5])
def test_python_discovers_a_checked_bounded_equivalence_graph(prime):
    field = auslander.PrimeField(prime)
    limits = auslander.EquivalenceDiscoveryLimits(max_directed_mutations=2)
    graph = auslander.discover_equivalences(
        auslander.Algebra.linear_an(2), field, limits
    )
    _assert_discovered_graph(graph)
    _assert_cancelled_graph(field)


def _assert_discovered_graph(graph):

    assert graph.stop == "mutation_limit"
    assert graph.completed_mutations == 2
    assert len(graph.keys) >= 1
    assert graph.vertex_count == len(graph.keys)
    assert graph.verify()
    assert "stop mutation_limit" in str(auslander.show(graph))
    assert "left" in auslander.to_dot(graph)
    assert "\\xrightarrow" in auslander.to_latex(graph)
    assert auslander.explain(graph).unfinished == "mutation_limit"


def _assert_cancelled_graph(field):
    control = auslander.ComputationControl()
    control.cancel()
    cancelled = auslander.discover_equivalences(
        auslander.Algebra.linear_an(2), field, control=control
    )
    assert cancelled.stop == "cancelled"
    assert cancelled.completed_mutations == 0
    assert cancelled.verify()
    assert control.stage == "mutation"


def test_python_renderings_and_artifacts_match_across_fresh_processes():
    script = r'''
import json
import auslander

field = auslander.PrimeField(5)
algebra = auslander.Algebra.linear_an(2)
rendered = auslander.show(algebra.quiver)
graph = auslander.discover_equivalences(
    algebra,
    field,
    limits=auslander.EquivalenceDiscoveryLimits(max_directed_mutations=1),
)
artifact = auslander.build_derived_artifact(algebra, [("left", 1)], field)
print(json.dumps({
    "text": str(rendered),
    "html": rendered._repr_html_(),
    "svg": rendered._repr_svg_(),
    "dot": auslander.to_dot(algebra.quiver),
    "latex": auslander.to_latex(algebra.quiver),
    "keys": graph.keys,
    "edges": graph.edges,
    "stop": graph.stop,
    "artifact": artifact,
}, sort_keys=True, separators=(",", ":")))
'''

    def run(seed):
        environment = os.environ | {"PYTHONHASHSEED": str(seed)}
        return subprocess.run(
            [sys.executable, "-c", script],
            check=True,
            capture_output=True,
            text=True,
            env=environment,
        ).stdout

    assert run(1) == run(2)


@pytest.mark.parametrize("prime", [2, 5])
def test_python_automatic_transport_accepts_ordinary_complexes(prime):
    field = auslander.PrimeField(prime)
    algebra = auslander.Algebra.an_with_relations(3, [(0, 2)])
    dual = algebra.module(
        field,
        [2, 2, 1],
        [
            [[0, 0], [1, 0]],
            [[0], [1]],
        ],
    )
    classified = auslander.ClassicalTiltingModule.classify(
        dual, auslander.TiltingLimits(4, 8)
    )
    target = classified.tilting.target_presentation(auslander.TargetLimits())
    certificate = auslander.DerivedEquivalenceCertificate(classified.tilting, target)
    transport = certificate.automatic_transport
    source = auslander.BoundedComplex(0, [algebra.simple(field, 0)], [])

    forward = transport.forward(source)
    assert isinstance(forward, auslander.DerivedTransportResult)
    assert forward.direction == "forward"
    assert forward.verify()
    reverse = transport.reverse(forward.output)
    assert isinstance(reverse, auslander.DerivedTransportResult)
    assert reverse.direction == "reverse"
    assert reverse.verify()


def test_complete_python_session_runs_the_workbench(tmp_path):
    session = auslander.Session(5)
    field = session.field
    algebra = session.algebra("A", PRESENTATION)
    source = auslander.BoundedComplex(0, [algebra.simple(field, 0)], [])
    target = auslander.BoundedComplex(0, [algebra.simple(field, 2)], [])
    assert source.perfect_replacement().verify()
    assert source.derived_hom(target).dimension(2) == 1

    dual = algebra.module(
        field,
        [2, 2, 1],
        [[[0, 0], [1, 0]], [[0], [1]]],
    )
    tilting = auslander.ClassicalTiltingModule.classify(
        dual, auslander.TiltingLimits(4, 8)
    ).tilting
    presentation = tilting.target_presentation(auslander.TargetLimits())
    transport = auslander.DerivedEquivalenceCertificate(
        tilting, presentation
    ).automatic_transport
    assert transport.forward(source).verify()

    mutation_algebra = auslander.Algebra.linear_an(2)
    graph = auslander.discover_equivalences(
        mutation_algebra,
        field,
        auslander.EquivalenceDiscoveryLimits(max_vertices=3),
    )
    assert graph.verify()
    text = auslander.build_derived_artifact(
        mutation_algebra, [("left", 1)], field
    )
    assert auslander.verify_derived_artifact(text).canonical_json == text

    session.add_artifact("A2-left", text)
    path = tmp_path / "workbench-session.json"
    session.save(path)
    assert auslander.Session.load(path).artifacts["A2-left"] == text

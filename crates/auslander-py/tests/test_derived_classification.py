"""Test derived invariants, gentle presentations, and certified classification."""

import json
import re
from pathlib import Path

import pytest

import auslander

F2 = auslander.PrimeField(2)
RECORD = (
    Path(__file__).resolve().parents[2]
    / "auslander/artifacts/research/derived-classification-f2-n3.json"
)
GUIDE = Path(__file__).resolve().parents[1] / "docs/derived-classification.md"


def _record():
    return json.loads(RECORD.read_text())


def _values(invariants):
    return {reading.kind: reading.value for reading in invariants.readings}


def _a3_with_relation():
    quiver = auslander.Quiver(3, [(0, 1), (1, 2)])
    return auslander.Algebra(quiver, [[0, 1]], field=F2)


def _commutative_square():
    quiver = auslander.Quiver(4, [(0, 1), (1, 3), (0, 2), (2, 3)])
    return auslander.Algebra.from_relations(quiver, [[(1, [0, 1]), (-1, [2, 3])]], F2)


@pytest.fixture(scope="module")
def n3():
    family = auslander.connected_gentle_algebras(3, F2)
    return auslander.classify_derived(family)


def test_invariant_kinds_are_in_table_order():
    assert auslander.DERIVED_INVARIANT_KINDS == (
        "vertex_count",
        "cartan_determinant",
        "cartan_factors",
        "symmetric_factors",
        "skew_factors",
        "cartan_pencil",
        "aag_function",
        "winding_class",
        "hochschild_dimensions",
        "center_dimension",
    )


def test_invariants_of_the_a3_path_algebra():
    invariants = auslander.Algebra.linear_an(3).derived_invariants(field=F2)

    assert [reading.kind for reading in invariants.readings] == list(
        auslander.DERIVED_INVARIANT_KINDS
    )
    assert all(reading.status == "finished" for reading in invariants.readings)
    assert _values(invariants) == {
        "vertex_count": 3,
        "cartan_determinant": 1,
        "cartan_factors": [1, 1, 1],
        "symmetric_factors": [1, 1, 4],
        "skew_factors": [1, 1, 0],
        "cartan_pencil": [1, 1, 1, 1],
        "aag_function": [(4, 2)],
        "winding_class": "planar",
        "hochschild_dimensions": [1, 0, 0],
        "center_dimension": 1,
    }
    assert invariants.first_difference(_a3_with_relation().derived_invariants()) is None


def test_invariants_of_the_kronecker_algebra():
    kronecker = auslander.Algebra.kronecker(2, F2).derived_invariants()

    assert _values(kronecker) == {
        "vertex_count": 2,
        "cartan_determinant": 1,
        "cartan_factors": [1, 1],
        "symmetric_factors": [2, 0],
        "skew_factors": [2, 2],
        "cartan_pencil": [1, -2, 1],
        "aag_function": [(1, 1), (1, 1)],
        "winding_class": "planar",
        "hochschild_dimensions": [1, 3, 0],
        "center_dimension": 1,
    }
    a2 = auslander.Algebra.linear_an(2).derived_invariants(field=F2)
    assert kronecker.first_difference(a2) == "symmetric_factors"
    assert kronecker["symmetric_factors"].separates(a2["symmetric_factors"])

    witness = auslander.DerivedInequivalenceWitness(kronecker, a2)
    assert witness.kind == "symmetric_factors"
    assert (witness.left_value, witness.right_value) == ([2, 0], [1, 3])
    assert witness.verify()


def test_readings_type_their_stops_and_failed_hypotheses():
    limits = auslander.InvariantLimits(
        hochschild_degree=1, bar=auslander.BarLimits(1, 1, 1, 1)
    )
    invariants = _commutative_square().derived_invariants(limits)

    aag = invariants.reading("aag_function")
    assert (aag.status, aag.value, aag.stop) == ("not_applicable", None, None)
    assert "monomial" in aag.reason
    hochschild = invariants["hochschild_dimensions"]
    assert (hochschild.status, hochschild.stop) == ("stopped", "bar_cut")
    assert hochschild.bar_diagnostics.reason == "max_tensor_tuples"
    assert invariants["cartan_determinant"].status == "finished"
    assert not aag.separates(aag)


def test_invariant_errors_are_value_errors():
    invariants = _a3_with_relation().derived_invariants()
    with pytest.raises(ValueError, match="unknown invariant kind"):
        invariants.reading("euler_form")
    with pytest.raises(ValueError, match="no finished invariant"):
        auslander.DerivedInequivalenceWitness(invariants, invariants)
    with pytest.raises(ValueError, match="does not separate"):
        auslander.DerivedInequivalenceWitness(invariants, invariants, "vertex_count")
    with pytest.raises(ValueError, match="needs a field"):
        auslander.Algebra.linear_an(2).derived_invariants()


def test_gentle_presentation_reports_aag_function_and_genus():
    presentation = _a3_with_relation().gentle()

    assert presentation.aag_function == [(4, 2)]
    assert presentation.genus == 0
    assert presentation.relations == [(0, 1)]
    assert presentation.key == presentation.key.algebra(F2).gentle().key
    assert [len(thread) for thread in presentation.permitted_threads] == [1, 0, 1, 0]
    assert presentation.full_relation_cycles == []


def test_complete_gentle_invariant_matches_the_path_algebra():
    invariant = _a3_with_relation().gentle().complete_invariant()
    assert (invariant.aag_function, invariant.genus) == ([(4, 2)], 0)
    assert invariant.winding_class == "planar"
    assert invariant == auslander.Algebra.linear_an(3).gentle(F2).complete_invariant()


@pytest.mark.parametrize("n", [1, 2, 3, 4])
def test_path_algebras_of_type_a_have_one_aag_pair(n):
    presentation = auslander.Algebra.linear_an(n).gentle(F2)

    assert presentation.aag_function == [(n + 1, n - 1)]
    assert presentation.genus == 0


def test_rejected_recognition_is_a_typed_value_error():
    with pytest.raises(auslander.NotGentleError) as caught:
        _commutative_square().gentle()

    assert isinstance(caught.value, ValueError)
    assert caught.value.kind == "non_monomial"


def test_family_counts_match_the_record():
    families = _record()["families"]

    for family in families:
        keys = auslander.connected_gentle_keys(family["vertices"])
        algebras = auslander.connected_gentle_algebras(family["vertices"], F2)
        assert len(keys) == len(algebras) == family["members"]
        assert keys == sorted(keys)
    assert [family["members"] for family in families] == [2, 9, 77]


def test_genus_identity_holds_for_every_three_vertex_presentation():
    for algebra in auslander.connected_gentle_algebras(3, F2):
        presentation = algebra.gentle()
        threads = len(presentation.permitted_threads)
        doubled = 3 - threads - len(presentation.aag_function) + 2
        assert doubled == 2 * presentation.genus


def test_gentle_isomorphism_relabels_arrows_and_vertices():
    reversed_labels = auslander.Algebra(
        auslander.Quiver(3, [(1, 0), (2, 1)]), [[1, 0]], field=F2
    )
    isomorphism = auslander.AlgebraIsomorphism.from_gentle(
        _a3_with_relation(), reversed_labels
    )

    assert isomorphism.vertex_map == [2, 1, 0]
    assert isomorphism.verify()
    with pytest.raises(ValueError, match="different canonical keys"):
        auslander.AlgebraIsomorphism.from_gentle(
            _a3_with_relation(), auslander.Algebra.linear_an(3).over(F2)
        )
    with pytest.raises(auslander.NotGentleError):
        auslander.AlgebraIsomorphism.from_gentle(
            _commutative_square(), _commutative_square()
        )


def _summary(result):
    kinds = [separation.witness.kind for separation in result.separations]
    return {
        "members": len(result.family),
        "classes": len(result.classes),
        "merged": sum(len(derived_class.merges) for derived_class in result.classes),
        "separated": len(result.separations),
        "unresolved": len(result.unresolved),
        "status": result.status,
        "open_pairs": [
            [result.classes[index].members for index in pair.classes]
            for pair in result.unresolved
        ],
        "walks": len(result.walks),
        "separations_by_kind": {kind: kinds.count(kind) for kind in set(kinds)},
    }


def _expected(family):
    by_kind = family["stage2"]["separations_by_kind"]
    return {
        "members": family["members"],
        "classes": family["classes"],
        "merged": family["merged"],
        "separated": family["separated"],
        "unresolved": family["unresolved"],
        "status": family["status"],
        "open_pairs": family["open_pairs"],
        "walks": family["stage3"]["walks"],
        "separations_by_kind": {
            _snake(kind): count for kind, count in by_kind.items() if count
        },
    }


def _snake(name):
    return "".join(f"_{c.lower()}" if c.isupper() else c for c in name).lstrip("_")


def test_default_limits_are_the_limits_of_the_record():
    recorded = _record()["limits"]
    limits = auslander.ClassificationLimits()

    assert limits.invariants.hochschild_degree == recorded["hochschild_degree"]
    assert limits.discovery.max_vertices == recorded["walk_vertices"]
    assert limits.discovery.max_directed_mutations == recorded["walk_mutations"]
    assert limits.discovery.max_total_terms == recorded["walk_terms"]
    assert limits.discovery.max_matrix_entries == recorded["walk_matrix_entries"]


@pytest.mark.parametrize("vertices", [1, 2])
def test_small_classifications_match_the_record(vertices):
    family = _record()["families"][vertices - 1]
    result = auslander.classify_derived(
        auslander.connected_gentle_algebras(vertices, F2)
    )

    assert _summary(result) == _expected(family)
    assert result.verify() is family["verified"]


def test_three_vertex_classification_matches_the_record(n3):
    family = _record()["families"][2]

    assert _summary(n3) == _expected(family)
    assert n3.verify() is family["verified"]
    counts = ("members", "classes", "merged", "separated", "unresolved")
    assert [family[key] for key in counts] == [77, 30, 47, 435, 0]
    assert family["stage3"]["walks"] == 21


def test_winding_class_separates_equal_aag_functions(n3):
    separation = next(
        s for s in n3.separations if s.witness.kind == "winding_class"
    )
    left, right = (n3.family[member].gentle() for member in separation.members)

    assert left.aag_function == right.aag_function
    assert left.genus == right.genus == 1
    assert left.complete_invariant() != right.complete_invariant()
    assert separation.witness.verify()


def test_classes_partition_the_family_with_spanning_merges(n3):
    members = sorted(m for derived_class in n3.classes for m in derived_class.members)
    assert members == list(range(len(n3.family)))
    for index, derived_class in enumerate(n3.classes):
        assert len(derived_class.merges) == len(derived_class) - 1
        assert {n3.class_of(member) for member in derived_class.members} == {index}


def test_merges_and_separations_recheck_one_by_one(n3):
    merges = [merge for c in n3.classes for merge in c.merges]
    merge = next(merge for merge in merges if not merge.is_duplicate)
    assert merge.recipe
    assert merge.isomorphism.verify()
    assert n3.separations[0].witness.verify()
    assert n3.verification == "computed"


def test_cancellation_leaves_pairs_unresolved():
    control = auslander.ComputationControl()
    control.cancel()
    family = auslander.connected_gentle_algebras(2, F2)
    result = auslander.classify_derived(family, control=control)

    assert result.status == "incomplete"
    assert result.walks
    assert all(walk.stop == "cancelled" for walk in result.walks)
    assert all(walk.stop_limit is None for walk in result.walks)
    center = result.invariants[0]["center_dimension"]
    assert (center.status, center.stop) == ("stopped", "cancelled")
    assert result.verify()
    assert "rerun without cancellation" in result.explain().next_action


def test_classification_rejects_mixed_fields():
    family = [
        auslander.Algebra.linear_an(2).over(F2),
        auslander.Algebra.linear_an(2).over(auslander.PrimeField(3)),
    ]
    with pytest.raises(ValueError, match=r"GF.*Algebra\.over\(field\)"):
        auslander.classify_derived(family)
    with pytest.raises(ValueError, match="needs a field"):
        auslander.classify_derived([auslander.Algebra.linear_an(2)])
    bound = auslander.classify_derived([auslander.Algebra.linear_an(2)], field=F2)
    assert bound.status == "complete"


def _tight_limits():
    walk = auslander.EquivalenceDiscoveryLimits(
        max_vertices=1,
        max_directed_mutations=4,
        max_total_terms=32,
        max_matrix_entries=2048,
    )
    return auslander.ClassificationLimits(discovery=walk)


def _silting_walk():
    return auslander.EquivalenceDiscoveryLimits(
        max_vertices=32,
        max_directed_mutations=128,
        max_total_terms=1024,
        max_matrix_entries=65536,
        through_silting=True,
    )


def test_through_silting_is_off_by_default_and_overridable():
    walk = _silting_walk()
    assert walk.through_silting
    assert "through_silting=True" in repr(walk)
    assert auslander.ClassificationLimits(discovery=walk).through_silting
    override = auslander.ClassificationLimits(discovery=walk, through_silting=False)
    assert not override.through_silting
    assert not auslander.ClassificationLimits().through_silting
    assert not auslander.EquivalenceDiscoveryLimits().through_silting


def test_a_silting_walk_merges_members_470_and_724():
    pair = [
        auslander.Algebra(
            auslander.Quiver(4, [(0, 1), (0, 2), (3, 1), (2, 3), (2, 3)]),
            [[1, 4], [4, 2]],
            field=F2,
        ),
        auslander.Algebra(
            auslander.Quiver(4, [(0, 1), (1, 2), (0, 1), (2, 3), (2, 3)]),
            [[0, 1], [1, 4]],
            field=F2,
        ),
    ]
    walk = _silting_walk()
    limits = auslander.ClassificationLimits(discovery=walk)
    tilting = auslander.ClassificationLimits(discovery=walk, through_silting=False)
    assert auslander.classify_derived(pair, limits=tilting).status == "incomplete"
    result = auslander.classify_derived(pair, limits=limits)
    assert result.status == "complete"
    assert result.verify()
    text = result.to_artifact().canonical_json
    assert "\"through_silting\":true" in text
    replayed = auslander.verify_derived_atlas(text)
    assert replayed.verification == "replayed"


def test_explanation_names_each_open_pair_and_the_next_limit():
    family = auslander.connected_gentle_algebras(2, F2)
    result = auslander.classify_derived(family, limits=_tight_limits())
    explanation = result.explain()

    assert explanation.status == result.status == "incomplete"
    assert explanation.verification == "computed"
    assert len(explanation.details) == len(result.unresolved) > 0
    assert explanation.next_action == (
        "raise discovery.max_vertices above 1 or walk through silting complexes "
        "with through_silting=True"
    )
    assert "complete gentle invariants agree" in explanation.details[0]
    assert "walks from members [0, 3]: 2 stopped on vertex_limit 1" in explanation.details[0]
    assert str(explanation).splitlines()[0] == (
        "DerivedClassification: status incomplete, verification computed"
    )
    assert auslander.explain(result) == explanation
    assert result.verify()


def test_a_replayed_explanation_marks_walk_stops_as_recorded():
    family = auslander.connected_gentle_algebras(2, F2)
    result = auslander.classify_derived(family, limits=_tight_limits())
    replayed = auslander.verify_derived_atlas(result.to_artifact().canonical_json)
    recorded = "recorded walks (not replayed) from members [0, 3]"
    assert recorded in replayed.explain().details[0]


def test_complete_explanation_says_every_pair_is_separated(n3):
    explanation = n3.explain()

    assert explanation.status == n3.status == "complete"
    assert "every pair of classes is separated" in explanation.completed
    assert (explanation.unfinished, explanation.next_action) == (None, None)
    assert explanation.details == ()


def test_notebook_display_is_bounded_html(n3):
    html = n3._repr_html_()

    assert html.startswith("<div>")
    assert html.endswith("</div>")
    assert html.count("<table>") == 2
    assert "every pair of classes is separated" in html
    assert "rows omitted" in auslander.show(n3, max_items=5).html
    invariants = n3.invariants[0]
    assert invariants._repr_html_().count("<tr>") == 1 + len(invariants)


def test_plain_repr_lists_classes_and_open_pairs(n3):
    text = repr(n3)

    assert f"{len(n3.classes)} classes" in text
    assert "every pair of classes is separated" in text
    assert "items omitted" in str(auslander.show(n3, max_items=5))
    assert repr(n3.invariants[0]).startswith("DerivedInvariants:")


def test_guide_examples_run():
    namespace = {}
    for block in re.findall(r"```python\n(.*?)```", GUIDE.read_text(), re.S):
        exec(block, namespace)


def test_guide_explanation_output_is_current():
    text = GUIDE.read_text().split("The explanation reads:")[1]
    printed = re.search(r"```text\n(.*?)```", text, re.S).group(1)
    family = auslander.connected_gentle_algebras(2, F2)
    explanation = auslander.classify_derived(family, limits=_tight_limits()).explain()

    assert printed.splitlines() == [explanation.next_action, *explanation.details]

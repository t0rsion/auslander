"""Test the v0.10 Python surface at its edges: limits, walks, fields, and families."""

import pytest

import auslander

F2 = auslander.PrimeField(2)
F5 = auslander.PrimeField(5)


def _a3_with_relation():
    quiver = auslander.Quiver(3, [(0, 1), (1, 2)])
    return auslander.Algebra(quiver, [[0, 1]], field=F2)


def _a2_walk(**limits):
    walk = auslander.EquivalenceDiscoveryLimits(**limits)
    return auslander.discover_equivalences(auslander.Algebra.linear_an(2), F5, walk)


def _record(graph):
    return (graph.keys, graph.edges, graph.stop, graph.total_terms, graph.matrix_entries)


def test_a_silting_walk_stores_what_a_tilting_walk_blocks():
    tilting = _a2_walk(max_vertices=4)
    silting = _a2_walk(max_vertices=4, through_silting=True)

    assert tilting.blocked[0] == (0, "left", 0, "silting_only")
    assert silting.edges[0] == (0, 1, "left", 0)
    assert all(reason != "silting_only" for *_, reason in silting.blocked)
    assert silting.verify() and tilting.verify()
    again = _a2_walk(max_vertices=4, through_silting=True)
    assert _record(again) == _record(silting)


def test_an_undetermined_regular_complex_is_a_verified_empty_walk():
    graph = _a2_walk(max_hom_spaces=0)

    assert graph.stop == "exhausted_frontier"
    assert (graph.vertex_count, graph.total_terms, graph.matrix_entries) == (0, 0, 0)
    assert graph.blocked == [(0, "left", 0, "undetermined")]
    assert graph.verify()


def test_limits_keep_every_field():
    walk = auslander.EquivalenceDiscoveryLimits(max_hom_spaces=7, max_total_terms=3)
    limits = auslander.ClassificationLimits(discovery=walk)

    assert (walk.max_hom_spaces, walk.max_total_terms) == (7, 3)
    assert limits.discovery.max_hom_spaces == 7


def _a3_pair():
    return [auslander.Algebra.linear_an(3).over(F2), _a3_with_relation()]


def test_walks_count_targets_outside_the_family():
    result = auslander.classify_derived(_a3_pair())

    assert (result.groups, result.status) == ([[0, 1]], "complete")
    assert sum(walk.unmatched for walk in result.walks) > 0
    assert sum(walk.target_cuts for walk in result.walks) == 0


def test_target_cuts_leave_the_pair_open():
    target = auslander.TargetLimits(max_endo_dimension=0)
    limits = auslander.ClassificationLimits(target=target)
    result = auslander.classify_derived(_a3_pair(), limits=limits)

    assert result.status == "incomplete"
    for walk in result.walks:
        assert walk.examined > 0
        assert (walk.target_cuts, walk.unmatched, walk.merges) == (walk.examined, 0, 0)


def test_a_merge_exposes_its_recovered_target_and_coordinates():
    family = _a3_pair()
    merge = auslander.classify_derived(family).classes[0].merges[0]
    target, images = merge.recovered_target, merge.isomorphism.arrow_images

    assert not merge.is_duplicate
    assert merge.isomorphism.source.dim == target.dim == family[merge.member].dim
    assert len(images) == len(target.quiver.arrows)
    assert {len(image) for image in images} == {target.dim}
    assert set(sum(images, [])) <= {0, 1}
    assert merge.isomorphism.verify()


def test_gentle_threads_carry_their_signs():
    presentation = _a3_with_relation().gentle()
    threads = presentation.permitted_threads + presentation.forbidden_threads
    first = presentation.forbidden_threads[0]

    assert (first.start, first.end, first.arrows) == (0, 2, [0, 1])
    assert (first.sigma, first.epsilon) == (1, 1)
    assert [len(t) for t in presentation.forbidden_threads] == [2, 0, 0, 0]
    assert {t.sigma for t in threads} | {t.epsilon for t in threads} == {1, -1}


def test_gentle_keys_order_hash_and_describe_their_bound_quiver():
    key = _a3_with_relation().gentle().key
    keys = auslander.connected_gentle_keys(2)

    assert (key.vertices, key.arrows, key.relations) == (3, [(0, 1), (1, 2)], [(0, 1)])
    assert len(set(keys)) == len(keys) == 9
    assert all(left < right for left, right in zip(keys, keys[1:]))
    assert {key.vertices for key in keys} == {2}


@pytest.mark.parametrize("prime", [3, 5])
def test_other_fields_give_the_classes_of_f2(prime):
    field = auslander.PrimeField(prime)
    result = auslander.classify_derived(auslander.connected_gentle_algebras(2, field))
    over_f2 = auslander.classify_derived(auslander.connected_gentle_algebras(2, F2))

    assert [c.members for c in result.classes] == [c.members for c in over_f2.classes]
    text = result.to_artifact().canonical_json
    assert f'"field":{prime},' in text
    replayed = auslander.verify_derived_atlas(text)
    assert replayed.verification == "replayed"
    assert replayed.to_artifact().canonical_json == text


def test_an_empty_family_is_complete_and_has_no_atlas():
    result = auslander.classify_derived([], field=F2)

    assert (result.status, result.classes, result.walks) == ("complete", [], [])
    with pytest.raises(ValueError, match="no member"):
        result.to_artifact()

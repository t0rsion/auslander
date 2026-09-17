"""Complete indecomposable catalogs and higher Ext orthogonality."""

import auslander
import pytest


def test_catalog_rejects_a_field_free_presentation_without_a_field():
    algebra = auslander.Algebra.linear_an(2)

    with pytest.raises(ValueError, match="field-free"):
        auslander.catalog(algebra)


def test_catalog_builds_and_indexes_a_field_free_presentation_after_binding():
    algebra = auslander.Algebra.linear_an(2)
    field = auslander.PrimeField(5)

    complete = auslander.catalog(algebra, field)
    assert algebra.catalog(field).provenance == complete.provenance
    assert isinstance(complete, auslander.IndecomposableCatalog)
    assert complete.provenance == "dynkin_zero_ideal"
    assert complete.field.p == 5
    assert len(complete) == len(complete.entries) == 3
    assert complete[0].dims == complete.entries[0].dims
    with pytest.raises(IndexError):
        complete[len(complete)]


def test_explicit_catalog_routes_keep_their_classification():
    field = auslander.PrimeField(5)
    dynkin = auslander.Algebra.linear_an(2)
    nakayama = auslander.Algebra.truncated_poly(3)

    assert (
        auslander.IndecomposableCatalog.dynkin(dynkin, field).provenance
        == "dynkin_zero_ideal"
    )
    assert (
        auslander.IndecomposableCatalog.nakayama(nakayama, field).provenance
        == "nakayama"
    )


def gentle_tree():
    quiver = auslander.Quiver(4, [(0, 1), (1, 2), (3, 2)])
    return auslander.Algebra(quiver, [[0, 1]])


def test_auto_catalog_uses_the_gentle_tree_route():
    field = auslander.PrimeField(5)
    catalog = auslander.catalog(gentle_tree(), field)
    assert catalog.provenance == "gentle_tree"
    assert len(catalog) == 8
    assert all(module.total_dim > 0 for module in catalog.entries)
    assert (
        auslander.IndecomposableCatalog.gentle_tree(gentle_tree(), field).provenance
        == "gentle_tree"
    )


def test_catalog_ar_quiver_forwards_the_completed_catalog():
    field = auslander.PrimeField(5)
    catalog = auslander.catalog(auslander.Algebra.linear_an(2), field)

    ar_quiver = catalog.ar_quiver()

    assert len(ar_quiver.vertices()) == len(catalog)
    assert all(vertex.module.dims == catalog[vertex.id].dims for vertex in ar_quiver.vertices())


def test_unsupported_auto_catalog_keeps_the_route_error_typed():
    field = auslander.PrimeField(5)
    with pytest.raises(auslander.UnsupportedDomainError, match="gentle-tree"):
        auslander.catalog(auslander.Algebra.kronecker(2), field)


def _assert_single_a1_result(result, complete):
    assert result.provenance == "dynkin_zero_ideal"
    assert (result.chosen, result.max_degree) == ([0], 2)
    assert (result.left, result.right) == ([0], [0])
    assert (result.is_rigid, result.is_two_sided_maximal) == (True, True)
    assert result.verify(complete)
    assert (result.work.resolutions, result.work.ext_tables) == (1, 1)
    row = result.pairs[0]
    assert (
        len(result.pairs),
        row.source,
        row.target,
        row.dimensions,
        row.ext_dimensions,
        row.vanishes,
    ) == (1, 0, 0, [0, 0], [0, 0], True)


def test_higher_orthogonality_keeps_catalog_entries_and_work():
    field = auslander.PrimeField(5)
    complete = auslander.catalog(auslander.Algebra.linear_an(1), field)
    limits = auslander.HigherOrthogonalityLimits(max_pairs=4, max_ext_cells=8)

    result = auslander.higher_orthogonality(complete, [0], 2, limits)
    _assert_single_a1_result(result, complete)


def test_higher_orthogonality_accepts_empty_selection():
    field = auslander.PrimeField(5)
    complete = auslander.catalog(auslander.Algebra.linear_an(1), field)

    empty = auslander.HigherOrthogonality.compute(complete, [], 2)
    assert empty.left == empty.right == [0]
    assert empty.is_rigid
    assert not empty.is_two_sided_maximal
    assert empty.work.resolutions == empty.work.ext_tables == 0


def test_higher_orthogonality_checks_pair_limits():
    field = auslander.PrimeField(5)
    complete = auslander.catalog(auslander.Algebra.linear_an(1), field)

    with pytest.raises(auslander.BudgetExhaustedError) as exhausted:
        auslander.higher_orthogonality(
            complete,
            [0],
            2,
            auslander.HigherOrthogonalityLimits(max_pairs=0),
        )
    assert exhausted.value.requested == 1
    assert exhausted.value.limit == 0


def test_higher_orthogonality_rejects_duplicate_indices():
    field = auslander.PrimeField(5)
    complete = auslander.catalog(auslander.Algebra.linear_an(1), field)

    with pytest.raises(ValueError) as duplicate:
        auslander.higher_orthogonality(complete, [0, 0], 1)
    assert duplicate.value.index == 0
    assert (duplicate.value.first, duplicate.value.second) == (0, 1)


def test_higher_orthogonality_rejects_unknown_indices():
    field = auslander.PrimeField(5)
    complete = auslander.catalog(auslander.Algebra.linear_an(1), field)

    with pytest.raises(ValueError) as unknown:
        auslander.higher_orthogonality(complete, [1], 1)
    assert unknown.value.index == 1
    assert unknown.value.catalog == 1

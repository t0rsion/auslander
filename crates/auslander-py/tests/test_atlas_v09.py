"""Test the checked catalog atlas and multiplicity result surface."""

import pytest

import auslander


def _atlas():
    algebra = auslander.Algebra.truncated_poly(3, field=auslander.PrimeField(5))
    catalog = algebra.catalog()
    return catalog, catalog.atlas(3)


def test_catalog_atlas_exposes_scope():
    catalog, atlas = _atlas()

    assert atlas.catalog.provenance == catalog.provenance == "nakayama"
    assert atlas.catalog.field.p == 5
    assert len(atlas) == len(catalog) == 3
    assert atlas.max_degree == 3
    assert atlas.status == "complete"
    assert atlas.verification == "computed"


def test_catalog_atlas_reports_cached_table_scope():
    _, atlas = _atlas()

    assert atlas.ext_table.catalog_len == 3
    assert atlas.ext_table.max_degree == 3
    assert len(atlas.ext_table) == len(atlas.pairs) == 9
    assert atlas.verify()


def test_catalog_atlas_returns_ordered_ext_rows():
    _, atlas = _atlas()

    row = atlas.ext_table.row(0, 0)
    assert row is not None
    assert (row.source, row.target) == (0, 0)
    assert row.dimensions == atlas.ext_dimensions(0, 0)
    assert atlas.ext_dim(0, 0, 0) == row.dimensions[0]
    assert atlas.ext_table.row(3, 0) is None


def test_catalog_atlas_explanation_reports_scope_completion_and_computation():
    _, atlas = _atlas()

    explanation = auslander.explain(atlas)

    assert explanation.status == "complete"
    assert explanation.verification == "computed"


def test_atlas_materializes_checked_direct_sums():
    _, atlas = _atlas()
    multiplicities = [1, 0, 1]
    module = atlas.materialize(multiplicities)

    assert module.dims == [4]


def test_atlas_scores_and_vanishing_are_checked():
    _, atlas = _atlas()
    multiplicities = [1, 0, 1]
    module = atlas.materialize(multiplicities)

    assert atlas.self_ext_scores(multiplicities) == module.ext_table(module, 3)
    assert atlas.self_ext_vanishes([0, 0, 0])
    assert not atlas.self_ext_vanishes(multiplicities, 0, 3)
    assert atlas.ext_scores([0, 0, 0], [0, 0, 0]) == [0, 0, 0, 0]
    assert atlas.ext_vanishes([0, 0, 0], [0, 0, 0])


def test_atlas_rejects_invalid_score_and_materialization_inputs():
    _, atlas = _atlas()

    with pytest.raises(ValueError):
        atlas.self_ext_scores([1, 0], 0, 0)
    with pytest.raises(ValueError):
        atlas.materialize([1, 0])


def test_complete_multiplicity_result_is_typed():
    _, atlas = _atlas()

    complete = atlas.enumerate([4])
    assert complete.status == "complete"
    assert complete.verification == "computed"
    assert complete.is_complete and not complete.is_cut


def test_complete_multiplicity_result_keeps_solutions():
    _, atlas = _atlas()
    expected = [[0, 2, 0], [1, 0, 1], [2, 1, 0], [4, 0, 0]]

    complete = atlas.enumerate([4])
    assert complete.solutions == expected
    assert complete.complete is not None
    assert isinstance(complete.complete, auslander.MultiplicityComplete)
    assert complete.complete.solutions == expected
    assert complete.complete.status == "complete"


def test_complete_multiplicity_result_keeps_scope():
    _, atlas = _atlas()

    complete = atlas.enumerate([4])
    assert complete.cut is None
    assert complete.cut_reason is None
    assert complete.target_dimensions == [4]
    assert complete.catalog.field.p == 5


def test_cut_multiplicity_result_keeps_reason_and_prefix():
    _, atlas = _atlas()

    cut = atlas.enumerate([4], auslander.MultiplicityLimits(max_solutions=1))
    assert cut.status == "cut"
    assert cut.is_cut and not cut.is_complete
    assert isinstance(cut.cut, auslander.MultiplicityCut)
    assert cut.cut.reason.kind == "solution_limit"
    assert cut.cut.reason.limit == 1


def test_cut_multiplicity_result_keeps_prefix_and_scope():
    _, atlas = _atlas()
    expected = [[0, 2, 0]]

    cut = atlas.enumerate([4], auslander.MultiplicityLimits(max_solutions=1))
    assert cut.solutions == expected
    assert cut.cut.solutions == expected
    assert cut.cut_reason.kind == "solution_limit"
    assert cut.complete is None
    assert cut.coverage == 1
    assert len(cut) == 1
    assert cut[0] == expected[0]


def test_atlas_limits_expose_checked_materialization_cell_ceiling():
    limits = auslander.CatalogAtlasLimits(max_materialized_cells=17)

    assert limits.max_materialized_cells == 17
    assert limits.max_materialized_summands > 0
    assert "max_materialized_cells=17" in repr(limits)

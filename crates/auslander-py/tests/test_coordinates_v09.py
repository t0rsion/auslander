"""Map checked modules to complete catalog coordinates."""

import pytest

import auslander


def a2_catalog(prime=5):
    field = auslander.PrimeField(prime)
    algebra = auslander.Algebra.linear_an(2).over(field)
    return algebra, auslander.IndecomposableCatalog.dynkin(algebra)


def test_catalog_coordinates_return_exact_multiplicities_and_witnesses():
    algebra, catalog = a2_catalog()
    module = catalog.entries[0]

    result = catalog.coordinates(module)

    _assert_exact_result_shape(result, catalog)
    _assert_exact_result_witness(result, catalog, module)
    _assert_exact_result_verification(result, algebra, catalog, module)


def _assert_exact_result_shape(result, catalog):
    assert isinstance(result, auslander.CatalogCoordinates)
    assert result.status == "exact"
    assert result.is_exact
    assert sum(result.multiplicities) == 1
    assert result.multiplicities[0] == 1
    assert len(result.matches) == 1


def _assert_exact_result_witness(result, catalog, module):
    match = result.matches[0]
    assert (match.summand, match.catalog_entry) == (0, 0)
    assert match.witness.is_isomorphism()
    assert match.witness.source.dims == result.decomposition.summands[0].dims
    assert match.witness.target.dims == catalog.entries[0].dims


def _assert_exact_result_verification(result, algebra, catalog, module):
    assert result.progress.multiplicities == result.multiplicities
    assert result.progress.matches[0].catalog_entry == 0
    assert result.verification == "computed"
    assert result.progress.verification == "computed"
    assert result.verify(catalog, module)
    assert result.progress.verify(catalog, module)
    assert result.field.p == algebra.field.p
    assert result.provenance == catalog.provenance


def test_catalog_coordinate_limit_returns_a_checked_cut_prefix():
    _, catalog = a2_catalog()
    module = catalog.entries[0]
    limits = auslander.CatalogCoordinateLimits(max_work_units=0)

    result = catalog.coordinates(module, limits=limits)

    _assert_cut_result_reason(result)
    _assert_cut_result_prefix(result, catalog)
    _assert_cut_result_verification(result, catalog, module)


def _assert_cut_result_reason(result):
    assert isinstance(result, auslander.CatalogCoordinateCut)
    assert result.status == "cut"
    assert not result.is_exact
    assert result.kind == "work_limit"
    assert result.limit == 0
    assert result.reason.kind == "work_limit"
    assert result.reason.limit == 0
    assert result.work_units == 0


def _assert_cut_result_prefix(result, catalog):
    assert result.multiplicities == [0] * len(catalog)
    assert result.matches == []
    assert len(result.decomposition) == 1


def _assert_cut_result_verification(result, catalog, module):
    assert result.verification == "computed"
    assert result.progress.verification == "computed"
    assert result.verify(catalog, module)
    assert result.progress.verify(catalog, module)


def test_catalog_coordinate_limits_keep_the_unbounded_default_explicit():
    limits = auslander.CatalogCoordinateLimits()

    assert limits.max_work_units > 0
    assert repr(limits).startswith("CatalogCoordinateLimits(")


def test_catalog_coordinates_reject_a_module_from_another_field():
    _, catalog = a2_catalog(5)
    other_field = auslander.Algebra.linear_an(2).over(auslander.PrimeField(7))

    with pytest.raises(ValueError, match="catalog uses F_5.*module uses F_7"):
        catalog.coordinates(other_field.simple(0))

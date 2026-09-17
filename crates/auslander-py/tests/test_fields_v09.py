"""Tests for the v0.9 field-bound algebra surface."""

import pytest

import auslander


def test_named_constructors_accept_an_optional_field():
    field = auslander.PrimeField(5)
    quiver = auslander.Quiver(1, [(0, 0)])
    algebras = [
        auslander.Algebra(quiver, [[0, 0]], field=field),
        auslander.Algebra.linear_an(2, field=field),
        auslander.Algebra.kronecker(2, field=field),
        auslander.Algebra.dual_numbers(field=field),
        auslander.Algebra.truncated_poly(3, field=field),
        auslander.Algebra.linear_nakayama([3, 2, 1], field=field),
        auslander.Algebra.cyclic_nakayama([2, 2, 2], field=field),
        auslander.Algebra.radical_square_zero_cycle(3, field=field),
        auslander.Algebra.an_with_relations(3, [(0, 2)], field=field),
    ]
    assert [algebra.field.p for algebra in algebras] == [5] * len(algebras)


def test_bound_algebra_omits_field_for_core_module_constructors():
    field = auslander.PrimeField(5)
    algebra = auslander.Algebra.linear_an(2, field=field)
    assert algebra.simple(0).dims == [1, 0]
    assert algebra.projective(0).dims == [1, 1]
    assert algebra.injective(1).dims == [1, 1]
    module = algebra.module([1, 1], [[[1]]])
    sparse = algebra.module_sparse([1, 1], [[(0, 0, 1)]])
    assert module.maps == sparse.maps == [[[1]]]


def test_bound_algebra_checks_explicit_fields():
    field = auslander.PrimeField(5)
    other = auslander.PrimeField(7)
    algebra = auslander.Algebra.linear_an(2, field=field)
    assert algebra.simple(0, field=field).dims == [1, 0]
    with pytest.raises(ValueError, match="built over F_5"):
        algebra.simple(0, field=other)
    with pytest.raises(ValueError, match="built over F_5"):
        algebra.over(other)


def test_field_free_algebra_rejects_unbound_module_constructors():
    algebra = auslander.Algebra.linear_an(2)
    assert algebra.field is None
    with pytest.raises(ValueError, match="needs a field"):
        algebra.simple(0)
    with pytest.raises(ValueError, match="needs a field"):
        algebra.module([1, 1], [[[1]]])


def test_field_free_algebra_can_be_bound_to_a_field():
    field = auslander.PrimeField(5)
    algebra = auslander.Algebra.linear_an(2)
    bound = algebra.over(field)
    assert bound.field.p == 5
    assert bound.simple(0).dims == [1, 0]


def test_field_free_algebra_reuses_a_same_field_binding():
    field = auslander.PrimeField(5)
    algebra = auslander.Algebra.linear_an(2)
    same_field_bound = algebra.over(field)
    assert same_field_bound.simple(0).dims == [1, 0]
    assert algebra.simple(0, field=field).hom(same_field_bound.simple(0))


def test_general_algebra_is_bound_at_construction():
    field = auslander.PrimeField(5)
    other = auslander.PrimeField(7)
    quiver = auslander.Quiver(2, [(0, 1)])
    algebra = auslander.Algebra.from_relations(quiver, [], field)
    assert algebra.simple(0).dims == [1, 0]
    with pytest.raises(ValueError, match="built over F_5"):
        algebra.simple(0, field=other)
    with pytest.raises(ValueError, match="built over F_5"):
        algebra.over(other)


def test_certificate_field_check_is_explicit():
    field = auslander.PrimeField(5)
    other = auslander.PrimeField(7)
    text = auslander.Algebra.linear_an(1, field=field).certificate_json()
    assert auslander.Algebra.from_certificate(text, field=field).field.p == 5
    with pytest.raises(ValueError, match="certificate is over F_5"):
        auslander.Algebra.from_certificate(text, field=other)

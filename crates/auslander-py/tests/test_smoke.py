"""Smoke tests for the auslander Python module.

Facts checked here are the textbook values from the fixture suite: kA_3/(ab)
has dimension 5 with Ext^2(S_0, S_2) = 1 and pd S_0 = 2; the dual numbers
k[x]/(x^2) have Ext^k(S, S) = 1 for all k.
"""

import pytest

import auslander


def test_ka3_mod_ab():
    A = auslander.MonomialAlgebra.an_with_relations(3, [(0, 2)])
    assert A.dim == 5
    assert A.num_vertices == 3
    assert A.cartan_matrix() == [[1, 1, 0], [0, 1, 1], [0, 0, 1]]

    F = auslander.PrimeField(5)
    S0 = A.simple(F, 0)
    S2 = A.simple(F, 2)
    assert S0.dims == [1, 0, 0]
    assert S0.ext_dim(S2, 2) == 1

    P0 = A.projective(F, 0)
    assert P0.dims == [1, 1, 0]

    res = S0.resolve(10)
    assert res.status.kind == auslander.ResolutionKind.FINITE
    assert res.status.at is None
    assert res.status == auslander.ResolutionStatus(auslander.ResolutionKind.FINITE)
    assert repr(res.status) == "ResolutionStatus(ResolutionKind.FINITE)"
    assert repr(res.pd(10)) == "Exact(2)"
    assert res.pd(10).exact == 2
    assert res.pd(10).at_least is None

    gd = auslander.global_dimension(A, F, 10)
    assert repr(gd) == "Exact(2)"


def test_dual_numbers_ext_table():
    D = auslander.MonomialAlgebra.dual_numbers()
    F = auslander.PrimeField(5)
    S = D.simple(F, 0)
    assert S.ext_table(S, 2) == [1, 1, 1]

    res = S.resolve(3)
    assert res.status.kind == auslander.ResolutionKind.CUT
    assert res.status.at == 3
    assert res.status == auslander.ResolutionStatus(auslander.ResolutionKind.CUT, 3)
    assert res.status != auslander.ResolutionStatus(auslander.ResolutionKind.CUT, 2)
    assert repr(res.status) == "ResolutionStatus(ResolutionKind.CUT, at=3)"
    assert repr(res.pd(3)) == "AtLeast(4)"


def test_resolution_status_enforces_its_invariant():
    K = auslander.ResolutionKind
    with pytest.raises(ValueError):
        auslander.ResolutionStatus(K.FINITE, 3)
    with pytest.raises(ValueError):
        auslander.ResolutionStatus(K.CUT)


def test_hom_basis_between_a2_projectives():
    # Right modules over linearly oriented A_2: Hom(P_0, P_1) = 0 and
    # Hom(P_1, P_0) = k, spanned by e_1 -> a.
    A = auslander.MonomialAlgebra.linear_an(2)
    F = auslander.PrimeField(5)
    P0 = A.projective(F, 0)
    P1 = A.projective(F, 1)
    assert P0.hom(P1) == []
    basis = P1.hom(P0)
    assert len(basis) == 1
    f = basis[0]
    # The vertex matrices use the same list-of-rows shapes algebra.module takes:
    # dims P1 = [0, 1] and dims P0 = [1, 1], so a 0x1 matrix at vertex 0 (no
    # rows) and a 1x1 matrix at vertex 1.
    assert f.maps == [[], [[1]]]
    # Round trip through the checked constructor: same shapes, same morphism.
    g = P1.morphism(P0, f.maps)
    assert g.maps == f.maps
    assert not f.is_isomorphism()


def test_is_isomorphism_on_identity_and_zero():
    A = auslander.MonomialAlgebra.linear_an(2)
    F = auslander.PrimeField(5)
    P0 = A.projective(F, 0)
    identity = P0.morphism(P0, [[[1]], [[1]]])
    zero = P0.morphism(P0, [[[0]], [[0]]])
    assert identity.is_isomorphism()
    assert not zero.is_isomorphism()


def test_morphism_construction_is_checked():
    A = auslander.MonomialAlgebra.linear_an(2)
    F = auslander.PrimeField(5)
    P0 = A.projective(F, 0)
    P1 = A.projective(F, 1)
    # f_1 = [1] with the empty f_0 violates the commuting square at the arrow.
    with pytest.raises(ValueError):
        P0.morphism(P1, [[[]], [[1]]])
    # Wrong shape at vertex 0.
    with pytest.raises(ValueError):
        P0.morphism(P0, [[[1, 1]], [[1]]])


def test_nonprime_modulus_raises():
    with pytest.raises(ValueError):
        auslander.PrimeField(10)


def test_invalid_module_raises():
    D = auslander.MonomialAlgebra.dual_numbers()
    F = auslander.PrimeField(5)
    # x acting as the identity violates x^2 = 0.
    with pytest.raises(ValueError):
        D.module(F, [1], [[[1]]])
    # Wrong number of vertex dimensions.
    with pytest.raises(ValueError):
        D.module(F, [1, 1], [[[0]]])


def test_module_construction_and_invariants():
    A = auslander.MonomialAlgebra.an_with_relations(3, [(0, 2)])
    F = auslander.PrimeField(5)
    # The projective P_0: k -> k -> 0 with the arrow a acting as the identity;
    # the map for b: 1 -> 2 is the 1x0 matrix, one empty row.
    M = A.module(F, [1, 1, 0], [[[1]], [[]]])
    assert M.total_dim == 2
    assert M.top_dims() == [1, 0, 0]
    assert M.socle_dims() == [0, 1, 0]
    assert M.radical_series_dims() == [[1, 1, 0], [0, 1, 0], [0, 0, 0]]
    assert M.loewy_length() == 2
    assert M.hom_dim(A.projective(F, 0)) == 1

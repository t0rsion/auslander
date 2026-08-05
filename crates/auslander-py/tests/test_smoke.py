"""Smoke tests for the auslander Python module.

Facts checked here are the textbook values from the fixture suite: kA_3/(ab)
has dimension 5 with Ext^2(S_0, S_2) = 1 and pd S_0 = 2; the dual numbers
k[x]/(x^2) have Ext^k(S, S) = 1 for all k; k[x]/(x^n) is self-injective; and a
quiver of Dynkin type has n(n+1)/2 indecomposables for A_n and 12 for D_4.
"""

import struct

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


def test_is_isomorphic_itself_with_witness():
    A = auslander.MonomialAlgebra.linear_an(3)
    F = auslander.PrimeField(5)
    P0 = A.projective(F, 0)
    r = P0.is_isomorphic(P0)
    assert r.isomorphic is True
    assert r.obstruction is None
    assert r.obstruction_kind is None
    assert r.reason is None
    assert r.witness.is_isomorphism()
    assert repr(r) == "IsoResult(isomorphic=True)"
    assert P0.morphism(P0, r.witness.maps).is_isomorphism()


def test_is_isomorphic_distinguishes_no_from_unknown():
    A = auslander.MonomialAlgebra.linear_an(3)
    F = auslander.PrimeField(5)
    r = A.simple(F, 0).is_isomorphic(A.simple(F, 1))
    # False, not None: a proof-shaped obstruction.
    assert r.isomorphic is False
    assert r.witness is None
    assert r.reason is None
    assert r.obstruction == "dimension vectors differ: [1, 0, 0] vs [0, 1, 0]"
    assert r.obstruction_kind == "dimension_vector"


def test_is_isomorphic_kronecker_radical_criterion():
    # The representations (a, b) -> ([1], [0]) and ([0], [1]) share dimension
    # vector [1, 1]; only the radical criterion tells them apart.
    A = auslander.MonomialAlgebra.kronecker(2)
    F = auslander.PrimeField(5)
    M = A.module(F, [1, 1], [[[1]], [[0]]])
    N = A.module(F, [1, 1], [[[0]], [[1]]])
    r = M.is_isomorphic(N)
    assert r.isomorphic is False
    assert r.obstruction.startswith("radical criterion")
    assert r.obstruction_kind == "radical_criterion"
    assert M.is_isomorphic(M).isomorphic is True


def test_decompose_p0_plus_s1_with_certificates():
    # P_0 ⊕ S_1 over linear A_2, built block-diagonally: dims [1, 2] with the
    # arrow landing in the P_0 column.
    A = auslander.MonomialAlgebra.linear_an(2)
    F = auslander.PrimeField(5)
    M = A.module(F, [1, 2], [[[1, 0]]])
    d = M.decompose()
    assert [c.kind for c in d.certificates] == ["indecomposable", "indecomposable"]
    assert all(c.attempts is None for c in d.certificates)
    assert sorted(s.dims for s in d.summands) == [[0, 1], [1, 1]]
    # Summands are usable Modules over the same algebra object.
    P0 = A.projective(F, 0)
    summand_dims = {tuple(s.dims): s for s in d.summands}
    assert summand_dims[(1, 1)].is_isomorphic(P0).isomorphic is True
    assert summand_dims[(0, 1)].is_isomorphic(A.simple(F, 1)).isomorphic is True
    # Inclusions and projections are checked Morphisms splitting the sum:
    # each composite inclusion-then-projection is the identity on its summand.
    for s, inc, proj in zip(d.summands, d.inclusions, d.projections):
        composite = [_mat_mul(a, b, 5) for a, b in zip(inc.maps, proj.maps)]
        assert composite == [_identity(dim) for dim in s.dims]


def _mat_mul(a, b, p):
    return [
        [sum(x * y for x, y in zip(row, col)) % p for col in zip(*b)] if b else []
        for row in a
    ]


def _identity(n):
    return [[1 if i == j else 0 for j in range(n)] for i in range(n)]


def test_decompose_indecomposable_is_a_single_summand():
    A = auslander.MonomialAlgebra.linear_an(2)
    F = auslander.PrimeField(5)
    d = A.projective(F, 0).decompose()
    assert len(d.summands) == 1
    assert [c.kind for c in d.certificates] == ["indecomposable"]


def test_krull_schmidt_multiplicities_on_s1_p0_s1():
    # S_1 ⊕ P_0 ⊕ S_1 over linear A_2: dims [1, 3], the arrow hitting the
    # middle (P_0) column.
    A = auslander.MonomialAlgebra.linear_an(2)
    F = auslander.PrimeField(5)
    M = A.module(F, [1, 3], [[[0, 1, 0]]])
    r = M.krull_schmidt()
    assert r.reason is None
    classes = {tuple(rep.dims): mult for rep, mult in r.classes}
    assert classes == {(0, 1): 2, (1, 1): 1}
    # The representatives are usable Modules over the same algebra object.
    for rep, _ in r.classes:
        assert rep.is_isomorphic(rep).isomorphic is True


def test_tau_of_a_projective_is_none_and_of_a_simple_is_a_module():
    # Hand-derived translates over linear A_3: tau S_0 = [0, 1, 0] and
    # tau S_1 = [0, 0, 1]; every projective has tau = 0, reported as None
    # (a definite answer, not partiality).
    A = auslander.MonomialAlgebra.linear_an(3)
    F = auslander.PrimeField(5)
    for v in range(3):
        assert A.projective(F, v).tau() is None
    t0 = A.simple(F, 0).tau()
    assert t0.dims == [0, 1, 0]
    # The translate is a usable Module over the same algebra object.
    assert t0.is_isomorphic(A.simple(F, 1)).isomorphic is True
    assert A.simple(F, 1).tau().dims == [0, 0, 1]


def test_nakayama_indecomposables_count_is_the_kupisch_sum():
    F = auslander.PrimeField(5)
    for kupisch in ([2, 2, 1], [3, 2, 1]):
        A = auslander.MonomialAlgebra.linear_nakayama(kupisch)
        mods = auslander.nakayama_indecomposables(A, F)
        assert len(mods) == sum(kupisch) == A.dim
        for m, cert in mods:
            assert cert.kind == "indecomposable"
            assert cert.attempts is None
            assert [c.kind for c in m.decompose().certificates] == ["indecomposable"]


def test_nakayama_indecomposables_rejects_non_nakayama():
    F = auslander.PrimeField(5)
    with pytest.raises(ValueError):
        auslander.nakayama_indecomposables(auslander.MonomialAlgebra.kronecker(2), F)


def test_injective_coresolution_of_s2_over_ka3_mod_ab():
    # The injectives of kA_3/(ab) are I_0 = (1,0,0), I_1 = (1,1,0) and
    # I_2 = (0,1,1). The socle of S_2 sits at vertex 2, so I^0 = I_2 with
    # cokernel S_1, whose envelope is I_1 with cokernel S_0 = I_0.
    A = auslander.MonomialAlgebra.an_with_relations(3, [(0, 2)])
    F = auslander.PrimeField(32003)
    S2 = A.simple(F, 2)
    c = S2.coresolve(5)
    assert c.terms_dims == [[0, 1, 1], [1, 1, 0], [1, 0, 0]]
    assert [t.dims for t in c.terms] == c.terms_dims
    assert len(c.maps) == len(c.terms) - 1
    assert c.status.kind == auslander.ResolutionKind.FINITE
    assert c.status.at is None
    assert c.status == auslander.ResolutionStatus(auslander.ResolutionKind.FINITE)
    assert repr(c) == "InjectiveCoresolution(terms=3, status=finite)"
    # The coaugmentation is the injective envelope, and its source is S_2, so
    # the terms are usable Modules over the same algebra object.
    envelope, embedding = S2.injective_envelope()
    assert envelope.dims == c.terms[0].dims == A.injective(F, 2).dims
    assert c.coaugmentation.maps == embedding.maps
    assert c.terms[0].is_isomorphic(envelope).isomorphic is True
    assert S2.injective_dimension(5).exact == 2
    assert A.simple(F, 1).injective_dimension(5).exact == 1
    assert A.simple(F, 0).injective_dimension(5).exact == 0


def test_projective_resolution_exposes_terms_maps_and_augmentation():
    # Dual in shape to InjectiveCoresolution: the minimal resolution of S_0
    # over kA_3/(ab) is 0 -> P_2 -> P_1 -> P_0 -> S_0 -> 0.
    A = auslander.MonomialAlgebra.an_with_relations(3, [(0, 2)])
    F = auslander.PrimeField(32003)
    S0 = A.simple(F, 0)
    res = S0.resolve(5)
    assert res.terms_dims == [[1, 1, 0], [0, 1, 1], [0, 0, 1]]
    assert [t.dims for t in res.terms] == res.terms_dims
    assert len(res.maps) == len(res.terms) - 1
    assert res.status.kind == auslander.ResolutionKind.FINITE
    # The augmentation is the projective cover, and its target is S_0, so the
    # terms are usable Modules over the same algebra object.
    cover, epi = S0.projective_cover()
    assert cover.dims == res.terms[0].dims == A.projective(F, 0).dims
    assert res.augmentation.maps == epi.maps
    assert res.terms[0].is_isomorphic(cover).isomorphic is True


def test_injective_dimension_separates_exact_from_at_least():
    # Omega S = S over k[x]/(x^2) dualizes to a periodic cosyzygy, so the
    # minimal coresolution of the simple never stops, while the regular module
    # is injective.
    D = auslander.MonomialAlgebra.dual_numbers()
    F = auslander.PrimeField(32003)
    S = D.simple(F, 0)
    c = S.coresolve(6)
    assert c.terms_dims == [[2]] * 7
    assert c.status.kind == auslander.ResolutionKind.CUT
    assert c.status.at == 6
    assert c.status == auslander.ResolutionStatus(auslander.ResolutionKind.CUT, 6)

    unbounded = S.injective_dimension(10)
    assert unbounded.exact is None
    assert unbounded.at_least == 11
    assert repr(unbounded) == "AtLeast(11)"

    exact = D.projective(F, 0).injective_dimension(10)
    assert exact.exact == 0
    assert exact.at_least is None
    assert repr(exact) == "Exact(0)"
    assert exact != unbounded


def test_truncated_polynomial_algebras_are_self_injective():
    F = auslander.PrimeField(32003)
    for n in range(2, 6):
        T = auslander.MonomialAlgebra.truncated_poly(n)
        P = T.projective(F, 0)
        assert P.dims == [n]
        assert P.injective_dimension(6).exact == 0
        assert P.coresolve(6).terms_dims == [[n]]
        # The regular module is the unique indecomposable injective as well.
        assert P.is_isomorphic(T.injective(F, 0)).isomorphic is True


def test_dynkin_recognition_of_an_and_d4():
    DF = auslander.DiagramFamily
    for n in range(1, 6):
        t = auslander.DynkinType(DF.A, n)
        q = auslander.dynkin_quiver(t)
        assert q.num_vertices == t.num_vertices == n
        assert auslander.dynkin_type(q) == t
        assert auslander.euclidean_type(q) is None
        assert str(t) == "A_%d" % n
        assert t.family == DF.A
        assert t.n == n
    # D_4 is the three-armed star; recognition ignores the orientation.
    d4 = auslander.DynkinType(DF.D, 4)
    inward = auslander.Quiver(4, [(0, 2), (1, 2), (3, 2)])
    outward = auslander.Quiver(4, [(2, 0), (2, 1), (2, 3)])
    assert auslander.dynkin_type(inward) == auslander.dynkin_type(outward) == d4
    assert repr(d4) == "DynkinType(DiagramFamily.D, n=4)"
    assert str(d4) == "D_4"
    assert d4.n == 4 and d4.num_vertices == 4
    assert auslander.generalized_cartan_matrix(inward) == [
        [2, 0, -1, 0],
        [0, 2, -1, 0],
        [-1, -1, 2, -1],
        [0, 0, -1, 2],
    ]
    # A_3 has the six interval roots, ordered by height then lexicographically.
    a3 = auslander.dynkin_quiver(auslander.DynkinType(DF.A, 3))
    assert auslander.positive_roots(a3) == [
        [0, 0, 1],
        [0, 1, 0],
        [1, 0, 0],
        [0, 1, 1],
        [1, 1, 0],
        [1, 1, 1],
    ]


def test_diagram_types_enforce_their_parameters():
    DF = auslander.DiagramFamily
    with pytest.raises(ValueError):
        auslander.DynkinType(DF.A, 0)
    with pytest.raises(ValueError):
        auslander.DynkinType(DF.D, 3)
    with pytest.raises(ValueError):
        auslander.DynkinType(DF.A)
    with pytest.raises(ValueError):
        auslander.DynkinType(DF.E6, 6)
    with pytest.raises(ValueError):
        auslander.EuclideanType(DF.D, 3)
    # E6, E7, E8 name single diagrams, so their parameter is None.
    e6 = auslander.DynkinType(DF.E6)
    assert e6.n is None
    assert e6.num_vertices == 6
    assert e6.indecomposable_count == 36


def test_diagram_types_reject_counts_that_do_not_fit():
    """A representable count must be returned, an unrepresentable one refused.

    n(n+1)/2 fits for n = 5e9 while the intermediate product n(n+1) does not,
    so a naive checked multiplication would refuse a perfectly good answer; and
    a parameter whose count really does overflow must be rejected at
    construction rather than panicking in a getter.
    """
    DF = auslander.DiagramFamily
    # Both pointer widths need an n whose raw product overflows while its
    # triangular number still fits.
    bits = 8 * struct.calcsize("P")
    n = 5_000_000_000 if bits >= 64 else 80_000
    big = auslander.DynkinType(DF.A, n)
    assert big.indecomposable_count == n * (n + 1) // 2
    unrepresentable = 2**bits - 1
    with pytest.raises(OverflowError):
        auslander.DynkinType(DF.A, unrepresentable)
    with pytest.raises(OverflowError):
        auslander.DynkinType(DF.D, unrepresentable)
    with pytest.raises(OverflowError):
        auslander.EuclideanType(DF.A, unrepresentable)
    with pytest.raises(OverflowError):
        auslander.EuclideanType(DF.D, unrepresentable)


def test_diagram_quivers_reject_vertex_counts_beyond_u32():
    """A diagram past the u32 vertex limit is a valid abstract diagram, but a
    Quiver cannot represent it; materialization must refuse, never truncate."""
    DF = auslander.DiagramFamily
    bits = 8 * struct.calcsize("P")
    if bits < 64:
        pytest.skip("at 32 bits usize itself enforces the bound")
    t = auslander.DynkinType(DF.A, 2**32)
    assert t.num_vertices == 2**32
    with pytest.raises(ValueError):
        auslander.dynkin_quiver(t)
    with pytest.raises(ValueError):
        auslander.euclidean_quiver(auslander.EuclideanType(DF.A, 2**32))
    with pytest.raises(ValueError):
        auslander.euclidean_quiver(auslander.EuclideanType(DF.D, 2**32))


def test_dynkin_indecomposable_counts_are_the_positive_root_counts():
    F = auslander.PrimeField(32003)
    DF = auslander.DiagramFamily
    types = [auslander.DynkinType(DF.A, n) for n in range(1, 6)]
    types.append(auslander.DynkinType(DF.D, 4))
    for t in types:
        q = auslander.dynkin_quiver(t)
        A = auslander.MonomialAlgebra(q, [])
        mods = auslander.dynkin_indecomposables(A, F)
        assert len(mods) == t.indecomposable_count
        assert [m.dims for m, _ in mods] == auslander.positive_roots(q)
        for _, cert in mods:
            assert cert.kind == "indecomposable"
            assert cert.attempts is None
    assert auslander.DynkinType(DF.A, 4).indecomposable_count == 4 * 5 // 2
    assert auslander.DynkinType(DF.D, 4).indecomposable_count == 12


def test_kronecker_is_euclidean_and_rejected_by_the_enumerator():
    F = auslander.PrimeField(32003)
    DF = auslander.DiagramFamily
    K = auslander.MonomialAlgebra.kronecker(2)
    affine_a1 = auslander.EuclideanType(DF.A, 1)
    assert auslander.euclidean_type(K.quiver) == affine_a1
    assert auslander.dynkin_type(K.quiver) is None
    # No finite root system, so no root list rather than a truncated one.
    assert auslander.positive_roots(K.quiver) is None
    assert auslander.generalized_cartan_matrix(K.quiver) == [[2, -2], [-2, 2]]
    assert str(affine_a1) == "affine A_1"
    assert affine_a1.n == 1
    assert affine_a1.num_vertices == 2

    with pytest.raises(auslander.NotDynkinError) as caught:
        auslander.dynkin_indecomposables(K, F)
    # The rejected precondition survives as the exception class, and the
    # Euclidean type as an attribute; neither is left in the message only.
    assert caught.value.euclidean == affine_a1
    assert isinstance(caught.value, auslander.DynkinError)
    assert isinstance(caught.value, ValueError)


def test_a_graph_that_is_neither_dynkin_nor_euclidean_reports_no_euclidean_type():
    F = auslander.PrimeField(5)
    # Two isolated vertices: a disconnected graph is neither.
    A = auslander.MonomialAlgebra(auslander.Quiver(2, []), [])
    with pytest.raises(auslander.NotDynkinError) as caught:
        auslander.dynkin_indecomposables(A, F)
    assert caught.value.euclidean is None


def test_bound_algebra_is_rejected_for_a_nonzero_ideal():
    F = auslander.PrimeField(32003)
    # kA_3/(ab) is Dynkin as a quiver, so only the ideal stands in the way and
    # the rejection must say so rather than blame the graph.
    A = auslander.MonomialAlgebra.an_with_relations(3, [(0, 2)])
    assert auslander.dynkin_type(A.quiver) == auslander.DynkinType(
        auslander.DiagramFamily.A, 3
    )
    with pytest.raises(auslander.NonzeroIdealError) as caught:
        auslander.dynkin_indecomposables(A, F)
    assert caught.value.forbidden_words == 1
    assert isinstance(caught.value, auslander.DynkinError)
    assert not isinstance(caught.value, auslander.NotDynkinError)


def test_is_isomorphic_needs_one_algebra_object():
    F = auslander.PrimeField(5)
    A = auslander.MonomialAlgebra.linear_an(2)
    B = auslander.MonomialAlgebra.linear_an(2)
    with pytest.raises(ValueError):
        A.simple(F, 0).is_isomorphic(B.simple(F, 0))

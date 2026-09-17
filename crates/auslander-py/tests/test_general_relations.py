"""Tests for general-relation support in the auslander Python module.

Pinned facts come from the QPA oracle fixtures (tests/qpa-oracle, schema v6):
the commutative square with ab - cd has dim 9 over every field, Cartan matrix
[[1,1,1,1],[0,1,0,1],[0,0,1,1],[0,0,0,1]], tau S_0 = [1,1,1,0],
tau S_1 = [0,0,1,1], tau S_2 = [0,1,0,1], S_3 projective, and pd S_0 = 2; the
preprojective algebra of A_3 has dim 10. The certificate workflow round-trips
through canonical JSON, and every tampered certificate is rejected.
"""

import pytest

import auslander


def square(field):
    # a: 0 -> 1, b: 1 -> 3, c: 0 -> 2, d: 2 -> 3, and the relation ab - cd.
    Q = auslander.Quiver(4, [(0, 1), (1, 3), (0, 2), (2, 3)])
    return auslander.Algebra.from_relations(Q, [[(1, [0, 1]), (-1, [2, 3])]], field)


def test_commutative_square_over_f5():
    F = auslander.PrimeField(5)
    A = square(F)
    assert A.dim == 9
    assert A.num_vertices == 4
    assert A.field.p == 5
    assert A.cartan_matrix() == [
        [1, 1, 1, 1],
        [0, 1, 0, 1],
        [0, 0, 1, 1],
        [0, 0, 0, 1],
    ]
    assert repr(A) == "Algebra(dim=9, vertices=4, field=F_5)"


def test_monomial_algebra_is_field_free():
    # One monomial algebra object is usable over every prime.
    M = auslander.Algebra.linear_an(2)
    assert M.field is None
    assert M.simple(0, field=auslander.PrimeField(5)).dims == [1, 0]
    assert M.simple(0, field=auslander.PrimeField(7)).dims == [1, 0]


def test_duplicate_python_names_are_absent():
    assert not hasattr(auslander, "MonomialAlgebra")
    module = auslander.Algebra.linear_an(2).simple(0, field=auslander.PrimeField(5))
    assert not hasattr(module, "dim_vector")


def test_general_algebra_refuses_other_fields():
    A = square(auslander.PrimeField(5))
    F7 = auslander.PrimeField(7)
    with pytest.raises(ValueError, match="built over F_5"):
        A.simple(0, field=F7)
    with pytest.raises(ValueError, match="built over F_5"):
        A.certificate_json(F7)
    assert A.simple(0, field=auslander.PrimeField(5)).dims == [1, 0, 0, 0]


def test_decompose_p0_s1_s1_with_multiplicities():
    # P_0 ⊕ S_1 ⊕ S_1, block diagonal: vertex-1 coordinate 0 carries P_0.
    F = auslander.PrimeField(5)
    A = square(F)
    M = A.module([1, 3, 1, 1], [[[1, 0, 0]], [[1], [0], [0]], [[1]], [[1]]], field=F)
    d = M.decompose()
    _assert_square_decomposition(M, d, A, F)


def _assert_square_decomposition(M, d, A, F):
    _assert_square_decomposition_parts(d)
    _assert_square_krull_schmidt(M, A, F)


def _assert_square_decomposition_parts(d):
    assert [c.kind for c in d.certificates] == ["indecomposable"] * 3
    assert sorted(s.dims for s in d.summands) == [
        [0, 1, 0, 0],
        [0, 1, 0, 0],
        [1, 1, 1, 1],
    ]


def _assert_square_krull_schmidt(M, A, F):
    ks = M.krull_schmidt()
    assert ks.reason is None
    classes = {tuple(rep.dims): mult for rep, mult in ks.classes}
    assert classes == {(1, 1, 1, 1): 1, (0, 1, 0, 0): 2}
    reps = {tuple(rep.dims): rep for rep, _ in ks.classes}
    assert reps[(1, 1, 1, 1)].is_isomorphic(A.projective(0, field=F)).isomorphic is True
    assert reps[(0, 1, 0, 0)].is_isomorphic(A.simple(1, field=F)).isomorphic is True


def test_tau_over_the_square_matches_the_oracle():
    # QPA oracle, commutative-square f5: tau S_0 = [1,1,1,0],
    # tau S_1 = [0,0,1,1], tau S_2 = [0,1,0,1]. S_3 is projective, so
    # tau S_3 is the zero module.
    F = auslander.PrimeField(5)
    A = square(F)
    assert A.simple(0, field=F).tau().dims == [1, 1, 1, 0]
    assert A.simple(1, field=F).tau().dims == [0, 0, 1, 1]
    assert A.simple(2, field=F).tau().dims == [0, 1, 0, 1]
    assert A.simple(3, field=F).tau().dims == [0, 0, 0, 0]


def test_projective_resolution_of_s0_over_the_square():
    # 0 -> P_3 -> P_1 ⊕ P_2 -> P_0 -> S_0 -> 0; pd S_0 = 2 per the oracle.
    F = auslander.PrimeField(5)
    A = square(F)
    res = A.simple(0, field=F).resolve(5)
    assert res.terms_dims == [[1, 1, 1, 1], [0, 1, 1, 2], [0, 0, 0, 1]]
    assert res.status.kind == auslander.ResolutionKind.FINITE
    assert res.pd(5).exact == 2


def test_homological_surface_over_the_square():
    # QPA oracle: Ext^1(S_0, S_1) = 1, Ext^2(S_0, S_3) = 1, id S_3 = 2,
    # and I_3 has dimension vector [1, 1, 1, 1].
    F = auslander.PrimeField(5)
    A = square(F)
    S0 = A.simple(0, field=F)
    _assert_square_ext(S0, A, F)
    _assert_square_projective(A, F)
    _assert_square_injective(A, F)


def _assert_square_ext(S0, A, F):
    assert S0.ext_table(A.simple(1, field=F), 2) == [0, 1, 0]
    assert S0.ext_dim(A.simple(3, field=F), 2) == 1
    assert A.injective(3, field=F).dims == [1, 1, 1, 1]
    assert A.simple(3, field=F).injective_dimension(5).exact == 2
    assert auslander.global_dimension(A, F, 5).exact == 2


def _assert_square_projective(A, F):
    P0 = A.projective(0, field=F)
    assert P0.radical_series_dims() == [[1, 1, 1, 1], [0, 1, 1, 1], [0, 0, 0, 1], [0, 0, 0, 0]]
    assert P0.top_dims() == [1, 0, 0, 0]
    assert P0.socle_dims() == [0, 0, 0, 1]


def _assert_square_injective(A, F):
    cover, epi = A.simple(1, field=F).projective_cover()
    assert cover.dims == [0, 1, 0, 1]
    assert epi.maps[1] == [[1]]
    envelope, _ = A.simple(1, field=F).injective_envelope()
    assert envelope.dims == [1, 1, 0, 0]
    c = A.simple(3, field=F).coresolve(5)
    assert c.status.kind == auslander.ResolutionKind.FINITE


def test_certificate_round_trip():
    F = auslander.PrimeField(5)
    A = square(F)
    js = A.certificate_json()
    assert js == A.certificate_json(F)
    B = auslander.Algebra.from_certificate(js)
    assert B.dim == A.dim == 9
    assert B.cartan_matrix() == A.cartan_matrix()
    assert B.field.p == 5
    # The bytes are canonical, so dumping the reloaded algebra reproduces them.
    assert B.certificate_json() == js
    assert B.simple(1, field=F).tau().dims == [0, 0, 1, 1]


def test_tampered_certificate_raises_value_error():
    A = square(auslander.PrimeField(5))
    js = A.certificate_json()
    # Flip the non-leading coefficient of the one basis element: -1 to -2.
    tampered = js.replace(
        '"basis":[[[1,[2,3]],[4,[0,1]]]]', '"basis":[[[1,[2,3]],[3,[0,1]]]]'
    )
    assert tampered != js
    with pytest.raises(ValueError):
        auslander.Algebra.from_certificate(tampered)
    with pytest.raises(ValueError):
        auslander.Algebra.from_certificate(
            js.replace("completion-certificate-v1", "completion-certificate-v2")
        )


def test_monomial_certificate_needs_a_field_and_round_trips():
    F = auslander.PrimeField(5)
    M = auslander.Algebra.an_with_relations(3, [(0, 2)])
    with pytest.raises(ValueError, match="field-free"):
        M.certificate_json()
    B = auslander.Algebra.from_certificate(M.certificate_json(F))
    # The reloaded algebra is field-bound even though the ideal is monomial.
    assert B.dim == M.dim == 5
    assert B.field.p == 5


def preprojective_a3_relations():
    # Double quiver of A_3: a: 0 -> 1 (arrow 0), b: 1 -> 2 (1), abar: 1 -> 0
    # (2), bbar: 2 -> 1 (3); relations a·abar, abar·a - b·bbar, bbar·b.
    Q = auslander.Quiver(3, [(0, 1), (1, 2), (1, 0), (2, 1)])
    return Q, [[(1, [0, 2])], [(1, [2, 0]), (-1, [1, 3])], [(1, [3, 1])]]


def test_preprojective_a3_dim_matches_the_oracle():
    Q, rels = preprojective_a3_relations()
    A = auslander.Algebra.from_relations(Q, rels, auslander.PrimeField(3))
    assert A.dim == 10


def test_truncation_raises_a_runtime_error_with_diagnostics():
    Q, rels = preprojective_a3_relations()
    with pytest.raises(auslander.TruncationError) as caught:
        auslander.Algebra.from_relations(
            Q, rels, auslander.PrimeField(3), max_steps=1
        )
    e = caught.value
    assert isinstance(e, RuntimeError)
    assert e.reason == "step_budget"
    assert e.steps_used == 1
    assert e.basis_len >= 1
    assert e.pending_ambiguities >= 1


def test_completion_limits_property_on_both_kinds():
    # A monomial algebra reports the limits derived from its presentation:
    # x^65 raises the word budget to 2*65 - 1 for self-overlap superpositions.
    M = auslander.Algebra.truncated_poly(65)
    assert M.completion_limits == {
        "max_basis": 4096,
        "max_word_len": 129,
        "max_steps": 1_000_000,
        "max_origin_terms": 4096,
        "max_ambiguities": 65_536,
    }
    # A general-relation algebra reports its stored limits.
    A = square(auslander.PrimeField(5))
    assert A.completion_limits == {
        "max_basis": 4096,
        "max_word_len": 64,
        "max_steps": 1_000_000,
        "max_origin_terms": 4096,
        "max_ambiguities": 65_536,
    }


def test_from_certificate_limit_kwargs_propagate():
    js = square(auslander.PrimeField(5)).certificate_json()
    B = auslander.Algebra.from_certificate(
        js,
        max_basis=8192,
        max_word_len=96,
        max_steps=2_000_000,
        max_origin_terms=8192,
        max_ambiguities=1024,
    )
    assert B.completion_limits == {
        "max_basis": 8192,
        "max_word_len": 96,
        "max_steps": 2_000_000,
        "max_origin_terms": 8192,
        "max_ambiguities": 1024,
    }
    # Without keywords the reload keeps the defaults: certificate bytes never
    # carry or select budgets.
    C = auslander.Algebra.from_certificate(js)
    assert C.completion_limits == {
        "max_basis": 4096,
        "max_word_len": 64,
        "max_steps": 1_000_000,
        "max_origin_terms": 4096,
        "max_ambiguities": 65_536,
    }


def test_nested_truncation_raises_truncation_error_with_diagnostics():
    # Rebuild k[x]/(x^3) with a word budget below the opposite's self-overlap
    # superposition length 5. Loading succeeds because verification runs no
    # completion; tau and every injective path then truncate while building
    # the opposite algebra.
    F = auslander.PrimeField(5)
    js = auslander.Algebra.truncated_poly(3).certificate_json(F)
    B = auslander.Algebra.from_certificate(js, max_word_len=3)
    S = B.simple(0, field=F)
    for fail in [
        S.tau,
        S.injective_envelope,
        lambda: S.coresolve(3),
        lambda: S.injective_dimension(3),
    ]:
        with pytest.raises(auslander.TruncationError) as caught:
            fail()
        e = caught.value
        assert isinstance(e, RuntimeError)
        assert e.reason == "word_len_budget"
        assert e.basis_len >= 1
        assert e.pending_ambiguities >= 1
        assert e.steps_used >= 0


def test_infinite_dimensional_raises_with_a_witness():
    # A free loop: no relations, so every power of the loop is irreducible.
    loop = auslander.Quiver(1, [(0, 0)])
    with pytest.raises(ValueError, match=r"infinite dimensional.*cycle \[0\]"):
        auslander.Algebra.from_relations(loop, [], auslander.PrimeField(5))


def test_rejected_relations_raise_value_error():
    F = auslander.PrimeField(5)
    Q = auslander.Quiver(4, [(0, 1), (1, 2), (1, 3)])
    # Non-uniform: the paths ab and ac end at different vertices.
    with pytest.raises(ValueError, match="ends at a different vertex"):
        auslander.Algebra.from_relations(Q, [[(1, [0, 1]), (1, [0, 2])]], F)
    # A coefficient that reduces to zero mod p is rejected, not dropped.
    with pytest.raises(ValueError, match="coefficient zero"):
        auslander.Algebra.from_relations(Q, [[(5, [0, 1])]], F)
    # A word of length one violates admissibility.
    with pytest.raises(ValueError, match="length >= 2"):
        auslander.Algebra.from_relations(Q, [[(1, [0])]], F)


def test_readme_example():
    # The end-to-end non-monomial example from README.md, kept in sync with it.
    F = auslander.PrimeField(5)
    Q = auslander.Quiver(4, [(0, 1), (1, 3), (0, 2), (2, 3)])
    A = auslander.Algebra.from_relations(Q, [[(1, [0, 1]), (-1, [2, 3])]], F)
    assert A.dim == 9

    res = A.simple(0, field=F).resolve(5)
    assert res.terms_dims == [[1, 1, 1, 1], [0, 1, 1, 2], [0, 0, 0, 1]]
    assert res.pd(5).exact == 2

    M = A.module([1, 3, 1, 1], [[[1, 0, 0]], [[1], [0], [0]], [[1]], [[1]]], field=F)
    classes = {tuple(rep.dims): mult for rep, mult in M.krull_schmidt().classes}
    assert classes == {(1, 1, 1, 1): 1, (0, 1, 0, 0): 2}

    assert A.simple(1, field=F).tau().dims == [0, 0, 1, 1]

    B = auslander.Algebra.from_certificate(A.certificate_json())
    assert B.dim == 9

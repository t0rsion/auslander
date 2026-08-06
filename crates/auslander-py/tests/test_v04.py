"""Tests for the v0.4 Ext and Auslander-Reiten surface of the auslander module.

Pinned facts are textbook. Over k[x]/(x^3) the simple S has
dim Ext^k(S, S) = 1 for every k, the Yoneda square of the degree-1 class is
zero, and the almost-split sequence ending at S is 0 -> S -> P/rad^2 -> S -> 0
with middle dimension 2; over the dual numbers k[x]/(x^2) that same square is
nonzero. The AR quiver of k[x]/(x^3) has three vertices and four arrows, the
one of the path algebra of linearly oriented A_3 has six vertices (one per
positive root) and six arrows, and the commutative square with ab - cd has
neither a Dynkin nor a Nakayama enumeration, so it has no AR quiver here.
"""

import pytest

import auslander


def truncated(n):
    return auslander.Algebra.truncated_poly(n)


def square(field):
    # a: 0 -> 1, b: 1 -> 3, c: 0 -> 2, d: 2 -> 3, and the relation ab - cd.
    Q = auslander.Quiver(4, [(0, 1), (1, 3), (0, 2), (2, 3)])
    return auslander.Algebra.from_relations(Q, [[(1, [0, 1]), (-1, [2, 3])]], field)


def test_ext_space_dims_match_ext_dim_on_truncated_poly():
    F = auslander.PrimeField(5)
    A = truncated(3)
    uniserial = A.module(F, [2], [[[0, 1], [0, 0]]])
    modules = [A.simple(F, 0), uniserial, A.projective(F, 0)]
    for m in modules:
        for n in modules:
            for k in range(4):
                space = m.ext_space(n, k)
                assert space.dim == m.ext_dim(n, k)
                assert space.degree == k
                assert space.source.dims == m.dims
                assert space.target.dims == n.dims
                assert len(space.basis()) == space.dim
    S = A.simple(F, 0)
    assert [S.ext_space(S, k).dim for k in range(4)] == [1, 1, 1, 1]


def test_ext_space_dims_match_ext_dim_on_commutative_square():
    F = auslander.PrimeField(5)
    A = square(F)
    simples = [A.simple(F, v) for v in range(4)]
    for m in simples:
        for n in simples:
            for k in range(3):
                assert m.ext_space(n, k).dim == m.ext_dim(n, k)
    # pd S_0 = 2 through the resolution 0 -> P_3 -> P_1 + P_2 -> P_0.
    assert simples[0].ext_space(simples[3], 2).dim == 1


def test_ext_class_arithmetic_and_representatives():
    F = auslander.PrimeField(5)
    A = truncated(3)
    S = A.simple(F, 0)
    space = S.ext_space(S, 1)
    e = space.basis()[0]
    assert e.coordinates == [1]
    assert e.degree == 1
    assert e.source.dims == [1] and e.target.dims == [1]
    assert not e.is_zero
    assert (e + e).coordinates == [2]
    assert (-e).coordinates == [4]
    assert (3 * e).coordinates == [3]
    assert (e * 3).coordinates == [3]
    # 5 e = 0 over F_5, and the zero class is the class of no extension.
    assert (5 * e).is_zero
    assert space.zero_class().is_zero
    assert e == space.class_from_coordinates([1])
    assert e == space.class_from_coordinates([6])
    assert not (e == space.zero_class())
    rep = e.representative()
    # The representative is a cocycle P_1 -> S, and P_1 is the free module.
    assert rep.maps == [[[1], [0], [0]]]
    assert repr(e) == "ExtClass(degree=1, coordinates=[1])"

    # Degree 0 is Hom, and its identity class is the Yoneda unit.
    endo = S.ext_space(S, 0)
    assert endo.dim == S.hom_dim(S) == 1
    unit = endo.identity_class()
    assert unit.coordinates == [1]
    assert e.then(unit) == e
    assert unit.then(e) == e


def test_incompatible_spaces_raise_instead_of_answering_false():
    F = auslander.PrimeField(5)
    A = truncated(3)
    S = A.simple(F, 0)
    # A second simple object is a second module, so its Ext space is a
    # different space even though the two modules look alike.
    other = A.simple(F, 0)
    left = S.ext_space(S, 1).basis()[0]
    right = other.ext_space(other, 1).basis()[0]
    with pytest.raises(auslander.IncompatibleSpacesError):
        left == right
    with pytest.raises(auslander.IncompatibleSpacesError):
        left + right
    with pytest.raises(auslander.IncompatibleSpacesError):
        left == 5
    with pytest.raises(
        auslander.IncompatibleSpacesError, match="not the right class's source"
    ):
        left.then(right)
    with pytest.raises(ValueError, match=r"Ext\^0\(M, M\)"):
        S.ext_space(S, 1).identity_class()
    with pytest.raises(ValueError, match="dimension 1"):
        S.ext_space(S, 1).class_from_coordinates([1, 2])


def test_yoneda_square_vanishes_on_x3_and_survives_on_x2():
    F = auslander.PrimeField(5)
    S3 = truncated(3).simple(F, 0)
    e3 = S3.ext_space(S3, 1).basis()[0]
    square3 = e3.then(e3)
    assert square3.degree == 2
    assert S3.ext_dim(S3, 2) == 1
    assert square3.is_zero

    S2 = auslander.Algebra.dual_numbers().simple(F, 0)
    e2 = S2.ext_space(S2, 1).basis()[0]
    square2 = e2.then(e2)
    assert square2.degree == 2
    assert not square2.is_zero
    assert square2.coordinates == [1]


def test_extension_round_trip_recovers_the_class():
    F = auslander.PrimeField(5)
    A = truncated(3)
    S = A.simple(F, 0)
    space = S.ext_space(S, 1)
    for coords in ([0], [1], [2], [4]):
        cls = space.class_from_coordinates(coords)
        seq = cls.extension()
        assert seq.sub.dims == [1] and seq.quotient.dims == [1]
        assert seq.ext1_class().coordinates == cls.coordinates
        assert seq.verify()

    B = auslander.Algebra.linear_an(3)
    S0 = B.simple(F, 0)
    S1 = B.simple(F, 1)
    cls = S0.ext_space(S1, 1).basis()[0]
    seq = cls.extension()
    assert seq.sub.dims == [0, 1, 0]
    assert seq.middle.dims == [1, 1, 0]
    assert seq.quotient.dims == [1, 0, 0]
    assert seq.inclusion.maps[1] == [[1]]
    assert seq.ext1_class().coordinates == [1]


def test_split_and_non_split_carry_their_witnesses():
    F = auslander.PrimeField(5)
    A = truncated(3)
    S = A.simple(F, 0)
    space = S.ext_space(S, 1)

    split = space.zero_class().extension()
    assert split.is_split
    assert split.middle.dims == [2]
    witness = split.split_status
    assert isinstance(witness, auslander.SplitWitness)
    assert witness.retraction.maps[0] == [[1], [0]]
    assert witness.section.maps[0] == [[0, 1]]
    assert split.verify()

    non_split = space.basis()[0].extension()
    assert not non_split.is_split
    assert non_split.middle.dims == [2]
    dual = non_split.split_status
    assert isinstance(dual, auslander.NonSplitWitness)
    # The dual vector proves the retraction system unsolvable. The contract
    # is a nonempty integer vector whose sequence verifies; the entries are
    # pinned by y A = 0 and y b = 1 inside verify, not by a normalization.
    assert dual.dual
    assert all(isinstance(c, int) for c in dual.dual)
    assert non_split.verify()
    # A non-split extension of S by S is the uniserial module P/rad^2.
    assert non_split.middle.loewy_length() == 2


def test_almost_split_of_the_simple_over_x3():
    F = auslander.PrimeField(5)
    A = truncated(3)
    S = A.simple(F, 0)
    seq = S.almost_split()
    assert isinstance(seq, auslander.AlmostSplitSequence)
    assert seq.start.dims == [1]
    assert seq.middle.dims == [2]
    assert seq.end.dims == [1]
    assert seq.witness_route == "ar_duality"
    assert seq.inclusion.maps[0] == [[0, 1]]
    assert seq.projection.maps[0] == [[1], [0]]
    cls = seq.ext1_class()
    assert cls.degree == 1
    assert not cls.is_zero
    assert seq.verify()
    summary = seq.verification_summary()
    assert summary == {
        "action_traces": True,
        "duality_dimensions": True,
        "non_split": True,
        "sequence_exact": True,
        "socle_dimension": True,
        "socle_membership": True,
    }
    assert all(summary.values())
    assert repr(seq) == (
        "AlmostSplitSequence(start_dims=[1], middle_dims=[2], end_dims=[1])"
    )


def test_almost_split_middle_term_over_x3_splits_into_the_neighbours():
    F = auslander.PrimeField(5)
    A = truncated(3)
    # The uniserial P/rad^2: its almost-split sequence has middle S + P.
    M = A.module(F, [2], [[[0, 1], [0, 0]]])
    seq = M.almost_split()
    assert seq.start.dims == [2] and seq.end.dims == [2]
    assert seq.middle.dims == [4]
    classes = sorted(rep.dims for rep, _ in seq.middle.krull_schmidt().classes)
    assert classes == [[1], [3]]
    assert seq.verify()


def test_almost_split_of_a_projective_is_an_outcome_not_an_error():
    F = auslander.PrimeField(5)
    P = truncated(3).projective(F, 0)
    outcome = P.almost_split()
    assert outcome is auslander.AlmostSplitOutcome.PROJECTIVE
    assert outcome is not None
    assert repr(outcome) == "AlmostSplitOutcome.PROJECTIVE"
    # The same object every time; the member is the answer, not a copy of it.
    assert P.almost_split() is outcome


def test_almost_split_rejects_a_decomposable_module():
    F = auslander.PrimeField(5)
    A = truncated(3)
    S_plus_S = A.module(F, [2], [[[0, 0], [0, 0]]])
    with pytest.raises(auslander.NotIndecomposableError) as caught:
        S_plus_S.almost_split()
    error = caught.value
    assert "splits into 2 summands" in str(error)
    assert error.kind == "decomposable"
    assert error.summands == 2
    assert error.attempts is None

    zero = A.module(F, [0], [[]])
    with pytest.raises(auslander.NotIndecomposableError) as caught:
        zero.almost_split()
    assert caught.value.kind == "zero"


def test_category_radical_on_linear_a3():
    F = auslander.PrimeField(5)
    A = auslander.Algebra.linear_an(3)
    P0 = A.projective(F, 0)
    P1 = A.projective(F, 1)
    S0 = A.simple(F, 0)
    assert P0.dims == [1, 1, 1] and P1.dims == [0, 1, 1]

    # End(P_0) = k, so the radical of the endomorphism algebra is zero.
    assert P0.category_radical(P0).dim == 0
    assert P0.hom_dim(P0) == 1
    assert P1.category_radical(P1).dim == 0
    # Between non-isomorphic indecomposables every map is radical.
    assert P1.category_radical(P0).dim == P1.hom_dim(P0) == 1
    assert P0.category_radical(S0).dim == P0.hom_dim(S0) == 1
    assert P0.category_radical(P1).dim == P0.hom_dim(P1) == 0

    radical = P1.category_radical(P0)
    basis = radical.basis()
    assert len(basis) == 1
    assert basis[0].maps[1] == [[1]]
    assert not basis[0].is_isomorphism()

    decomposable = A.module(F, [2, 0, 0], [[[], []], []])
    with pytest.raises(auslander.NotIndecomposableError, match="source module"):
        decomposable.category_radical(P0)
    with pytest.raises(auslander.NotIndecomposableError, match="target module"):
        P0.category_radical(decomposable)


def test_ar_quiver_of_truncated_poly():
    F = auslander.PrimeField(5)
    A = truncated(3)
    quiver = A.ar_quiver(F)
    assert repr(quiver) == "ArQuiver(vertices=3, arrows=4)"
    vertices = quiver.vertices()
    assert [v.id for v in vertices] == [0, 1, 2]
    assert [v.module.dims for v in vertices] == [[1], [2], [3]]
    assert [v.residue_degree for v in vertices] == [1, 1, 1]
    # k[x]/(x^3) is self-injective: the only projective is also the only
    # injective, and it is the free module.
    assert [v.projective for v in vertices] == [False, False, True]
    assert [v.injective for v in vertices] == [False, False, True]

    arrows = quiver.arrows()
    assert [(a.source, a.target) for a in arrows] == [(0, 1), (1, 0), (1, 2), (2, 1)]
    assert [a.base_field_dim for a in arrows] == [1, 1, 1, 1]
    assert [a.dim_over_source_residue for a in arrows] == [1, 1, 1, 1]
    assert [a.dim_over_target_residue for a in arrows] == [1, 1, 1, 1]
    # Every residue degree here is 1, so every arrow is plain. A valued arrow
    # would raise ValuedArrowError on this accessor; no valued arrow exists on
    # the catalog domains of this release, so that path has no fixture here.
    assert [a.plain_multiplicity for a in arrows] == [1, 1, 1, 1]
    assert all(isinstance(a.plain_multiplicity, int) for a in arrows)
    for arrow in arrows:
        assert len(arrow.representatives()) == arrow.base_field_dim


def test_ar_quiver_of_linear_a3():
    F = auslander.PrimeField(5)
    A = auslander.Algebra.linear_an(3)
    quiver = A.ar_quiver(F)
    vertices = quiver.vertices()
    arrows = quiver.arrows()
    # One vertex per positive root of A_3, six of them.
    assert len(vertices) == 6
    assert len(arrows) == 6
    assert sorted(v.module.dims for v in vertices) == [
        [0, 0, 1],
        [0, 1, 0],
        [0, 1, 1],
        [1, 0, 0],
        [1, 1, 0],
        [1, 1, 1],
    ]
    assert [v.residue_degree for v in vertices] == [1] * 6
    # The three projectives P_0, P_1, P_2 and the three injectives I_0, I_1, I_2.
    assert sum(v.projective for v in vertices) == 3
    assert sum(v.injective for v in vertices) == 3
    by_id = {v.id: v.module.dims for v in vertices}
    assert [(by_id[a.source], by_id[a.target]) for a in arrows] == [
        ([0, 0, 1], [0, 1, 1]),
        ([0, 1, 0], [1, 1, 0]),
        ([0, 1, 1], [0, 1, 0]),
        ([0, 1, 1], [1, 1, 1]),
        ([1, 1, 0], [1, 0, 0]),
        ([1, 1, 1], [1, 1, 0]),
    ]
    assert [a.plain_multiplicity for a in arrows] == [1] * 6


def test_ar_quiver_rejects_an_unsupported_domain():
    F = auslander.PrimeField(5)
    A = square(F)
    with pytest.raises(auslander.UnsupportedDomainError) as caught:
        A.ar_quiver()
    message = str(caught.value)
    assert "Gabriel" in message
    assert "Nakayama" in message
    # A monomial presentation is field-free, so it needs the field.
    with pytest.raises(ValueError, match="field-free"):
        truncated(3).ar_quiver()


def test_exception_taxonomy():
    assert issubclass(auslander.BudgetExhaustedError, RuntimeError)
    assert issubclass(auslander.TruncationError, auslander.BudgetExhaustedError)
    assert issubclass(auslander.TruncationError, RuntimeError)
    assert issubclass(auslander.DefectError, RuntimeError)
    assert issubclass(auslander.NotIndecomposableError, ValueError)
    assert issubclass(auslander.IncompatibleSpacesError, ValueError)
    assert issubclass(auslander.UnsupportedDomainError, ValueError)
    assert issubclass(auslander.ValuedArrowError, ValueError)
    # A budget exhaustion is a limit, never bad input.
    assert not issubclass(auslander.BudgetExhaustedError, ValueError)
    assert not issubclass(auslander.DefectError, ValueError)


def test_readme_ar_example():
    F = auslander.PrimeField(5)
    A = auslander.Algebra.truncated_poly(3)
    S = A.simple(F, 0)
    assert S.ext_space(S, 1).dim == 1

    sequence = S.almost_split()
    assert sequence.start.dims == [1]
    assert sequence.middle.dims == [2]
    assert sequence.end.dims == [1]
    assert sequence.witness_route == "ar_duality"
    assert sequence.verify()
    assert all(sequence.verification_summary().values())

    quiver = A.ar_quiver(F)
    assert len(quiver.vertices()) == 3
    assert [a.plain_multiplicity for a in quiver.arrows()] == [1, 1, 1, 1]

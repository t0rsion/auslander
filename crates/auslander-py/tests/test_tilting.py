"""Tests for the v0.5 support tau-tilting surface: tau-rigidity, pairs,
mutation, graphs.

Three independent sources agree on the counts pinned here: the closed mutation
graph, the catalog enumeration, and the literature. A semisimple
algebra on n vertices has 2^n support tau-tilting pairs, one per subset of the
vertices. Linearly oriented A_n has the Catalan number C(n+1) of them, so 5 for
n = 2 and 14 for n = 3. k[x]/(x^3) is local with a unique simple, so it has 2.
The path algebra of D_4 has 50, distributed [1, 4, 9, 16, 20] by |M|.

A closed graph and a truncated walk are two classes, not one class with a mode
flag. Only the closed one has `pairs()`. A pair that fails a condition is a
value with a `rejection`, never an exception.
"""

import pytest

import auslander

DF = auslander.DiagramFamily
F = auslander.PrimeField(5)


def semisimple(n):
    """kQ for the quiver with n vertices and no arrows."""
    return auslander.Algebra(auslander.Quiver(n, []), [])


def d4():
    return auslander.Algebra(auslander.dynkin_quiver(auslander.DynkinType(DF.D, 4)), [])


def dims_of(pair):
    return sorted(m.dims for m in pair.module_summands)


COUNTS = [
    (semisimple(2), 4, [1, 2, 1]),
    (semisimple(3), 8, [1, 3, 3, 1]),
    (semisimple(4), 16, [1, 4, 6, 4, 1]),
    (auslander.Algebra.linear_an(2), 5, [1, 2, 2]),
    (auslander.Algebra.linear_an(3), 14, [1, 3, 5, 5]),
    (auslander.Algebra.truncated_poly(3), 2, [1, 1]),
    (d4(), 50, [1, 4, 9, 16, 20]),
]


@pytest.mark.parametrize("algebra, count, histogram", COUNTS)
def test_the_closed_graph_counts_every_pair(algebra, count, histogram):
    graph = algebra.support_tau_tilting_graph(F)
    assert isinstance(graph, auslander.ClosedSupportTauTiltingGraph)
    assert len(graph) == count
    assert graph.histogram() == histogram
    assert sum(graph.histogram()) == count
    assert graph.work_units() > 0


@pytest.mark.parametrize("algebra, count, histogram", COUNTS)
def test_the_catalog_enumeration_agrees_with_the_graph(algebra, count, histogram):
    # Independent route: no mutation, no approximation, no theorem about the
    # support tau-tilting quiver. Only Hom, tau, and the four conditions.
    listing = algebra.enumerate_over_catalog(F)
    assert len(listing) == count
    assert listing.histogram() == histogram
    assert listing.provenance in ("nakayama", "dynkin_zero_ideal")
    assert listing.catalog_len > 0
    assert listing.nodes_visited > 0


def test_the_closed_graph_and_the_catalog_list_the_same_module_parts():
    algebra = auslander.Algebra.linear_an(3)
    walked = sorted(dims_of(p) for p in algebra.support_tau_tilting_graph(F).pairs())
    listed = sorted(dims_of(p) for p in algebra.enumerate_over_catalog(F).pairs())
    assert walked == listed


def test_a_two_support_tau_tilting_quiver_is_the_pentagon():
    graph = auslander.Algebra.linear_an(2).support_tau_tilting_graph(F)
    edges = sorted((m.source_vertex, m.target_vertex) for m in graph.mutations())
    assert len(graph) == 5
    assert edges == [(0, 1), (0, 2), (1, 3), (2, 4), (3, 4)]
    # Five vertices and five edges, every vertex on exactly two of them: the
    # pentagon, traversed from (A, 0) at vertex 0 down to (0, A) at vertex 4.
    ends = [v for edge in edges for v in edge]
    assert sorted(ends.count(v) for v in range(5)) == [2, 2, 2, 2, 2]
    assert graph.pairs()[0].projective_support == []
    assert graph.pairs()[4].module_summands == []


def test_every_slot_of_a_closed_graph_is_decided():
    graph = auslander.Algebra.linear_an(2).support_tau_tilting_graph(F)
    mutations, fac = 0, 0
    for pair in graph.pairs():
        for slot in range(len(pair.module_summands)):
            outcome = pair.mutate_at(slot)
            assert outcome.verify()
            if isinstance(outcome, auslander.Mutation):
                mutations += 1
            else:
                assert isinstance(outcome, auslander.FacWitness)
                assert outcome.image_dims == outcome.summand.dims
                fac += 1
    # Six module summands over the five vertices: five slots mutate left, and
    # the sixth is the Fac branch, which proves no left mutation exists there.
    assert (mutations, fac) == (5, 1)


def test_a_mutation_carries_its_shape_and_its_target():
    graph = auslander.Algebra.linear_an(2).support_tau_tilting_graph(F)
    first = graph.mutations()[0]
    assert first.source_vertex == 0
    assert first.target_vertex == 1
    assert first.shape == "replaced_by_module"
    assert first.multiplicity == 1
    assert first.exchanged_vertex is None
    assert first.verify()
    assert dims_of(first.target) == dims_of(graph.pairs()[1])

    drop = [m for m in graph.mutations() if m.shape == "moves_to_projective"][0]
    assert drop.multiplicity is None
    assert drop.exchanged_vertex in (0, 1)
    assert drop.verify()


def test_a_walk_that_runs_out_of_budget_is_a_second_class():
    limits = auslander.MutationGraphLimits(max_vertices=6)
    graph = auslander.Algebra.kronecker(2).support_tau_tilting_graph(F, limits=limits)

    assert isinstance(graph, auslander.IncompleteSupportTauTiltingGraph)
    assert not hasattr(graph, "pairs")
    assert graph.reason == "budget_exhausted"
    assert len(graph.vertices_found) == 6
    assert graph.verify_parts()

    diagnostics = graph.diagnostics
    assert isinstance(diagnostics, auslander.GraphBudgetDiagnostics)
    assert diagnostics.limit == "max_vertices"
    assert diagnostics.vertices_found == 6
    assert diagnostics.open_slots > 0
    assert diagnostics.work_units == graph.work_units()

    # The truncated set is a biased sample: the walk descends the preprojective
    # ray (m, m + 1) + (m + 1, m + 2) and reaches no preinjective vertex.
    found = [sorted(m.dims for m in p.module_summands) for p in graph.vertices_found]
    assert [1, 2] in [d for part in found for d in part]


def test_the_budget_keywords_default_and_read_back():
    limits = auslander.MutationGraphLimits(max_vertices=7, max_work_units=1000)
    assert limits.max_vertices == 7
    assert limits.max_work_units == 1000
    assert limits.max_directed_mutations == auslander.MutationGraphLimits().max_directed_mutations
    assert limits.max_matrix_entries == auslander.MutationGraphLimits().max_matrix_entries
    with pytest.raises(TypeError):
        auslander.MutationGraphLimits(7)


def test_a_work_unit_budget_also_truncates():
    limits = auslander.MutationGraphLimits(max_work_units=500)
    graph = d4().support_tau_tilting_graph(F, limits=limits)
    assert isinstance(graph, auslander.IncompleteSupportTauTiltingGraph)
    assert graph.diagnostics.limit == "max_work_units"
    assert graph.reason == "budget_exhausted"


def test_tau_rigidity_answers_both_ways_and_never_raises():
    projective = auslander.Algebra.linear_an(3).projective(F, 0)
    rigid = projective.tau_rigidity()
    assert rigid.is_tau_rigid
    assert rigid.morphism is None
    assert rigid.summand_pair is None
    assert rigid.verify()
    # tau of a projective is the zero module, so its witness set is empty.
    assert all(d == 0 for d in rigid.vanishing.translates[0].dims)
    assert rigid.vanishing.vanishing_pairs == []
    assert [m.dims for m in rigid.vanishing.summands] == [[1, 1, 1]]
    assert rigid.vanishing.verify()

    simple = auslander.Algebra.truncated_poly(3).simple(F, 0)
    not_rigid = simple.tau_rigidity()
    assert not not_rigid.is_tau_rigid
    assert not_rigid.vanishing is None
    assert not_rigid.summand_pair == (0, 0)
    assert not not_rigid.morphism.is_zero
    assert not_rigid.morphism.source.dims == [1]
    assert not_rigid.verify()


def test_the_zero_module_is_tau_rigid_with_an_empty_witness_set():
    algebra = auslander.Algebra.linear_an(2)
    zero = algebra.module(F, [0, 0], [[]])
    rigid = zero.tau_rigidity()
    assert rigid.is_tau_rigid
    assert rigid.vanishing.is_zero_module
    assert rigid.vanishing.summands == []
    assert rigid.verify()


def test_an_accepted_pair_carries_its_parts():
    algebra = auslander.Algebra.linear_an(3)
    pair = auslander.SupportTauTiltingPair.classify(
        algebra, [algebra.projective(F, v) for v in range(3)], [], F
    )
    assert pair.is_pair
    assert pair.rejection is None
    assert pair.is_tau_tilting
    assert pair.summand_count == 3
    assert pair.projective_support == []
    assert dims_of(pair) == [[0, 0, 1], [0, 1, 1], [1, 1, 1]]
    assert pair.verify()

    # (0, A): the zero module with every vertex in the projective support.
    empty = auslander.SupportTauTiltingPair.classify(algebra, [], [0, 1, 2], F)
    assert empty.is_pair
    assert not empty.is_tau_tilting
    assert empty.module_summands == []
    assert empty.verify()


def test_a_rejected_pair_is_a_value_and_names_its_condition():
    algebra = auslander.Algebra.truncated_poly(3)
    # Condition 2: Hom(P, M) is not zero, named by the vertex and the
    # dimension. Hom(P_v, M) = M_v for right modules, so there is no morphism
    # to carry and `witness` is None here.
    hom = auslander.SupportTauTiltingPair.classify(algebra, [algebra.projective(F, 0)], [0], F)
    assert not hom.is_pair
    assert hom.rejection.condition() == 2
    assert hom.rejection.kind == "hom_from_projective_nonzero"
    assert hom.rejection.witness is None
    assert hom.rejection.hom_from_projective == {"vertex": 0, "dim": 3}
    assert hom.rejection.summand_counts is None
    assert hom.module_summands is None
    assert hom.is_tau_tilting is None
    assert hom.verify()

    # Condition 3: M is not tau-rigid, with the nonzero X_i -> tau X_j.
    rigid = auslander.SupportTauTiltingPair.classify(algebra, [algebra.simple(F, 0)], [], F)
    assert rigid.rejection.condition() == 3
    assert rigid.rejection.kind == "not_tau_rigid"
    assert not rigid.rejection.witness.is_zero
    assert rigid.verify()

    # Condition 4: the summand counts do not add up to the vertex count.
    an = auslander.Algebra.linear_an(3)
    count = auslander.SupportTauTiltingPair.classify(an, [an.projective(F, 0)], [], F)
    assert count.rejection.condition() == 4
    assert count.rejection.kind == "summand_count"
    assert count.rejection.witness is None
    assert count.rejection.hom_from_projective is None
    assert count.rejection.summand_counts == {"expected": 3, "module": 1, "projective": 0}
    assert count.verify()

    # Condition 1 is the two parts over different algebras, and the pair
    # constructor rejects that as input before any condition is tested.
    other = auslander.Algebra.linear_an(2)
    with pytest.raises(ValueError, match="another algebra object"):
        auslander.SupportTauTiltingPair.classify(an, [other.projective(F, 0)], [], F)


def test_an_almost_complete_pair_takes_one_summand_fewer():
    algebra = auslander.Algebra.linear_an(2)
    pair = auslander.AlmostCompletePair.classify(algebra, [algebra.projective(F, 0)], [], F)
    assert pair.is_pair
    assert pair.summand_count == 1
    assert pair.projective_support == []
    assert pair.verify()

    full = auslander.AlmostCompletePair.classify(
        algebra, [algebra.projective(F, 0), algebra.projective(F, 1)], [], F
    )
    assert not full.is_pair
    assert full.rejection.condition() == 4
    assert full.rejection.summand_counts == {"expected": 1, "module": 2, "projective": 0}
    assert full.verify()


def test_verify_holds_on_everything_the_v05_layer_accepts():
    algebra = auslander.Algebra.linear_an(3)
    graph = algebra.support_tau_tilting_graph(F)
    assert graph.verify()
    assert all(pair.verify() for pair in graph.pairs())
    assert all(mutation.verify() for mutation in graph.mutations())

    listing = algebra.enumerate_over_catalog(F)
    assert listing.verify()
    assert all(pair.verify() for pair in listing.pairs())

    assert all(
        module.tau_rigidity().verify()
        for pair in graph.pairs()
        for module in pair.module_summands
    )


def test_the_exception_taxonomy_separates_answers_from_failures():
    algebra = auslander.Algebra.truncated_poly(3)
    # A rejected pair is an answer, so nothing raises and nothing has to be
    # caught to read it.
    rejected = auslander.SupportTauTiltingPair.classify(algebra, [algebra.simple(F, 0)], [], F)
    assert not rejected.is_pair

    # A blocked certification is its own RuntimeError subclass, never a
    # ValueError, and it is not budget exhaustion.
    assert issubclass(auslander.CertificationBlockedError, RuntimeError)
    assert not issubclass(auslander.CertificationBlockedError, ValueError)
    assert not issubclass(auslander.CertificationBlockedError, auslander.BudgetExhaustedError)

    # An algebra outside both catalog domains has no exhaustive catalog, so the
    # enumeration route is refused rather than truncated.
    with pytest.raises(auslander.UnsupportedDomainError):
        auslander.Algebra.kronecker(2).enumerate_over_catalog(F)

    # A non-basic module part is rejected input.
    with pytest.raises(ValueError, match="not basic"):
        auslander.SupportTauTiltingPair.classify(
            algebra, [algebra.projective(F, 0), algebra.projective(F, 0)], [], F
        )
    with pytest.raises(ValueError, match="out of range"):
        auslander.SupportTauTiltingPair.classify(algebra, [], [4], F)

    # A rejection has no slots, and neither has a slot past the last summand.
    with pytest.raises(ValueError, match="not a pair"):
        rejected.mutate_at(0)
    graph = auslander.Algebra.linear_an(2).support_tau_tilting_graph(F)
    with pytest.raises(ValueError, match="out of range"):
        graph.pairs()[0].mutate_at(9)

    # A monomial presentation is field-free and a graph is not.
    with pytest.raises(ValueError, match="pass a field"):
        algebra.support_tau_tilting_graph()

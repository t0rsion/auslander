"""Test value semantics, exception taxonomy, and morphism endpoints.

Typed results compare and hash by value: an equal pair is one dict key.
Engine defects are RuntimeError, never ValueError. A Morphism carries its
endpoints, so a witness handed back on its own still says what it maps
between, and composition is checked against those endpoints.
"""

import sys
import threading

import pytest

import auslander

DF = auslander.DiagramFamily


def a3():
    return auslander.Algebra.linear_an(3)


def test_resolution_status_and_bounded_hash_by_value():
    field = auslander.PrimeField(5)
    resolution = a3().simple(0, field=field).resolve(4)
    status = resolution.status
    same = auslander.ResolutionStatus(status.kind, status.at)
    cut = auslander.ResolutionStatus(auslander.ResolutionKind.CUT, 2)

    assert status == same
    assert hash(status) == hash(same)
    assert {status: "finite"}[same] == "finite"
    assert len({status, same, cut}) == 2

    exact = resolution.pd(4)
    assert {exact: "pd"}[a3().simple(0, field=field).resolve(4).pd(4)] == "pd"
    assert hash(exact) != hash(auslander.Algebra.kronecker(2).simple(0, field=field).resolve(0).pd(0))


def test_diagram_types_hash_by_value():
    a_three = auslander.DynkinType(DF.A, 3)
    counts = {auslander.DynkinType(DF.A, 3): 6, auslander.DynkinType(DF.D, 4): 12}
    assert counts[a_three] == 6
    assert len({auslander.DynkinType(DF.E6), auslander.DynkinType(DF.E6)}) == 1

    affine = auslander.EuclideanType(DF.D, 4)
    assert {auslander.EuclideanType(DF.D, 4): 5}[affine] == 5
    assert len({auslander.EuclideanType(DF.A, 1), affine}) == 2


def test_the_member_enums_hash_by_value():
    kinds = {auslander.ResolutionKind.FINITE: "finite", auslander.ResolutionKind.CUT: "cut"}
    assert kinds[auslander.ResolutionKind.CUT] == "cut"
    families = {DF.A: 1, DF.D: 4, DF.E8: 8}
    assert families[DF.E8] == 8
    assert {auslander.AlmostSplitOutcome.PROJECTIVE: "p"}[auslander.AlmostSplitOutcome.PROJECTIVE]


def test_diagram_parameters_are_rejected_the_same_way_for_both_types():
    for kind, name in [(auslander.DynkinType, "DynkinType"), (auslander.EuclideanType, "EuclideanType")]:
        with pytest.raises(ValueError, match=f"{name}: A needs an integer n >= 1"):
            kind(DF.A, 0)
        with pytest.raises(ValueError, match=f"{name}: D needs an integer n >= 4"):
            kind(DF.D, 3)
        with pytest.raises(ValueError, match=f"{name}: E6, E7 and E8 take n=None"):
            kind(DF.E6, 6)


def test_engine_defects_never_cross_as_value_error():
    # Every defect route reports DefectError, so `except ValueError` cannot
    # swallow a bug in this library. The AR-quiver and category-radical hom
    # and space variants raise DefectError.
    assert issubclass(auslander.DefectError, RuntimeError)
    assert not issubclass(auslander.DefectError, ValueError)
    assert issubclass(auslander.TauAgreementUnknown, RuntimeError)
    assert not issubclass(auslander.TauAgreementUnknown, ValueError)


def test_rejected_input_of_the_ar_layer_stays_value_error():
    field = auslander.PrimeField(5)
    algebra = a3()
    # The endpoints are validated before the call, so both rejections are the
    # ValueError subclass of the failed precondition, not a defect.
    projective = algebra.projective(0, field=field)
    doubled = algebra.module([2, 2, 2], [[[1, 0], [0, 1]], [[1, 0], [0, 1]]], field=field)
    with pytest.raises(auslander.NotIndecomposableError) as rejected:
        doubled.category_radical(projective)
    assert rejected.value.kind == "decomposable"
    assert issubclass(auslander.NotIndecomposableError, ValueError)

    square = auslander.Algebra.from_relations(
        auslander.Quiver(4, [(0, 1), (1, 3), (0, 2), (2, 3)]),
        [[(1, [0, 1]), (-1, [2, 3])]],
        field,
    )
    with pytest.raises(auslander.UnsupportedDomainError):
        square.ar_quiver()


def test_morphism_carries_its_endpoints():
    field = auslander.PrimeField(5)
    algebra = a3()
    p0 = algebra.projective(0, field=field)
    identity = p0.morphism(p0, [[[1]], [[1]], [[1]]])

    assert identity.source.dims == p0.dims
    assert identity.target.dims == p0.dims
    assert not identity.is_zero
    assert identity.is_isomorphism()

    composite = identity.then(identity)
    assert composite.maps == identity.maps
    assert composite.source.dims == p0.dims
    assert composite.target.dims == p0.dims


def test_morphism_composition_checks_the_endpoints():
    field = auslander.PrimeField(5)
    algebra = a3()
    p0 = algebra.projective(0, field=field)
    s2 = algebra.simple(2, field=field)
    zero = p0.morphism(s2, [[[]], [[]], [[0]]])

    assert zero.is_zero
    assert zero.source.dims == p0.dims
    assert zero.target.dims == s2.dims
    with pytest.raises(ValueError, match="target of the first morphism is not the source"):
        zero.then(zero)


def test_map_at_reads_one_vertex_matrix():
    field = auslander.PrimeField(5)
    algebra = a3()
    p0 = algebra.projective(0, field=field)
    identity = p0.morphism(p0, [[[1]], [[1]], [[1]]])

    assert [identity.map_at(v) for v in range(3)] == identity.maps
    with pytest.raises(ValueError, match="vertex 3 out of range"):
        identity.map_at(3)


def test_len_of_ar_quiver_and_decomposition():
    field = auslander.PrimeField(5)
    algebra = auslander.Algebra.truncated_poly(3)
    quiver = algebra.ar_quiver(field)
    assert len(quiver) == 3
    assert len(quiver) == len(quiver.vertices())

    simple = algebra.simple(0, field=field)
    assert len(simple.decompose()) == 1
    doubled = algebra.module([2], [[[0, 0], [0, 0]]], field=field)
    decomposition = doubled.decompose()
    assert len(decomposition) == 2
    assert len(decomposition) == len(decomposition.summands)


def test_computations_release_the_gil():
    field = auslander.PrimeField(5)
    algebra = auslander.Algebra.linear_an(14, field=field)
    ready = threading.Event()
    start_native = threading.Event()
    native_active = False
    worker_observations = []
    worker_errors = []

    def worker():
        try:
            ready.set()
            if not start_native.wait(timeout=10):
                raise AssertionError("worker did not receive the native start signal")
            worker_observations.append(native_active)
        except BaseException as error:
            worker_errors.append(error)

    thread = threading.Thread(target=worker)
    previous_interval = sys.getswitchinterval()
    # Suppress interpreter-driven switches so the observation depends on the
    # native call releasing the GIL.
    sys.setswitchinterval(60.0)
    try:
        thread.start()
        if not ready.wait(timeout=10):
            raise AssertionError("worker did not become ready")
        native_active = True
        start_native.set()
        quiver = algebra.ar_quiver()
    finally:
        native_active = False
        start_native.set()
        sys.setswitchinterval(previous_interval)
        thread.join(timeout=10)

    if thread.is_alive():
        raise AssertionError("worker did not finish")
    if worker_errors:
        raise worker_errors[0]
    assert worker_observations == [True]
    assert len(quiver) == 105

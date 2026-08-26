"""Checked complexes, relative bar Hochschild cohomology, and classical tilting."""

import threading
import time

import pytest

import auslander


def generous_bar_limits(**changes):
    values = {
        "max_tensor_tuples": 10_000,
        "max_cochain_dim": 100_000,
        "max_matrix_entries": 10_000_000,
        "max_work_units": 1_000_000_000,
    }
    values.update(changes)
    return auslander.BarLimits(**values)


def test_checked_complex_reports_exactness_and_first_homology():
    field = auslander.PrimeField(5)
    algebra = auslander.Algebra.linear_an(2)
    simple = algebra.simple(field, 0)
    resolution = simple.resolve(2)
    complex_ = auslander.CheckedComplex(
        [resolution.terms[1], resolution.terms[0], simple],
        [resolution.maps[0], resolution.augmentation],
    )

    assert complex_.verify()
    assert len(complex_) == 3
    assert [term.dims for term in complex_.terms] == [[0, 1], [1, 1], [1, 0]]
    assert [complex_.homology_dimensions(i).dimension_vector for i in range(3)] == [
        [0, 0],
        [0, 0],
        [0, 0],
    ]
    exact = complex_.exactness()
    assert isinstance(exact, auslander.ExactComplex)
    assert exact.verify()
    assert exact.complex.verify()

    nonexact = auslander.CheckedComplex([simple], []).exactness()
    assert isinstance(nonexact, auslander.NonExactWitness)
    assert nonexact.index == 0
    assert nonexact.dimension_vector == [1, 0]
    assert nonexact.homology.dimension_vector == [1, 0]
    assert nonexact.verify()


def test_checked_complex_rejects_bad_shapes_endpoints_and_composites():
    field = auslander.PrimeField(5)
    algebra = auslander.Algebra.linear_an(2)
    simple = algebra.simple(field, 0)
    identity = simple.morphism(simple, [[[1]], []])

    with pytest.raises(ValueError, match="at least one term"):
        auslander.CheckedComplex([], [])
    with pytest.raises(ValueError, match="expected 0"):
        auslander.CheckedComplex([simple], [identity])
    with pytest.raises(ValueError, match="adjacent terms"):
        auslander.CheckedComplex([simple, algebra.simple(field, 1)], [identity])
    with pytest.raises(ValueError, match="nonzero composite"):
        auslander.CheckedComplex([simple, simple, simple], [identity, identity])


def dual_of_a3_mod_ab(field):
    algebra = auslander.Algebra.an_with_relations(3, [(0, 2)])
    # D(A) = I_0 + I_1 + I_2. The two arrow maps are block diagonal in that
    # summand order.
    module = algebra.module(
        field,
        [2, 2, 1],
        [
            [[0, 0], [1, 0]],
            [[0], [1]],
        ],
    )
    return algebra, module


@pytest.mark.parametrize("prime", [2, 5])
def test_pd2_classical_tilting_carries_the_checked_generation_complex(prime):
    field = auslander.PrimeField(prime)
    _, module = dual_of_a3_mod_ab(field)
    limits = auslander.TiltingLimits(4, 5)
    result = auslander.ClassicalTiltingModule.classify(module, limits)

    assert isinstance(result, auslander.ClassicalTiltingResult)
    assert result.is_tilting is True
    assert result.rejection is None
    assert result.blocker is None
    assert result.verify()
    tilting = result.tilting
    assert tilting.projective_dimension == 2
    assert tilting.module.dims == [2, 2, 1]
    assert tilting.limits.max_projective_dimension == 4
    assert tilting.resolution.status.kind == auslander.ResolutionKind.FINITE
    assert [term.dims for term in tilting.generation_complex.complex.terms] == [
        [1, 2, 2],
        [1, 3, 2],
        [1, 1, 0],
        [1, 0, 0],
    ]
    assert tilting.generation_complex.verify()
    assert len(tilting.ext_spaces) == 2
    assert all(space.dim == 0 for space in tilting.ext_spaces)
    assert len(tilting.add_witnesses) == 3
    assert all(witness.verify() for witness in tilting.add_witnesses)
    assert tilting.verify()


def test_classical_tilting_keeps_negative_and_undetermined_distinct():
    field = auslander.PrimeField(5)

    dual_numbers = auslander.Algebra.dual_numbers()
    periodic = dual_numbers.simple(field, 0)
    cut = auslander.ClassicalTiltingModule.classify(
        periodic, auslander.TiltingLimits(2, 3)
    )
    assert cut.is_tilting is None
    assert cut.tilting is None and cut.rejection is None
    assert cut.blocker.kind == "projective_dimension"
    assert cut.blocker.projective_dimension.at_least == 3
    assert cut.blocker.projective_dimension_bound == 2
    assert cut.blocker.verify()

    kronecker = auslander.Algebra.kronecker(2)
    self_extending = kronecker.module(field, [1, 1], [[[1]], [[0]]])
    rejected = auslander.ClassicalTiltingModule.classify(
        self_extending, auslander.TiltingLimits(4, 5)
    )
    assert rejected.is_tilting is False
    assert rejected.tilting is None and rejected.blocker is None
    assert rejected.rejection.degree == 1
    assert rejected.rejection.dimension == 1
    assert rejected.rejection.verify()
    assert rejected.verify()


def test_classical_tilting_generation_cut_keeps_its_partial_complex():
    field = auslander.PrimeField(5)
    _, module = dual_of_a3_mod_ab(field)
    result = auslander.ClassicalTiltingModule.classify(
        module, auslander.TiltingLimits(2, 2)
    )
    blocker = result.blocker
    assert result.is_tilting is None
    assert blocker.kind == "generation"
    assert blocker.generation_kind == "step_limit"
    assert blocker.stage == 2
    assert blocker.max_generation_steps == 2
    assert len(blocker.partial_complex) == 3
    assert blocker.cokernel_dimension_vector == blocker.cokernel.dims
    assert blocker.kernel_dimension_vector is None
    assert blocker.verify()


@pytest.mark.parametrize("prime, dimensions", [(2, [2, 2, 2]), (5, [2, 1, 1])])
def test_relative_bar_pins_the_dual_number_sign(prime, dimensions):
    field = auslander.PrimeField(prime)
    algebra = auslander.Algebra.dual_numbers()
    result = algebra.hochschild_cohomology(field, 2, generous_bar_limits())

    assert isinstance(result, auslander.HochschildCohomology)
    assert result.requested_degree == 2
    assert result.dimensions == dimensions
    assert result.diagnostics.work_units > 0
    assert result.verify()
    for degree, dimension in enumerate(dimensions):
        space = result.degree(degree)
        assert space.degree == degree
        assert space.dim == dimension
        assert space.verify()


def test_relative_bar_decodes_inputs_and_evaluates_classes():
    field = auslander.PrimeField(5)
    algebra = auslander.Algebra.truncated_poly(3)
    result = algebra.hochschild_cohomology(field, 2, generous_bar_limits())
    assert result.dimensions == [3, 2, 2]

    degree_two = result.degree(2)
    assert [degree_two.input_for_rank(rank) for rank in range(4)] == [
        [1, 1],
        [1, 2],
        [2, 1],
        [2, 2],
    ]
    assert degree_two.basis_word(0) == (0, 0, [])
    assert degree_two.basis_word(1) == (0, 0, [0])
    with pytest.raises(ValueError, match="tuple rank"):
        degree_two.input_for_rank(4)

    dual = auslander.Algebra.dual_numbers().hochschild_cohomology(
        field, 1, generous_bar_limits()
    )
    degree_one = dual.degree(1)
    cls = degree_one.class_from_coordinates([1])
    assert cls.coordinates == [1]
    assert not cls.is_zero
    assert cls.verify()
    assert len(cls.evaluate([1])) == 1
    assert degree_one.zero_class().is_zero
    with pytest.raises(ValueError, match="vertex idempotent"):
        cls.evaluate([0])
    with pytest.raises(ValueError, match="degree 2, expected 1"):
        cls.evaluate([1, 1])


@pytest.mark.parametrize(
    "change, reason",
    [
        ({"max_tensor_tuples": 0}, "max_tensor_tuples"),
        ({"max_cochain_dim": 0}, "max_cochain_dim"),
        ({"max_matrix_entries": 0}, "max_matrix_entries"),
        ({"max_work_units": 0}, "max_work_units"),
    ],
)
def test_relative_bar_cuts_are_typed_values(change, reason):
    field = auslander.PrimeField(5)
    result = auslander.Algebra.dual_numbers().hochschild_cohomology(
        field, 1, generous_bar_limits(**change)
    )
    assert isinstance(result, auslander.IncompleteHochschildCohomology)
    assert not hasattr(result, "degree")
    assert not hasattr(result, "requested_degree")
    assert result.reason == reason
    assert result.diagnostics.reason == reason
    assert result.diagnostics.proposed > result.diagnostics.ceiling
    assert result.diagnostics.first_uncomputed_differential >= 0
    assert result.verify()


def test_v06_acceptance_path():
    field = auslander.PrimeField(5)
    algebra, dual = dual_of_a3_mod_ab(field)
    simple = algebra.simple(field, 0)
    resolution = simple.resolve(2)
    exact = auslander.CheckedComplex(
        [resolution.terms[2], resolution.terms[1], resolution.terms[0], simple],
        [resolution.maps[1], resolution.maps[0], resolution.augmentation],
    ).exactness()
    assert isinstance(exact, auslander.ExactComplex)
    assert exact.verify()

    x_cubed = auslander.Algebra.truncated_poly(3)
    cohomology = x_cubed.hochschild_cohomology(field, 2, generous_bar_limits())
    assert cohomology.dimensions == [3, 2, 2]
    cut = x_cubed.hochschild_cohomology(
        field, 2, generous_bar_limits(max_work_units=0)
    )
    assert isinstance(cut, auslander.IncompleteHochschildCohomology)
    assert cut.completed_degrees == []
    assert cut.verify()

    for prime in (2, 5):
        _, dual = dual_of_a3_mod_ab(auslander.PrimeField(prime))
        result = auslander.ClassicalTiltingModule.classify(
            dual, auslander.TiltingLimits(4, 5)
        )
        assert result.is_tilting is True
        assert result.tilting.projective_dimension == 2
        assert result.tilting.generation_complex.verify()
        assert result.verify()


def test_v06_long_calls_release_gil():
    ticks = [0]
    stop = threading.Event()

    def count():
        while not stop.is_set():
            ticks[0] += 1

    worker = threading.Thread(target=count)
    worker.start()
    try:
        time.sleep(0.01)
        field = auslander.PrimeField(5)
        algebra = auslander.Algebra.truncated_poly(3)
        before_bar = ticks[0]
        for _ in range(3):
            result = algebra.hochschild_cohomology(field, 3, generous_bar_limits())
            assert isinstance(result, auslander.HochschildCohomology)
        after_bar = ticks[0]

        _, module = dual_of_a3_mod_ab(field)
        before_tilting = ticks[0]
        for _ in range(3):
            result = auslander.ClassicalTiltingModule.classify(
                module, auslander.TiltingLimits(4, 5)
            )
            assert result.is_tilting is True
        after_tilting = ticks[0]
    finally:
        stop.set()
        worker.join()

    assert after_bar > before_bar
    assert after_tilting > before_tilting

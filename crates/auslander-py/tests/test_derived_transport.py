"""Target algebras, graded Ext, homotopy, and derived transport."""

import gc
import sys

import pytest

import auslander


def classify_tilting(module):
    result = auslander.ClassicalTiltingModule.classify(
        module, auslander.TiltingLimits(4, 8)
    )
    assert result.is_tilting is True
    return result.tilting


def pd2_dual(field):
    algebra = auslander.Algebra.an_with_relations(3, [(0, 2)])
    module = algebra.module(
        [2, 2, 1],
        [
            [[0, 0], [1, 0]],
            [[0], [1]],
        ],
        field=field,
    )
    return algebra, module


def pd2_derived(field):
    _, module = pd2_dual(field)
    tilting = classify_tilting(module)
    target = tilting.target_presentation(auslander.TargetLimits())
    certificate = auslander.DerivedEquivalenceCertificate(tilting, target)
    return tilting, target, certificate


def add_t_complex(tilting, complex_):
    witnesses = []
    for term in complex_.terms:
        witness = tilting.add_closure_witness(term)
        assert witness is not None
        witnesses.append(witness)
    return auslander.AddTComplex(complex_, witnesses)


@pytest.mark.parametrize("prime", [2, 5])
def test_split_target_presentation_keeps_maps_relations_and_work(prime):
    field = auslander.PrimeField(prime)
    algebra = auslander.Algebra.dual_numbers()
    tilting = classify_tilting(algebra.projective(0, field=field))
    target = tilting.target_presentation(auslander.TargetLimits())
    _assert_split_target_shape(target)
    _assert_split_target_work(target)
    _assert_split_target_coordinates(target)


def _assert_split_target_shape(target):

    assert isinstance(target, auslander.TargetPresentation)
    assert target.target.dim == 2
    assert target.target.quiver.arrows == [(0, 0)]
    assert target.target.cartan_matrix() == [[2]]


def _assert_split_target_work(target):
    assert target.work.endo_dimension == 2
    assert target.work.paths == 1
    assert target.work.relation_terms == 1
    assert target.radical_nilpotency_index == 2


def _assert_split_target_coordinates(target):
    assert len(target.certificate_json) > 0
    assert target.preimage_coordinates(target.map_coordinates([1, 1])) == [1, 1]
    assert target.verify()


@pytest.mark.parametrize("prime", [2, 5])
def test_pd1_and_pd2_targets_cover_opposite_orientation(prime):
    field = auslander.PrimeField(prime)
    hereditary = auslander.Algebra.linear_an(2)
    pd1 = hereditary.module([2, 1], [[[1], [0]]], field=field)
    pd1_target = classify_tilting(pd1).target_presentation(auslander.TargetLimits())
    assert pd1_target.target.quiver.arrows == [(1, 0)]
    assert pd1_target.verify()

    _, pd2 = pd2_dual(field)
    pd2_target = classify_tilting(pd2).target_presentation(auslander.TargetLimits())
    assert pd2_target.target.num_vertices == 3
    assert pd2_target.target.dim == pd2_target.work.endo_dimension
    assert len(pd2_target.summands) == 3
    assert len(pd2_target.inclusions) == len(pd2_target.projections) == 3
    assert len(pd2_target.endomorphism_basis) == pd2_target.target.dim
    assert pd2_target.endomorphism([1] + [0] * (pd2_target.target.dim - 1)).source.dims
    assert pd2_target.verify()


@pytest.mark.parametrize("prime", [2, 5])
@pytest.mark.parametrize(
    "change, stage_kind",
    [
        ({"max_endo_dimension": 1}, "endomorphism_dimension"),
        ({"max_radical_products": 0}, "radical_power"),
        ({"max_paths": 0}, "paths"),
        ({"max_relation_terms": 0}, "relations"),
        ({"max_steps": 0}, "completion"),
    ],
)
def test_target_cuts_retain_the_first_rejected_reservation(prime, change, stage_kind):
    field = auslander.PrimeField(prime)
    tilting = classify_tilting(auslander.Algebra.dual_numbers().projective(0, field=field))
    cut = tilting.target_presentation(auslander.TargetLimits(**change))

    assert isinstance(cut, auslander.IncompleteTargetPresentation)
    assert cut.stage_kind == stage_kind
    if cut.kind == "target_budget":
        assert cut.used is not None
        assert cut.requested is not None
        assert cut.limit is not None
    else:
        assert cut.kind == "completion_budget"
        assert cut.completion_steps_used is not None
    assert cut.verify()


@pytest.mark.parametrize("prime", [2, 5])
def test_bounded_ext_algebra_keeps_complete_and_cut_distinct(prime):
    field = auslander.PrimeField(prime)
    hereditary = auslander.Algebra.linear_an(2)
    projective = hereditary.projective(0, field=field)
    complete = projective.ext_algebra(2)
    _assert_complete_ext_algebra(complete)

    periodic = auslander.Algebra.dual_numbers().simple(0, field=field)
    cut = periodic.ext_algebra(4)
    _assert_cut_ext_algebra(cut)


def _assert_complete_ext_algebra(complete):
    assert isinstance(complete, auslander.ExtAlgebra)
    assert complete.bound == 2
    assert complete.dimensions == [1, 0, 0]
    assert complete.resolution_status.kind == auslander.ResolutionKind.FINITE
    assert complete.verify()


def _assert_cut_ext_algebra(cut):
    assert isinstance(cut, auslander.IncompleteExtAlgebra)
    assert cut.bound == 4
    assert cut.first_omitted_degree == 5
    assert cut.dimensions == [1, 1, 1, 1, 1]
    assert cut.resolution_status.kind == auslander.ResolutionKind.CUT
    assert cut.verify()


@pytest.mark.parametrize("prime", [2, 5])
def test_ext_tensors_expose_products_and_the_unit(prime):
    field = auslander.PrimeField(prime)
    simple = auslander.Algebra.truncated_poly(3).simple(0, field=field)
    algebra = simple.ext_algebra(4)

    unit = algebra.unit
    degree_one = algebra.basis(1)[0]
    degree_two = algebra.basis(2)[0]
    tensor = algebra.multiplication(1, 1)
    independent, witness = degree_one.then_with_witness(degree_one)
    _assert_ext_tensor_shape(tensor)
    _assert_ext_tensor_product(tensor, independent, witness)
    _assert_ext_tensor_multiplication(algebra, degree_one, degree_two, unit)
    _assert_ext_product_records(algebra)


def _assert_ext_tensor_shape(tensor):

    assert tensor.shape == (1, 1, 1)
    assert tensor.coefficients == tensor.basis_product(0, 0)


def _assert_ext_tensor_product(tensor, independent, witness):
    assert tensor.product(0, 0) == independent
    assert witness.verify(independent)
    assert tensor.witness(0, 0).verify(tensor.product(0, 0))


def _assert_ext_tensor_multiplication(algebra, degree_one, degree_two, unit):
    _assert_ext_degree_products(algebra, degree_one, degree_two)
    _assert_ext_unit_products(algebra, unit, degree_two)


def _assert_ext_degree_products(algebra, degree_one, degree_two):
    assert algebra.multiply(degree_one, degree_one).is_zero
    assert not algebra.multiply(degree_one, degree_two).is_zero
    assert not algebra.multiply(degree_two, degree_one).is_zero
    assert not algebra.multiply(degree_two, degree_two).is_zero


def _assert_ext_unit_products(algebra, unit, degree_two):
    assert algebra.multiply(unit, degree_two) == degree_two
    assert algebra.multiply(degree_two, unit) == degree_two
    assert algebra.degree(4).dim == 1


def _assert_ext_product_records(algebra):
    records = algebra.product_records()
    _assert_ext_record_verification(records)
    _assert_ext_record_order(algebra, records)


def _assert_ext_record_verification(records):
    assert all(record.verify() for record in records)


def _assert_ext_record_order(algebra, records):
    assert [
        (record.left_degree, record.left_basis, record.right_degree, record.right_basis)
        for record in records
    ] == sorted(
        (
            record.left_degree,
            record.left_basis,
            record.right_degree,
            record.right_basis,
        )
        for record in records
    )
    with pytest.raises(ValueError, match="outside"):
        algebra.multiplication(3, 2)


@pytest.mark.parametrize("prime", [2, 5])
def test_bounded_homotopy_checks_shifts_cones_and_quotients(prime):
    field = auslander.PrimeField(prime)
    simple = auslander.Algebra.linear_an(1).simple(0, field=field)
    identity = simple.morphism(simple, [[[1]]])
    one_term = auslander.BoundedComplex(0, [simple], [])
    _assert_complex_shift(one_term)
    _assert_identity_cone(one_term)
    _assert_hom_quotient(one_term)
    _assert_degree_one_quotient(one_term)


def _assert_complex_shift(one_term):

    assert one_term.degree_range == (0, 0)
    assert one_term.shift(3).degree_range == (3, 3)
    assert one_term.verify()


def _assert_identity_cone(one_term):
    identity_chain = one_term.identity()
    cone = identity_chain.mapping_cone()
    assert cone.degree_range == (0, 1)
    assert cone.verify()
    assert cone.identity().is_null_homotopic()


def _assert_hom_quotient(one_term):
    hom = one_term.hom(one_term)
    quotient = hom.quotient()
    _assert_hom_dimensions(hom, quotient)
    _assert_hom_reduction(quotient)


def _assert_hom_dimensions(hom, quotient):
    assert hom.degree == quotient.degree == 0
    assert hom.dim == quotient.dim == 1


def _assert_hom_reduction(quotient):
    representative = quotient.representative([1])
    coordinates, remainder = quotient.reduce(representative)
    assert coordinates == [1]
    assert remainder.is_null_homotopic()
    assert quotient.verify()


def _assert_degree_one_quotient(one_term):
    degree_one = auslander.HomotopyHom(one_term, one_term, 1)
    assert degree_one.shifted_target.degree_range == (1, 1)
    assert degree_one.quotient().dim == 0
    assert degree_one.verify()


@pytest.mark.parametrize("prime", [2, 5])
def test_explicit_homotopy_contracts_the_identity_differential(prime):
    field = auslander.PrimeField(prime)
    simple = auslander.Algebra.linear_an(1).simple(0, field=field)
    identity = simple.morphism(simple, [[[1]]])
    complex_ = auslander.BoundedComplex(0, [simple, simple], [identity])
    identity_chain = complex_.identity()
    zero_chain = complex_.zero_map(complex_)
    homotopy = auslander.ChainHomotopy.between(
        identity_chain, zero_chain, [identity]
    )

    assert homotopy.verify()
    assert identity_chain.homotopic_to(zero_chain, homotopy)
    assert homotopy.boundary().agrees_with(identity_chain)
    assert identity_chain.is_null_homotopic()
    assert complex_.hom(complex_).quotient().dim == 0

    with pytest.raises(ValueError, match="nonzero composite"):
        auslander.BoundedComplex(
            0, [simple, simple, simple], [identity, identity]
        )


@pytest.mark.parametrize("prime", [2, 5])
def test_pd2_derived_certificate_and_strict_transport_round_trips(prime):
    field = auslander.PrimeField(prime)
    tilting, target, certificate = pd2_derived(field)
    _assert_pd2_certificate(certificate, target)

    transport = certificate.transport
    fixture = _build_transport_fixture(tilting, transport)
    source, source_map, target_complex, target_map, target_map_again, complex_ = fixture
    _assert_transport_shapes(source, target_complex, complex_)
    _assert_transport_round_trips(transport, source, target_complex, target_map)
    _assert_transport_products(
        transport, source, source_map, target_complex, target_map, target_map_again
    )
    _assert_transport_homotopy(transport, complex_, source, target_complex)
    _assert_transport_cones_and_shifts(
        transport, tilting, complex_, source, source_map, target_complex, target_map
    )


def _assert_pd2_certificate(certificate, target):
    _assert_certificate_parts(certificate)
    _assert_certificate_graded_homotopy(certificate)
    _assert_certificate_identification(certificate, target)


def _assert_certificate_parts(certificate):

    assert certificate.verify()
    assert certificate.tilting.verify()
    assert certificate.target.verify()
    assert certificate.resolution_complex.verify()


def _assert_certificate_graded_homotopy(certificate):
    assert [space.degree for space in certificate.graded_homotopy] == [-2, -1, 0, 1, 2]
    assert all(
        space.quotient.dim == 0
        for space in certificate.graded_homotopy
        if space.degree != 0
    )


def _assert_certificate_identification(certificate, target):
    zero = next(space for space in certificate.graded_homotopy if space.degree == 0)
    identification = certificate.degree_zero_identification
    assert zero.verify()
    assert identification.quotient.verify()
    assert len(identification.coordinates) == zero.quotient.dim
    assert all(len(row) == target.target.dim for row in identification.coordinates)


def _build_transport_fixture(tilting, transport):
    module = tilting.module
    differential = next(
        map_
        for map_ in module.hom(module)
        if not map_.is_zero and not map_.is_isomorphism()
    )
    complex_ = auslander.BoundedComplex(0, [module, module], [differential])
    source = add_t_complex(tilting, complex_)
    source_map = auslander.ChainMap(complex_, complex_, [differential, differential])
    target_complex = transport.forward(source)
    target_map = transport.forward_chain_map(source, source, source_map)
    target_map_again = transport.forward_chain_map(source, source, source_map)
    return source, source_map, target_complex, target_map, target_map_again, complex_


def _assert_transport_shapes(source, target_complex, complex_):
    _assert_transport_complexes(source, target_complex)
    _assert_transport_dimensions(complex_, target_complex)


def _assert_transport_complexes(source, target_complex):
    assert source.verify()
    assert target_complex.verify()


def _assert_transport_dimensions(complex_, target_complex):
    source_dims = [
        complex_.hom(complex_, degree).quotient().dim for degree in range(-2, 3)
    ]
    target_dims = [
        target_complex.complex.hom(target_complex.complex, degree).quotient().dim
        for degree in range(-2, 3)
    ]
    assert source_dims == target_dims == [0, 3, 6, 3, 0]


def _assert_transport_round_trips(transport, source, target_complex, target_map):
    _assert_transport_certificates(transport, source, target_complex)
    _assert_transport_map(transport, target_complex, target_map)


def _assert_transport_certificates(transport, source, target_complex):
    assert transport.verify()
    assert transport.reverse(target_complex).verify()
    assert transport.source_round_trip(source).verify()
    assert transport.target_round_trip(target_complex).verify()


def _assert_transport_map(transport, target_complex, target_map):
    assert target_map.verify()
    assert transport.reverse_chain_map(target_complex, target_complex, target_map).verify()


def _assert_transport_products(
    transport, source, source_map, target_complex, target_map, target_map_again
):
    source_product = source_map.then(source_map)
    target_product = transport.forward_chain_map(source, source, source_product)
    assert target_product.agrees_with(target_map.then(target_map_again))
    reverse_map = transport.reverse_chain_map(target_complex, target_complex, target_map)
    reverse_again = transport.reverse_chain_map(
        target_complex, target_complex, target_map_again
    )
    reverse_product = transport.reverse_chain_map(
        target_complex, target_complex, target_product
    )
    assert reverse_product.agrees_with(reverse_map.then(reverse_again))


def _assert_transport_homotopy(transport, complex_, source, target_complex):
    zero_component = complex_.zero_map(complex_).components[0]
    homotopy = auslander.ChainHomotopy.between(
        complex_.identity(), complex_.identity(), [zero_component]
    )
    target_homotopy = transport.forward_homotopy(source, source, homotopy)
    assert target_homotopy.verify()
    assert transport.reverse_homotopy(
        target_complex, target_complex, target_homotopy
    ).verify()


def _assert_transport_cones_and_shifts(
    transport, tilting, complex_, source, source_map, target_complex, target_map
):
    _assert_transport_cone(transport, source, source_map, target_map)
    _assert_transport_shift(transport, tilting, complex_, source, target_complex)


def _assert_transport_cone(transport, source, source_map, target_map):
    assert transport.forward_cone(source, source, source_map).agrees_with(
        target_map.mapping_cone()
    )


def _assert_transport_shift(transport, tilting, complex_, source, target_complex):
    shifted_source = add_t_complex(tilting, complex_.shift(2))
    assert transport.forward_shift(source, 2).complex.agrees_with(
        transport.forward(shifted_source).complex
    )
    assert transport.reverse_shift(target_complex, -2).verify()
    assert transport.forward_direct_sum([source, source]).verify()
    assert transport.reverse_direct_sum([target_complex, target_complex]).verify()


def test_derived_transport_rejections_and_homotopy_overflow_are_typed():
    field = auslander.PrimeField(5)
    tilting, target, certificate = pd2_derived(field)
    module = tilting.module
    one_term = auslander.BoundedComplex(0, [module], [])
    source = add_t_complex(tilting, one_term)

    with pytest.raises(auslander.TransportInputError) as caught:
        auslander.AddTComplex(one_term, [])
    assert caught.value.expected == 1
    assert caught.value.got == 0

    shifted = add_t_complex(tilting, one_term.shift(1))
    with pytest.raises(auslander.TransportInputError, match="chain map"):
        certificate.transport.forward_chain_map(
            source, shifted, one_term.identity()
        )

    for vertex in range(target.target.num_vertices):
        nonprojective = target.target.simple(vertex, field=field)
        complex_ = auslander.BoundedComplex(0, [nonprojective], [])
        try:
            certificate.transport.target_complex(complex_)
        except auslander.TransportInputError as caught:
            assert caught.term == 0
            break
    else:
        pytest.fail("the nonsemisimple target has a nonprojective simple")

    edge = auslander.Algebra.linear_an(1).simple(0, field=field)
    maximal = auslander.BoundedComplex(2**31 - 1, [edge], [])
    with pytest.raises(OverflowError, match="cannot be shifted"):
        auslander.HomotopyHom(maximal, maximal, 1)


def test_ext_successor_degree_overflow_is_typed():
    field = auslander.PrimeField(5)
    algebra = auslander.Algebra.linear_an(1)
    simple = algebra.simple(0, field=field)
    largest_usize = 2 * sys.maxsize + 1
    with pytest.raises(OverflowError):
        simple.ext_dim(simple, largest_usize)
    with pytest.raises(OverflowError):
        simple.ext_table(simple, largest_usize)
    with pytest.raises(OverflowError):
        simple.ext_space(simple, largest_usize)


def test_derived_wrappers_retain_checked_data_without_python_inputs():
    field = auslander.PrimeField(5)

    def build():
        tilting, target, certificate = pd2_derived(field)
        source = add_t_complex(
            tilting, auslander.BoundedComplex(0, [tilting.module], [])
        )
        return certificate, certificate.transport, source, target

    certificate, transport, source, target = build()
    del target
    gc.collect()

    image = transport.forward(source)
    assert certificate.verify()
    assert transport.verify()
    assert image.verify()
    assert transport.source_round_trip(source).verify()

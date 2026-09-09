use auslander::derived::{
    AddTComplex, DerivedEquivalenceCertificate, ProjectiveTargetComplex, StrictTransport,
};
use auslander::field::PrimeField;
use auslander::homotopy::{ChainMap, HomotopyHom, HomotopyHomQuotient};
use auslander::linalg::DenseMat;

use super::fixtures::{shifted_source, two_term_source, witnessed_source, zero_chain_map};

pub(super) struct TwoTermHomotopyData {
    degrees: Vec<i32>,
    source: AddTComplex,
    target: ProjectiveTargetComplex,
    source_shifts: Vec<AddTComplex>,
    target_shifts: Vec<ProjectiveTargetComplex>,
    source_homs: Vec<HomotopyHom>,
    target_homs: Vec<HomotopyHom>,
    source_quotients: Vec<HomotopyHomQuotient>,
    target_quotients: Vec<HomotopyHomQuotient>,
    source_basis: Vec<Vec<ChainMap>>,
    target_basis: Vec<Vec<ChainMap>>,
}

pub(super) fn two_term_homotopy_data(
    certificate: &DerivedEquivalenceCertificate,
    transport: &StrictTransport,
) -> TwoTermHomotopyData {
    let source = two_term_source(certificate);
    let target = transport.forward(&source).unwrap();
    let degrees = vec![-2, -1, 0, 1, 2];
    let source_shifts: Vec<AddTComplex> = degrees
        .iter()
        .map(|&degree| shifted_source(&source, degree))
        .collect();
    let target_shifts: Vec<_> = source_shifts
        .iter()
        .map(|shifted| transport.forward(shifted).unwrap())
        .collect();
    let source_homs: Vec<HomotopyHom> = degrees
        .iter()
        .map(|&degree| HomotopyHom::new(source.complex(), source.complex(), degree).unwrap())
        .collect();
    let target_homs: Vec<HomotopyHom> = degrees
        .iter()
        .map(|&degree| HomotopyHom::new(target.complex(), target.complex(), degree).unwrap())
        .collect();
    let source_quotients: Vec<_> = source_homs
        .iter()
        .map(|hom| hom.quotient().unwrap())
        .collect();
    let target_quotients: Vec<_> = target_homs
        .iter()
        .map(|hom| hom.quotient().unwrap())
        .collect();
    let source_basis: Vec<Vec<ChainMap>> = source_homs
        .iter()
        .map(|hom| hom.basis_iter().collect())
        .collect();
    let target_basis: Vec<Vec<ChainMap>> = source_homs
        .iter()
        .zip(&source_shifts)
        .map(|(hom, shifted)| {
            hom.basis_iter()
                .map(|map| transport.forward_chain_map(&source, shifted, &map).unwrap())
                .collect()
        })
        .collect();
    TwoTermHomotopyData {
        degrees,
        source,
        target,
        source_shifts,
        target_shifts,
        source_homs,
        target_homs,
        source_quotients,
        target_quotients,
        source_basis,
        target_basis,
    }
}

fn assert_two_term_dimensions(data: &TwoTermHomotopyData) {
    let source_dims: Vec<usize> = data
        .source_quotients
        .iter()
        .map(|quotient| quotient.dim())
        .collect();
    let target_dims: Vec<usize> = data
        .target_quotients
        .iter()
        .map(|quotient| quotient.dim())
        .collect();
    // The two terms are T in degrees 0 and 1. A degree q map has components
    // C_i -> C_(i + q), so |q| > 1 has no nonzero component. Row reduction for
    // the selected square-zero radical differential gives chain-map kernels
    // [0, 3, 9, 5, 0] and homotopy-boundary ranks [0, 0, 2, 1, 0]. Subtracting
    // those ranks pins the quotient dimensions [0, 3, 7, 4, 0].
    let expected_dims = vec![0, 3, 7, 4, 0];
    assert_eq!(source_dims, expected_dims);
    assert_eq!(target_dims, expected_dims);
}

fn assert_two_term_cycle_rank(data: &TwoTermHomotopyData, field: &PrimeField, index: usize) {
    let target_hom = &data.target_homs[index];
    let cycle_image_rows: Vec<Vec<_>> = data.target_basis[index]
        .iter()
        .map(|map| target_hom.coords(map).unwrap())
        .collect();
    let cycle_images = if cycle_image_rows.is_empty() {
        DenseMat::zero(0, target_hom.dim())
    } else {
        DenseMat::from_rows(&cycle_image_rows)
    };
    assert_eq!(
        cycle_images.rank(field),
        data.source_homs[index].dim(),
        "transported cycle basis loses rank in degree {}",
        data.degrees[index]
    );
}

fn assert_two_term_quotient_rank(
    data: &TwoTermHomotopyData,
    transport: &StrictTransport,
    field: &PrimeField,
    index: usize,
) {
    let source_quotient = &data.source_quotients[index];
    let target_quotient = &data.target_quotients[index];
    let mut quotient_image_rows = Vec::new();
    for basis_index in 0..source_quotient.dim() {
        let mut coordinates = vec![field.zero(); source_quotient.dim()];
        coordinates[basis_index] = field.one();
        let representative = source_quotient.representative(&coordinates);
        let image = transport
            .forward_chain_map(&data.source, &data.source_shifts[index], &representative)
            .unwrap();
        quotient_image_rows.push(target_quotient.reduce(&image).unwrap().0);
    }
    let quotient_images = if quotient_image_rows.is_empty() {
        DenseMat::zero(0, target_quotient.dim())
    } else {
        DenseMat::from_rows(&quotient_image_rows)
    };
    assert_eq!(
        quotient_images.rank(field),
        source_quotient.dim(),
        "transported quotient basis loses rank in degree {}",
        data.degrees[index]
    );
}

fn assert_two_term_basis_classes(data: &TwoTermHomotopyData, index: usize) {
    for (source_map, target_map) in data.source_basis[index]
        .iter()
        .zip(&data.target_basis[index])
    {
        assert_eq!(
            source_map.is_null_homotopic().unwrap(),
            target_map.is_null_homotopic().unwrap(),
            "transport changes a basis map's zero class in degree {}",
            data.degrees[index]
        );
    }
}

fn assert_two_term_zero_transport(
    data: &TwoTermHomotopyData,
    transport: &StrictTransport,
    index: usize,
) {
    let source_zero =
        ChainMap::zero(data.source.complex(), data.source_shifts[index].complex()).unwrap();
    let target_zero =
        ChainMap::zero(data.target.complex(), data.target_shifts[index].complex()).unwrap();
    let transported_zero = transport
        .forward_chain_map(&data.source, &data.source_shifts[index], &source_zero)
        .unwrap();
    assert!(zero_chain_map(&source_zero));
    assert!(zero_chain_map(&transported_zero));
    assert!(transported_zero.agrees_with(&target_zero));
    assert!(source_zero.is_null_homotopic().unwrap());
    assert!(transported_zero.is_null_homotopic().unwrap());
    assert!(target_zero.is_null_homotopic().unwrap());
}

fn assert_two_term_degree(
    data: &TwoTermHomotopyData,
    transport: &StrictTransport,
    field: &PrimeField,
    index: usize,
) {
    let source_hom = &data.source_homs[index];
    let target_hom = &data.target_homs[index];
    let source_quotient = &data.source_quotients[index];
    let target_quotient = &data.target_quotients[index];
    assert_eq!(
        source_hom.dim(),
        target_hom.dim(),
        "chain Hom degree {}",
        data.degrees[index]
    );
    assert_eq!(
        source_quotient.dim(),
        target_quotient.dim(),
        "homotopy Hom degree {}",
        data.degrees[index]
    );
    assert_two_term_cycle_rank(data, field, index);
    assert_two_term_quotient_rank(data, transport, field, index);
    assert_two_term_basis_classes(data, index);
    assert_two_term_zero_transport(data, transport, index);
}

fn assert_two_term_degrees(
    data: &TwoTermHomotopyData,
    transport: &StrictTransport,
    field: &PrimeField,
) {
    assert_two_term_dimensions(data);
    for index in 0..data.degrees.len() {
        assert_two_term_degree(data, transport, field, index);
    }
}

fn assert_two_term_units(data: &TwoTermHomotopyData, transport: &StrictTransport) {
    let index = data
        .degrees
        .iter()
        .position(|&degree| degree == 0)
        .expect("the degree list contains zero");
    let source_identity = ChainMap::identity(data.source.complex());
    let target_identity = ChainMap::identity(data.target.complex());
    let transported_identity = transport
        .forward_chain_map(&data.source, &data.source_shifts[index], &source_identity)
        .unwrap();
    assert!(transported_identity.agrees_with(&target_identity));
    let source_unit = data.source_quotients[index]
        .reduce(&source_identity)
        .unwrap()
        .0;
    let target_unit = data.target_quotients[index]
        .reduce(&transported_identity)
        .unwrap()
        .0;
    assert!(source_unit.iter().any(|value| !value.is_zero()));
    assert!(target_unit.iter().any(|value| !value.is_zero()));
    let source_shift_identity = ChainMap::identity(data.source_shifts[index].complex());
    let target_shift_identity = ChainMap::identity(data.target_shifts[index].complex());
    for (source_map, target_map) in data.source_basis[index]
        .iter()
        .zip(&data.target_basis[index])
    {
        assert!(
            source_identity
                .then(source_map)
                .unwrap()
                .agrees_with(source_map)
        );
        assert!(
            source_map
                .then(&source_shift_identity)
                .unwrap()
                .agrees_with(source_map)
        );
        assert!(
            target_identity
                .then(target_map)
                .unwrap()
                .agrees_with(target_map)
        );
        assert!(
            target_map
                .then(&target_shift_identity)
                .unwrap()
                .agrees_with(target_map)
        );
    }
}

fn compare_two_term_product(
    data: &TwoTermHomotopyData,
    transport: &StrictTransport,
    left_index: usize,
    left_map_index: usize,
    right_map: &ChainMap,
    right_target_map: &ChainMap,
    right_degree: i32,
) {
    let left_map = &data.source_basis[left_index][left_map_index];
    let left_target_map = &data.target_basis[left_index][left_map_index];
    let source_product = left_map.then(right_map).unwrap();
    let add_target = data.source.witnesses()[0].target();
    let product_source = witnessed_source(source_product.source().clone(), add_target);
    let product_target = witnessed_source(source_product.target().clone(), add_target);
    let transported_product = transport
        .forward_chain_map(&product_source, &product_target, &source_product)
        .unwrap();
    let target_product = left_target_map.then(right_target_map).unwrap();
    assert!(transported_product.agrees_with(&target_product));
    assert_eq!(
        source_product.is_null_homotopic().unwrap(),
        target_product.is_null_homotopic().unwrap(),
        "product zero class disagrees for degrees {} and {}",
        data.degrees[left_index],
        right_degree
    );
}

fn compare_two_term_product_pairs(
    data: &TwoTermHomotopyData,
    transport: &StrictTransport,
    left_index: usize,
    right_basis: &[ChainMap],
    right_target_basis: &[ChainMap],
    right_degree: i32,
) -> usize {
    let mut products = 0;
    for (left_map_index, _) in data.source_basis[left_index].iter().enumerate() {
        for (right_map, right_target_map) in right_basis.iter().zip(right_target_basis) {
            products += 1;
            compare_two_term_product(
                data,
                transport,
                left_index,
                left_map_index,
                right_map,
                right_target_map,
                right_degree,
            );
        }
    }
    products
}

fn compare_two_term_product_degree(
    data: &TwoTermHomotopyData,
    transport: &StrictTransport,
    left_index: usize,
    product_index: usize,
    right_degree: i32,
) -> usize {
    let right_hom = HomotopyHom::new(
        data.source_shifts[left_index].complex(),
        data.source_shifts[left_index].complex(),
        right_degree,
    )
    .unwrap();
    let right_target_hom = HomotopyHom::new(
        data.target_shifts[left_index].complex(),
        data.target_shifts[left_index].complex(),
        right_degree,
    )
    .unwrap();
    let right_basis: Vec<ChainMap> = right_hom.basis_iter().collect();
    let right_target_basis: Vec<ChainMap> = right_basis
        .iter()
        .map(|map| {
            transport
                .forward_chain_map(
                    &data.source_shifts[left_index],
                    &data.source_shifts[product_index],
                    map,
                )
                .unwrap()
        })
        .collect();
    assert_eq!(right_basis.len(), right_target_hom.dim());
    compare_two_term_product_pairs(
        data,
        transport,
        left_index,
        &right_basis,
        &right_target_basis,
        right_degree,
    )
}

fn compare_two_term_products_for_left_degree(
    data: &TwoTermHomotopyData,
    transport: &StrictTransport,
    left_index: usize,
) -> usize {
    let left_degree = data.degrees[left_index];
    let mut products = 0;
    for &right_degree in &data.degrees {
        let product_degree = left_degree + right_degree;
        let Some(product_index) = data
            .degrees
            .iter()
            .position(|&degree| degree == product_degree)
        else {
            continue;
        };
        products += compare_two_term_product_degree(
            data,
            transport,
            left_index,
            product_index,
            right_degree,
        );
    }
    products
}

fn assert_two_term_products(data: &TwoTermHomotopyData, transport: &StrictTransport) {
    let mut products = 0;
    for left_index in 0..data.degrees.len() {
        products += compare_two_term_products_for_left_degree(data, transport, left_index);
    }
    assert!(
        products > 0,
        "the two-term fixture must have composable basis products"
    );
}

pub(super) fn compare_two_term_homotopy(certificate: &DerivedEquivalenceCertificate) {
    let transport = certificate.transport();
    let data = two_term_homotopy_data(certificate, transport);
    assert!(data.source.verify());
    assert!(data.target.verify());
    assert!(transport.source_round_trip(&data.source).unwrap().verify());
    assert!(transport.target_round_trip(&data.target).unwrap().verify());
    let field = certificate.target().target().field();
    assert_two_term_degrees(&data, transport, &field);
    assert_two_term_units(&data, transport);
    assert_two_term_products(&data, transport);
}

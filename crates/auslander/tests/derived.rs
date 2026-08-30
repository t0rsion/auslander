//! Public acceptance and fresh-process gates for strict derived transport.

use std::env;
use std::fmt::Write as _;
use std::time::Duration;

use auslander::algebra::an_with_relations;
use auslander::basic::{AddClosureWitness, BasicDecomposition};
use auslander::derived::{AddTComplex, DerivedEquivalenceCertificate};
use auslander::endo::EndoAlgebra;
use auslander::field::PrimeField;
use auslander::hom::Morphism;
use auslander::homotopy::{BoundedComplex, ChainMap, HomotopyHom};
use auslander::linalg::DenseMat;
use auslander::module::{Module, direct_sum};
use auslander::target::{TargetLimits, TargetPresentationOutcome, present_target};
use auslander::tilting::{ClassicalTiltingModule, ClassicalTiltingResult, TiltingLimits};

mod common;

const CHILD_ENV: &str = "AUSLANDER_DERIVED_DETERMINISM_CHILD";
const MARKER: &str = "derived-fingerprint:";
const CHILD_TIMEOUT: Duration = Duration::from_secs(60);

fn pd2_tilting(field: PrimeField) -> ClassicalTiltingModule {
    let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
    let injectives: Vec<Module> = (0..3)
        .map(|vertex| Module::injective(&algebra, vertex))
        .collect();
    let module = direct_sum(&injectives.iter().collect::<Vec<_>>()).0;
    let limits = TiltingLimits {
        max_projective_dimension: 4,
        max_generation_steps: 8,
    };
    let ClassicalTiltingResult::Tilting(tilting) =
        ClassicalTiltingModule::classify(&module, limits).unwrap()
    else {
        panic!("the dual A3/(ab) fixture is classical tilting")
    };
    assert_eq!(tilting.projective_dimension(), 2);
    tilting
}

fn certificate(field: PrimeField) -> DerivedEquivalenceCertificate {
    let tilting = pd2_tilting(field);
    let TargetPresentationOutcome::Presented(target) =
        present_target(&tilting, &TargetLimits::default()).unwrap()
    else {
        panic!("the dual A3/(ab) target is split")
    };
    DerivedEquivalenceCertificate::new(tilting, target).unwrap()
}

fn one_term_source(certificate: &DerivedEquivalenceCertificate) -> AddTComplex {
    let module = certificate.tilting().module();
    let basic = BasicDecomposition::new(module).unwrap();
    let witness = AddClosureWitness::from_module(module, &basic)
        .unwrap()
        .expect("T belongs to add(T)");
    AddTComplex::new(
        BoundedComplex::new(0, vec![module.clone()], Vec::new()).unwrap(),
        vec![witness],
    )
    .unwrap()
}

fn two_term_source(certificate: &DerivedEquivalenceCertificate) -> AddTComplex {
    let module = certificate.tilting().module();
    let endo = EndoAlgebra::new(module);
    let differential = endo
        .basis()
        .iter()
        .find(|map| {
            !map.is_zero()
                && !map.is_isomorphism()
                && map.then(map).is_ok_and(|square| square.is_zero())
        })
        .expect("the pd2 fixture has a nonzero square-zero radical endomorphism")
        .clone();
    let complex = BoundedComplex::new(0, vec![module.clone(), module.clone()], vec![differential])
        .expect("the selected radical endomorphism forms a two-term complex");
    let basic = BasicDecomposition::new(module).expect("the tilting module is basic");
    let witness = AddClosureWitness::from_module(module, &basic)
        .expect("membership decomposes")
        .expect("T belongs to add(T)");
    AddTComplex::new(complex, vec![witness.clone(), witness])
        .expect("the two-term complex has add(T) witnesses")
}

fn shifted_source(source: &AddTComplex, degree: i32) -> AddTComplex {
    AddTComplex::new(
        source
            .complex()
            .shift(degree)
            .expect("the fixture shift fits in homological degrees"),
        source.witnesses().to_vec(),
    )
    .expect("shifting preserves add(T) witnesses")
}

fn zero_chain_map(map: &ChainMap) -> bool {
    map.components().iter().all(Morphism::is_zero)
}

fn witnessed_source(complex: BoundedComplex, target: &Module) -> AddTComplex {
    let basic = BasicDecomposition::new(target).expect("the source witness target is basic");
    let witnesses = complex
        .terms()
        .iter()
        .map(|term| {
            AddClosureWitness::from_module(term, &basic)
                .expect("the padded term decomposes")
                .expect("every padded term lies in add(T)")
        })
        .collect();
    AddTComplex::new(complex, witnesses).expect("padded source witnesses match terms")
}

fn compare_two_term_homotopy(certificate: &DerivedEquivalenceCertificate) {
    let transport = certificate.transport();
    let source = two_term_source(certificate);
    let target = transport.forward(&source).unwrap();
    assert!(source.verify());
    assert!(target.verify());
    assert!(transport.source_round_trip(&source).unwrap().verify());
    assert!(transport.target_round_trip(&target).unwrap().verify());

    let degrees = [-2, -1, 0, 1, 2];
    let source_shifts: Vec<AddTComplex> = degrees
        .iter()
        .map(|&degree| shifted_source(&source, degree))
        .collect();
    let target_shifts: Vec<_> = source_shifts
        .iter()
        .map(|shifted| transport.forward(shifted).unwrap())
        .collect();
    let source_homs: Vec<_> = degrees
        .iter()
        .map(|&degree| HomotopyHom::new(source.complex(), source.complex(), degree).unwrap())
        .collect();
    let target_homs: Vec<_> = degrees
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
    let source_dims: Vec<usize> = source_quotients
        .iter()
        .map(|quotient| quotient.dim())
        .collect();
    let target_dims: Vec<usize> = target_quotients
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
    let field = certificate.target().target().field();

    for index in 0..degrees.len() {
        let source_hom = &source_homs[index];
        let target_hom = &target_homs[index];
        let source_quotient = &source_quotients[index];
        let target_quotient = &target_quotients[index];
        assert_eq!(
            source_hom.dim(),
            target_hom.dim(),
            "chain Hom degree {}",
            degrees[index]
        );
        assert_eq!(
            source_quotient.dim(),
            target_quotient.dim(),
            "homotopy Hom degree {}",
            degrees[index]
        );

        let cycle_image_rows: Vec<Vec<_>> = target_basis[index]
            .iter()
            .map(|map| target_hom.coords(map).unwrap())
            .collect();
        let cycle_images = if cycle_image_rows.is_empty() {
            DenseMat::zero(0, target_hom.dim())
        } else {
            DenseMat::from_rows(&cycle_image_rows)
        };
        assert_eq!(
            cycle_images.rank(&field),
            source_hom.dim(),
            "transported cycle basis loses rank in degree {}",
            degrees[index]
        );

        let mut quotient_image_rows = Vec::new();
        for basis_index in 0..source_quotient.dim() {
            let mut coordinates = vec![field.zero(); source_quotient.dim()];
            coordinates[basis_index] = field.one();
            let representative = source_quotient.representative(&coordinates);
            let image = transport
                .forward_chain_map(&source, &source_shifts[index], &representative)
                .unwrap();
            quotient_image_rows.push(target_quotient.reduce(&image).unwrap().0);
        }
        let quotient_images = if quotient_image_rows.is_empty() {
            DenseMat::zero(0, target_quotient.dim())
        } else {
            DenseMat::from_rows(&quotient_image_rows)
        };
        assert_eq!(
            quotient_images.rank(&field),
            source_quotient.dim(),
            "transported quotient basis loses rank in degree {}",
            degrees[index]
        );
        for (source_map, target_map) in source_basis[index].iter().zip(&target_basis[index]) {
            assert_eq!(
                source_map.is_null_homotopic().unwrap(),
                target_map.is_null_homotopic().unwrap(),
                "transport changes a basis map's zero class in degree {}",
                degrees[index]
            );
        }

        let source_zero = ChainMap::zero(source.complex(), source_shifts[index].complex()).unwrap();
        let target_zero = ChainMap::zero(target.complex(), target_shifts[index].complex()).unwrap();
        let transported_zero = transport
            .forward_chain_map(&source, &source_shifts[index], &source_zero)
            .unwrap();
        assert!(zero_chain_map(&source_zero));
        assert!(zero_chain_map(&transported_zero));
        assert!(transported_zero.agrees_with(&target_zero));
        assert!(source_zero.is_null_homotopic().unwrap());
        assert!(transported_zero.is_null_homotopic().unwrap());
        assert!(target_zero.is_null_homotopic().unwrap());

        if degrees[index] == 0 {
            let source_identity = ChainMap::identity(source.complex());
            let target_identity = ChainMap::identity(target.complex());
            let transported_identity = transport
                .forward_chain_map(&source, &source_shifts[index], &source_identity)
                .unwrap();
            assert!(transported_identity.agrees_with(&target_identity));
            let source_unit = source_quotient.reduce(&source_identity).unwrap().0;
            let target_unit = target_quotient.reduce(&transported_identity).unwrap().0;
            assert!(source_unit.iter().any(|value| !value.is_zero()));
            assert!(target_unit.iter().any(|value| !value.is_zero()));
            let source_shift_identity = ChainMap::identity(source_shifts[index].complex());
            let target_shift_identity = ChainMap::identity(target_shifts[index].complex());
            for (source_map, target_map) in source_basis[index].iter().zip(&target_basis[index]) {
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
    }

    let mut products = 0usize;
    for (left_index, &left_degree) in degrees.iter().enumerate() {
        for &right_degree in &degrees {
            let product_degree = left_degree + right_degree;
            let Some(product_index) = degrees.iter().position(|&degree| degree == product_degree)
            else {
                continue;
            };
            let right_hom = HomotopyHom::new(
                source_shifts[left_index].complex(),
                source_shifts[left_index].complex(),
                right_degree,
            )
            .unwrap();
            let right_target_hom = HomotopyHom::new(
                target_shifts[left_index].complex(),
                target_shifts[left_index].complex(),
                right_degree,
            )
            .unwrap();
            let right_basis: Vec<ChainMap> = right_hom.basis_iter().collect();
            let right_target_basis: Vec<ChainMap> = right_basis
                .iter()
                .map(|map| {
                    transport
                        .forward_chain_map(
                            &source_shifts[left_index],
                            &source_shifts[product_index],
                            map,
                        )
                        .unwrap()
                })
                .collect();
            assert_eq!(right_basis.len(), right_target_hom.dim());
            for (left_map, left_target_map) in source_basis[left_index]
                .iter()
                .zip(&target_basis[left_index])
            {
                for (right_map, right_target_map) in right_basis.iter().zip(&right_target_basis) {
                    products += 1;
                    let source_product = left_map.then(right_map).unwrap();
                    let add_target = source.witnesses()[0].target();
                    let product_source =
                        witnessed_source(source_product.source().clone(), add_target);
                    let product_target =
                        witnessed_source(source_product.target().clone(), add_target);
                    let transported_product = transport
                        .forward_chain_map(&product_source, &product_target, &source_product)
                        .unwrap();
                    let target_product = left_target_map.then(right_target_map).unwrap();
                    assert!(transported_product.agrees_with(&target_product));
                    assert_eq!(
                        source_product.is_null_homotopic().unwrap(),
                        target_product.is_null_homotopic().unwrap(),
                        "product zero class disagrees for degrees {left_degree} and {right_degree}"
                    );
                }
            }
        }
    }
    assert!(
        products > 0,
        "the two-term fixture must have composable basis products"
    );
}

fn matrix_text(matrix: &DenseMat) -> String {
    format!(
        "{}x{}:{:?}",
        matrix.rows(),
        matrix.cols(),
        matrix.entries_u64()
    )
}

fn morphism_text(morphism: &Morphism) -> String {
    let mut text = String::new();
    for vertex in 0..morphism.source().algebra().quiver().num_vertices() {
        if vertex != 0 {
            text.push('|');
        }
        text.push_str(&matrix_text(morphism.map_at(vertex)));
    }
    text
}

fn map_text(map: &ChainMap) -> String {
    let mut text = format!("{}..{}", map.range().lower(), map.range().upper());
    for component in map.components() {
        text.push(';');
        text.push_str(&morphism_text(component));
    }
    text
}

fn compare_one_term_hom(certificate: &DerivedEquivalenceCertificate, out: &mut String) {
    let transport = certificate.transport();
    let source = one_term_source(certificate);
    let target = transport.forward(&source).unwrap();
    let reverse = transport.reverse(&target).unwrap();
    assert!(reverse.verify());
    let source_unit = transport.source_round_trip(&source).unwrap();
    assert!(source_unit.verify());
    assert!(transport.target_round_trip(&target).unwrap().verify());

    for degree in -1..=1 {
        let source_hom = HomotopyHom::new(source.complex(), source.complex(), degree).unwrap();
        let target_hom = HomotopyHom::new(target.complex(), target.complex(), degree).unwrap();
        let source_quotient = source_hom.quotient().unwrap();
        let target_quotient = target_hom.quotient().unwrap();
        assert_eq!(source_hom.dim(), target_hom.dim());
        assert_eq!(source_quotient.dim(), target_quotient.dim());
        write!(
            out,
            "q={degree}:hom={}:quotient={};",
            source_hom.dim(),
            source_quotient.dim()
        )
        .unwrap();

        let shifted = AddTComplex::new(
            source.complex().shift(degree).unwrap(),
            source.witnesses().to_vec(),
        )
        .unwrap();
        assert!(transport.forward(&shifted).unwrap().verify());
        assert!(transport.source_round_trip(&shifted).unwrap().verify());
        let mut rows = Vec::new();
        for basis in source_hom.basis_iter() {
            let image = transport
                .forward_chain_map(&source, &shifted, &basis)
                .unwrap();
            let coordinates = target_hom.coords(&image).unwrap();
            rows.push(coordinates);
            write!(out, "map={};", map_text(&image)).unwrap();
        }
        let coordinates = if rows.is_empty() {
            DenseMat::zero(0, target_hom.dim())
        } else {
            DenseMat::from_rows(&rows)
        };
        assert_eq!(
            coordinates.rank(&certificate.target().target().field()),
            source_hom.dim()
        );
        write!(out, "coordinates={};", matrix_text(&coordinates)).unwrap();

        if degree == 0 {
            for left in source_hom.basis_iter() {
                let left_image = transport
                    .forward_chain_map(&source, &source, &left)
                    .unwrap();
                for right in source_hom.basis_iter() {
                    let right_image = transport
                        .forward_chain_map(&source, &source, &right)
                        .unwrap();
                    let source_product = left.then(&right).unwrap();
                    let transported_product = transport
                        .forward_chain_map(&source, &source, &source_product)
                        .unwrap();
                    assert!(
                        transported_product.agrees_with(&left_image.then(&right_image).unwrap())
                    );
                }
            }
            let identity = ChainMap::identity(source.complex());
            let transported_identity = transport
                .forward_chain_map(&source, &source, &identity)
                .unwrap();
            assert!(transported_identity.agrees_with(&ChainMap::identity(target.complex())));
        }
    }
}

fn determinism_payload() -> String {
    let mut out = String::new();
    for field in [common::f2(), common::f5()] {
        let modulus = field.modulus();
        let certificate = certificate(field);
        assert!(certificate.verify());
        write!(
            out,
            "field={modulus};target={:?};resolution={}..{};degree-zero={};",
            certificate.target().target().quiver().arrows(),
            certificate.resolution_complex().lower(),
            certificate.resolution_complex().upper(),
            matrix_text(certificate.degree_zero_identification().coordinates()),
        )
        .unwrap();
        for graded in certificate.graded_homotopy() {
            write!(
                out,
                "graded={}:{}:{}:{};",
                graded.degree(),
                graded.quotient().dim(),
                matrix_text(graded.quotient().null_homotopic_basis()),
                matrix_text(graded.quotient().complement_basis()),
            )
            .unwrap();
        }
        compare_one_term_hom(&certificate, &mut out);
    }
    out
}

#[test]
fn pd2_certificates_and_strict_transport_agree_over_f2_and_f5() {
    for field in [common::f2(), common::f5()] {
        let certificate = certificate(field);
        assert!(certificate.verify());
        assert_eq!(
            certificate
                .graded_homotopy()
                .iter()
                .map(|space| space.degree())
                .collect::<Vec<_>>(),
            vec![-2, -1, 0, 1, 2]
        );
        assert!(
            certificate
                .graded_homotopy()
                .iter()
                .filter(|space| space.degree() != 0)
                .all(|space| space.quotient().dim() == 0)
        );
        assert_eq!(
            certificate
                .graded_homotopy()
                .iter()
                .find(|space| space.degree() == 0)
                .unwrap()
                .quotient()
                .dim(),
            certificate.target().endo().dim()
        );
        compare_one_term_hom(&certificate, &mut String::new());
    }
}

#[test]
fn nontrivial_two_term_homotopy_transport_preserves_all_finite_support_data() {
    for field in [common::f2(), common::f5()] {
        compare_two_term_homotopy(&certificate(field));
    }
}

#[test]
fn derived_determinism_child_prints_fingerprint() {
    if env::var(CHILD_ENV).is_err() {
        return;
    }
    println!("{}", common::fingerprint(MARKER, &determinism_payload()));
}

fn child_fingerprint() -> String {
    let stdout = common::child_test_stdout(
        "derived_determinism_child_prints_fingerprint",
        CHILD_ENV,
        CHILD_TIMEOUT,
    );
    common::marked_line(&stdout, MARKER)
}

#[test]
fn derived_data_is_deterministic_across_fresh_processes() {
    let payload = determinism_payload();
    assert_eq!(payload, determinism_payload());
    let first = child_fingerprint();
    let second = child_fingerprint();
    assert_eq!(first, second, "fresh processes disagree on derived data");
    assert_eq!(
        first,
        common::fingerprint(MARKER, &payload),
        "child processes disagree with this process"
    );
}

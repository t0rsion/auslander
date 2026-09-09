use std::fmt::Write as _;

use auslander::derived::{AddTComplex, DerivedEquivalenceCertificate};
use auslander::hom::Morphism;
use auslander::homotopy::{ChainMap, HomotopyHom};
use auslander::linalg::DenseMat;

use super::common;
use super::fixtures::{certificate, one_term_source};

pub(super) fn matrix_text(matrix: &DenseMat) -> String {
    format!(
        "{}x{}:{:?}",
        matrix.rows(),
        matrix.cols(),
        matrix.entries_u64()
    )
}

pub(super) fn morphism_text(morphism: &Morphism) -> String {
    let mut text = String::new();
    for vertex in 0..morphism.source().algebra().quiver().num_vertices() {
        if vertex != 0 {
            text.push('|');
        }
        text.push_str(&matrix_text(morphism.map_at(vertex)));
    }
    text
}

pub(super) fn map_text(map: &ChainMap) -> String {
    let mut text = format!("{}..{}", map.range().lower(), map.range().upper());
    for component in map.components() {
        text.push(';');
        text.push_str(&morphism_text(component));
    }
    text
}

pub(super) fn compare_one_term_hom(certificate: &DerivedEquivalenceCertificate, out: &mut String) {
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

pub(super) fn determinism_payload() -> String {
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

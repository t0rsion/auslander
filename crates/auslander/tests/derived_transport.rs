//! Acceptance tests for automatic classical tilting transport.

mod common;

use auslander::algebra::an_with_relations;
use auslander::basic::{AddClosureWitness, BasicDecomposition};
use auslander::derived::{AddTComplex, DerivedEquivalenceCertificate};
use auslander::derived_transport::{
    DerivedForwardOutcome, DerivedReverseOutcome, DerivedTransport,
};
use auslander::field::PrimeField;
use auslander::hom::zero_morphism;
use auslander::homotopy::BoundedComplex;
use auslander::module::{Module, direct_sum};
use auslander::perfect::ReplacementLimits;
use auslander::target::{TargetLimits, TargetPresentationOutcome, present_target};
use auslander::tilting::{ClassicalTiltingModule, ClassicalTiltingResult, TiltingLimits};

fn certificate(field: PrimeField) -> DerivedEquivalenceCertificate {
    let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
    let injectives: Vec<Module> = (0..3)
        .map(|vertex| Module::injective(&algebra, vertex))
        .collect();
    let module = direct_sum(&injectives.iter().collect::<Vec<_>>()).0;
    let ClassicalTiltingResult::Tilting(tilting) = ClassicalTiltingModule::classify(
        &module,
        TiltingLimits {
            max_projective_dimension: 4,
            max_generation_steps: 8,
        },
    )
    .unwrap() else {
        panic!("the fixed dual module is tilting")
    };
    let TargetPresentationOutcome::Presented(target) =
        present_target(&tilting, &TargetLimits::default()).unwrap()
    else {
        panic!("the fixed tilting target is split")
    };
    DerivedEquivalenceCertificate::new(tilting, target).unwrap()
}

fn homology_at(complex: &BoundedComplex, degree: i32) -> Vec<usize> {
    let display = complex.to_checked().unwrap();
    display
        .homology_dimensions((complex.upper() - degree) as usize)
        .unwrap()
        .dimension_vector()
        .to_vec()
}

#[test]
fn automatic_forward_transport_extends_the_strict_path_over_f2_and_f5() {
    for field in [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()] {
        let certificate = certificate(field);
        let transport = DerivedTransport::new(certificate.clone()).unwrap();
        let tilting = certificate.tilting().module();
        let basic = BasicDecomposition::new(tilting).unwrap();
        let witness = AddClosureWitness::from_module(tilting, &basic)
            .unwrap()
            .unwrap();
        let strict_source = AddTComplex::new(common::one_term(tilting), vec![witness]).unwrap();
        let strict_output = certificate.transport().forward(&strict_source).unwrap();
        let DerivedForwardOutcome::Transported(forward) = transport
            .forward(strict_source.complex(), ReplacementLimits::default(), None)
            .unwrap()
        else {
            panic!("the strict source has a complete forward model")
        };
        assert!(forward.verify());
        for degree in forward.output().complex().lower()..=forward.output().complex().upper() {
            let homology = homology_at(forward.output().complex(), degree);
            if degree == 0 {
                assert_eq!(homology, strict_output.complex().terms()[0].dim_vector());
            } else {
                assert!(homology.iter().all(|&dimension| dimension == 0));
            }
        }
    }
}

#[test]
fn ordinary_source_complexes_enter_forward_transport() {
    let certificate = certificate(PrimeField::new(5).unwrap());
    let transport = DerivedTransport::new(certificate.clone()).unwrap();
    let simple = Module::simple(certificate.tilting().module().algebra(), 0);
    let DerivedForwardOutcome::Transported(forward) = transport
        .forward(
            &common::one_term(&simple),
            ReplacementLimits::default(),
            None,
        )
        .unwrap()
    else {
        panic!("the ordinary source has a complete forward model")
    };
    assert!(forward.verify());
    assert!(forward.output().verify());

    let DerivedReverseOutcome::Transported(reverse) = transport
        .reverse(
            forward.output().complex(),
            ReplacementLimits::default(),
            None,
        )
        .unwrap()
    else {
        panic!("the forward projective target reverses without a cut")
    };
    assert!(reverse.verify());
    let original = common::one_term(&simple);
    let round_trip = reverse.output().complex();
    let lower = original.lower().min(round_trip.lower());
    let upper = original.upper().max(round_trip.upper());
    for degree in lower..=upper {
        let expected = if original.range().contains(degree) {
            homology_at(&original, degree)
        } else {
            vec![0; simple.algebra().quiver().num_vertices() as usize]
        };
        let actual = if round_trip.range().contains(degree) {
            homology_at(round_trip, degree)
        } else {
            vec![0; simple.algebra().quiver().num_vertices() as usize]
        };
        assert_eq!(actual, expected);
    }
}

#[test]
fn two_term_ordinary_sources_use_cone_models() {
    let certificate = certificate(PrimeField::new(5).unwrap());
    let transport = DerivedTransport::new(certificate.clone()).unwrap();
    let algebra = certificate.tilting().module().algebra();
    let lower = Module::simple(algebra, 0);
    let upper = Module::simple(algebra, 1);
    let differential = zero_morphism(&upper, &lower).unwrap();
    let input = BoundedComplex::new(-1, vec![lower, upper], vec![differential]).unwrap();
    let DerivedForwardOutcome::Transported(forward) = transport
        .forward(&input, ReplacementLimits::default(), None)
        .unwrap()
    else {
        panic!("the fixed two-term source has a complete model")
    };
    assert!(forward.verify());
    assert!(forward.source_model().model().complex().len() > 1);
    assert!(forward.output().verify());
}

#[test]
fn ordinary_target_complexes_use_checked_inverse_replacement() {
    let certificate = certificate(PrimeField::new(5).unwrap());
    let transport = DerivedTransport::new(certificate.clone()).unwrap();
    let tilting = certificate.tilting().module();
    let basic = BasicDecomposition::new(tilting).unwrap();
    let witness = AddClosureWitness::from_module(tilting, &basic)
        .unwrap()
        .unwrap();
    let source = AddTComplex::new(common::one_term(tilting), vec![witness]).unwrap();
    let strict_target = certificate.transport().forward(&source).unwrap();
    let DerivedReverseOutcome::Transported(reverse) = transport
        .derived_tensor(strict_target.complex(), ReplacementLimits::default(), None)
        .unwrap()
    else {
        panic!("a projective target needs no nontrivial replacement")
    };
    assert!(reverse.verify());
    assert!(
        reverse
            .replacement()
            .projective()
            .complex()
            .agrees_with(strict_target.complex())
    );
    assert!(
        reverse.output().complex().terms()[0]
            .dim_vector()
            .iter()
            .zip(tilting.dim_vector())
            .all(|(left, right)| left == right)
    );
}

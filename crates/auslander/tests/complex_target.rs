//! Acceptance tests for targets of multi-degree tilting complexes.

mod common;

use auslander::algebra::linear_an;
use auslander::complex_target::{
    ComplexTargetOutcome, HomotopyEndomorphismAlgebra, present_complex_target,
};
use auslander::field::PrimeField;
use auslander::target::{TargetCutReason, TargetLimits};

#[test]
fn regular_and_multi_degree_a2_targets_verify_over_f2_and_f5() {
    for field in [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()] {
        let algebra = linear_an(2, field);
        for tilting in [
            common::certified_regular(&algebra),
            common::genuine_left_mutation(&common::certified_regular(&algebra)),
        ] {
            let endo = HomotopyEndomorphismAlgebra::new(&tilting).unwrap();
            assert!(endo.verify());
            assert_eq!(endo.dim(), 3);
            assert_eq!(endo.radical_basis().rows(), 1);
            let outcome = present_complex_target(&tilting, &TargetLimits::default()).unwrap();
            let ComplexTargetOutcome::Presented(target) = outcome else {
                panic!("the A2 target was cut")
            };
            assert!(target.verify());
            assert_eq!(target.target().dim(), 3);
            assert_eq!(target.target().quiver().num_vertices(), 2);
            assert_eq!(target.target().quiver().num_arrows(), 1);
            assert_eq!(target.work().endo_dimension, 3);
            assert_eq!(target.work().radical_products, 9);
            assert_eq!(target.work().paths, 0);
            assert_eq!(target.work().relation_terms, 0);
        }
    }
}

#[test]
fn complex_target_keeps_its_endomorphism_dimension_cut() {
    let algebra = linear_an(2, PrimeField::new(5).unwrap());
    let tilting = common::genuine_left_mutation(&common::certified_regular(&algebra));
    let limits = TargetLimits {
        max_endo_dimension: 2,
        ..TargetLimits::default()
    };
    let outcome = present_complex_target(&tilting, &limits).unwrap();
    let ComplexTargetOutcome::Cut(cut) = outcome else {
        panic!("the target should exceed the dimension limit")
    };
    assert!(cut.verify());
    assert!(matches!(cut.reason(), TargetCutReason::Budget(_)));
}

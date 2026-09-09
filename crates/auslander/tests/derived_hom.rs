//! Acceptance tests for automatic derived Hom.

mod common;

use auslander::algebra::{an_with_relations, dual_numbers};
use auslander::control::ComputationControl;
use auslander::derived_hom::{
    DerivedHomCutReason, DerivedHomLimits, DerivedHomOutcome, derived_hom,
};
use auslander::ext::ExtSpace;
use auslander::field::PrimeField;
use auslander::module::Module;
use auslander::perfect::ReplacementLimits;

#[test]
fn module_derived_hom_matches_ext_over_f2_and_f5() {
    for field in [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()] {
        let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
        let source = Module::simple(&algebra, 0);
        let target = Module::simple(&algebra, 2);
        let DerivedHomOutcome::Complete(value) = derived_hom(
            &common::one_term(&source),
            &common::one_term(&target),
            DerivedHomLimits::default(),
            None,
        )
        .unwrap() else {
            panic!("the pd2 source has complete derived Hom")
        };
        assert!(value.verify());
        assert_eq!(value.work().completed_degrees(), 3);
        assert_eq!(value.work().chain_map_dimensions(), 1);
        assert_eq!(value.work().quotient_dimensions(), 1);
        assert_eq!(value.work().work_units(), 5);
        assert_eq!(value.support().lower(), 0);
        assert_eq!(value.support().upper(), 2);
        for degree in 0..=2 {
            assert_eq!(
                value.dimension(degree),
                ExtSpace::new(&source, &target, degree as usize)
                    .unwrap()
                    .dim()
            );
        }
        assert_eq!(value.dimension(-1), 0);
        assert_eq!(value.dimension(3), 0);
        for space in value.spaces() {
            for index in 0..space.dim() {
                let field = source.field();
                let mut coordinates = vec![field.zero(); space.dim()];
                coordinates[index] = field.one();
                assert!(value.class(space.degree(), &coordinates).unwrap().verify());
            }
        }
    }
}

#[test]
fn a_degree_limit_keeps_only_complete_spaces() {
    let algebra = an_with_relations(3, &[(0, 2)], PrimeField::new(5).unwrap()).unwrap();
    let source = Module::simple(&algebra, 0);
    let target = Module::simple(&algebra, 2);
    let limits = DerivedHomLimits {
        max_degrees: 1,
        ..DerivedHomLimits::default()
    };
    let DerivedHomOutcome::WorkCut(cut) = derived_hom(
        &common::one_term(&source),
        &common::one_term(&target),
        limits,
        None,
    )
    .unwrap() else {
        panic!("the second support degree exceeds the limit")
    };
    assert!(cut.verify());
    assert_eq!(cut.spaces().len(), 1);
    assert_eq!(cut.next_degree(), 1);
    assert!(matches!(
        cut.reason(),
        DerivedHomCutReason::DegreeLimit {
            requested: 2,
            limit: 1
        }
    ));
}

#[test]
fn replacement_cuts_remain_distinct_from_hom_cuts() {
    let algebra = dual_numbers(PrimeField::new(5).unwrap());
    let simple = Module::simple(&algebra, 0);
    let limits = DerivedHomLimits {
        replacement: ReplacementLimits {
            max_resolution_steps: 2,
            ..ReplacementLimits::default()
        },
        ..DerivedHomLimits::default()
    };
    let outcome = derived_hom(
        &common::one_term(&simple),
        &common::one_term(&simple),
        limits,
        None,
    )
    .unwrap();
    assert!(matches!(outcome, DerivedHomOutcome::ReplacementCut(_)));
}

#[test]
fn cancellation_after_replacement_is_typed() {
    let algebra = an_with_relations(3, &[(0, 2)], PrimeField::new(5).unwrap()).unwrap();
    let simple = Module::simple(&algebra, 0);
    let control = ComputationControl::new();
    control.cancel();
    let outcome = derived_hom(
        &common::one_term(&simple),
        &common::one_term(&simple),
        DerivedHomLimits::default(),
        Some(&control),
    )
    .unwrap();
    assert!(matches!(
        outcome,
        DerivedHomOutcome::ReplacementCancelled(_)
    ));
}

#[test]
fn composition_recovers_the_nonzero_degree_two_ext_product() {
    for field in [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()] {
        let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
        let s0 = Module::simple(&algebra, 0);
        let s1 = Module::simple(&algebra, 1);
        let s2 = Module::simple(&algebra, 2);
        let DerivedHomOutcome::Complete(first) = derived_hom(
            &common::one_term(&s0),
            &common::one_term(&s1),
            DerivedHomLimits::default(),
            None,
        )
        .unwrap() else {
            panic!("the first Ext factor completes")
        };
        let DerivedHomOutcome::Complete(second) = derived_hom(
            &common::one_term(&s1),
            &common::one_term(&s2),
            DerivedHomLimits::default(),
            None,
        )
        .unwrap() else {
            panic!("the second Ext factor completes")
        };
        assert_eq!(first.dimension(1), 1);
        assert_eq!(second.dimension(1), 1);
        let alpha = first.class(1, &[field.one()]).unwrap();
        let beta = second.class(1, &[field.one()]).unwrap();
        let product = alpha.then(&beta).unwrap();
        assert!(product.verify());
        assert_eq!(product.degree(), 2);
        assert_eq!(product.space().dim(), 1);
        assert_ne!(product.coordinates(), &[field.zero()]);
    }
}

//! Acceptance tests for tilting complexes and left mutation.

mod common;

use auslander::algebra::linear_an;
use auslander::field::PrimeField;
use auslander::tilting_complex::{
    TiltingComplexBlocker, TiltingComplexLimits, TiltingComplexResult, TiltingMutationOutcome,
    left_tilting_mutation, regular_tilting_complex, right_tilting_mutation,
};

#[test]
fn regular_classification_reports_its_exact_hom_limit() {
    let algebra = linear_an(2, PrimeField::new(5).unwrap());
    let outcome =
        regular_tilting_complex(&algebra, TiltingComplexLimits { max_hom_spaces: 3 }).unwrap();
    assert!(matches!(
        outcome,
        TiltingComplexResult::Undetermined(TiltingComplexBlocker::HomLimit {
            completed: 2,
            limit: 3,
        })
    ));
}

#[test]
fn regular_projective_generators_certify_over_f2_and_f5() {
    for field in [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()] {
        let algebra = linear_an(3, field);
        let tilting = common::certified_regular(&algebra);
        assert!(tilting.verify());
        assert_eq!(tilting.candidate().len(), 3);
        assert!(
            tilting
                .zero_shifted_homs()
                .iter()
                .all(|check| check.quotient().dim() == 0 && check.verify())
        );
    }
}

#[test]
fn a2_left_mutation_produces_a_genuine_multi_degree_tilting_complex() {
    for field in [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()] {
        let algebra = linear_an(2, field);
        let regular = common::certified_regular(&algebra);
        let outcomes: Vec<_> = (0..2)
            .map(|summand| {
                left_tilting_mutation(&regular, summand, TiltingComplexLimits::default()).unwrap()
            })
            .collect();
        let mutation = outcomes
            .iter()
            .find_map(|outcome| match outcome {
                TiltingMutationOutcome::Tilting(value)
                    if value
                        .candidate()
                        .summands()
                        .iter()
                        .any(|summand| summand.complex().len() > 1) =>
                {
                    Some(value)
                }
                _ => None,
            })
            .expect("one A2 mutation has a genuine cone summand");
        assert!(mutation.verify());
        assert!(mutation.generation().verify(mutation.candidate()));
    }
}

#[test]
fn a2_right_mutation_produces_a_genuine_multi_degree_tilting_complex() {
    for field in [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()] {
        let algebra = linear_an(2, field);
        let regular = common::certified_regular(&algebra);
        let mutation = (0..2)
            .find_map(|summand| {
                match right_tilting_mutation(&regular, summand, TiltingComplexLimits::default())
                    .unwrap()
                {
                    TiltingMutationOutcome::Tilting(value)
                        if value
                            .candidate()
                            .summands()
                            .iter()
                            .any(|summand| summand.complex().len() > 1) =>
                    {
                        Some(value)
                    }
                    _ => None,
                }
            })
            .expect("one A2 right mutation has a genuine cone summand");
        assert!(mutation.verify());
        assert!(mutation.generation().verify(mutation.candidate()));
    }
}

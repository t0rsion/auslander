//! Acceptance tests for composable Rickard equivalence edges.

mod common;

use auslander::algebra::linear_an;
use auslander::equivalence_edge::{
    DerivedEquivalenceEdge, DerivedEquivalenceEdgeOutcome, DerivedEquivalencePath,
};
use auslander::field::PrimeField;
use auslander::target::TargetLimits;
use auslander::tilting_complex::CertifiedTiltingComplex;

fn edge(tilting: CertifiedTiltingComplex) -> DerivedEquivalenceEdge {
    match DerivedEquivalenceEdge::recover(tilting, &TargetLimits::default()).unwrap() {
        DerivedEquivalenceEdgeOutcome::Certified(value) => *value,
        DerivedEquivalenceEdgeOutcome::Cut(_) => panic!("the A2 edge was cut"),
    }
}

#[test]
fn regular_edge_composes_and_reverses_over_f2_and_f5() {
    for field in [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()] {
        let algebra = linear_an(2, field);
        let edge = edge(common::certified_regular(&algebra));
        assert!(edge.verify());
        let twice = edge.path().then(&edge.path()).unwrap();
        assert!(twice.verify());
        assert_eq!(twice.steps().len(), 2);
        let round_trip = edge.path().then_edge(edge.inverse()).unwrap();
        assert!(round_trip.verify());
        assert_eq!(round_trip.source().certificate(), algebra.certificate());
        assert_eq!(round_trip.target().certificate(), algebra.certificate());
        assert!(round_trip.inverse().verify());
        assert!(DerivedEquivalencePath::identity(&algebra).verify());
    }
}

#[test]
fn a_multi_degree_edge_has_a_checked_formal_inverse() {
    let algebra = linear_an(2, PrimeField::new(5).unwrap());
    let mutation = common::genuine_left_mutation(&common::certified_regular(&algebra));
    let edge = edge(mutation);
    let round_trip = edge.path().then_edge(edge.inverse()).unwrap();
    assert!(round_trip.verify());
    assert_eq!(round_trip.source().certificate(), algebra.certificate());
    assert_eq!(round_trip.target().certificate(), algebra.certificate());
}

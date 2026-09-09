//! Acceptance tests for budgeted tilting-complex discovery.

use auslander::algebra::linear_an;
use auslander::control::ComputationControl;
use auslander::equivalence_discovery::{DiscoveryLimits, DiscoveryStop, discover_equivalences};
use auslander::field::PrimeField;

fn small_limits() -> DiscoveryLimits {
    DiscoveryLimits {
        max_vertices: 3,
        max_directed_mutations: 16,
        max_total_terms: 64,
        max_matrix_entries: 1_024,
        max_work_units: 16,
        ..DiscoveryLimits::default()
    }
}

#[test]
fn a2_walk_keeps_verified_prefixes_and_stable_keys() {
    for field in [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()] {
        let algebra = linear_an(2, field);
        let first =
            discover_equivalences(&algebra, small_limits(), &ComputationControl::new()).unwrap();
        let second =
            discover_equivalences(&algebra, small_limits(), &ComputationControl::new()).unwrap();
        assert!(first.verify());
        assert!(second.verify());
        assert_eq!(first.keys(), second.keys());
        assert_eq!(first.edges(), second.edges());
        assert_eq!(first.blocked(), second.blocked());
        assert_eq!(first.stop(), second.stop());
        assert_eq!(first.vertices().len(), 3);
        assert_eq!(first.completed_mutations(), 5);
        assert_eq!(first.vertices().len(), 3);
        assert_eq!(first.total_terms(), 8);
        assert_eq!(first.matrix_entries(), 6);
        assert!(matches!(first.stop(), DiscoveryStop::VertexLimit { .. }));
    }
}

#[test]
fn cancellation_keeps_the_regular_vertex_without_claiming_closure() {
    let algebra = linear_an(2, PrimeField::new(5).unwrap());
    let control = ComputationControl::new();
    control.cancel();
    let graph = discover_equivalences(&algebra, small_limits(), &control).unwrap();
    assert!(graph.verify());
    assert_eq!(graph.vertices().len(), 1);
    assert!(graph.edges().is_empty());
    assert!(matches!(
        graph.stop(),
        DiscoveryStop::Cancelled {
            completed_mutations: 0
        }
    ));
}

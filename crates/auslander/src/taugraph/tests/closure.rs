use super::super::*;
use super::common::*;

use super::super::support::regular_parts;
use super::super::verify::{close, reachable_from_root};
use crate::algebra::linear_an;
use crate::supporttau::SupportTauTiltingPair;

/// The gate refuses a drained walk whose closure recheck fails.
///
/// A drained frontier is not the certificate. This takes a closed graph,
/// drops one slot record, and sends the parts back through the gate, which
/// is the only route to a `ClosedSupportTauTiltingGraph`. The result is
/// [`GraphError::Defect`], so no caller can hold a closed graph whose own
/// `verify` returns false.
#[test]
fn the_gate_refuses_a_witness_that_fails_its_recheck() {
    let algebra = linear_an(2, f2());
    let graph = walk(&algebra);
    let work_units = graph.work_units();
    let ClosureWitness {
        mut vertices,
        mutations,
        ..
    } = graph.witness;
    vertices[0].slots.pop();
    match close(&algebra, vertices, mutations, work_units) {
        Ok(_) => panic!("the gate handed out a graph whose recheck fails"),
        Err(GraphError::Defect { reason }) => {
            assert!(reason.contains("closure recheck failed"), "{reason}");
        }
        Err(other) => panic!("a failed recheck is a defect, not {other}"),
    }
}

/// An untouched drained walk passes the gate, so the gate is no blanket
/// refusal.
#[test]
fn the_gate_admits_an_intact_witness() {
    let algebra = linear_an(2, f2());
    let graph = walk(&algebra);
    let work_units = graph.work_units();
    let ClosureWitness {
        vertices,
        mutations,
        ..
    } = graph.witness;
    let regated = close(&algebra, vertices, mutations, work_units)
        .expect("an intact witness passes the gate");
    assert_eq!(regated.len(), 5);
    assert_eq!(regated.work_units(), work_units);
}

/// A slot record dropped from a vertex fails obligation 4.
#[test]
fn a_missing_slot_fails_the_closure_witness() {
    let mut graph = walk(&linear_an(2, f2()));
    assert!(graph.verify());
    graph.witness.vertices[0].slots.pop();
    assert!(!graph.witness.slots_resolved());
    assert!(!graph.verify());
}

/// A vertex stored twice fails obligation 2.
#[test]
fn a_duplicated_vertex_fails_the_closure_witness() {
    let algebra = linear_an(2, f2());
    let mut graph = walk(&algebra);
    let (module, support) = regular_parts(&algebra).expect("A_2 has a regular pair");
    let indices: Vec<usize> = (0..module.len()).collect();
    let pair = SupportTauTiltingPair::classify_with_cache(module, support, &indices, None)
        .expect("(A, 0) classifies")
        .into_pair()
        .expect("(A, 0) is a pair");
    graph.witness.vertices.push(GraphVertex {
        pair,
        slots: Vec::new(),
    });
    assert!(!graph.witness.pairwise_distinct());
    assert!(!graph.verify());
}

/// An edge pointed at the wrong vertex fails obligation 5.
///
/// This is the left-only form of a broken involution: the target index and
/// the stored pair-isomorphism witness no longer describe the same pair.
#[test]
fn a_retargeted_edge_fails_the_closure_witness() {
    let mut graph = walk(&linear_an(3, f2()));
    assert!(graph.witness.endpoints_bound());
    let target = graph.witness.mutations[0].target;
    let other = graph
        .witness
        .mutations
        .iter()
        .map(|edge| edge.target)
        .find(|candidate| *candidate != target)
        .expect("A_3 has more than one mutation target");
    graph.witness.mutations[0].target = other;
    assert!(!graph.witness.endpoints_bound());
    assert!(!graph.verify());
}

/// An endpoint witness taken from another edge fails obligation 5.
#[test]
fn an_endpoint_witness_from_another_edge_fails() {
    let mut graph = walk(&linear_an(3, f2()));
    let borrowed = graph.witness.mutations[1].endpoint.clone();
    graph.witness.mutations[0].endpoint = borrowed;
    assert!(!graph.witness.endpoints_bound());
    assert!(!graph.verify());
}

/// Connectivity is recomputed from the edge list, so an edge set that
/// leaves `(A, 0)` isolated fails obligation 6.
#[test]
fn a_broken_edge_list_is_not_connected_from_the_root() {
    let graph = walk(&linear_an(3, f2()));
    let all: Vec<(usize, usize)> = graph
        .mutations()
        .iter()
        .map(|edge| (edge.source(), edge.target()))
        .collect();
    assert_eq!(
        reachable_from_root(graph.len(), all.iter().copied()),
        graph.len()
    );
    let cut: Vec<(usize, usize)> = all
        .iter()
        .copied()
        .filter(|(source, _)| *source != 0)
        .collect();
    assert!(reachable_from_root(graph.len(), cut.iter().copied()) < graph.len());
    assert_eq!(reachable_from_root(graph.len(), std::iter::empty()), 1);
}

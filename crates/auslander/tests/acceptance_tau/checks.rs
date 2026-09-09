use std::sync::Arc;

use auslander::algebra::Algebra;
use auslander::basic::{BasicDecomposition, ProjectiveSupport, SupportPairIsoOutcome, pair_iso};
use auslander::module::{Module, direct_sum};
use auslander::supporttau::{CatalogEnumeration, SupportTauTiltingPair};
use auslander::taugraph::ClosedSupportTauTiltingGraph;

/// Whether the two pairs are isomorphic, with the stored witness rechecked.
///
/// `pair_iso` has no `Unknown` outcome: both inputs are certified basic pairs
/// and the radical criterion is total between certified indecomposables.
fn same_pair(a: &SupportTauTiltingPair, b: &SupportTauTiltingPair) -> bool {
    match pair_iso(a.module(), &a.projective(), b.module(), &b.projective())
        .expect("both pairs are over one algebra value")
    {
        SupportPairIsoOutcome::Isomorphic(witness) => {
            assert!(
                witness.verify(),
                "an isomorphism witness failed its recheck"
            );
            true
        }
        SupportPairIsoOutcome::NotIsomorphic(_) => false,
    }
}

/// Asserts that each pair of one list has exactly one partner in the other,
/// in both directions.
///
/// Exactly one, not at least one, so the assertion also carries the
/// distinctness of both lists.
pub(crate) fn assert_same_pair_set(
    name: &str,
    graph: &ClosedSupportTauTiltingGraph,
    listed: &CatalogEnumeration,
) {
    let from_graph: Vec<&SupportTauTiltingPair> = graph.pairs().collect();
    let from_catalog: Vec<&SupportTauTiltingPair> = listed.pairs().iter().collect();
    assert_eq!(from_graph.len(), from_catalog.len(), "{name}: list lengths");
    for a in &from_graph {
        let hits = from_catalog.iter().filter(|b| same_pair(a, b)).count();
        assert_eq!(
            hits,
            1,
            "{name}: graph pair {:?} has {hits} partners in the catalog list",
            key(a)
        );
    }
    for b in &from_catalog {
        let hits = from_graph.iter().filter(|a| same_pair(b, a)).count();
        assert_eq!(
            hits,
            1,
            "{name}: catalog pair {:?} has {hits} partners in the graph",
            key(b)
        );
    }
}

/// The sorted module dimension vectors and the projective support, which name
/// a pair uniquely on the A_2 fixture.
pub(crate) fn key(pair: &SupportTauTiltingPair) -> (Vec<Vec<usize>>, Vec<u32>) {
    let mut dims = pair.module().dim_vectors();
    dims.sort();
    (dims, pair.projective().vertices().to_vec())
}

pub(crate) fn decomposition(m: &Module) -> BasicDecomposition {
    BasicDecomposition::new(m).expect("the fixture modules are basic and certified")
}

pub(crate) fn support(algebra: &Arc<Algebra>, vertices: &[u32]) -> ProjectiveSupport {
    ProjectiveSupport::new(algebra, vertices).expect("the vertices are in range")
}

pub(crate) fn sum(parts: &[&Module]) -> Module {
    direct_sum(parts).0
}

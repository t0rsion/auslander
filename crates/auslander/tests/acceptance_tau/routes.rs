use super::checks::assert_same_pair_set;
use super::fixtures::{computed, walked};

/// The pair counts and histograms of design section 10, each derived in
/// `catalog_fixtures`.
///
/// Three sources agree on them: the derivation in the comment, the catalog
/// route here, and the mutation graph in
/// `the_mutation_graph_reproduces_the_derived_counts`.
#[test]
fn the_catalog_route_reproduces_the_derived_counts() {
    for entry in computed() {
        let fixture = &entry.fixture;
        assert_eq!(
            entry.listed.len(),
            fixture.pairs,
            "{}: pair count",
            fixture.name
        );
        assert_eq!(
            entry.listed.histogram(),
            fixture.histogram,
            "{}: histogram by |M|",
            fixture.name
        );
        assert_eq!(
            entry.listed.provenance(),
            fixture.provenance,
            "{}: completeness provenance",
            fixture.name
        );
        assert_eq!(
            entry.listed.catalog_len(),
            fixture.catalog.len(),
            "{}: catalog size",
            fixture.name
        );
        // The walk visits the tau-rigid subsets and tests each remaining
        // catalog entry once per visit, so it never visits fewer subsets than
        // it lists pairs.
        assert!(
            entry.listed.nodes_visited() >= entry.listed.len(),
            "{}: nodes visited",
            fixture.name
        );
        // |M| + |P| = n on every listed pair.
        let n = fixture.histogram.len() - 1;
        for pair in entry.listed.pairs() {
            assert_eq!(pair.summand_count(), n, "{}: |M| + |P|", fixture.name);
        }
    }
}

/// The closed mutation graph reports the same counts as the catalog route and
/// the derivation.
///
/// The two routes share no code. The graph rests on AIR Theorem 2.18 and
/// Theorem 2.35(b), the catalog route on Gabriel's theorem or the Nakayama
/// classification.
#[test]
fn the_mutation_graph_reproduces_the_derived_counts() {
    for (fixture, graph) in walked() {
        assert_eq!(graph.len(), fixture.pairs, "{}: pair count", fixture.name);
        assert_eq!(
            graph.histogram(),
            fixture.histogram,
            "{}: histogram by |M|",
            fixture.name
        );
        // Every slot of a closed graph is decided, by obligation 4 of the
        // closure witness.
        for vertex in graph.vertices() {
            assert_eq!(
                vertex.slots().len(),
                vertex.pair().module().len(),
                "{}: undecided slot",
                fixture.name
            );
        }
    }
}

/// Every closed graph rechecks its own completeness certificate.
///
/// `ClosureWitness::verify` reruns all seven obligations of design section 8,
/// including the connectivity recheck, which is recomputed from the edge list
/// rather than inferred from the walk that built it.
#[test]
fn every_closed_graph_rechecks_its_closure_witness() {
    for (fixture, graph) in walked() {
        assert!(
            graph.verify(),
            "{}: the closure witness failed",
            fixture.name
        );
        assert_eq!(graph.witness().vertices().len(), graph.len());
        // Slot accounting: every module slot of every vertex is either a
        // recorded left-mutation edge or a Fac witness, and no slot is both.
        let slots: usize = graph
            .vertices()
            .iter()
            .map(|vertex| vertex.pair().module().len())
            .sum();
        let fac = graph
            .vertices()
            .iter()
            .flat_map(|vertex| vertex.slots())
            .filter(|record| record.fac_witness().is_some())
            .count();
        assert_eq!(
            slots,
            graph.mutations().len() + fac,
            "{}: slots against edges plus Fac witnesses",
            fixture.name
        );
    }
}

/// Cross-route agreement, asserted in both directions.
#[test]
fn the_two_routes_list_the_same_pairs() {
    for entry in computed() {
        let Some(graph) = entry.graph.as_ref() else {
            continue;
        };
        assert_same_pair_set(&entry.fixture.name, graph, &entry.listed);
    }
}

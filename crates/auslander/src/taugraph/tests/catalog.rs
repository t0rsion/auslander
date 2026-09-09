use super::common::*;

use crate::context::VerificationContext;
use crate::profile::Site;
use crate::supporttau::{SupportTauTiltingPair, enumerate_over_catalog};

/// The pair counts, from three sources that agree.
///
/// The semisimple algebra on `n` vertices has every module projective, so
/// every module is tau-rigid and a pair is a split of the `n` simples into
/// a module part and a projective part: `2^n` pairs, the Boolean lattice.
/// Linearly oriented `A_n` is hereditary of Dynkin type, so the count is
/// the W-Catalan number `C_{n+1}`: 5 at `n = 2` and 14 at `n = 3`. The
/// three Nakayama fixtures were counted by hand in the cost spike and
/// again by two enumeration routes there: `truncated_poly(3)` gives 2,
/// `radical_square_zero_cycle(3)` gives 14, `linear_nakayama([2, 2, 1])`
/// gives 12.
///
/// The three sources are this walk, the published W-Catalan numbers, and
/// the cost spike's brute-force routes. `the_walk_and_the_catalog_route_
/// list_the_same_pairs` adds a fourth inside the crate.
#[test]
fn the_pair_counts_agree_with_three_independent_sources() {
    let expected = [4usize, 8, 16, 5, 14, 2, 14, 12];
    for field in fields() {
        let fixtures = catalog_fixtures(field);
        assert_eq!(fixtures.len(), expected.len());
        for ((name, algebra, _), count) in fixtures.iter().zip(expected) {
            let graph = walk(algebra);
            assert_eq!(graph.len(), count, "{name}");
            assert_eq!(graph.pairs().len(), count, "{name}");
        }
    }
}

/// D_4 with the zero ideal has 50 pairs, the W-Catalan number of type
/// D_4, and the histogram by module-summand count is [1, 4, 9, 16, 20].
///
/// The one pair with no module summand is `(0, A)`. The 20 with four are
/// the tau-tilting modules. The cost spike confirmed both the total and
/// the histogram by brute force over the 12 indecomposables.
#[test]
fn the_d4_graph_has_fifty_pairs_and_the_published_histogram() {
    for field in fields() {
        let graph = walk(&d4(field));
        assert_eq!(graph.len(), 50, "over F_{}", field.modulus());
        assert_eq!(graph.histogram(), vec![1, 4, 9, 16, 20]);
        // 50 vertices, 4-regular, so 100 undirected edges, and every edge
        // is one left mutation.
        assert_eq!(graph.mutations().len(), 100);
    }
}

/// A shared verification context removes repeated primitive computations.
#[test]
fn a_d4_f5_closure_context_has_hits_and_misses() {
    let _reset_guard = crate::profile::tests::reset_lock();
    let graph = walk(&d4(f5()));
    let without_fingerprints = graph.witness.fingerprints_without_context();
    let primitive_calls = |counts: &[u64]| {
        [
            Site::HomDim,
            Site::Tau,
            Site::TauWithOpposite,
            Site::EndoNew,
            Site::Decompose,
            Site::PairIso,
        ]
        .into_iter()
        .map(|site| counts[site as usize])
        .sum::<u64>()
    };

    crate::profile::reset();
    assert!(graph.witness.verify_without_context());
    let without_counts = crate::profile::snapshot();
    let without_distinct = crate::profile::distinct_snapshot();
    let without_context = primitive_calls(&without_counts);

    crate::profile::reset();
    let context = VerificationContext::new();
    assert!(graph.witness.verify_with_context(&context));
    assert_eq!(
        without_fingerprints,
        graph.witness.fingerprints_with_context(&context)
    );
    let (hits, misses) = context.memo_stats();
    assert!(hits > 0, "the context has no hit");
    assert!(misses > 0, "the context has no miss");
    let with_counts = crate::profile::snapshot();
    let with_distinct = crate::profile::distinct_snapshot();
    let with_context = primitive_calls(&with_counts);

    if crate::profile::ENABLED {
        let sites = [
            Site::HomDim,
            Site::Tau,
            Site::TauWithOpposite,
            Site::EndoNew,
            Site::Decompose,
            Site::PairIso,
        ];
        eprintln!(
            "D4/F5 context: memo hits {hits}, misses {misses}; primitive calls {without_context} -> {with_context}; distinct {:?} -> {:?}",
            sites
                .iter()
                .map(|site| without_distinct[*site as usize])
                .collect::<Vec<_>>(),
            sites
                .iter()
                .map(|site| with_distinct[*site as usize])
                .collect::<Vec<_>>()
        );
        assert!(
            with_context < without_context,
            "context made {with_context} primitive calls versus {without_context} uncached"
        );
    }
}

/// The walk and the catalog enumeration list the same pairs.
///
/// The two routes share no code and rest on different theorems. The walk
/// mutates from `(A, 0)` and its completeness is AIR Theorem 2.35(b). The
/// catalog route takes subsets of an exhaustive catalog and checks the
/// definition, and its completeness is the Nakayama classification or
/// Gabriel's theorem. Set equality is asserted both ways, matched by
/// certified isomorphism rather than by dimension vector.
#[test]
fn the_walk_and_the_catalog_route_list_the_same_pairs() {
    for field in fields() {
        for (name, algebra, catalog) in catalog_fixtures(field) {
            let graph = walk(&algebra);
            let enumeration = enumerate_over_catalog(&catalog).expect("the catalog route runs");
            let walked: Vec<&SupportTauTiltingPair> = graph.pairs().collect();
            let listed: Vec<&SupportTauTiltingPair> = enumeration.pairs().iter().collect();
            assert_eq!(walked.len(), listed.len(), "{name}");
            assert!(same_pair_set(&walked, &listed), "{name}: walk into catalog");
            assert!(same_pair_set(&listed, &walked), "{name}: catalog into walk");
        }
    }
}

/// Every closed graph rechecks its closure witness.
///
/// The gate already ran this recheck on each of these graphs. The test
/// asserts the public promise: a value of this type answers `true`, and
/// it answers `true` on a second call.
#[test]
fn every_closed_graph_verifies_its_closure_witness() {
    for field in fields() {
        for (name, algebra, _) in catalog_fixtures(field) {
            let graph = walk(&algebra);
            assert!(graph.verify(), "{name}");
        }
    }
}

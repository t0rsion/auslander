use auslander::algebra::kronecker;
use auslander::arquiver::IndecomposableCatalog;
use auslander::dynkin::{DynkinError, EuclideanType};
use auslander::enumerate::EnumerateError;
use auslander::taugraph::{
    GraphLimit, IncompleteReason, IncompleteSupportTauTiltingGraph, MutationGraphLimits,
    support_tau_tilting_graph,
};

use super::checks::assert_same_pair_set;
use super::fixtures::{cached, computed, fields, walk};

/// Rechecks a truncated Kronecker walk: the typed reason, the diagnostics, and
/// the certification of every part that was reached.
fn assert_kronecker_truncation(partial: &IncompleteSupportTauTiltingGraph, max_vertices: usize) {
    let diagnostics = match partial.reason() {
        IncompleteReason::BudgetExhausted(diagnostics) => diagnostics,
        IncompleteReason::CertificationBlocked(blocker) => {
            panic!("the Kronecker walk should exhaust a budget, not block: {blocker}")
        }
    };
    assert_eq!(diagnostics.limit(), GraphLimit::Vertices);
    assert_eq!(diagnostics.vertices_found(), max_vertices);
    assert_eq!(partial.vertices_found().len(), max_vertices);
    assert!(diagnostics.work_units() > 0);
    assert_eq!(partial.work_units(), diagnostics.work_units());
    // The part that was reached is still certified, vertex by vertex and edge
    // by edge.
    assert!(partial.verify_parts());
    for vertex in partial.vertices_found() {
        assert!(vertex.pair().verify());
        // Kronecker has two vertices, so |M| + |P| = 2 on every pair.
        assert_eq!(vertex.pair().summand_count(), 2);
    }
    for edge in partial.verified_mutations() {
        assert!(edge.mutation().verify());
        assert!(edge.endpoint().verify());
    }
}

/// The Kronecker algebra is tau-tilting infinite, so the walk truncates and
/// says so in the type.
///
/// The design records the shape of the truncation: the descending walk runs
/// down the preprojective ray and reaches no preinjective vertex, so the
/// vertices found are a biased sample. Nothing here reads them as a list of
/// pairs, and `IncompleteSupportTauTiltingGraph` has no `pairs` accessor to
/// read them with.
///
/// The budget is 8 vertices rather than the 16 of design section 11. The
/// preprojective ray grows, so vertex 16 carries much larger modules than
/// vertex 8. Measured on this branch over two fields: this test runs in 0.04 s
/// to 0.05 s, while `the_kronecker_walk_at_sixteen_vertices_truncates` runs
/// the design's case at 1.18 s, which does not fit the always-on block.
#[test]
fn the_kronecker_walk_truncates_with_a_typed_reason() {
    let limits = MutationGraphLimits {
        max_vertices: 8,
        ..MutationGraphLimits::default()
    };
    for field in fields() {
        let algebra = kronecker(2, field);
        let outcome = support_tau_tilting_graph(&algebra, &limits)
            .expect("a budget stop is an outcome, not an error");
        assert!(!outcome.is_closed());
        assert!(outcome.closed().is_none(), "no completeness claim");
        let partial = outcome
            .incomplete()
            .expect("the walk cannot close on a tau-tilting infinite algebra");
        assert_kronecker_truncation(partial, 8);
    }
}

/// Neither catalog constructor accepts the Kronecker algebra, and each says
/// why in its own error type.
///
/// The quiver is two vertices with two parallel arrows and a zero ideal, so
/// vertex 0 has two outgoing arrows and is not Nakayama, and the underlying
/// graph is the Euclidean diagram A~_1, not a Dynkin diagram.
#[test]
fn both_catalog_constructors_reject_the_kronecker_algebra() {
    for field in fields() {
        let algebra = kronecker(2, field);
        assert_eq!(
            IndecomposableCatalog::nakayama(&algebra).unwrap_err(),
            EnumerateError::NotNakayama {
                vertex: 0,
                incoming: 0,
                outgoing: 2,
            }
        );
        assert_eq!(
            IndecomposableCatalog::dynkin(&algebra).unwrap_err(),
            DynkinError::NotDynkin {
                euclidean: Some(EuclideanType::A(1)),
            }
        );
    }
}

/// Work-unit ceilings, which are deterministic and profile-independent.
///
/// The ceilings are snapshots, not derivations. Measured on this branch: A_2
/// 6668 units, A_3 145712, D_4 3951020. Each ceiling is the next power of two
/// at or above twice the measurement. The assertion is that the count is
/// reproducible, so a change in the call sequence of the walk shows up here
/// instead of as a slower test.
///
/// The counts rose from 1416, 12895, and 140428 when every rate gained the
/// size factor `e`, the unknown count of `Hom(M, M)`. See
/// [`ClosedSupportTauTiltingGraph::work_units`]: the old rates charged one
/// unit per Hom system whatever its size, which did not brake a tau-tilting
/// infinite walk.
#[test]
fn the_walk_stays_under_its_work_unit_ceilings() {
    for (id, ceiling) in [("linear_an(2)", 16_384u64), ("linear_an(3)", 524_288)] {
        let mut counts = Vec::new();
        for entry in cached(id) {
            let graph = entry
                .graph
                .as_ref()
                .expect("the fixture is in the walk tier");
            assert!(
                graph.work_units() <= ceiling,
                "{}: {} work units, ceiling {ceiling}",
                entry.fixture.name,
                graph.work_units()
            );
            counts.push(graph.work_units());
        }
        // The model charges by call, so the count does not depend on the field.
        assert_eq!(counts[0], counts[1], "{id}: work units across fields");
    }
}

/// Exhaustive tier: the full D_4 cross-check, the largest case in the file.
///
/// The walk and its closure recheck together cost more than the always-on
/// budget, so that block keeps only the D_4 catalog route. This adds the walk,
/// the closure recheck, the cross-route agreement over all 50 pairs, and the
/// work-unit ceiling. Measured on this branch at 0.42 s to 0.64 s over two
/// fields, with the recheck the slower half.
#[test]
#[ignore = "exhaustive tier: the D_4 walk, closure recheck, and 50-pair cross-route"]
fn the_two_routes_agree_on_d4() {
    for entry in cached("dynkin_quiver(D(4))") {
        let fixture = &entry.fixture;
        let graph = walk(&fixture.algebra);
        assert_eq!(graph.len(), 50, "{}: pair count", fixture.name);
        assert_eq!(graph.histogram(), vec![1, 4, 9, 16, 20], "{}", fixture.name);
        assert!(graph.verify(), "{}: closure witness", fixture.name);
        // Snapshot ceiling, as in `the_walk_stays_under_its_work_unit_ceilings`.
        assert!(graph.work_units() <= 8_388_608, "{}", fixture.name);
        assert_same_pair_set(&fixture.name, &graph, &entry.listed);
    }
}

/// Exhaustive tier: `CatalogEnumeration::verify` on every fixture.
///
/// The recheck reverifies each listed pair and then compares every surviving
/// fingerprint bucket with `pair_iso`, which is quadratic in the list. On D_4
/// that is 50 pairs and 2500 comparisons.
#[test]
#[ignore = "exhaustive tier: the per-pair recheck of all nine catalog lists"]
fn every_catalog_list_rechecks() {
    for entry in computed() {
        assert!(
            entry.listed.verify(),
            "{}: the catalog list failed its recheck",
            entry.fixture.name
        );
    }
}

/// Exhaustive tier: the Kronecker budget of design section 11.
///
/// The always-on version stops at 8 vertices. This one stops at the 16 the
/// design names. Measured on this branch at 1.18 s over two fields, against
/// 0.04 s to 0.05 s for the 8-vertex version.
#[test]
#[ignore = "exhaustive tier: the 16-vertex Kronecker truncation of design section 11"]
fn the_kronecker_walk_at_sixteen_vertices_truncates() {
    let limits = MutationGraphLimits {
        max_vertices: 16,
        ..MutationGraphLimits::default()
    };
    for field in fields() {
        let outcome = support_tau_tilting_graph(&kronecker(2, field), &limits)
            .expect("a budget stop is an outcome, not an error");
        assert!(outcome.closed().is_none(), "no completeness claim");
        assert_kronecker_truncation(
            outcome
                .incomplete()
                .expect("the walk cannot close on a tau-tilting infinite algebra"),
            16,
        );
    }
}

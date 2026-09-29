use super::*;
use crate::algebra::{kronecker, linear_an};
use crate::field::PrimeField;
use crate::tilting_complex::TiltingComplexBlocker;

fn kronecker_limits() -> DiscoveryLimits {
    DiscoveryLimits {
        max_directed_mutations: 12,
        ..DiscoveryLimits::default()
    }
}

/// A cancellation at a fixed work unit stops the Kronecker walk inside a
/// mutation. No unit starts after it, and the walk keeps a verified prefix of
/// the uncancelled walk.
#[test]
fn cancellation_inside_a_mutation_starts_no_further_work_unit() {
    let algebra = kronecker(2, PrimeField::new(2).unwrap());
    let control = ComputationControl::new();
    let mut meter = WorkMeter::new(&control);
    let full = discover_metered(&algebra, kronecker_limits(), &control, &mut meter).unwrap();
    let total = meter.charged();
    assert!(total > 2);
    for units in [1, total / 2, total - 1] {
        let control = ComputationControl::new();
        let mut meter = WorkMeter::cancelling_at(&control, units);
        let graph = discover_metered(&algebra, kronecker_limits(), &control, &mut meter).unwrap();
        assert_eq!(meter.charged(), units);
        let DiscoveryStop::Cancelled {
            completed_mutations,
        } = *graph.stop()
        else {
            panic!("the walk did not stop at cancellation: {:?}", graph.stop());
        };
        assert_eq!(completed_mutations, graph.completed_mutations() as u64);
        assert!(completed_mutations < full.completed_mutations() as u64);
        assert_eq!(graph.edges(), &full.edges()[..graph.edges().len()]);
        assert_eq!(graph.blocked(), &full.blocked()[..graph.blocked().len()]);
        assert!(graph.verify());
    }
}

fn linear_a2_graph() -> IncompleteEquivalenceGraph {
    let algebra = linear_an(2, PrimeField::new(5).unwrap());
    discover_equivalences(&algebra, kronecker_limits(), &ComputationControl::new()).unwrap()
}

/// Over `A_2`, some mutation of a non-regular vertex returns the regular
/// complex. That attempt is an edge into vertex 0, not a new vertex.
#[test]
fn a_mutation_back_ends_at_the_stored_vertex() {
    let graph = linear_a2_graph();
    assert!(graph.verify());
    assert!(
        graph
            .edges()
            .iter()
            .any(|edge| edge.source() != 0 && edge.target() == 0)
    );
}

/// Reordering the summands of a vertex keeps its key and its identity.
#[test]
fn vertex_identity_ignores_summand_order() {
    let graph = linear_a2_graph();
    let meter = &mut WorkMeter::default();
    for (index, vertex) in graph.vertices().iter().enumerate() {
        let reversed = vertex.with_summand_order(&[1, 0]);
        assert_eq!(TiltingComplexKey::new(&reversed), graph.keys()[index]);
        for (other, stored) in graph.vertices().iter().enumerate() {
            assert_eq!(
                isomorphic(&reversed, stored, meter).ok(),
                Some(index == other)
            );
        }
    }
}

/// The `A_2` walk over `F_5` under the default limits changed by `edit`.
fn a2_walk(edit: impl FnOnce(&mut DiscoveryLimits)) -> IncompleteEquivalenceGraph {
    let mut limits = DiscoveryLimits::default();
    edit(&mut limits);
    let algebra = linear_an(2, PrimeField::new(5).unwrap());
    let graph = discover_equivalences(&algebra, limits, &ComputationControl::new()).unwrap();
    assert!(graph.verify(), "{limits:?}");
    graph
}

/// Each count limit stops the `A_2` walk exactly at its value. A limit of 0
/// stores or attempts nothing. A storage limit equal to the root sizes keeps
/// the root and stops at the next new vertex.
#[test]
fn every_limit_stops_exactly_at_its_value() {
    let root = a2_walk(|l| l.max_vertices = 1);
    let widen = |count: usize| u64::try_from(count).unwrap();
    let (terms, entries) = (widen(root.total_terms()), widen(root.matrix_entries()));
    assert_eq!(root.vertices().len(), 1);
    let stop = |edit: &dyn Fn(&mut DiscoveryLimits)| {
        let graph = a2_walk(edit);
        (graph.vertices().len(), graph.stop().clone())
    };
    use DiscoveryStop as Stop;
    let vertex = |stored| Stop::VertexLimit {
        stored,
        limit: stored,
    };
    assert_eq!(stop(&|l| l.max_vertices = 0), (0, vertex(0)));
    assert_eq!(stop(&|l| l.max_vertices = 1), (1, vertex(1)));
    let (completed, limit) = (0, 0);
    let mutations = Stop::MutationLimit { completed, limit };
    assert_eq!(stop(&|l| l.max_directed_mutations = 0), (1, mutations));
    let (stored, requested) = (0, terms);
    let term_cut = Stop::TermLimit {
        stored,
        requested,
        limit: terms - 1,
    };
    assert_eq!(stop(&|l| l.max_total_terms = terms - 1), (0, term_cut));
    let (stored, requested) = (0, entries);
    let entry_cut = Stop::MatrixLimit {
        stored,
        requested,
        limit: entries - 1,
    };
    assert_eq!(
        stop(&|l| l.max_matrix_entries = entries - 1),
        (0, entry_cut)
    );
    let at_terms = stop(&|l| l.max_total_terms = terms);
    assert!(matches!(at_terms, (1, Stop::TermLimit { stored, .. }) if stored == terms));
    let at_entries = stop(&|l| l.max_matrix_entries = entries);
    assert!(matches!(at_entries, (1, Stop::MatrixLimit { stored, .. }) if stored == entries));
}

/// With no Hom space allowed, the regular complex stays undetermined. The
/// walk stores no vertex, and its closure claim holds only with that
/// blocker.
#[test]
fn an_undetermined_regular_complex_blocks_the_whole_walk() {
    let graph = a2_walk(|l| l.tilting.max_hom_spaces = 0);
    assert_eq!(graph.stop(), &DiscoveryStop::ExhaustedFrontier);
    assert!(graph.vertices().is_empty() && graph.edges().is_empty());
    let [blocked] = graph.blocked() else {
        panic!("one blocker expected: {:?}", graph.blocked());
    };
    assert!(matches!(
        blocked.reason(),
        BlockedMutationReason::Undetermined(TiltingComplexBlocker::HomLimit { limit: 0, .. })
    ));
    let mut forged = graph.clone();
    forged.blocked[0].reason =
        BlockedMutationReason::Undetermined(TiltingComplexBlocker::Generation);
    assert!(!forged.verify());
    let mut forged = graph.clone();
    forged.stop = DiscoveryStop::MutationLimit {
        completed: 0,
        limit: 0,
    };
    assert!(!forged.verify());
}

/// In `A_2`, left mutation at `P_0` is silting but not tilting. A tilting
/// walk blocks it as `SiltingOnly`. A walk through silting complexes stores
/// it, repeats exactly, and fails verification once its limits claim a
/// tilting walk.
#[test]
fn a_silting_walk_stores_the_blocked_silting_vertex() {
    let is_silting_only = |b: &BlockedTiltingMutation| {
        matches!(b.reason(), BlockedMutationReason::SiltingOnly { .. })
    };
    let tilting = a2_walk(|l| l.max_vertices = 4);
    let first = &tilting.blocked()[0];
    assert!(is_silting_only(first) && first.source() == 0 && first.summand() == 0);
    let silting = a2_walk(|l| (l.max_vertices, l.through_silting) = (4, true));
    assert!(!silting.blocked().iter().any(is_silting_only));
    let edge = &silting.edges()[0];
    assert_eq!((edge.source(), edge.summand(), edge.target()), (0, 0, 1));
    assert!(silting.vertices()[1].to_tilting().is_none());
    let again = a2_walk(|l| (l.max_vertices, l.through_silting) = (4, true));
    assert_eq!(
        (again.keys(), again.edges(), again.blocked(), again.stop()),
        (
            silting.keys(),
            silting.edges(),
            silting.blocked(),
            silting.stop()
        )
    );
    let mut claimed = silting.clone();
    claimed.limits.through_silting = false;
    assert!(!claimed.verify());
}

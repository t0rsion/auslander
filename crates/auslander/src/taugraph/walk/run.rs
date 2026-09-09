use std::collections::{HashMap, VecDeque};
use std::sync::Arc;

use crate::algebra::Algebra;
use crate::taurigid::TauCache;

use super::super::contracts::{
    CertificationBlocker, GraphBudgetDiagnostics, GraphError, GraphLimit, IncompleteReason,
    IncompleteSupportTauTiltingGraph, MutationGraphLimits, SupportTauTiltingGraphOutcome,
};
use super::super::support::regular_parts;
use super::super::verify::close;
use super::accounting::WorkLedger;
use super::registry::{Stop, SummandRegistry, Walk};

impl Walk<'_> {
    accessor_methods! {
        /// The stop for a ledger already past `max_work_units`, or `None`.
        ///
        /// The precheck in [`Walk::visit_slot`] reserves that slot's own model and
        /// nothing else. The graph layer charges the tau misses, the fingerprint,
        /// the isomorphism tests, and a new vertex after the reservation, so a walk
        /// whose queue holds no further slot needs this check to stay inside the
        /// budget. Without it the one-vertex algebra closes over its ceiling: its
        /// only slot lands on `(0, A)`, which has no slot to precheck.
        over_work_budget() -> Option<Stop> = |this|
            (this.ledger.units > this.limits.max_work_units)
                .then_some(Stop::Budget(GraphLimit::WorkUnits));
    }

    /// Walks until the frontier empties or a budget stops it.
    fn run(&mut self) -> Result<Option<Stop>, GraphError> {
        while let Some(vertex) = self.queue.pop_front() {
            let slots = self.vertices[vertex].pair.module().len();
            for slot in 0..slots {
                if let Some(stop) = self.visit_slot(vertex, slot)? {
                    return Ok(Some(stop));
                }
                if let Some(stop) = self.over_work_budget() {
                    return Ok(Some(stop));
                }
            }
            self.at_slot = None;
        }
        Ok(self.over_work_budget())
    }

    fn diagnostics(&self, limit: GraphLimit) -> GraphBudgetDiagnostics {
        GraphBudgetDiagnostics {
            vertices_found: self.vertices.len(),
            verified_slots: self.verified_slots,
            new_vertices: self.new_vertices,
            repeated_endpoints: self.repeated_endpoints,
            frontier: self.queue.len(),
            vertex: self.at_vertex,
            slot: self.at_slot,
            open_slots: self.total_slots - self.verified_slots,
            work_units: self.ledger.units,
            limit,
        }
    }

    fn blocker(&self, reason: String) -> CertificationBlocker {
        CertificationBlocker {
            vertex: self.at_vertex,
            slot: self.at_slot,
            reason,
            vertices_found: self.vertices.len(),
            work_units: self.ledger.units,
        }
    }
}

/// Walks the support tau-tilting quiver of `algebra` from `(A, 0)`, closing
/// under left mutation.
///
/// The walk is breadth first: vertices take indices in discovery order, and
/// the slots of a vertex are visited in increasing order. One
/// [`crate::taurigid::TauCache`] is shared across the run, keyed by nominal module identity, so
/// `tau` runs once per summand value and never on an assembled module.
///
/// The outcome is [`SupportTauTiltingGraphOutcome::Closed`] only when every
/// slot of every vertex is decided, every left mutation lands inside the
/// vertex set, and the closure recheck passes. Then the vertex list is
/// complete, by AIR Theorem 2.35(b) applied to a finite left-closed set; see
/// the module documentation. Otherwise the outcome is
/// [`SupportTauTiltingGraphOutcome::Incomplete`], which keeps the certified
/// part and makes no completeness claim.
///
/// The run is deterministic. Two runs over one algebra with one limit set
/// produce the same vertex order, the same edge order, and the same stored
/// witnesses.
///
/// # Errors
/// The wrapped errors of the basic, support tau-tilting, and mutation layers
/// when an input is rejected, and [`GraphError::Defect`] when a check
/// contradicts a theorem whose hypotheses hold, the closure recheck of a
/// drained walk included. A blocked certification is no error: it comes back
/// as [`IncompleteReason::CertificationBlocked`].
pub fn support_tau_tilting_graph(
    algebra: &Arc<Algebra>,
    limits: &MutationGraphLimits,
) -> Result<SupportTauTiltingGraphOutcome, GraphError> {
    let mut walk = Walk {
        algebra: algebra.clone(),
        limits,
        cache: TauCache::new(),
        registry: SummandRegistry::default(),
        ledger: WorkLedger::default(),
        vertices: Vec::new(),
        indices: Vec::new(),
        fingerprints: Vec::new(),
        buckets: HashMap::new(),
        mutations: Vec::new(),
        queue: VecDeque::new(),
        total_slots: 0,
        verified_slots: 0,
        new_vertices: 0,
        repeated_endpoints: 0,
        at_vertex: 0,
        at_slot: None,
    };
    let (module, support) = regular_parts(algebra)?;
    let stop = match walk.push_vertex(module, support, None)? {
        Ok(_) => walk.run()?,
        Err(stop) => Some(stop),
    };
    let work_units = walk.ledger.units;
    let reason = match stop {
        None => {
            return Ok(SupportTauTiltingGraphOutcome::Closed(close(
                algebra,
                walk.vertices,
                walk.mutations,
                work_units,
            )?));
        }
        Some(Stop::Budget(limit)) => IncompleteReason::BudgetExhausted(walk.diagnostics(limit)),
        Some(Stop::Blocked(reason)) => IncompleteReason::CertificationBlocked(walk.blocker(reason)),
    };
    Ok(SupportTauTiltingGraphOutcome::Incomplete(
        IncompleteSupportTauTiltingGraph {
            algebra: algebra.clone(),
            vertices: walk.vertices,
            mutations: walk.mutations,
            reason,
            work_units,
        },
    ))
}

//! Budgeted breadth-first discovery of tilting-complex mutations, optionally
//! through silting complexes.

mod key;
mod storage;
mod types;

pub use key::TiltingComplexKey;
use key::isomorphic;
use storage::{complex_terms, matrix_entries, storage_stop};
pub use types::{
    BlockedMutationReason, BlockedTiltingMutation, DiscoveryLimits, DiscoveryStop,
    TiltingMutationEdge,
};

use std::collections::{BTreeMap, VecDeque};
use std::sync::Arc;

use crate::algebra::Algebra;
use crate::control::{ComputationControl, ProgressStage, WorkMeter};
use crate::tilting_complex::{
    ApproximationDirection, CertifiedSiltingComplex, Interrupt, TiltingComplexBlocker,
    TiltingComplexError, TiltingComplexResult, TiltingMutationOutcome, metered_tilting_mutation,
    regular_tilting_complex, tilting_mutation,
};

/// A verified mutation graph of pairwise non-isomorphic tilting complexes,
/// and of silting complexes under [`DiscoveryLimits::through_silting`].
///
/// Each edge ends at the stored vertex isomorphic to its mutation. The graph
/// claims no closure beyond [`DiscoveryStop::ExhaustedFrontier`].
#[derive(Clone, Debug)]
pub struct IncompleteEquivalenceGraph {
    algebra: Arc<Algebra>,
    limits: DiscoveryLimits,
    vertices: Vec<CertifiedSiltingComplex>,
    keys: Vec<TiltingComplexKey>,
    edges: Vec<TiltingMutationEdge>,
    blocked: Vec<BlockedTiltingMutation>,
    stop: DiscoveryStop,
    completed_mutations: usize,
    total_terms: usize,
    matrix_entries: usize,
}

impl IncompleteEquivalenceGraph {
    accessor_methods! {
        /// The source algebra.
        pub algebra() -> &Arc<Algebra> = |this| &this.algebra;
        /// The effective discovery limits.
        pub limits() -> DiscoveryLimits = |this| this.limits;
        /// The certified vertices in breadth-first order. A vertex is tilting
        /// exactly when [`CertifiedSiltingComplex::to_tilting`] returns a
        /// certificate. Without [`DiscoveryLimits::through_silting`], every
        /// vertex is tilting.
        pub vertices() -> &[CertifiedSiltingComplex] = |this| &this.vertices;
        /// One homotopy-invariant key per stored vertex. Distinct vertices can
        /// share a key.
        pub keys() -> &[TiltingComplexKey] = |this| &this.keys;
        /// The certified mutation edges in attempt order.
        pub edges() -> &[TiltingMutationEdge] = |this| &this.edges;
        /// Complete attempts that yielded no edge.
        pub blocked() -> &[BlockedTiltingMutation] = |this| &this.blocked;
        /// Why the walk stopped without a closure claim.
        pub stop() -> &DiscoveryStop = |this| &this.stop;
        /// The number of completed directed mutation attempts.
        pub completed_mutations() -> usize = |this| this.completed_mutations;
        /// The sum of stored term counts.
        pub total_terms() -> usize = |this| this.total_terms;
        /// The sum of stored representation and differential matrix entries.
        pub matrix_entries() -> usize = |this| this.matrix_entries;
    }

    /// Rechecks each vertex, key, edge, blocker, and exact work total, and
    /// that no two vertices are isomorphic.
    pub fn verify(&self) -> bool {
        if self.vertices.is_empty() && !self.blocked.is_empty() {
            return self.verify_regular_blocker();
        }
        self.records_match()
            && self.vertices_are_distinct()
            && self.edges.iter().all(|edge| self.verify_edge(edge))
            && self
                .blocked
                .iter()
                .all(|blocked| self.verify_blocked(blocked))
    }

    /// Whether the keys, totals, and attempt count match the stored
    /// vertices, edges, and blockers.
    fn records_match(&self) -> bool {
        let unretained = usize::from(
            matches!(
                self.stop,
                DiscoveryStop::VertexLimit { .. }
                    | DiscoveryStop::TermLimit { .. }
                    | DiscoveryStop::MatrixLimit { .. }
            ) && !self.vertices.is_empty(),
        );
        self.vertices.len() == self.keys.len()
            && self.vertices.iter().all(|vertex| self.admits(vertex))
            && self
                .vertices
                .iter()
                .zip(&self.keys)
                .all(|(vertex, key)| TiltingComplexKey::new(vertex) == *key)
            && self.total_terms == self.vertices.iter().map(complex_terms).sum()
            && self.matrix_entries == self.vertices.iter().map(matrix_entries).sum()
            && self.completed_mutations == self.edges.len() + self.blocked.len() + unretained
    }

    /// Whether this is the walk that stops before its root: the regular
    /// complex stays undetermined, and its blocker is the only record.
    fn verify_regular_blocker(&self) -> bool {
        let regular = regular_start(&self.algebra, self.limits);
        self.stop == DiscoveryStop::ExhaustedFrontier
            && self.keys.is_empty()
            && self.edges.is_empty()
            && [
                self.completed_mutations,
                self.total_terms,
                self.matrix_entries,
            ] == [0; 3]
            && matches!(regular, Ok(RegularStart::Undetermined(root)) if root.blocked == self.blocked)
    }

    fn mutation(
        &self,
        source: usize,
        direction: ApproximationDirection,
        summand: usize,
    ) -> Result<TiltingMutationOutcome, TiltingComplexError> {
        let Some(parent) = self.vertices.get(source) else {
            return Ok(TiltingMutationOutcome::Undetermined(
                TiltingComplexBlocker::Generation,
            ));
        };
        let step = (direction, self.limits.goal());
        tilting_mutation(parent, summand, self.limits.tilting, step)
    }

    /// Whether `vertex` verifies and is tilting unless the walk goes through
    /// silting complexes.
    fn admits(&self, vertex: &CertifiedSiltingComplex) -> bool {
        vertex.verify() && (self.limits.through_silting || vertex.negative_class().is_none())
    }

    fn vertices_are_distinct(&self) -> bool {
        let meter = &mut WorkMeter::default();
        self.keys.iter().enumerate().all(|(index, key)| {
            (0..index).all(|other| {
                self.keys[other] != *key
                    || matches!(
                        isomorphic(&self.vertices[index], &self.vertices[other], meter),
                        Ok(false)
                    )
            })
        })
    }

    fn verify_edge(&self, edge: &TiltingMutationEdge) -> bool {
        let (Some(target), Some(target_key)) =
            (self.vertices.get(edge.target), self.keys.get(edge.target))
        else {
            return false;
        };
        let outcome = self.mutation(edge.source, edge.direction, edge.summand);
        outcome.ok().and_then(stored_value).is_some_and(|value| {
            self.admits(&value)
                && TiltingComplexKey::new(&value) == *target_key
                && matches!(
                    isomorphic(&value, target, &mut WorkMeter::default()),
                    Ok(true)
                )
        })
    }

    fn verify_blocked(&self, blocked: &BlockedTiltingMutation) -> bool {
        let Ok(outcome) = self.mutation(blocked.source, blocked.direction, blocked.summand) else {
            return false;
        };
        blocked_reason(&outcome).is_some_and(|reason| reason == blocked.reason)
    }
}

/// The certificate a mutation stores as a vertex, if any.
fn stored_value(outcome: TiltingMutationOutcome) -> Option<Box<CertifiedSiltingComplex>> {
    match outcome {
        TiltingMutationOutcome::Tilting(value) => Some(Box::new(value.into_silting())),
        TiltingMutationOutcome::Silting(value) => Some(value),
        _ => None,
    }
}

fn blocked_reason(outcome: &TiltingMutationOutcome) -> Option<BlockedMutationReason> {
    match outcome {
        TiltingMutationOutcome::Tilting(_) | TiltingMutationOutcome::Silting(_) => None,
        TiltingMutationOutcome::SiltingOnly(rejection) => {
            Some(BlockedMutationReason::SiltingOnly {
                source: rejection.source(),
                target: rejection.target(),
                degree: rejection.degree(),
                dimension: rejection.dimension(),
            })
        }
        TiltingMutationOutcome::Undetermined(blocker) => {
            Some(BlockedMutationReason::Undetermined(blocker.clone()))
        }
    }
}

#[derive(Default)]
struct DiscoveryContents {
    vertices: Vec<CertifiedSiltingComplex>,
    keys: Vec<TiltingComplexKey>,
    edges: Vec<TiltingMutationEdge>,
    blocked: Vec<BlockedTiltingMutation>,
    completed_mutations: usize,
    total_terms: usize,
    matrix_entries: usize,
}

fn finish(
    algebra: &Arc<Algebra>,
    limits: DiscoveryLimits,
    contents: DiscoveryContents,
    stop: DiscoveryStop,
) -> IncompleteEquivalenceGraph {
    IncompleteEquivalenceGraph {
        algebra: algebra.clone(),
        limits,
        vertices: contents.vertices,
        keys: contents.keys,
        edges: contents.edges,
        blocked: contents.blocked,
        stop,
        completed_mutations: contents.completed_mutations,
        total_terms: contents.total_terms,
        matrix_entries: contents.matrix_entries,
    }
}

enum RegularStart {
    Ready(Box<CertifiedSiltingComplex>),
    Undetermined(DiscoveryContents),
}

enum DiscoveryStart<'m> {
    Ready(DiscoveryState<'m>),
    Finished(IncompleteEquivalenceGraph),
}

/// One completed mutation: a vertex with its stored match, or a blocker.
enum Attempt {
    Vertex(Box<CertifiedSiltingComplex>, Option<usize>),
    Blocked(BlockedMutationReason),
}

struct DiscoveryState<'m> {
    contents: DiscoveryContents,
    buckets: BTreeMap<TiltingComplexKey, Vec<usize>>,
    frontier: VecDeque<usize>,
    meter: &'m mut WorkMeter,
}

impl<'m> DiscoveryState<'m> {
    fn new(
        regular: CertifiedSiltingComplex,
        root_terms: usize,
        root_entries: usize,
        meter: &'m mut WorkMeter,
    ) -> DiscoveryState<'m> {
        let root_key = TiltingComplexKey::new(&regular);
        DiscoveryState {
            contents: DiscoveryContents {
                vertices: vec![regular],
                keys: vec![root_key.clone()],
                completed_mutations: 0,
                total_terms: root_terms,
                matrix_entries: root_entries,
                ..DiscoveryContents::default()
            },
            buckets: BTreeMap::from([(root_key, vec![0usize])]),
            frontier: VecDeque::from([0usize]),
            meter,
        }
    }

    fn next_stop(
        &self,
        limits: DiscoveryLimits,
        control: &ComputationControl,
    ) -> Option<DiscoveryStop> {
        let completed = self.contents.completed_mutations as u64;
        if control.is_cancelled() {
            Some(DiscoveryStop::Cancelled {
                completed_mutations: completed,
            })
        } else if completed >= limits.max_directed_mutations {
            Some(DiscoveryStop::MutationLimit {
                completed,
                limit: limits.max_directed_mutations,
            })
        } else {
            None
        }
    }

    fn store_vertex(
        &mut self,
        key: TiltingComplexKey,
        value: Box<CertifiedSiltingComplex>,
        limits: DiscoveryLimits,
    ) -> Result<usize, DiscoveryStop> {
        let terms = complex_terms(&value);
        let entries = matrix_entries(&value);
        if let Some(stop) = storage_stop(
            self.contents.vertices.len(),
            self.contents.total_terms,
            self.contents.matrix_entries,
            terms,
            entries,
            limits,
        ) {
            return Err(stop);
        }
        let target = self.contents.vertices.len();
        self.contents.total_terms += terms;
        self.contents.matrix_entries += entries;
        self.contents.vertices.push(*value);
        self.contents.keys.push(key.clone());
        self.buckets.entry(key).or_default().push(target);
        self.frontier.push_back(target);
        Ok(target)
    }

    /// The stored vertex isomorphic to `value`, searched within its key.
    fn stored_match(
        &mut self,
        key: &TiltingComplexKey,
        value: &CertifiedSiltingComplex,
    ) -> Result<Option<usize>, Interrupt> {
        for &index in self.buckets.get(key).into_iter().flatten() {
            if isomorphic(value, &self.contents.vertices[index], self.meter)? {
                return Ok(Some(index));
            }
        }
        Ok(None)
    }

    fn process_vertex(
        &mut self,
        edge: TiltingMutationEdge,
        value: Box<CertifiedSiltingComplex>,
        stored: Option<usize>,
        limits: DiscoveryLimits,
    ) -> Option<DiscoveryStop> {
        let target = match stored {
            Some(target) => target,
            None => match self.store_vertex(TiltingComplexKey::new(&value), value, limits) {
                Ok(target) => target,
                Err(stop) => return Some(stop),
            },
        };
        self.contents
            .edges
            .push(TiltingMutationEdge { target, ..edge });
        None
    }

    /// Runs one mutation and matches a stored result against stored vertices.
    fn metered_attempt(
        &mut self,
        source: usize,
        direction: ApproximationDirection,
        summand: usize,
        limits: DiscoveryLimits,
    ) -> Result<Attempt, Interrupt> {
        let outcome = metered_tilting_mutation(
            &self.contents.vertices[source],
            summand,
            limits.tilting,
            (direction, limits.goal()),
            self.meter,
        )?;
        let reason = blocked_reason(&outcome);
        let Some(value) = stored_value(outcome) else {
            return Ok(Attempt::Blocked(
                reason.expect("an outcome without a vertex has a blocker"),
            ));
        };
        let stored = self.stored_match(&TiltingComplexKey::new(&value), &value)?;
        Ok(Attempt::Vertex(value, stored))
    }

    fn attempt(
        &mut self,
        source: usize,
        direction: ApproximationDirection,
        summand: usize,
        limits: DiscoveryLimits,
        control: &ComputationControl,
    ) -> Result<Option<DiscoveryStop>, TiltingComplexError> {
        let completed = self.contents.completed_mutations;
        control.update(ProgressStage::Mutation, completed, completed + 1);
        let attempt = match self.metered_attempt(source, direction, summand, limits) {
            Ok(attempt) => attempt,
            Err(Interrupt::Cancelled) => {
                return Ok(Some(DiscoveryStop::Cancelled {
                    completed_mutations: completed as u64,
                }));
            }
            Err(Interrupt::Error(error)) => return Err(error),
        };
        self.contents.completed_mutations += 1;
        let completed = self.contents.completed_mutations;
        control.update(ProgressStage::Mutation, completed, completed);
        match attempt {
            Attempt::Vertex(value, stored) => {
                let edge = TiltingMutationEdge {
                    source,
                    target: source,
                    direction,
                    summand,
                };
                Ok(self.process_vertex(edge, value, stored, limits))
            }
            Attempt::Blocked(reason) => {
                self.contents.blocked.push(BlockedTiltingMutation {
                    source,
                    direction,
                    summand,
                    reason,
                });
                Ok(None)
            }
        }
    }

    fn walk_direction(
        &mut self,
        source: usize,
        direction: ApproximationDirection,
        summands: usize,
        limits: DiscoveryLimits,
        control: &ComputationControl,
    ) -> Result<Option<DiscoveryStop>, TiltingComplexError> {
        for summand in 0..summands {
            if let Some(stop) = self.next_stop(limits, control) {
                return Ok(Some(stop));
            }
            if let Some(stop) = self.attempt(source, direction, summand, limits, control)? {
                return Ok(Some(stop));
            }
        }
        Ok(None)
    }

    fn walk_source(
        &mut self,
        source: usize,
        limits: DiscoveryLimits,
        control: &ComputationControl,
    ) -> Result<Option<DiscoveryStop>, TiltingComplexError> {
        let summands = self.contents.vertices[source].candidate().len();
        for direction in [ApproximationDirection::Left, ApproximationDirection::Right] {
            if let Some(stop) = self.walk_direction(source, direction, summands, limits, control)? {
                return Ok(Some(stop));
            }
        }
        Ok(None)
    }

    fn walk(
        &mut self,
        limits: DiscoveryLimits,
        control: &ComputationControl,
    ) -> Result<DiscoveryStop, TiltingComplexError> {
        while let Some(source) = self.frontier.pop_front() {
            if let Some(stop) = self.walk_source(source, limits, control)? {
                return Ok(stop);
            }
        }
        Ok(DiscoveryStop::ExhaustedFrontier)
    }
}

fn regular_start(
    algebra: &Arc<Algebra>,
    limits: DiscoveryLimits,
) -> Result<RegularStart, TiltingComplexError> {
    match regular_tilting_complex(algebra, limits.tilting)? {
        TiltingComplexResult::Tilting(value) => {
            Ok(RegularStart::Ready(Box::new(value.into_silting())))
        }
        TiltingComplexResult::NotTilting(_) => unreachable!("the regular generator is tilting"),
        TiltingComplexResult::Undetermined(blocker) => {
            Ok(RegularStart::Undetermined(DiscoveryContents {
                blocked: vec![BlockedTiltingMutation {
                    source: 0,
                    direction: ApproximationDirection::Left,
                    summand: 0,
                    reason: BlockedMutationReason::Undetermined(blocker),
                }],
                ..DiscoveryContents::default()
            }))
        }
    }
}

fn initial_state<'m>(
    algebra: &Arc<Algebra>,
    limits: DiscoveryLimits,
    meter: &'m mut WorkMeter,
) -> Result<DiscoveryStart<'m>, TiltingComplexError> {
    let regular = match regular_start(algebra, limits)? {
        RegularStart::Ready(regular) => *regular,
        RegularStart::Undetermined(contents) => {
            return Ok(DiscoveryStart::Finished(finish(
                algebra,
                limits,
                contents,
                DiscoveryStop::ExhaustedFrontier,
            )));
        }
    };
    let root_terms = complex_terms(&regular);
    let root_entries = matrix_entries(&regular);
    if let Some(stop) = storage_stop(0, 0, 0, root_terms, root_entries, limits) {
        return Ok(DiscoveryStart::Finished(finish(
            algebra,
            limits,
            DiscoveryContents::default(),
            stop,
        )));
    }
    Ok(DiscoveryStart::Ready(DiscoveryState::new(
        regular,
        root_terms,
        root_entries,
        meter,
    )))
}

fn update_completion_progress(
    stop: &DiscoveryStop,
    completed: usize,
    control: &ComputationControl,
) {
    if *stop == DiscoveryStop::ExhaustedFrontier {
        control.update(ProgressStage::Complete, completed, completed);
    }
}

/// Walks left and right tilting mutations in deterministic breadth-first order.
///
/// With [`DiscoveryLimits::through_silting`], a silting result that is not
/// tilting is stored and walked like any vertex.
///
/// Cancellation is observed before each mutation and before each work unit
/// inside one. A cancelled walk keeps every completed mutation and discards
/// the one in progress.
pub fn discover_equivalences(
    algebra: &Arc<Algebra>,
    limits: DiscoveryLimits,
    control: &ComputationControl,
) -> Result<IncompleteEquivalenceGraph, TiltingComplexError> {
    discover_metered(algebra, limits, control, &mut WorkMeter::new(control))
}

fn discover_metered(
    algebra: &Arc<Algebra>,
    limits: DiscoveryLimits,
    control: &ComputationControl,
    meter: &mut WorkMeter,
) -> Result<IncompleteEquivalenceGraph, TiltingComplexError> {
    control.update(ProgressStage::Mutation, 0, 0);
    let start = initial_state(algebra, limits, meter)?;
    let mut state = match start {
        DiscoveryStart::Ready(state) => state,
        DiscoveryStart::Finished(graph) => return Ok(graph),
    };
    let stop = state.walk(limits, control)?;
    let completed = state.contents.completed_mutations;
    update_completion_progress(&stop, completed, control);
    Ok(finish(algebra, limits, state.contents, stop))
}

#[cfg(test)]
mod tests;

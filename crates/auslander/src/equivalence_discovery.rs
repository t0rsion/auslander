//! Budgeted breadth-first discovery of tilting-complex mutations.

mod key;

pub use key::TiltingComplexKey;

use std::collections::{BTreeMap, VecDeque};
use std::sync::Arc;

use crate::algebra::Algebra;
use crate::control::{ComputationControl, ProgressStage};
use crate::quiver::ArrowId;
use crate::tilting_complex::{
    ApproximationDirection, CertifiedTiltingComplex, TiltingComplexBlocker, TiltingComplexError,
    TiltingComplexLimits, TiltingComplexResult, TiltingMutationOutcome, left_tilting_mutation,
    regular_tilting_complex, right_tilting_mutation,
};

/// Deterministic limits for one mutation walk.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DiscoveryLimits {
    /// The greatest number of stored tilting complexes.
    pub max_vertices: usize,
    /// The greatest number of attempted directed mutations.
    pub max_directed_mutations: usize,
    /// The greatest sum of stored bounded-complex term counts.
    pub max_total_terms: usize,
    /// The greatest sum of stored module and differential matrix entries.
    pub max_matrix_entries: usize,
    /// The greatest number of charged mutation work units.
    pub max_work_units: usize,
    /// Limits for each tilting-complex classification.
    pub tilting: TiltingComplexLimits,
}

impl Default for DiscoveryLimits {
    fn default() -> Self {
        DiscoveryLimits {
            max_vertices: 1_024,
            max_directed_mutations: 16_384,
            max_total_terms: 65_536,
            max_matrix_entries: 16_777_216,
            max_work_units: 16_384,
            tilting: TiltingComplexLimits::default(),
        }
    }
}

/// The exact reason a mutation walk stopped.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DiscoveryStop {
    /// Every stored vertex and mutation direction was attempted.
    ExhaustedFrontier,
    /// The caller requested cancellation before the next mutation.
    Cancelled { completed_mutations: usize },
    /// The next directed mutation exceeded its count limit.
    MutationLimit { completed: usize, limit: usize },
    /// The next work unit exceeded its count limit.
    WorkLimit { completed: usize, limit: usize },
    /// A new vertex exceeded the stored-vertex limit.
    VertexLimit { stored: usize, limit: usize },
    /// A new vertex exceeded the total term limit.
    TermLimit {
        stored: usize,
        requested: usize,
        limit: usize,
    },
    /// A new vertex exceeded the matrix-entry limit.
    MatrixLimit {
        stored: usize,
        requested: usize,
        limit: usize,
    },
}

/// A mutation that completed but did not produce a certified tilting complex.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BlockedMutationReason {
    /// A shifted Hom class made the result silting but not tilting.
    SiltingOnly {
        source: usize,
        target: usize,
        degree: i32,
        dimension: usize,
    },
    /// A classification obligation remained open.
    Undetermined(TiltingComplexBlocker),
}

/// One stored non-edge from a complete mutation attempt.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockedTiltingMutation {
    source: usize,
    direction: ApproximationDirection,
    summand: usize,
    reason: BlockedMutationReason,
}

impl BlockedTiltingMutation {
    accessor_methods! {
        /// The source vertex index.
        pub source() -> usize = |this| this.source;
        /// The attempted mutation direction.
        pub direction() -> ApproximationDirection = |this| this.direction;
        /// The replaced summand index.
        pub summand() -> usize = |this| this.summand;
        /// Why no tilting edge was stored.
        pub reason() -> &BlockedMutationReason = |this| &this.reason;
    }
}

/// One certified directed mutation edge.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TiltingMutationEdge {
    source: usize,
    target: usize,
    direction: ApproximationDirection,
    summand: usize,
}

impl TiltingMutationEdge {
    accessor_methods! {
        /// The source vertex index.
        pub source() -> usize = |this| this.source;
        /// The target vertex index.
        pub target() -> usize = |this| this.target;
        /// The checked mutation direction.
        pub direction() -> ApproximationDirection = |this| this.direction;
        /// The replaced summand index.
        pub summand() -> usize = |this| this.summand;
    }
}

/// A verified mutation graph with no closure claim.
#[derive(Clone, Debug)]
pub struct IncompleteEquivalenceGraph {
    algebra: Arc<Algebra>,
    limits: DiscoveryLimits,
    vertices: Vec<CertifiedTiltingComplex>,
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
        /// The certified tilting-complex vertices in breadth-first order.
        pub vertices() -> &[CertifiedTiltingComplex] = |this| &this.vertices;
        /// One stable key per stored vertex.
        pub keys() -> &[TiltingComplexKey] = |this| &this.keys;
        /// The certified mutation edges in attempt order.
        pub edges() -> &[TiltingMutationEdge] = |this| &this.edges;
        /// Complete attempts that yielded no tilting edge.
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

    /// Rechecks each vertex, key, edge, blocker, and exact work total.
    pub fn verify(&self) -> bool {
        let unretained = usize::from(
            matches!(
                self.stop,
                DiscoveryStop::VertexLimit { .. }
                    | DiscoveryStop::TermLimit { .. }
                    | DiscoveryStop::MatrixLimit { .. }
            ) && !self.vertices.is_empty(),
        );
        if self.vertices.len() != self.keys.len()
            || self.vertices.iter().any(|vertex| !vertex.verify())
            || self
                .vertices
                .iter()
                .zip(&self.keys)
                .any(|(vertex, key)| TiltingComplexKey::new(vertex) != *key)
            || self.total_terms != self.vertices.iter().map(complex_terms).sum()
            || self.matrix_entries != self.vertices.iter().map(matrix_entries).sum()
            || self.completed_mutations != self.edges.len() + self.blocked.len() + unretained
        {
            return false;
        }
        let mut unique = self.keys.clone();
        unique.sort();
        unique.dedup();
        if unique.len() != self.keys.len() {
            return false;
        }
        self.edges.iter().all(|edge| self.verify_edge(edge))
            && self
                .blocked
                .iter()
                .all(|blocked| self.verify_blocked(blocked))
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
        mutate(parent, direction, summand, self.limits.tilting)
    }

    fn verify_edge(&self, edge: &TiltingMutationEdge) -> bool {
        let Some(target_key) = self.keys.get(edge.target) else {
            return false;
        };
        matches!(
            self.mutation(edge.source, edge.direction, edge.summand),
            Ok(TiltingMutationOutcome::Tilting(value))
                if value.verify() && TiltingComplexKey::new(&value) == *target_key
        )
    }

    fn verify_blocked(&self, blocked: &BlockedTiltingMutation) -> bool {
        let Ok(outcome) = self.mutation(blocked.source, blocked.direction, blocked.summand) else {
            return false;
        };
        blocked_reason(&outcome).is_some_and(|reason| reason == blocked.reason)
    }
}

fn complex_terms(value: &CertifiedTiltingComplex) -> usize {
    value
        .candidate()
        .summands()
        .iter()
        .map(|summand| summand.complex().len())
        .sum()
}

fn matrix_entries(value: &CertifiedTiltingComplex) -> usize {
    value
        .candidate()
        .summands()
        .iter()
        .map(|summand| {
            let complex = summand.complex();
            let actions: usize = complex
                .terms()
                .iter()
                .map(|term| {
                    (0..term.algebra().quiver().num_arrows())
                        .map(|arrow| {
                            let map = term.map(ArrowId(arrow as u32));
                            map.rows() * map.cols()
                        })
                        .sum::<usize>()
                })
                .sum();
            let differentials: usize = complex
                .differentials()
                .iter()
                .map(|differential| {
                    (0..complex.terms()[0].algebra().quiver().num_vertices())
                        .map(|vertex| {
                            let map = differential.map_at(vertex);
                            map.rows() * map.cols()
                        })
                        .sum::<usize>()
                })
                .sum();
            actions + differentials
        })
        .sum()
}

fn mutate(
    parent: &CertifiedTiltingComplex,
    direction: ApproximationDirection,
    summand: usize,
    limits: TiltingComplexLimits,
) -> Result<TiltingMutationOutcome, TiltingComplexError> {
    match direction {
        ApproximationDirection::Left => left_tilting_mutation(parent, summand, limits),
        ApproximationDirection::Right => right_tilting_mutation(parent, summand, limits),
    }
}

fn blocked_reason(outcome: &TiltingMutationOutcome) -> Option<BlockedMutationReason> {
    match outcome {
        TiltingMutationOutcome::Tilting(_) => None,
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
    vertices: Vec<CertifiedTiltingComplex>,
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
    Ready(CertifiedTiltingComplex),
    Undetermined(DiscoveryContents),
}

enum DiscoveryStart {
    Ready(DiscoveryState),
    Finished(IncompleteEquivalenceGraph),
}

struct DiscoveryState {
    contents: DiscoveryContents,
    indices: BTreeMap<TiltingComplexKey, usize>,
    frontier: VecDeque<usize>,
}

impl DiscoveryState {
    fn new(
        regular: CertifiedTiltingComplex,
        root_terms: usize,
        root_entries: usize,
    ) -> DiscoveryState {
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
            indices: BTreeMap::from([(root_key, 0usize)]),
            frontier: VecDeque::from([0usize]),
        }
    }

    fn next_stop(
        &self,
        limits: DiscoveryLimits,
        control: &ComputationControl,
    ) -> Option<DiscoveryStop> {
        let completed = self.contents.completed_mutations;
        if control.is_cancelled() {
            Some(DiscoveryStop::Cancelled {
                completed_mutations: completed,
            })
        } else if completed == limits.max_directed_mutations {
            Some(DiscoveryStop::MutationLimit {
                completed,
                limit: limits.max_directed_mutations,
            })
        } else if completed == limits.max_work_units {
            Some(DiscoveryStop::WorkLimit {
                completed,
                limit: limits.max_work_units,
            })
        } else {
            None
        }
    }

    fn store_vertex(
        &mut self,
        key: TiltingComplexKey,
        value: Box<CertifiedTiltingComplex>,
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
        self.indices.insert(key, target);
        self.frontier.push_back(target);
        Ok(target)
    }

    fn process_tilting(
        &mut self,
        source: usize,
        direction: ApproximationDirection,
        summand: usize,
        value: Box<CertifiedTiltingComplex>,
        limits: DiscoveryLimits,
    ) -> Result<Option<DiscoveryStop>, TiltingComplexError> {
        let key = TiltingComplexKey::new(&value);
        let target = if let Some(&target) = self.indices.get(&key) {
            target
        } else {
            match self.store_vertex(key.clone(), value, limits) {
                Ok(target) => target,
                Err(stop) => return Ok(Some(stop)),
            }
        };
        self.contents.edges.push(TiltingMutationEdge {
            source,
            target,
            direction,
            summand,
        });
        Ok(None)
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
        let outcome = mutate(
            &self.contents.vertices[source],
            direction,
            summand,
            limits.tilting,
        )?;
        self.contents.completed_mutations += 1;
        let completed = self.contents.completed_mutations;
        control.update(ProgressStage::Mutation, completed, completed);
        match outcome {
            TiltingMutationOutcome::Tilting(value) => {
                self.process_tilting(source, direction, summand, value, limits)
            }
            outcome => {
                self.contents.blocked.push(BlockedTiltingMutation {
                    source,
                    direction,
                    summand,
                    reason: blocked_reason(&outcome).expect("a non-tilting outcome has a blocker"),
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
        TiltingComplexResult::Tilting(value) => Ok(RegularStart::Ready(*value)),
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

fn storage_stop(
    stored_vertices: usize,
    stored_terms: usize,
    stored_entries: usize,
    requested_terms: usize,
    requested_entries: usize,
    limits: DiscoveryLimits,
) -> Option<DiscoveryStop> {
    if stored_vertices == limits.max_vertices {
        Some(DiscoveryStop::VertexLimit {
            stored: stored_vertices,
            limit: limits.max_vertices,
        })
    } else if stored_terms.saturating_add(requested_terms) > limits.max_total_terms {
        Some(DiscoveryStop::TermLimit {
            stored: stored_terms,
            requested: requested_terms,
            limit: limits.max_total_terms,
        })
    } else if stored_entries.saturating_add(requested_entries) > limits.max_matrix_entries {
        Some(DiscoveryStop::MatrixLimit {
            stored: stored_entries,
            requested: requested_entries,
            limit: limits.max_matrix_entries,
        })
    } else {
        None
    }
}

fn initial_state(
    algebra: &Arc<Algebra>,
    limits: DiscoveryLimits,
) -> Result<DiscoveryStart, TiltingComplexError> {
    let regular = match regular_start(algebra, limits)? {
        RegularStart::Ready(regular) => regular,
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
pub fn discover_equivalences(
    algebra: &Arc<Algebra>,
    limits: DiscoveryLimits,
    control: &ComputationControl,
) -> Result<IncompleteEquivalenceGraph, TiltingComplexError> {
    control.update(ProgressStage::Mutation, 0, 0);
    let start = initial_state(algebra, limits)?;
    let mut state = match start {
        DiscoveryStart::Ready(state) => state,
        DiscoveryStart::Finished(graph) => return Ok(graph),
    };
    let stop = state.walk(limits, control)?;
    let completed = state.contents.completed_mutations;
    update_completion_progress(&stop, completed, control);
    Ok(finish(algebra, limits, state.contents, stop))
}

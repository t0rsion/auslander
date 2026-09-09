//! Public contracts for the support tau-tilting mutation graph.

use std::sync::Arc;

use crate::algebra::Algebra;
use crate::ar::TauError;
use crate::basic::{BasicError, SupportPairIsoWitness};
use crate::indec::IndecError;
use crate::mutation::{FacWitness, Mutation, MutationError};
use crate::supporttau::{SupportTauError, SupportTauTiltingPair};
use crate::taurigid::TauRigidError;

use super::verify::ClosureWitness;

/// Rejected input or a failed internal cross-check of the graph layer.
///
/// A blocked certification is no error: it comes back as
/// [`IncompleteReason::CertificationBlocked`], which keeps the partial graph.
/// A defect is an error, because it contradicts a theorem whose hypotheses
/// hold.
#[derive(Clone, Debug)]
pub enum GraphError {
    /// The basic layer rejected an input.
    Basic(BasicError),
    /// The support tau-tilting layer rejected an input or could not run a
    /// check.
    SupportTau(SupportTauError),
    /// The mutation layer rejected an input or reported a defect.
    Mutation(MutationError),
    /// A failed internal cross-check: a theorem's hypotheses hold and the
    /// consequence the code checked did not.
    Defect {
        /// What contradicted the theorem.
        reason: String,
    },
}

display_error! { GraphError {
    Self::Basic(error) => "basic layer: {error}";
    Self::SupportTau(error) => "support tau-tilting layer: {error}";
    Self::Mutation(error) => "mutation layer: {error}";
    Self::Defect { reason } => "internal cross-check failed: {reason}";
} }

error_source!(GraphError {
    Self::Basic(error) => Some(error),
    Self::SupportTau(error) => Some(error),
    Self::Mutation(error) => Some(error),
    Self::Defect { .. } => None,
});

from_variants!(GraphError {
    BasicError => Basic,
    SupportTauError => SupportTau,
    MutationError => Mutation,
});

pub(super) fn defect(reason: String) -> GraphError {
    GraphError::Defect { reason }
}

/// The reason a certification could not be reached, or `None` when the error
/// is not a blocked certification.
///
/// The three sources are an undetermined split
/// ([`BasicError::CertificationBlocked`], [`IndecError::Undetermined`]) and an
/// undecided isomorphism test inside the `tau` cross-check
/// ([`TauError::AgreementUnknown`]). Each poisons a completeness claim. None
/// of them is budget exhaustion.
pub(super) fn basic_blocker(error: &BasicError) -> Option<String> {
    match error {
        BasicError::CertificationBlocked { reason } => Some(reason.clone()),
        _ => None,
    }
}

pub(super) fn support_blocker(error: &SupportTauError) -> Option<String> {
    match error {
        SupportTauError::Basic(inner) => basic_blocker(inner),
        SupportTauError::TauRigid(TauRigidError::Tau(TauError::AgreementUnknown {
            reason,
            ..
        })) => Some(format!("the two tau routes stayed undecided: {reason}")),
        _ => None,
    }
}

pub(super) fn mutation_blocker(error: &MutationError) -> Option<String> {
    match error {
        MutationError::Basic(inner) => basic_blocker(inner),
        MutationError::SupportTau(inner) => support_blocker(inner),
        MutationError::Indec(IndecError::Undetermined { attempts }) => Some(format!(
            "a cokernel summand stayed undetermined after {attempts} split attempts"
        )),
        _ => None,
    }
}

/// Budgets for one [`crate::taugraph::support_tau_tilting_graph`] run.
///
/// The defaults come from the cost spike. D_4 has 50 vertices and E_7 has
/// 4160, so `max_vertices` admits every finite type through E_7 and stops
/// before E_8's 25080. The measured worst-case `Fac` system in the fixture set
/// is 2950 entries; E_7's worst case is 2666520 entries and fits, while E_8's
/// 38235366 entries (306 MB at 8 bytes per field element) truncates with a
/// typed limit instead of allocating.
///
/// `max_work_units` is the budget that covers the whole walk. The other three
/// each gate one kind of step, and none of them is a ceiling on memory.
///
/// There are no wall-clock limits. A time limit would make the outcome depend
/// on the machine, and `docs/support-tau-tilting.md` section 14 requires the walk to
/// be deterministic across processes and platforms.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MutationGraphLimits {
    /// Distinct vertices the walk may hold. Checked when a further distinct
    /// vertex is inserted, so a budget equal to the true count still permits
    /// closure.
    pub max_vertices: usize,
    /// Left-mutation edges the walk may record.
    pub max_directed_mutations: usize,
    /// Work units the walk may charge. See
    /// [`ClosedSupportTauTiltingGraph::work_units`] for the rates.
    ///
    /// The default of 50 million is about 4 seconds of release-profile work on
    /// the Kronecker preprojective ray, where it stops the walk at 37 vertices.
    /// Under the default the D_4 walk charges 3951020 units and closes. A
    /// finite type larger than the fixture set can charge more than the
    /// default, so raise it rather than read a truncation there as tau-tilting
    /// infiniteness.
    ///
    /// A limit set to the exact count a walk charges can still truncate. The
    /// precheck reserves a slot's left-mutation cost before the branch is
    /// known, and a `Fac` slot then charges less than the reservation, so the
    /// last slots of D_4 stop against a ceiling of 3951020. Leave headroom.
    ///
    /// A closed outcome never reports more units than this. The precheck
    /// before a slot reserves that slot's model alone, so the tau misses, the
    /// fingerprints, the isomorphism tests, and a new vertex are checked once
    /// the slot returns and again when the frontier empties. Without the
    /// second check the one-vertex algebra closed over its ceiling: its only
    /// slot lands on `(0, A)`, which has no slot left to precheck.
    ///
    /// The closure recheck that gates a closed outcome is not charged here.
    /// It runs after the walk, over the result rather than the search.
    pub max_work_units: u64,
    /// Entries of the `Fac` system `Hom(U, X_j)`, checked before the mutation
    /// layer allocates it at a slot.
    ///
    /// This is not the largest Hom system the walk allocates. It gates one
    /// system per slot and no other: the fingerprint systems, the systems
    /// inside a Krull-Schmidt decomposition, the ones the target
    /// classification builds, and the ones inside `tau` all run without
    /// consulting it. Those cannot be sized before the call that builds them,
    /// `tau X_j` above all, so a gate in front of them would have to move into
    /// the layers themselves. `max_work_units` is what bounds them, by size as
    /// well as by call count.
    ///
    /// Within a slot the gated system is the widest the walk can size ahead of
    /// time: every approximation system `Hom(X_j, U_i)` has at most as many
    /// unknowns, since `U_i` is a summand of `U`.
    pub max_matrix_entries: usize,
}

impl Default for MutationGraphLimits {
    fn default() -> MutationGraphLimits {
        MutationGraphLimits {
            max_vertices: 10_000,
            max_directed_mutations: 100_000,
            max_work_units: 50_000_000,
            max_matrix_entries: 4_000_000,
        }
    }
}

/// Which budget of [`MutationGraphLimits`] ran out.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GraphLimit {
    /// `max_vertices`, hit when inserting a further distinct vertex.
    Vertices,
    /// `max_directed_mutations`, hit when recording a further left mutation.
    DirectedMutations,
    /// `max_work_units`, hit before a slot whose reserved cost would exceed
    /// it, or after a slot whose charges did.
    WorkUnits,
    /// `max_matrix_entries`, hit before allocating the `Fac` system of a slot.
    MatrixEntries,
}

display_error! { GraphLimit {
    Self::Vertices => "max_vertices";
    Self::DirectedMutations => "max_directed_mutations";
    Self::WorkUnits => "max_work_units";
    Self::MatrixEntries => "max_matrix_entries";
} }

/// The size factor of every rate below: the unknown count of `Hom(M, M)` for a
/// module of dimension vector `dims`, and never less than 1.
///
/// One unit is one unknown of one Hom system. Every rate names a number of Hom
/// systems and multiplies it by this factor, which is an upper bound for the
/// unknown count of each system in the modelled sequence: the arguments are
/// summands of `M` or simple modules, and `sum_v dim U_v dim W_v` is at most
/// `sum_v (dim M_v)^2` when `U` and `W` are summands of `M`.
///
/// The bound does not cover the systems inside `tau`, since the translate is
/// not known before the call. That term keeps the rate the design fixed for it,
/// scaled by the module the walk is standing on.
///
/// Without this factor a rate charged by call alone does not brake a
/// tau-tilting infinite walk. See [`ClosedSupportTauTiltingGraph::work_units`]
/// for the measured gap.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GraphBudgetDiagnostics {
    pub(super) vertices_found: usize,
    pub(super) verified_slots: usize,
    pub(super) new_vertices: usize,
    pub(super) repeated_endpoints: usize,
    pub(super) frontier: usize,
    pub(super) vertex: usize,
    pub(super) slot: Option<usize>,
    pub(super) open_slots: usize,
    pub(super) work_units: u64,
    pub(super) limit: GraphLimit,
}

impl GraphBudgetDiagnostics {
    accessor_methods! {
        /// Distinct vertices held when the limit was hit.
        pub vertices_found() -> usize = |this| this.vertices_found;
        /// Module-summand slots decided, counting both branches.
        pub verified_slots() -> usize = |this| this.verified_slots;
        /// Left mutations that landed on a pair no vertex was isomorphic to.
        pub new_vertices() -> usize = |this| this.new_vertices;
        /// Left mutations that landed on an existing vertex.
        pub repeated_endpoints() -> usize = |this| this.repeated_endpoints;
        /// Vertices waiting in the breadth-first queue.
        pub frontier() -> usize = |this| this.frontier;
        /// The vertex the walk was at.
        pub vertex() -> usize = |this| this.vertex;
        /// The slot the walk was at, or `None` when the limit was hit between
        /// slots.
        pub slot() -> Option<usize> = |this| this.slot;
        /// Module-summand slots of the discovered vertices still undecided.
        pub open_slots() -> usize = |this| this.open_slots;
        /// Work units charged.
        pub work_units() -> u64 = |this| this.work_units;
        /// The budget that ran out.
        pub limit() -> GraphLimit = |this| this.limit;
    }
}

display_error! { GraphBudgetDiagnostics {
    Self { limit, vertex, slot, vertices_found, verified_slots, open_slots, frontier, work_units, .. } => "{} ran out at vertex {} slot {:?}: {} vertices, {} slots decided, {} open, frontier {}, {} work units", limit, vertex, slot, vertices_found, verified_slots, open_slots, frontier, work_units;
} }

/// Where a certification was blocked, and why.
///
/// A blocker is not budget exhaustion. The crate could not certify a step, so
/// no completeness claim can rest on the walk.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertificationBlocker {
    pub(super) vertex: usize,
    pub(super) slot: Option<usize>,
    pub(super) reason: String,
    pub(super) vertices_found: usize,
    pub(super) work_units: u64,
}

impl CertificationBlocker {
    accessor_methods! {
        /// The vertex the walk was at.
        pub vertex() -> usize = |this| this.vertex;
        /// The slot the walk was at, or `None` when the block hit while building a
        /// vertex.
        pub slot() -> Option<usize> = |this| this.slot;
        /// What could not be certified.
        pub reason() -> &str = |this| &this.reason;
        /// Distinct vertices held when the block hit.
        pub vertices_found() -> usize = |this| this.vertices_found;
        /// Work units charged.
        pub work_units() -> u64 = |this| this.work_units;
    }
}

display_error! { CertificationBlocker {
    Self { vertex, slot, reason, .. } => "certification blocked at vertex {} slot {:?}: {}", vertex, slot, reason;
} }

/// Why a walk stopped short of closure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IncompleteReason {
    /// A budget of [`MutationGraphLimits`] ran out.
    BudgetExhausted(GraphBudgetDiagnostics),
    /// A step could not be certified.
    CertificationBlocked(CertificationBlocker),
}

display_error! { IncompleteReason {
    Self::BudgetExhausted(diagnostics) => "{diagnostics}";
    Self::CertificationBlocked(blocker) => "{blocker}";
} }

/// What one module-summand slot of a vertex admits.
#[derive(Debug)]
pub enum SlotRecord {
    /// The slot admits the left mutation stored at this index of the mutation
    /// list.
    LeftMutation {
        /// Index into [`ClosureWitness::mutations`].
        mutation: usize,
    },
    /// `X_j` lies in `Fac(M/X_j)`, so the mutation at this slot is a right
    /// mutation and the walk records no edge.
    NoLeftMutation(FacWitness),
}

impl SlotRecord {
    optional_accessors! {
        /// The index of the mutation, or `None` when the slot admits none.
        pub mutation() -> usize = Self::LeftMutation { mutation } => *mutation;
        /// The `Fac` witness, or `None` when the slot admits a left mutation.
        pub fac_witness() -> &FacWitness = Self::NoLeftMutation(witness) => witness;
    }
}

/// One vertex of the walk: a certified pair, and one record per module-summand
/// slot.
#[derive(Debug)]
pub struct GraphVertex {
    pub(super) pair: SupportTauTiltingPair,
    pub(super) slots: Vec<SlotRecord>,
}

impl GraphVertex {
    accessor_methods! {
        /// The certified pair.
        pub pair() -> &SupportTauTiltingPair = |this| &this.pair;
        /// One record per module summand, in slot order.
        ///
        /// A vertex whose slots were not all visited has fewer records than
        /// `pair().module().len()`. That only happens inside an
        /// [`IncompleteSupportTauTiltingGraph`].
        pub slots() -> &[SlotRecord] = |this| &this.slots;
    }
}

/// One left-mutation edge, with the pair-isomorphism witness that binds its
/// target to a vertex index.
#[derive(Debug)]
pub struct VerifiedMutation {
    pub(super) source: usize,
    pub(super) slot: usize,
    pub(super) target: usize,
    pub(super) mutation: Mutation,
    pub(super) endpoint: SupportPairIsoWitness,
}

impl VerifiedMutation {
    accessor_methods! {
        /// The vertex the mutation starts from.
        pub source() -> usize = |this| this.source;
        /// The module-summand slot the mutation was taken at.
        pub slot() -> usize = |this| this.slot;
        /// The vertex the mutation lands on.
        pub target() -> usize = |this| this.target;
        /// The mutation, with its target pair and its witness.
        pub mutation() -> &Mutation = |this| &this.mutation;
        /// The isomorphism from the mutation's own target pair to the pair stored
        /// at vertex [`VerifiedMutation::target`].
        pub endpoint() -> &SupportPairIsoWitness = |this| &this.endpoint;
    }
}

/// The vertices reachable from vertex zero along the stored edges.
///
/// The count is recomputed from the edge list alone, never from the order the
/// walk discovered vertices in.
#[derive(Debug)]
pub struct ClosedSupportTauTiltingGraph {
    pub(super) witness: ClosureWitness,
    pub(super) work_units: u64,
}

impl ClosedSupportTauTiltingGraph {
    accessor_methods! {
        /// The algebra the pairs live over.
        pub algebra() -> &Arc<Algebra> = |this| this.witness.algebra();
        /// Every basic support tau-tilting pair of the algebra, in discovery order
        /// from `(A, 0)`.
        pub pairs() -> impl ExactSizeIterator<Item = &SupportTauTiltingPair> =
            |this| this.witness.vertices().iter().map(GraphVertex::pair);
        /// The vertices, each with its slot records.
        pub vertices() -> &[GraphVertex] = |this| this.witness.vertices();
        /// The left-mutation edges.
        pub mutations() -> &[VerifiedMutation] = |this| this.witness.mutations();
        /// The number of pairs.
        pub len() -> usize = |this| this.witness.vertices().len();
        /// Whether the list is empty. It never is: `(A, 0)` is a pair over every
        /// algebra.
        pub is_empty() -> bool = |this| this.witness.vertices().is_empty();
    }

    /// Pair counts by `|M|`, indexed from zero to the number of vertices of
    /// the quiver.
    pub fn histogram(&self) -> Vec<usize> {
        let n = self.algebra().quiver().num_vertices() as usize;
        let mut out = vec![0; n + 1];
        for vertex in self.witness.vertices() {
            out[vertex.pair.module().len()] += 1;
        }
        out
    }

    accessor_methods! {
        /// The closure witness.
        pub witness() -> &ClosureWitness = |this| &this.witness;
        /// Work units charged by the walk that built this graph.
        ///
        /// One unit is one unknown of one Hom system. Write `s` for the summand
        /// count and `e` for `sum_v (dim M_v)^2`, the unknown count of
        /// `Hom(M, M)` for the module `M` the walk is standing on:
        ///
        /// ```text
        /// hom_dim / HomSpace::new(M, N)         = e units
        /// IndecomposableModule::new             = 8 * e units
        /// krull_schmidt / decompose             = 8 * s^3 * e units
        /// is_isomorphic(M, N)                   = (8 * s^3 + 16) * e units
        /// tau(M)                                = (64 * s + 8 * s^3) * e units
        /// ```
        ///
        /// The count is charged by call and by module size, never by time, so it
        /// is the same in every profile and on every platform.
        ///
        /// The count has three limits. The walk charges the call sequence of
        /// the layers it uses from a fixed model rather than instrumenting
        /// each call inside them, except for `tau`, which is counted from the
        /// shared cache's miss counter. `e` is an upper bound on the size of
        /// each modelled Hom system, not its exact size, since the arguments
        /// are summands of `M`. And the count covers the walk, not the
        /// closure recheck that gates this value and is the slower half of a
        /// closing walk on D_4. So the count is exact and reproducible, and
        /// it is a model of the work rather than a trace of it.
        ///
        /// `docs/support-tau-tilting.md` section 8 still prints the rates without the `e`
        /// factor. Those rates did not brake a tau-tilting infinite walk: a Hom
        /// system at Kronecker vertex 64 costs about a thousand times one at
        /// vertex 1 and was charged the same single unit.
        pub work_units() -> u64 = |this| this.work_units;
        /// Rechecks the closure witness. See [`ClosureWitness::verify`].
        ///
        /// This value cannot exist unless the same recheck already passed, so
        /// a caller gets `true` here or the crate has a defect. Call it to
        /// recheck a graph that crossed a process or a storage boundary, not
        /// to decide whether the completeness claim holds.
        pub verify() -> bool = |this| this.witness.verify();
    }
}

/// A walk that stopped short of closure, with the part it certified.
///
/// The vertices and the mutations stay individually certified, and
/// [`IncompleteSupportTauTiltingGraph::verify_parts`] rechecks them. There is
/// no completeness claim and no `pairs` accessor: the vertices are
/// [`IncompleteSupportTauTiltingGraph::vertices_found`], the edges are
/// [`IncompleteSupportTauTiltingGraph::verified_mutations`].
///
/// A truncated set is a biased sample. See the module documentation for what
/// the bias looks like on the Kronecker algebra.
#[derive(Debug)]
pub struct IncompleteSupportTauTiltingGraph {
    pub(super) algebra: Arc<Algebra>,
    pub(super) vertices: Vec<GraphVertex>,
    pub(super) mutations: Vec<VerifiedMutation>,
    pub(super) reason: IncompleteReason,
    pub(super) work_units: u64,
}

impl IncompleteSupportTauTiltingGraph {
    accessor_methods! {
        /// The algebra the pairs live over.
        pub algebra() -> &Arc<Algebra> = |this| &this.algebra;
        /// The vertices the walk reached, in discovery order from `(A, 0)`.
        ///
        /// This is a part of the support tau-tilting quiver, not a list of every
        /// pair.
        pub vertices_found() -> &[GraphVertex] = |this| &this.vertices;
        /// The left mutations the walk verified.
        pub verified_mutations() -> &[VerifiedMutation] = |this| &this.mutations;
        /// Why the walk stopped.
        pub reason() -> &IncompleteReason = |this| &this.reason;
        /// Work units charged before the walk stopped.
        pub work_units() -> u64 = |this| this.work_units;
        /// Rechecks each vertex and each mutation on its own.
        ///
        /// This is not a completeness check and cannot become one. It reruns
        /// [`SupportTauTiltingPair::verify`] on every vertex and
        /// [`Mutation::verify`] on every edge, so a stored value that does not
        /// hold up fails here.
        pub verify_parts() -> bool = |this| this.vertices.iter().all(|v| {
            Arc::ptr_eq(v.pair.module().module().algebra(), &this.algebra) && v.pair.verify()
        }) && this
            .mutations
            .iter()
            .all(|edge| edge.mutation.verify() && edge.endpoint.verify());
    }
}

/// What [`crate::taugraph::support_tau_tilting_graph`] produced.
#[derive(Debug)]
pub enum SupportTauTiltingGraphOutcome {
    /// The walk closed, so the vertex list is complete.
    Closed(ClosedSupportTauTiltingGraph),
    /// The walk stopped short, keeping the part it certified.
    Incomplete(IncompleteSupportTauTiltingGraph),
}

impl SupportTauTiltingGraphOutcome {
    binary_outcome_accessors!(
        Closed,
        Incomplete,
        closed -> ClosedSupportTauTiltingGraph = |value| value,
        incomplete -> IncompleteSupportTauTiltingGraph = |value| value,
        is_closed,
        into_closed -> ClosedSupportTauTiltingGraph = |value| value;
        flag = "Whether the walk closed.";
        positive = "The closed graph, or `None` when the walk stopped short.";
        negative = "The partial graph, or `None` when the walk closed.";
        into = "The closed graph by value, or `None` when the walk stopped short.";
    );
}

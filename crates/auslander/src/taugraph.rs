//! The budgeted mutation walk from `(A, 0)` and its closure certificate.
//!
//! [`support_tau_tilting_graph`] walks the support tau-tilting quiver breadth
//! first from the pair `(A, 0)`, closing under LEFT mutation alone. When the
//! frontier empties, the walk builds a [`ClosureWitness`] and reruns
//! [`ClosureWitness::verify`] on it before the outcome exists. Only a witness
//! that passes becomes [`SupportTauTiltingGraphOutcome::Closed`], whose vertex
//! list is every basic support tau-tilting pair of the algebra, up to
//! isomorphism. A drained frontier alone is not the certificate: it says the
//! builder found a branch at every slot, not that the seven obligations hold.
//! When a budget runs out or a certification is blocked, the outcome is
//! [`SupportTauTiltingGraphOutcome::Incomplete`], which keeps the partial
//! graph and makes no completeness claim. When the recheck itself fails, the
//! result is [`GraphError::Defect`] and no graph comes back at all.
//!
//! # The certificate
//!
//! What the obligations establish is finite left closure. Let `S` be a finite
//! set of basic support tau-tilting pairs with `(A, 0)` in `S`, such that
//! every left mutation of every member of `S` is again in `S`. Then `S` is
//! every basic support tau-tilting pair.
//!
//! The proof takes two facts from Adachi, Iyama, and Reiten, "tau-tilting
//! theory", Compositio Math. 150 (2014), 415-452. `(A, 0)` is the maximum of
//! the partial order on support tau-tilting modules (AIR, section 2, the
//! sentence introducing the order). Theorem 2.35(b) says that for `U < V`
//! there is a left mutation `V'` of `V` with `V' >= U`. Take any support
//! tau-tilting pair `U`. If `U` is `(A, 0)` it is in `S`. Otherwise
//! `(A, 0) > U`, so Theorem 2.35(b) gives a left mutation `V_1` of `(A, 0)`
//! with `V_1 >= U`, and `V_1` is in `S` by left closure. Iterating gives a
//! strictly decreasing chain `(A, 0) > V_1 > V_2 > ...` inside `S` with every
//! `V_i >= U`. `S` is finite, so the chain stops, and it can only stop at `U`.
//! Hence `U` is in `S`.
//!
//! The citation is AIR Theorem 2.35(b), equivalently the descending half of
//! the proof of AIR Corollary 2.38. It is not Theorem 2.18 applied to a finite
//! component, and it is not Corollary 2.38 itself. Corollary 2.38 reads "a
//! finite connected component of the support tau-tilting quiver is the whole
//! quiver", and appealing to it directly would also have to rule out mutations
//! from outside `S` landing inside it, which the walk never checks. The
//! argument above needs neither connectivity nor `n`-regularity, only the
//! maximum, left closure, and finiteness.
//!
//! The result the release states, in full: for a finite-dimensional admissible
//! bound quiver algebra over a checked prime field, a verified finite set
//! containing `(A, 0)` and closed under every left mutation is the complete set
//! of basic support tau-tilting pairs up to isomorphism, by AIR Theorem 2.18
//! and Theorem 2.35(b). It requires neither an algebraically closed base field
//! nor residue division rings equal to the base field.
//!
//! The field-generality clause rests on the AIR hypothesis itself, which
//! reads "let `Lambda` be a finite dimensional `k`-algebra". The paper
//! re-imposes the algebraically closed hypothesis at the head of section 5,
//! which would be pointless if it were already in force. Demonet, Iyama, and
//! Jasso, "tau-tilting finite algebras, bricks and g-vectors"
//! (arXiv:1503.00285), work over an arbitrary field with right modules, this
//! crate's setting, and restate the results the argument uses. Cite AIR
//! Theorem 2.35(b) by number and by statement: the published numbering may
//! differ from the arXiv v4 numbering the citation was checked against.
//!
//! Two consequences shape the code. Mutation at a summand of the projective
//! part is always a right mutation, so a descending walk never performs one
//! and a slot is an index into the module summands. And `n`-regularity of the
//! quiver is a cross-check here, not a step of the proof.
//!
//! # What closure means in code
//!
//! Closure is checked per vertex and per slot, never inferred. A set closed
//! under a subset of the left mutations proves nothing, so
//! [`ClosureWitness::verify`] requires that every module-summand slot of every
//! vertex carries one of two things: a verified left mutation whose target is
//! a vertex of the set, or a certified [`FacWitness`] proving that the slot
//! admits no left mutation.
//!
//! That recheck is a gate, not an optional call. It runs on
//! every drained walk before the closed value is built, so a construction
//! defect surfaces as [`GraphError::Defect`] rather than as a
//! [`ClosedSupportTauTiltingGraph`] whose own `verify` returns false. On D_4
//! it costs 74.4 ms to 124.2 ms against 18.7 ms to 30.9 ms for the walk, over
//! four dev-profile runs per field. The cost is not charged to
//! `max_work_units`, which budgets the walk.
//!
//! # Truncation is structurally biased
//!
//! An [`IncompleteSupportTauTiltingGraph`] is a biased sample, not a nearly
//! complete list. On a tau-tilting infinite algebra the descending walk runs
//! down one ray forever. Over the Kronecker algebra it descends the
//! preprojective ray, `(m, m + 1) + (m + 1, m + 2)`, and never reaches a
//! single preinjective vertex, because no finite chain of Hasse steps down
//! from `(A, 0)` leaves that ray. Do not read a truncated result as "the pairs
//! found so far, of which there may be a few more".
//!
//! The safe direction holds. A truncated set is never accidentally closed: at
//! the moment of truncation the deepest vertex still has an unvisited slot, so
//! the closure test fails. No false completeness certificate is possible; the
//! only risk is never getting one.
//!
//! # Cost and budgets
//!
//! One [`TauCache`] is shared across the whole walk, keyed by NOMINAL module
//! identity, one entry per discovered indecomposable summand. `tau` never runs
//! on an assembled module, which follows from additivity of `tau` and `Hom`
//! and so is not a heuristic. Identity keying is what makes the cache sound: a
//! dimension vector is an isomorphism invariant and no identifier, so an
//! earlier index-keyed cache returned the translate of one module for another
//! that merely shared its dimensions. A freshly rebuilt but isomorphic module
//! misses, which costs time and never correctness; preserving known
//! decompositions is what keeps those misses rare. The wall-clock figure that
//! once stood here was measured before the cache was keyed by identity and no
//! longer describes this code.
//!
//! The limit of that sharing is the price of the identity key. Every
//! decomposition returns fresh module values, so a module rebuilt from an
//! isomorphic one misses even though the class is already known. On D_4 the
//! walk computes 200 translates and answers 450 further calls from the cache,
//! against 12 isomorphism classes. Recovering those hits needs reuse across
//! separately reconstructed but isomorphic summands, which is deferred: it
//! must not reintroduce a key weaker than identity.
//!
//! [`MutationGraphLimits`] carries four budgets and no wall-clock limit. Work
//! units are charged by call and by module size, never by time, so the count is
//! the same in every profile and on every platform. `max_work_units` is the
//! only budget that covers the whole walk. `max_matrix_entries` gates one Hom
//! system per slot, the one the `Fac` test builds, and nothing else. See
//! [`MutationGraphLimits::max_matrix_entries`] for what falls outside it.
//!
//! The size half of that rate is what makes `max_work_units` brake a
//! tau-tilting infinite walk. Charged by call alone, a Kronecker walk charged
//! units that grew far more slowly than its cost, so a ceiling well below the
//! default never fired; the modules on the preprojective ray grow without
//! bound and every Hom system on them was charged one unit. Those figures are
//! not restated here because they measured a rate this code no longer uses.
//! With the size factor the same walk stops well short of its vertex ceiling
//! on the default 50 million work units, which is the point of the rate. See
//! [`ClosedSupportTauTiltingGraph::work_units`] for the rates.

use std::collections::{HashMap, VecDeque};
use std::fmt;
use std::sync::Arc;

use crate::algebra::Algebra;
use crate::ar::TauError;
use crate::basic::{
    BasicDecomposition, BasicError, PairFingerprint, ProjectiveSupport, SupportPairIsoOutcome,
    SupportPairIsoWitness, pair_iso,
};
use crate::indec::{IndecError, IndecomposableModule};
use crate::iso::indecomposable_iso;
use crate::module::{Module, direct_sum};
use crate::mutation::{FacWitness, Mutation, MutationError, SlotOutcome, mutate_at_with_cache};
use crate::supporttau::{SupportTauError, SupportTauTiltingClassification, SupportTauTiltingPair};
use crate::taurigid::{TauCache, TauRigidError};

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

impl fmt::Display for GraphError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Basic(error) => write!(f, "basic layer: {error}"),
            Self::SupportTau(error) => write!(f, "support tau-tilting layer: {error}"),
            Self::Mutation(error) => write!(f, "mutation layer: {error}"),
            Self::Defect { reason } => write!(f, "internal cross-check failed: {reason}"),
        }
    }
}

impl std::error::Error for GraphError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Basic(error) => Some(error),
            Self::SupportTau(error) => Some(error),
            Self::Mutation(error) => Some(error),
            Self::Defect { .. } => None,
        }
    }
}

impl From<BasicError> for GraphError {
    fn from(error: BasicError) -> GraphError {
        GraphError::Basic(error)
    }
}

impl From<SupportTauError> for GraphError {
    fn from(error: SupportTauError) -> GraphError {
        GraphError::SupportTau(error)
    }
}

impl From<MutationError> for GraphError {
    fn from(error: MutationError) -> GraphError {
        GraphError::Mutation(error)
    }
}

fn defect(reason: String) -> GraphError {
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
fn basic_blocker(error: &BasicError) -> Option<String> {
    match error {
        BasicError::CertificationBlocked { reason } => Some(reason.clone()),
        _ => None,
    }
}

fn support_blocker(error: &SupportTauError) -> Option<String> {
    match error {
        SupportTauError::Basic(inner) => basic_blocker(inner),
        SupportTauError::TauRigid(TauRigidError::Tau(TauError::AgreementUnknown {
            reason,
            ..
        })) => Some(format!("the two tau routes stayed undecided: {reason}")),
        _ => None,
    }
}

fn mutation_blocker(error: &MutationError) -> Option<String> {
    match error {
        MutationError::Basic(inner) => basic_blocker(inner),
        MutationError::SupportTau(inner) => support_blocker(inner),
        MutationError::Indec(IndecError::Undetermined { attempts }) => Some(format!(
            "a cokernel summand stayed undetermined after {attempts} split attempts"
        )),
        _ => None,
    }
}

/// Budgets for one [`support_tau_tilting_graph`] run.
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
/// on the machine, and `docs/v0.5-design.md` section 14 requires the walk to
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

impl fmt::Display for GraphLimit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Vertices => f.write_str("max_vertices"),
            Self::DirectedMutations => f.write_str("max_directed_mutations"),
            Self::WorkUnits => f.write_str("max_work_units"),
            Self::MatrixEntries => f.write_str("max_matrix_entries"),
        }
    }
}

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
fn scale_of(dims: &[usize]) -> u64 {
    let entries: u64 = dims.iter().map(|&d| (d as u64) * (d as u64)).sum();
    entries.max(1)
}

/// Units for `systems` Hom systems of at most `scale` unknowns each.
const fn hom_units(systems: u64, scale: u64) -> u64 {
    systems * scale
}

/// Units for one Krull-Schmidt decomposition of a module with `summands`
/// summands, which grows as the cube of the summand count.
fn decompose_units(summands: usize, scale: u64) -> u64 {
    8 * (summands as u64).pow(3) * scale
}

/// Units for one certified isomorphism test between modules with `summands`
/// summands.
fn iso_units(summands: usize, scale: u64) -> u64 {
    decompose_units(summands, scale) + 16 * scale
}

/// Units for one `tau` on a module with `summands` summands. The walk only
/// ever charges the indecomposable case.
fn tau_units(summands: usize, scale: u64) -> u64 {
    64 * summands as u64 * scale + decompose_units(summands, scale)
}

/// Units for one certified indecomposability gate.
fn indec_units(scale: u64) -> u64 {
    8 * scale
}

/// Units for one slot visit at a vertex with `summands` module summands, at
/// size factor `scale`.
///
/// The model is the call sequence of [`mutate_at_with_cache`], charged by the
/// rates of `docs/v0.5-design.md` section 8. The Fac test builds one Hom
/// system, `Hom(U, X_j)`, and a slot with no left mutation stops there. A left
/// mutation continues with the decomposition of `U`, the almost complete
/// pair's Hom systems, the decomposition of the cokernel and the
/// indecomposability gate on its first summand, the decomposition of the
/// target, the target pair's Hom systems, and the certified comparison of the
/// two endpoints.
///
/// `tau` is not charged here. It is counted exactly, from the miss counter of
/// the shared [`TauCache`], because the cache is what decides whether a call
/// runs at all.
fn slot_units(summands: usize, left_mutation: bool, scale: u64) -> u64 {
    let mut units = hom_units(1, scale);
    if !left_mutation {
        return units;
    }
    let kept = summands - 1;
    units += decompose_units(kept, scale) + kept as u64 * indec_units(scale);
    units += hom_units((kept * kept) as u64 + 1, scale);
    units += decompose_units(1, scale) + indec_units(scale);
    units += decompose_units(summands, scale) + summands as u64 * indec_units(scale);
    units += hom_units((summands * summands) as u64 + 1, scale);
    units + iso_units(summands, scale)
}

/// Units for classifying one vertex pair with `summands` module summands, at
/// size factor `scale`.
fn vertex_units(summands: usize, scale: u64) -> u64 {
    decompose_units(summands, scale)
        + summands as u64 * indec_units(scale)
        + hom_units((summands * summands) as u64 + 1, scale)
}

/// Units for one [`PairFingerprint`], which runs two Hom dimensions per
/// summand against each of the `vertices` simple modules.
fn fingerprint_units(summands: usize, vertices: usize, scale: u64) -> u64 {
    hom_units(2 * (summands * vertices) as u64, scale)
}

/// The entries of the Hom system for `(m, n)`, which has `sum_v dim m_v dim
/// n_v` unknowns.
fn hom_entries(m: &[usize], n: &[usize]) -> usize {
    m.iter().zip(n).map(|(a, b)| a * b).sum()
}

/// The running work-unit count of one walk.
///
/// Units are charged by call and by module size, never by time, so a count is
/// exact and profile-independent. The ledger is a model of the call sequence
/// the walk runs, at the rates above, with one exception: the `tau` term is
/// counted from the shared [`TauCache`] miss counter rather than modelled,
/// since the cache decides which calls run.
#[derive(Clone, Copy, Debug, Default)]
struct WorkLedger {
    units: u64,
}

impl WorkLedger {
    fn charge(&mut self, units: u64) {
        self.units += units;
    }

    /// Charges `misses` translates of an indecomposable at size factor
    /// `scale`.
    fn charge_tau_misses(&mut self, misses: u64, scale: u64) {
        self.units += misses * tau_units(1, scale);
    }

    /// Whether `extra` further units would exceed `limit`.
    fn would_exceed(&self, extra: u64, limit: u64) -> bool {
        self.units + extra > limit
    }
}

/// What the walk had done when a budget ran out.
///
/// Every field is a count the walk owns, so two runs over one algebra with one
/// limit set produce equal diagnostics.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GraphBudgetDiagnostics {
    vertices_found: usize,
    verified_slots: usize,
    new_vertices: usize,
    repeated_endpoints: usize,
    frontier: usize,
    vertex: usize,
    slot: Option<usize>,
    open_slots: usize,
    work_units: u64,
    limit: GraphLimit,
}

impl GraphBudgetDiagnostics {
    /// Distinct vertices held when the limit was hit.
    #[inline]
    pub fn vertices_found(&self) -> usize {
        self.vertices_found
    }

    /// Module-summand slots decided, counting both branches.
    #[inline]
    pub fn verified_slots(&self) -> usize {
        self.verified_slots
    }

    /// Left mutations that landed on a pair no vertex was isomorphic to.
    #[inline]
    pub fn new_vertices(&self) -> usize {
        self.new_vertices
    }

    /// Left mutations that landed on an existing vertex.
    #[inline]
    pub fn repeated_endpoints(&self) -> usize {
        self.repeated_endpoints
    }

    /// Vertices waiting in the breadth-first queue.
    #[inline]
    pub fn frontier(&self) -> usize {
        self.frontier
    }

    /// The vertex the walk was at.
    #[inline]
    pub fn vertex(&self) -> usize {
        self.vertex
    }

    /// The slot the walk was at, or `None` when the limit was hit between
    /// slots.
    #[inline]
    pub fn slot(&self) -> Option<usize> {
        self.slot
    }

    /// Module-summand slots of the discovered vertices still undecided.
    #[inline]
    pub fn open_slots(&self) -> usize {
        self.open_slots
    }

    /// Work units charged.
    #[inline]
    pub fn work_units(&self) -> u64 {
        self.work_units
    }

    /// The budget that ran out.
    #[inline]
    pub fn limit(&self) -> GraphLimit {
        self.limit
    }
}

impl fmt::Display for GraphBudgetDiagnostics {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} ran out at vertex {} slot {:?}: {} vertices, {} slots decided, {} open, \
             frontier {}, {} work units",
            self.limit,
            self.vertex,
            self.slot,
            self.vertices_found,
            self.verified_slots,
            self.open_slots,
            self.frontier,
            self.work_units
        )
    }
}

/// Where a certification was blocked, and why.
///
/// A blocker is never budget exhaustion and never "probably fine". It means
/// the crate could not certify a step, so no completeness claim can rest on
/// the walk.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertificationBlocker {
    vertex: usize,
    slot: Option<usize>,
    reason: String,
    vertices_found: usize,
    work_units: u64,
}

impl CertificationBlocker {
    /// The vertex the walk was at.
    #[inline]
    pub fn vertex(&self) -> usize {
        self.vertex
    }

    /// The slot the walk was at, or `None` when the block hit while building a
    /// vertex.
    #[inline]
    pub fn slot(&self) -> Option<usize> {
        self.slot
    }

    /// What could not be certified.
    #[inline]
    pub fn reason(&self) -> &str {
        &self.reason
    }

    /// Distinct vertices held when the block hit.
    #[inline]
    pub fn vertices_found(&self) -> usize {
        self.vertices_found
    }

    /// Work units charged.
    #[inline]
    pub fn work_units(&self) -> u64 {
        self.work_units
    }
}

impl fmt::Display for CertificationBlocker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "certification blocked at vertex {} slot {:?}: {}",
            self.vertex, self.slot, self.reason
        )
    }
}

/// Why a walk stopped short of closure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IncompleteReason {
    /// A budget of [`MutationGraphLimits`] ran out.
    BudgetExhausted(GraphBudgetDiagnostics),
    /// A step could not be certified.
    CertificationBlocked(CertificationBlocker),
}

impl fmt::Display for IncompleteReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BudgetExhausted(diagnostics) => write!(f, "{diagnostics}"),
            Self::CertificationBlocked(blocker) => write!(f, "{blocker}"),
        }
    }
}

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
    /// The index of the mutation, or `None` when the slot admits none.
    #[inline]
    pub fn mutation(&self) -> Option<usize> {
        match self {
            Self::LeftMutation { mutation } => Some(*mutation),
            Self::NoLeftMutation(_) => None,
        }
    }

    /// The `Fac` witness, or `None` when the slot admits a left mutation.
    #[inline]
    pub fn fac_witness(&self) -> Option<&FacWitness> {
        match self {
            Self::NoLeftMutation(witness) => Some(witness),
            Self::LeftMutation { .. } => None,
        }
    }
}

/// One vertex of the walk: a certified pair, and one record per module-summand
/// slot.
#[derive(Debug)]
pub struct GraphVertex {
    pair: SupportTauTiltingPair,
    slots: Vec<SlotRecord>,
}

impl GraphVertex {
    /// The certified pair.
    #[inline]
    pub fn pair(&self) -> &SupportTauTiltingPair {
        &self.pair
    }

    /// One record per module summand, in slot order.
    ///
    /// A vertex whose slots were not all visited has fewer records than
    /// `pair().module().len()`. That only happens inside an
    /// [`IncompleteSupportTauTiltingGraph`].
    #[inline]
    pub fn slots(&self) -> &[SlotRecord] {
        &self.slots
    }
}

/// One left-mutation edge, with the pair-isomorphism witness that binds its
/// target to a vertex index.
#[derive(Debug)]
pub struct VerifiedMutation {
    source: usize,
    slot: usize,
    target: usize,
    mutation: Mutation,
    endpoint: SupportPairIsoWitness,
}

impl VerifiedMutation {
    /// The vertex the mutation starts from.
    #[inline]
    pub fn source(&self) -> usize {
        self.source
    }

    /// The module-summand slot the mutation was taken at.
    #[inline]
    pub fn slot(&self) -> usize {
        self.slot
    }

    /// The vertex the mutation lands on.
    #[inline]
    pub fn target(&self) -> usize {
        self.target
    }

    /// The mutation, with its target pair and its witness.
    #[inline]
    pub fn mutation(&self) -> &Mutation {
        &self.mutation
    }

    /// The isomorphism from the mutation's own target pair to the pair stored
    /// at vertex [`VerifiedMutation::target`].
    #[inline]
    pub fn endpoint(&self) -> &SupportPairIsoWitness {
        &self.endpoint
    }
}

/// The vertices reachable from vertex zero along the stored edges.
///
/// The count is recomputed from the edge list alone, never from the order the
/// walk discovered vertices in.
fn reachable_from_root(vertex_count: usize, edges: &[(usize, usize)]) -> usize {
    if vertex_count == 0 {
        return 0;
    }
    let mut out: Vec<Vec<usize>> = vec![Vec::new(); vertex_count];
    for &(source, target) in edges {
        if source < vertex_count && target < vertex_count {
            out[source].push(target);
        }
    }
    let mut seen = vec![false; vertex_count];
    seen[0] = true;
    let mut queue = VecDeque::from([0usize]);
    let mut count = 1;
    while let Some(v) = queue.pop_front() {
        for &w in &out[v] {
            if !seen[w] {
                seen[w] = true;
                count += 1;
                queue.push_back(w);
            }
        }
    }
    count
}

/// The proof that a vertex set is closed under left mutation, rechecked from
/// the stored data.
///
/// [`ClosureWitness::verify`] recomputes every obligation. Nothing stored is
/// taken on trust and nothing is inferred from the walk that built it.
#[derive(Debug)]
pub struct ClosureWitness {
    algebra: Arc<Algebra>,
    vertices: Vec<GraphVertex>,
    mutations: Vec<VerifiedMutation>,
}

impl ClosureWitness {
    /// The algebra the pairs live over.
    #[inline]
    pub fn algebra(&self) -> &Arc<Algebra> {
        &self.algebra
    }

    /// The vertices, in discovery order from `(A, 0)`.
    #[inline]
    pub fn vertices(&self) -> &[GraphVertex] {
        &self.vertices
    }

    /// The left-mutation edges, in discovery order.
    #[inline]
    pub fn mutations(&self) -> &[VerifiedMutation] {
        &self.mutations
    }

    /// Obligation 1: every vertex is a verified basic support tau-tilting
    /// pair over this algebra.
    fn vertices_certified(&self) -> bool {
        self.vertices.iter().all(|v| {
            Arc::ptr_eq(v.pair.module().module().algebra(), &self.algebra) && v.pair.verify()
        })
    }

    /// Obligation 2: the vertices are pairwise non-isomorphic.
    ///
    /// [`PairFingerprint`] buckets the vertices and [`pair_iso`] decides
    /// inside a bucket. The fingerprint is a prefilter: a match is
    /// inconclusive, so the certified test still runs.
    fn pairwise_distinct(&self) -> bool {
        let mut fingerprints = Vec::with_capacity(self.vertices.len());
        for v in &self.vertices {
            match PairFingerprint::new(v.pair.module(), &v.pair.projective()) {
                Ok(fingerprint) => fingerprints.push(fingerprint),
                Err(_) => return false,
            }
        }
        for (i, left) in self.vertices.iter().enumerate() {
            for (j, right) in self.vertices.iter().enumerate().skip(i + 1) {
                if fingerprints[i] != fingerprints[j] {
                    continue;
                }
                match pair_iso(
                    left.pair.module(),
                    &left.pair.projective(),
                    right.pair.module(),
                    &right.pair.projective(),
                ) {
                    Ok(SupportPairIsoOutcome::NotIsomorphic(_)) => {}
                    _ => return false,
                }
            }
        }
        true
    }

    /// Obligation 3: vertex zero is certified isomorphic to `(A, 0)`.
    fn root_is_regular(&self) -> bool {
        let Some(root) = self.vertices.first() else {
            return false;
        };
        let Ok((module, support)) = regular_parts(&self.algebra) else {
            return false;
        };
        matches!(
            pair_iso(
                &module,
                &support,
                root.pair.module(),
                &root.pair.projective()
            ),
            Ok(SupportPairIsoOutcome::Isomorphic(_))
        )
    }

    /// Obligation 4: every module-summand slot of every vertex carries either
    /// a verified left mutation into the set or a certified `Fac` witness.
    fn slots_resolved(&self) -> bool {
        let mut referenced = vec![false; self.mutations.len()];
        for (v, vertex) in self.vertices.iter().enumerate() {
            if vertex.slots.len() != vertex.pair.module().len() {
                return false;
            }
            for (slot, record) in vertex.slots.iter().enumerate() {
                match record {
                    SlotRecord::LeftMutation { mutation } => {
                        let Some(edge) = self.mutations.get(*mutation) else {
                            return false;
                        };
                        if referenced[*mutation] {
                            return false;
                        }
                        referenced[*mutation] = true;
                        if edge.source != v || edge.slot != slot {
                            return false;
                        }
                        if edge.target >= self.vertices.len() {
                            return false;
                        }
                        if edge.mutation.slot() != slot || !edge.mutation.verify() {
                            return false;
                        }
                        // The stored mutation has to start at this vertex's
                        // module part, so a witness borrowed from elsewhere
                        // fails here.
                        if !edge
                            .mutation
                            .witness()
                            .source_module()
                            .ptr_eq(vertex.pair.module().module())
                            || edge.mutation.witness().source_projective()
                                != vertex.pair.projective().vertices()
                        {
                            return false;
                        }
                    }
                    SlotRecord::NoLeftMutation(witness) => {
                        if !witness.verify() {
                            return false;
                        }
                        let summands = vertex.pair.module().summands();
                        let Some(x) = summands.get(slot) else {
                            return false;
                        };
                        if !witness.summand().ptr_eq(x.module()) {
                            return false;
                        }
                        // The witness stores the summands of U, and the
                        // mutation layer built U by dropping this slot, so
                        // they are this vertex's own summand values in order.
                        // Bind them by pointer: a dimension vector is an
                        // isomorphism invariant and no identifier, so a sum
                        // comparison would admit a witness built over
                        // different modules of the same dimensions.
                        let kept = summands
                            .iter()
                            .enumerate()
                            .filter(|(i, _)| *i != slot)
                            .map(|(_, other)| other.module());
                        let stored = witness.summands();
                        if stored.len() + 1 != summands.len() {
                            return false;
                        }
                        if !kept.zip(stored).all(|(a, b)| a.ptr_eq(b)) {
                            return false;
                        }
                    }
                }
            }
        }
        referenced.iter().all(|used| *used)
    }

    /// Obligation 5: every edge endpoint carries a pair-isomorphism witness to
    /// its indexed vertex, and the stored maps run between those two pairs.
    fn endpoints_bound(&self) -> bool {
        for edge in &self.mutations {
            let Some(vertex) = self.vertices.get(edge.target) else {
                return false;
            };
            let built = edge.mutation.target();
            if built.projective().vertices() != vertex.pair.projective().vertices() {
                return false;
            }
            let from = built.module().summands();
            let to = vertex.pair.module().summands();
            let bijection = edge.endpoint.bijection();
            if bijection.len() != from.len() || from.len() != to.len() {
                return false;
            }
            if !edge.endpoint.verify() {
                return false;
            }
            for (i, &j) in bijection.iter().enumerate() {
                let (Some(source), Some(target)) = (from.get(i), to.get(j)) else {
                    return false;
                };
                let forward = &edge.endpoint.forward()[i];
                let backward = &edge.endpoint.backward()[i];
                if !forward.source().ptr_eq(source.module())
                    || !forward.target().ptr_eq(target.module())
                    || !backward.source().ptr_eq(target.module())
                    || !backward.target().ptr_eq(source.module())
                {
                    return false;
                }
            }
        }
        true
    }

    /// Obligation 6: every vertex is reachable from vertex zero along the
    /// stored left-mutation edges.
    fn connected(&self) -> bool {
        let edges: Vec<(usize, usize)> = self
            .mutations
            .iter()
            .map(|edge| (edge.source, edge.target))
            .collect();
        reachable_from_root(self.vertices.len(), &edges) == self.vertices.len()
    }

    /// Obligation 7, a cross-check: `incoming = Fac slots + |P|` at every
    /// vertex, and `outgoing + incoming = n`. See [`ClosureWitness::verify`]
    /// for why this is a cross-check rather than a gate.
    fn n_regular(&self) -> bool {
        let n = self.algebra.quiver().num_vertices() as usize;
        let mut incoming = vec![0usize; self.vertices.len()];
        for edge in &self.mutations {
            if edge.target >= incoming.len() {
                return false;
            }
            incoming[edge.target] += 1;
        }
        for (v, vertex) in self.vertices.iter().enumerate() {
            let outgoing = vertex
                .slots
                .iter()
                .filter(|record| record.mutation().is_some())
                .count();
            let fac = vertex.slots.len() - outgoing;
            if incoming[v] != fac + vertex.pair.projective().len() {
                return false;
            }
            if outgoing + incoming[v] != n {
                return false;
            }
        }
        true
    }

    /// Rechecks all seven obligations of `docs/v0.5-design.md` section 8.
    ///
    /// 1. Every vertex is a verified basic support tau-tilting pair.
    /// 2. The vertices are pairwise non-isomorphic.
    /// 3. Vertex zero is certified isomorphic to `(A, 0)`.
    /// 4. Every module-summand slot of every vertex carries a verified left
    ///    mutation whose target is a vertex of the set, or a certified
    ///    [`FacWitness`] proving that no left mutation exists there.
    /// 5. Every edge endpoint carries a pair-isomorphism witness to its
    ///    indexed vertex, and the stored maps run between those two pairs.
    /// 6. Every vertex is reachable from vertex zero along the stored edges.
    /// 7. As a cross-check, the graph is `n`-regular.
    ///
    /// Every check recomputes from the stored pairs and maps: the vertices are
    /// re-verified, the vertex comparisons rerun, the mutations re-verified,
    /// the endpoint witnesses rebound, and connectivity recomputed from the
    /// edge list rather than inferred from the walk.
    ///
    /// Obligation 7 is a cross-check and not a gate on soundness. The
    /// underlying graph of the support tau-tilting quiver is `n`-regular with
    /// `n` the number of simple modules, which here is the number of vertices
    /// of the quiver (Demonet, Iyama, and Jasso, arXiv:1503.00285, stated
    /// right after their result that arrows of the Hasse quiver are mutations;
    /// it follows from AIR Theorem 2.18). Each of the `n` slots of a vertex
    /// gives one neighbour: a module slot with a left mutation gives an
    /// outgoing edge, and a module slot in the `Fac` branch or a projective
    /// summand gives a right mutation, hence an incoming edge. So for every
    /// vertex
    ///
    /// ```text
    /// incoming edges = Fac slots + |P|      and      outgoing + incoming = n.
    /// ```
    ///
    /// The content is the first equation: the incoming count is read off the
    /// stored edge list, which no single vertex built, while the right side is
    /// read off the vertex itself.
    ///
    /// Completeness rests on obligations 1 to 5, which are finite left closure
    /// with `(A, 0)` present. Obligation 6 follows from those: the descending
    /// chain of AIR Theorem 2.35(b) reaches every pair from `(A, 0)` along
    /// edges obligation 4 stores. Obligation 7 is outside the argument
    /// altogether. Both stay gates all the same, because a failure of either
    /// contradicts a theorem whose hypotheses hold, so it is a crate defect.
    pub fn verify(&self) -> bool {
        self.vertices_certified()
            && self.pairwise_distinct()
            && self.root_is_regular()
            && self.slots_resolved()
            && self.endpoints_bound()
            && self.connected()
            && self.n_regular()
    }
}

/// A walk that closed: the complete list of basic support tau-tilting pairs of
/// one algebra, up to isomorphism.
///
/// Completeness comes from finite left closure and nothing else: the set is
/// finite, holds `(A, 0)`, and holds every left mutation of every member, so
/// AIR Theorem 2.35(b) leaves no pair outside it. The module documentation
/// gives the argument, why the citation is not Corollary 2.38, and the
/// field-generality note. The value exists only past
/// [`ClosedSupportTauTiltingGraph::verify`], which the walk runs before
/// building it.
///
/// The list is complete up to isomorphism of pairs. It is not a list of
/// modules: two vertices are distinct exactly when [`pair_iso`] proves them
/// non-isomorphic.
#[derive(Debug)]
pub struct ClosedSupportTauTiltingGraph {
    witness: ClosureWitness,
    work_units: u64,
}

impl ClosedSupportTauTiltingGraph {
    /// The algebra the pairs live over.
    #[inline]
    pub fn algebra(&self) -> &Arc<Algebra> {
        self.witness.algebra()
    }

    /// Every basic support tau-tilting pair of the algebra, in discovery order
    /// from `(A, 0)`.
    pub fn pairs(&self) -> impl ExactSizeIterator<Item = &SupportTauTiltingPair> {
        self.witness.vertices().iter().map(GraphVertex::pair)
    }

    /// The vertices, each with its slot records.
    #[inline]
    pub fn vertices(&self) -> &[GraphVertex] {
        self.witness.vertices()
    }

    /// The left-mutation edges.
    #[inline]
    pub fn mutations(&self) -> &[VerifiedMutation] {
        self.witness.mutations()
    }

    /// The number of pairs.
    #[inline]
    pub fn len(&self) -> usize {
        self.witness.vertices().len()
    }

    /// Whether the list is empty. It never is: `(A, 0)` is a pair over every
    /// algebra.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.witness.vertices().is_empty()
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

    /// The closure witness.
    #[inline]
    pub fn witness(&self) -> &ClosureWitness {
        &self.witness
    }

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
    /// The count has three limits. The walk charges the call sequence of the
    /// layers it uses from a fixed model rather than instrumenting each call
    /// inside them, except for `tau`, which is counted from the shared cache's
    /// miss counter. `e` is an upper bound on the size of each modelled Hom
    /// system, not its exact size, since the arguments are summands of `M`.
    /// And the count covers the walk, not the closure recheck that gates this
    /// value and is the slower half of a closing walk on D_4. So the count is
    /// exact and reproducible, and it is a model of the work rather than a
    /// trace of it.
    ///
    /// `docs/v0.5-design.md` section 8 still prints the rates without the `e`
    /// factor. Those rates did not brake a tau-tilting infinite walk: a Hom
    /// system at Kronecker vertex 64 costs about a thousand times one at
    /// vertex 1 and was charged the same single unit.
    #[inline]
    pub fn work_units(&self) -> u64 {
        self.work_units
    }

    /// Rechecks the closure witness. See [`ClosureWitness::verify`].
    ///
    /// This value cannot exist unless the same recheck already passed, so a
    /// caller gets `true` here or the crate has a defect. Call it to recheck a
    /// graph that crossed a process or a storage boundary, not to decide
    /// whether the completeness claim holds.
    pub fn verify(&self) -> bool {
        self.witness.verify()
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
    algebra: Arc<Algebra>,
    vertices: Vec<GraphVertex>,
    mutations: Vec<VerifiedMutation>,
    reason: IncompleteReason,
    work_units: u64,
}

impl IncompleteSupportTauTiltingGraph {
    /// The algebra the pairs live over.
    #[inline]
    pub fn algebra(&self) -> &Arc<Algebra> {
        &self.algebra
    }

    /// The vertices the walk reached, in discovery order from `(A, 0)`.
    ///
    /// This is a part of the support tau-tilting quiver, not a list of every
    /// pair.
    #[inline]
    pub fn vertices_found(&self) -> &[GraphVertex] {
        &self.vertices
    }

    /// The left mutations the walk verified.
    #[inline]
    pub fn verified_mutations(&self) -> &[VerifiedMutation] {
        &self.mutations
    }

    /// Why the walk stopped.
    #[inline]
    pub fn reason(&self) -> &IncompleteReason {
        &self.reason
    }

    /// Work units charged before the walk stopped.
    #[inline]
    pub fn work_units(&self) -> u64 {
        self.work_units
    }

    /// Rechecks each vertex and each mutation on its own.
    ///
    /// This is not a completeness check and cannot become one. It reruns
    /// [`SupportTauTiltingPair::verify`] on every vertex and
    /// [`Mutation::verify`] on every edge, so a stored value that does not
    /// hold up fails here.
    pub fn verify_parts(&self) -> bool {
        self.vertices.iter().all(|v| {
            Arc::ptr_eq(v.pair.module().module().algebra(), &self.algebra) && v.pair.verify()
        }) && self
            .mutations
            .iter()
            .all(|edge| edge.mutation.verify() && edge.endpoint.verify())
    }
}

/// What [`support_tau_tilting_graph`] produced.
#[derive(Debug)]
pub enum SupportTauTiltingGraphOutcome {
    /// The walk closed, so the vertex list is complete.
    Closed(ClosedSupportTauTiltingGraph),
    /// The walk stopped short, keeping the part it certified.
    Incomplete(IncompleteSupportTauTiltingGraph),
}

impl SupportTauTiltingGraphOutcome {
    /// Whether the walk closed.
    #[inline]
    pub fn is_closed(&self) -> bool {
        matches!(self, Self::Closed(_))
    }

    /// The closed graph, or `None` when the walk stopped short.
    #[inline]
    pub fn closed(&self) -> Option<&ClosedSupportTauTiltingGraph> {
        match self {
            Self::Closed(graph) => Some(graph),
            Self::Incomplete(_) => None,
        }
    }

    /// The partial graph, or `None` when the walk closed.
    #[inline]
    pub fn incomplete(&self) -> Option<&IncompleteSupportTauTiltingGraph> {
        match self {
            Self::Closed(_) => None,
            Self::Incomplete(graph) => Some(graph),
        }
    }

    /// The closed graph by value, or `None` when the walk stopped short.
    #[inline]
    pub fn into_closed(self) -> Option<ClosedSupportTauTiltingGraph> {
        match self {
            Self::Closed(graph) => Some(graph),
            Self::Incomplete(_) => None,
        }
    }
}

/// The module part and the projective support of `(A, 0)`.
fn regular_parts(
    algebra: &Arc<Algebra>,
) -> Result<(BasicDecomposition, ProjectiveSupport), BasicError> {
    let parts: Vec<Module> = (0..algebra.quiver().num_vertices())
        .map(|v| Module::projective(algebra, v))
        .collect();
    let refs: Vec<&Module> = parts.iter().collect();
    let module = if refs.is_empty() {
        Module::zero(algebra)
    } else {
        direct_sum(&refs).0
    };
    Ok((
        BasicDecomposition::new(&module)?,
        ProjectiveSupport::new(algebra, &[])?,
    ))
}

/// The indecomposables the walk has discovered, each with a stable index.
///
/// The index labels an isomorphism class for witnesses and for the Python
/// bindings. It does NOT key the shared [`TauCache`], which keys on nominal
/// module identity.
///
/// Module identity in this crate is nominal, and every decomposition returns
/// fresh module values, so an index is recovered by a certified isomorphism
/// test. Indices are never reused for a second isomorphism class.
#[derive(Default)]
struct SummandRegistry {
    entries: Vec<(usize, Module)>,
    next: usize,
}

impl SummandRegistry {
    /// An index no entry holds.
    fn fresh(&mut self) -> usize {
        let index = self.next;
        self.next += 1;
        index
    }

    /// The index of the entry isomorphic to `x`, or `None`.
    ///
    /// The dimension vector prefilters the scan, and the certified radical
    /// criterion decides. Charges one isomorphism test per candidate the
    /// prefilter admits.
    fn lookup(&self, x: &IndecomposableModule, ledger: &mut WorkLedger) -> Option<usize> {
        let scale = scale_of(x.module().dim_vector());
        for (index, entry) in &self.entries {
            if entry.dim_vector() != x.module().dim_vector() {
                continue;
            }
            ledger.charge(iso_units(1, scale));
            // The radical criterion takes the endomorphism algebra of its
            // first argument, so the query supplies it and the stored entry
            // needs only its module.
            if indecomposable_iso(x.module(), entry, x.endo()).is_some() {
                return Some(*index);
            }
        }
        None
    }

    fn insert(&mut self, index: usize, x: Module) {
        self.entries.push((index, x));
    }
}

/// Why the walk stopped before the frontier emptied.
enum Stop {
    Budget(GraphLimit),
    Blocked(String),
}

/// The state of one [`support_tau_tilting_graph`] run.
struct Walk<'a> {
    algebra: Arc<Algebra>,
    limits: &'a MutationGraphLimits,
    cache: TauCache,
    registry: SummandRegistry,
    ledger: WorkLedger,
    vertices: Vec<GraphVertex>,
    indices: Vec<Vec<usize>>,
    fingerprints: Vec<PairFingerprint>,
    buckets: HashMap<PairFingerprint, Vec<usize>>,
    mutations: Vec<VerifiedMutation>,
    queue: VecDeque<usize>,
    total_slots: usize,
    verified_slots: usize,
    new_vertices: usize,
    repeated_endpoints: usize,
    at_vertex: usize,
    at_slot: Option<usize>,
}

impl Walk<'_> {
    /// The number of vertices of the quiver, which is `n`.
    fn quiver_vertices(&self) -> usize {
        self.algebra.quiver().num_vertices() as usize
    }

    /// Charges the translates the shared cache computed since the miss count
    /// was `misses_before`, at the size factor of the module the walk stands
    /// on.
    ///
    /// A hit costs nothing, which is why the walk shares one cache.
    fn charge_tau(&mut self, misses_before: u64, scale: u64) {
        let misses = self.cache.misses() - misses_before;
        self.ledger.charge_tau_misses(misses, scale);
    }

    /// The stable index of each summand of `decomposition`, registering the
    /// ones the walk has not seen.
    ///
    /// `preferred` is the index a mutation already spent on its cokernel
    /// summand. Reusing it keeps ONE index per isomorphism class, so the
    /// registry does not grow a second label for the same class. It does not
    /// preserve the cached translate: the cache is keyed by module identity,
    /// and re-decomposition produces a fresh module value that misses.
    fn resolve_indices(
        &mut self,
        decomposition: &BasicDecomposition,
        preferred: Option<usize>,
    ) -> Vec<usize> {
        let mut preferred = preferred;
        let mut out = Vec::with_capacity(decomposition.len());
        for x in decomposition.summands() {
            if let Some(index) = self.registry.lookup(x, &mut self.ledger) {
                out.push(index);
                continue;
            }
            let index = preferred.take().unwrap_or_else(|| self.registry.fresh());
            self.registry.insert(index, x.module().clone());
            out.push(index);
        }
        out
    }

    /// Classifies `(module, support)` and pushes it as a further vertex.
    fn push_vertex(
        &mut self,
        module: BasicDecomposition,
        support: ProjectiveSupport,
        preferred: Option<usize>,
    ) -> Result<Result<usize, Stop>, GraphError> {
        let summands = module.len();
        let n = self.quiver_vertices();
        let scale = scale_of(module.module().dim_vector());
        self.ledger.charge(vertex_units(summands, scale));
        let indices = self.resolve_indices(&module, preferred);
        let misses = self.cache.misses();
        let classification = SupportTauTiltingPair::classify_with_cache(
            module,
            support,
            &indices,
            Some(&mut self.cache),
        );
        self.charge_tau(misses, scale);
        let classification = match classification {
            Ok(classification) => classification,
            Err(error) => {
                if let Some(reason) = support_blocker(&error) {
                    return Ok(Err(Stop::Blocked(reason)));
                }
                return Err(error.into());
            }
        };
        let pair = match classification {
            SupportTauTiltingClassification::Pair(pair) => pair,
            SupportTauTiltingClassification::Rejected(rejection) => {
                return Err(defect(format!(
                    "a mutation target left condition {} unmet: {rejection}",
                    rejection.condition()
                )));
            }
        };
        self.ledger.charge(fingerprint_units(summands, n, scale));
        let fingerprint = PairFingerprint::new(pair.module(), &pair.projective())?;
        let index = self.vertices.len();
        self.buckets
            .entry(fingerprint.clone())
            .or_default()
            .push(index);
        self.fingerprints.push(fingerprint);
        self.indices.push(indices);
        self.total_slots += summands;
        self.vertices.push(GraphVertex {
            pair,
            slots: Vec::with_capacity(summands),
        });
        self.queue.push_back(index);
        Ok(Ok(index))
    }

    /// The vertex isomorphic to `pair`, with the witness, or `None`.
    ///
    /// The fingerprint buckets the candidates and [`pair_iso`] decides. A
    /// fingerprint match is inconclusive, so the certified test always runs.
    fn find_vertex(
        &mut self,
        pair: &SupportTauTiltingPair,
    ) -> Result<Option<(usize, SupportPairIsoWitness)>, GraphError> {
        let summands = pair.module().len();
        let scale = scale_of(pair.module().module().dim_vector());
        self.ledger
            .charge(fingerprint_units(summands, self.quiver_vertices(), scale));
        let fingerprint = PairFingerprint::new(pair.module(), &pair.projective())?;
        let Some(bucket) = self.buckets.get(&fingerprint) else {
            return Ok(None);
        };
        let bucket = bucket.clone();
        for candidate in bucket {
            self.ledger.charge(iso_units(summands, scale));
            let vertex = &self.vertices[candidate];
            match pair_iso(
                pair.module(),
                &pair.projective(),
                vertex.pair.module(),
                &vertex.pair.projective(),
            )? {
                SupportPairIsoOutcome::Isomorphic(witness) => {
                    return Ok(Some((candidate, witness)));
                }
                SupportPairIsoOutcome::NotIsomorphic(_) => {}
            }
        }
        Ok(None)
    }

    /// Whether the Hom system of the `Fac` test at this slot fits in
    /// `max_matrix_entries`, checked before the mutation layer allocates it.
    ///
    /// The system is `Hom(U, X_j)`, with `sum_v dim U_v dim X_v` unknowns, and
    /// it is the widest one the slot allocates among those the walk can size
    /// ahead of the call: every approximation system `Hom(X_j, U_i)` has at
    /// most as many unknowns, since `U_i` is a summand of `U`. The systems
    /// `Hom(X_i, tau X_j)` are not covered, because `tau X_j` is not known
    /// before it is computed.
    fn fac_system_fits(&self, vertex: usize, slot: usize) -> bool {
        let summands = self.vertices[vertex].pair.module().summands();
        let x = summands[slot].module().dim_vector();
        let mut kept = vec![0usize; x.len()];
        for (i, other) in summands.iter().enumerate() {
            if i == slot {
                continue;
            }
            for (entry, dim) in kept.iter_mut().zip(other.module().dim_vector()) {
                *entry += dim;
            }
        }
        hom_entries(&kept, x) <= self.limits.max_matrix_entries
    }

    /// Visits one slot of one vertex.
    fn visit_slot(&mut self, vertex: usize, slot: usize) -> Result<Option<Stop>, GraphError> {
        self.at_vertex = vertex;
        self.at_slot = Some(slot);
        let summands = self.vertices[vertex].pair.module().len();
        let scale = scale_of(self.vertices[vertex].pair.module().module().dim_vector());
        if !self.fac_system_fits(vertex, slot) {
            return Ok(Some(Stop::Budget(GraphLimit::MatrixEntries)));
        }
        // The charge for a left mutation covers the Fac branch, so the check
        // runs before the branch is known.
        if self.ledger.would_exceed(
            slot_units(summands, true, scale),
            self.limits.max_work_units,
        ) {
            return Ok(Some(Stop::Budget(GraphLimit::WorkUnits)));
        }
        let fresh = self.registry.fresh();
        let indices = self.indices[vertex].clone();
        let misses = self.cache.misses();
        let outcome = mutate_at_with_cache(
            &self.vertices[vertex].pair,
            slot,
            &indices,
            fresh,
            Some(&mut self.cache),
        );
        self.charge_tau(misses, scale);
        let outcome = match outcome {
            Ok(outcome) => outcome,
            Err(error) => {
                if let Some(reason) = mutation_blocker(&error) {
                    return Ok(Some(Stop::Blocked(reason)));
                }
                return Err(error.into());
            }
        };
        let mutation = match outcome {
            SlotOutcome::NoLeftMutation(witness) => {
                self.ledger.charge(slot_units(summands, false, scale));
                self.vertices[vertex]
                    .slots
                    .push(SlotRecord::NoLeftMutation(witness));
                self.verified_slots += 1;
                return Ok(None);
            }
            SlotOutcome::LeftMutation(mutation) => mutation,
        };
        self.ledger.charge(slot_units(summands, true, scale));
        if self.mutations.len() >= self.limits.max_directed_mutations {
            return Ok(Some(Stop::Budget(GraphLimit::DirectedMutations)));
        }
        let (target, endpoint) = match self.find_vertex(mutation.target())? {
            Some((index, witness)) => {
                self.repeated_endpoints += 1;
                (index, witness)
            }
            None => {
                if self.vertices.len() >= self.limits.max_vertices {
                    return Ok(Some(Stop::Budget(GraphLimit::Vertices)));
                }
                // The target pair is rebuilt over the same module value, so
                // the vertex is decomposed and classified on its own rather
                // than inheriting the mutation's decomposition. Reusing the
                // target's `BasicDecomposition` would still reclassify it in
                // `push_vertex`, so it is not known to break the certificate;
                // it would make the `pair_iso` below an identity check rather
                // than a comparison of two separately built values. Measured
                // at roughly 3 percent of the walk. Deferred rather than
                // taken, so the endpoint binding stays the weaker and more
                // independent of the two.
                let module = BasicDecomposition::new(mutation.target().module().module())?;
                let support = ProjectiveSupport::new(
                    &self.algebra,
                    mutation.target().projective().vertices(),
                )?;
                // The mutation already spent `fresh` on the cokernel summand,
                // so the rebuilt vertex reuses that index and the registry
                // keeps one label per isomorphism class. The translate is
                // recomputed regardless, since the rebuilt module is a fresh
                // value under the identity key.
                let preferred = mutation.witness().replacement().map(|_| fresh);
                let index = match self.push_vertex(module, support, preferred)? {
                    Ok(index) => index,
                    Err(stop) => return Ok(Some(stop)),
                };
                self.new_vertices += 1;
                self.ledger.charge(iso_units(
                    mutation.target().module().len(),
                    scale_of(mutation.target().module().module().dim_vector()),
                ));
                let witness = match pair_iso(
                    mutation.target().module(),
                    &mutation.target().projective(),
                    self.vertices[index].pair.module(),
                    &self.vertices[index].pair.projective(),
                )? {
                    SupportPairIsoOutcome::Isomorphic(witness) => witness,
                    SupportPairIsoOutcome::NotIsomorphic(obstruction) => {
                        return Err(defect(format!(
                            "the rebuilt vertex is not isomorphic to the mutation target: \
                             {obstruction:?}"
                        )));
                    }
                };
                (index, witness)
            }
        };
        let edge = self.mutations.len();
        self.mutations.push(VerifiedMutation {
            source: vertex,
            slot,
            target,
            mutation: *mutation,
            endpoint,
        });
        self.vertices[vertex]
            .slots
            .push(SlotRecord::LeftMutation { mutation: edge });
        self.verified_slots += 1;
        Ok(None)
    }

    /// The stop for a ledger already past `max_work_units`, or `None`.
    ///
    /// The precheck in [`Walk::visit_slot`] reserves that slot's own model and
    /// nothing else. The graph layer charges the tau misses, the fingerprint,
    /// the isomorphism tests, and a new vertex after the reservation, so a walk
    /// whose queue holds no further slot needs this check to stay inside the
    /// budget. Without it the one-vertex algebra closes over its ceiling: its
    /// only slot lands on `(0, A)`, which has no slot to precheck.
    fn over_work_budget(&self) -> Option<Stop> {
        if self.ledger.units > self.limits.max_work_units {
            Some(Stop::Budget(GraphLimit::WorkUnits))
        } else {
            None
        }
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

/// Gates a drained walk on the closure recheck, then wraps it as closed.
///
/// The recheck runs before the value exists, so no
/// [`ClosedSupportTauTiltingGraph`] can be handed out whose own
/// [`ClosedSupportTauTiltingGraph::verify`] returns false, in Rust or through
/// the Python bindings. A drained frontier alone says the builder found a
/// branch at every slot and placed every target. It does not say the seven
/// obligations of [`ClosureWitness::verify`] hold, which is a separate recheck
/// of the stored pairs and maps.
///
/// The recheck is the slower half of a closing walk; the module documentation
/// gives the D_4 figures. There is no flag to skip it.
///
/// # Errors
/// [`GraphError::Defect`] when the recheck fails. That contradicts a theorem
/// whose hypotheses hold, so it is a defect rather than a truncation, and the
/// partial graph is not offered as a result.
fn close(
    algebra: &Arc<Algebra>,
    vertices: Vec<GraphVertex>,
    mutations: Vec<VerifiedMutation>,
    work_units: u64,
) -> Result<ClosedSupportTauTiltingGraph, GraphError> {
    let witness = ClosureWitness {
        algebra: algebra.clone(),
        vertices,
        mutations,
    };
    if !witness.verify() {
        return Err(defect(
            "the walk drained its frontier and the closure recheck failed".to_string(),
        ));
    }
    Ok(ClosedSupportTauTiltingGraph {
        witness,
        work_units,
    })
}

/// Walks the support tau-tilting quiver of `algebra` from `(A, 0)`, closing
/// under left mutation.
///
/// The walk is breadth first: vertices take indices in discovery order, and
/// the slots of a vertex are visited in increasing order. One [`TauCache`] is
/// shared across the run, keyed by nominal module identity, so `tau` runs once
/// per summand value and never on an assembled module.
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{
        kronecker, linear_an, linear_nakayama, radical_square_zero_cycle, truncated_poly,
    };
    use crate::arquiver::IndecomposableCatalog;
    use crate::dynkin::{DynkinType, dynkin_quiver};
    use crate::field::PrimeField;
    use crate::quiver::Quiver;
    use crate::supporttau::enumerate_over_catalog;

    fn f2() -> PrimeField {
        PrimeField::new(2).unwrap()
    }

    fn f5() -> PrimeField {
        PrimeField::new(5).unwrap()
    }

    fn fields() -> [PrimeField; 2] {
        [f2(), f5()]
    }

    fn path_algebra(quiver: Quiver, field: PrimeField) -> Arc<Algebra> {
        crate::algebra::path_algebra(quiver, field)
            .expect("the zero ideal over an acyclic quiver completes")
    }

    fn semisimple(n: u32, field: PrimeField) -> Arc<Algebra> {
        path_algebra(
            Quiver::new(n, &[]).expect("no arrow is out of range"),
            field,
        )
    }

    // D_4 as dynkin_quiver builds it: vertex 0 is the center, arrows 0 -> 1,
    // 0 -> 2, 0 -> 3.
    fn d4(field: PrimeField) -> Arc<Algebra> {
        path_algebra(
            dynkin_quiver(DynkinType::D(4)).expect("D_4 has a quiver"),
            field,
        )
    }

    fn walk(algebra: &Arc<Algebra>) -> ClosedSupportTauTiltingGraph {
        let outcome = support_tau_tilting_graph(algebra, &MutationGraphLimits::default())
            .expect("the fixture walks without a defect");
        match outcome {
            SupportTauTiltingGraphOutcome::Closed(graph) => graph,
            SupportTauTiltingGraphOutcome::Incomplete(graph) => {
                panic!("the walk stopped short: {}", graph.reason())
            }
        }
    }

    /// The catalog fixtures both routes run over, in one order.
    ///
    /// Every entry has an exhaustive [`IndecomposableCatalog`], so the second
    /// route can enumerate it from the definition. The list matches the one
    /// `supporttau` uses, so the two routes cover the same domains.
    fn catalog_fixtures(field: PrimeField) -> Vec<(String, Arc<Algebra>, IndecomposableCatalog)> {
        let modulus = field.modulus();
        let mut out = Vec::new();
        for n in [2u32, 3, 4] {
            let algebra = semisimple(n, field);
            let catalog =
                IndecomposableCatalog::nakayama(&algebra).expect("no arrow means Nakayama");
            out.push((
                format!("semisimple({n}) over F_{modulus}"),
                algebra,
                catalog,
            ));
        }
        for n in [2usize, 3] {
            let algebra = linear_an(n, field);
            let catalog = IndecomposableCatalog::dynkin(&algebra).expect("A_n is Dynkin");
            out.push((format!("linear_an({n}) over F_{modulus}"), algebra, catalog));
        }
        let tp = truncated_poly(3, field).expect("k[x]/(x^3) is admissible");
        let catalog = IndecomposableCatalog::nakayama(&tp).expect("one loop is Nakayama");
        out.push((format!("truncated_poly(3) over F_{modulus}"), tp, catalog));
        let cycle = radical_square_zero_cycle(3, field);
        let catalog = IndecomposableCatalog::nakayama(&cycle).expect("a cycle is Nakayama");
        out.push((
            format!("radical_square_zero_cycle(3) over F_{modulus}"),
            cycle,
            catalog,
        ));
        let nakayama = linear_nakayama(&[2, 2, 1], field).expect("[2, 2, 1] is a Kupisch series");
        let catalog =
            IndecomposableCatalog::nakayama(&nakayama).expect("a linear quiver is Nakayama");
        out.push((
            format!("linear_nakayama([2, 2, 1]) over F_{modulus}"),
            nakayama,
            catalog,
        ));
        out
    }

    /// Whether every pair of `left` has a partner in `right` and back, matched
    /// by [`pair_iso`].
    ///
    /// Both lists are pairwise non-isomorphic, so a pair matches at most one
    /// partner and the greedy scan decides set equality.
    fn same_pair_set(left: &[&SupportTauTiltingPair], right: &[&SupportTauTiltingPair]) -> bool {
        if left.len() != right.len() {
            return false;
        }
        let mut used = vec![false; right.len()];
        for a in left {
            let mut matched = false;
            for (j, b) in right.iter().enumerate() {
                if used[j] {
                    continue;
                }
                match pair_iso(a.module(), &a.projective(), b.module(), &b.projective())
                    .expect("both routes build pairs over one algebra")
                {
                    SupportPairIsoOutcome::Isomorphic(witness) => {
                        assert!(witness.verify(), "the matching isomorphism rechecks");
                        used[j] = true;
                        matched = true;
                        break;
                    }
                    SupportPairIsoOutcome::NotIsomorphic(_) => {}
                }
            }
            if !matched {
                return false;
            }
        }
        used.iter().all(|hit| *hit)
    }

    /// A normalized rendering of a closed graph, byte comparable across runs.
    fn render(graph: &ClosedSupportTauTiltingGraph) -> String {
        let mut out = String::new();
        for (v, vertex) in graph.vertices().iter().enumerate() {
            out.push_str(&format!(
                "v{v} {:?} p{:?}\n",
                vertex.pair().module().dim_vectors(),
                vertex.pair().projective().vertices()
            ));
            for (slot, record) in vertex.slots().iter().enumerate() {
                match record {
                    SlotRecord::LeftMutation { mutation } => {
                        out.push_str(&format!("  s{slot} -> e{mutation}\n"));
                    }
                    SlotRecord::NoLeftMutation(witness) => {
                        out.push_str(&format!(
                            "  s{slot} fac {:?} of {:?} maps {}\n",
                            witness.summand().dim_vector(),
                            witness.module().dim_vector(),
                            witness.maps().len()
                        ));
                    }
                }
            }
        }
        for (e, edge) in graph.mutations().iter().enumerate() {
            out.push_str(&format!(
                "e{e} {}:{} -> {} shape {:?} exchanged {:?} target {:?} bijection {:?}\n",
                edge.source(),
                edge.slot(),
                edge.target(),
                edge.mutation().shape(),
                edge.mutation().witness().exchanged().dim_vector(),
                edge.mutation().witness().target_module().dim_vector(),
                edge.endpoint().bijection()
            ));
        }
        out
    }

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
    /// stays because it asserts the public promise: a value of this type
    /// answers `true`, and it answers `true` on a second call.
    #[test]
    fn every_closed_graph_verifies_its_closure_witness() {
        for field in fields() {
            for (name, algebra, _) in catalog_fixtures(field) {
                let graph = walk(&algebra);
                assert!(graph.verify(), "{name}");
            }
        }
    }

    /// A budget equal to the true count still closes.
    ///
    /// `max_vertices` is checked when a further distinct vertex is inserted,
    /// so the fifth vertex of the A_2 pentagon fits into a budget of five.
    #[test]
    fn a_vertex_budget_equal_to_the_true_count_still_closes() {
        let limits = MutationGraphLimits {
            max_vertices: 5,
            ..MutationGraphLimits::default()
        };
        let outcome = support_tau_tilting_graph(&linear_an(2, f2()), &limits)
            .expect("A_2 walks without a defect");
        assert!(outcome.is_closed());
        assert_eq!(outcome.closed().expect("closed").len(), 5);

        let tight = MutationGraphLimits {
            max_vertices: 4,
            ..MutationGraphLimits::default()
        };
        let outcome = support_tau_tilting_graph(&linear_an(2, f2()), &tight)
            .expect("A_2 walks without a defect");
        let graph = outcome.incomplete().expect("four vertices are one too few");
        match graph.reason() {
            IncompleteReason::BudgetExhausted(diagnostics) => {
                assert_eq!(diagnostics.limit(), GraphLimit::Vertices);
            }
            IncompleteReason::CertificationBlocked(blocker) => {
                panic!("a vertex budget is no blocked certification: {blocker}")
            }
        }
    }

    /// The Kronecker algebra is tau-tilting infinite, so the walk truncates
    /// rather than closing or hanging.
    ///
    /// The descending walk leaves `(A, 0)` down the preprojective ray
    /// `(m, m + 1) + (m + 1, m + 2)`, which never ends. The result is a typed
    /// budget diagnostic, never a completeness claim, and the vertices it did
    /// reach stay individually certified.
    #[test]
    fn the_kronecker_walk_truncates_with_a_typed_budget() {
        let limits = MutationGraphLimits {
            max_vertices: 16,
            ..MutationGraphLimits::default()
        };
        let outcome = support_tau_tilting_graph(&kronecker(2, f2()), &limits)
            .expect("the Kronecker walk runs without a defect");
        assert!(!outcome.is_closed());
        let graph = outcome.incomplete().expect("the walk stopped short");
        let diagnostics = match graph.reason() {
            IncompleteReason::BudgetExhausted(diagnostics) => diagnostics,
            IncompleteReason::CertificationBlocked(blocker) => {
                panic!("the Kronecker walk certifies every step it takes: {blocker}")
            }
        };
        assert_eq!(diagnostics.limit(), GraphLimit::Vertices);
        assert_eq!(diagnostics.vertices_found(), 16);
        assert_eq!(graph.vertices_found().len(), 16);
        assert!(diagnostics.open_slots() > 0);
        assert!(diagnostics.work_units() > 0);
        // Every vertex the walk did reach stays certified on its own.
        // Rechecking the mutations as well costs 183 ms, so
        // `the_kronecker_mutations_recheck` carries that part.
        for vertex in graph.vertices_found() {
            assert!(vertex.pair().verify());
            assert_eq!(vertex.pair().summand_count(), 2);
        }
        // The bias is structural: every module part the walk reached is
        // preprojective, of dimension vector (m, m + 1), so no preinjective
        // vertex is in the sample.
        for vertex in graph.vertices_found() {
            for summand in vertex.pair().module().summands() {
                let dim = summand.module().dim_vector();
                assert!(dim[0] <= dim[1], "a preinjective summand {dim:?} appeared");
            }
        }
    }

    /// The work-unit counts, asserted against ceilings of about twice the
    /// measured count rounded up to a power of two.
    ///
    /// | fixture | measured | ceiling | before the size factor |
    /// | --- | --- | --- | --- |
    /// | A_2 | 6668 | 16384 | 1416 |
    /// | A_3 | 145712 | 524288 | 12895 |
    /// | A_4 | 2253257 | 8388608 | 107808 |
    /// | D_4 | 3951020 | 8388608 | 140428 |
    ///
    /// The last column is the count before every rate gained the size factor
    /// `e`, which is where most of the rise comes from: `e` grows with the
    /// modules the walk carries. The rest is later work in the layers below,
    /// which moves the `tau` miss count the ledger reads. Neither changes what
    /// the walk does, and each ceiling is about twice its measured count, so a
    /// count that drifts does not fail this test.
    ///
    /// The counts are charged by call and by module size, so they do not move
    /// with the profile or the platform.
    #[test]
    fn the_work_unit_counts_stay_under_their_ceilings() {
        let cases: [(&str, Arc<Algebra>, u64); 4] = [
            ("A_2", linear_an(2, f2()), 16_384),
            ("A_3", linear_an(3, f2()), 524_288),
            ("A_4", linear_an(4, f2()), 8_388_608),
            ("D_4", d4(f2()), 8_388_608),
        ];
        for (name, algebra, ceiling) in cases {
            let graph = walk(&algebra);
            assert!(
                graph.work_units() <= ceiling,
                "{name}: {} units over the ceiling {ceiling}",
                graph.work_units()
            );
        }
        // The ledger counts calls, and the call sequence does not depend on
        // the field, so A_3 charges the same over F_2 and F_5.
        assert_eq!(
            walk(&linear_an(3, f2())).work_units(),
            walk(&linear_an(3, f5())).work_units()
        );
    }

    /// The A_2 pentagon, vertex by vertex.
    ///
    /// The math spike computes every step of this graph by hand (section 3.2).
    /// `P_1 = (1, 1)`, `P_2 = S_2 = (0, 1)`, `S_1 = (1, 0)`, and the five pairs
    /// are `(P_1 + P_2, 0)`, `(P_1 + S_1, 0)`, `(S_1, P_2)`, `(S_2, P_1)`, and
    /// `(0, P_1 + P_2)`. The walk leaves `(A, 0)` twice: at `P_2` the minimal
    /// left `add(P_1)`-approximation is the socle inclusion `S_2 -> P_1` with
    /// cokernel `S_1`, giving `(P_1 + S_1, 0)`; at `P_1` the support drops
    /// vertex 1, giving `(S_2, P_1)`. Exactly one module slot has no left
    /// mutation: `S_1` in `(P_1 + S_1, 0)` is the top of `P_1`, so it lies in
    /// `Fac(P_1)` and that slot is a right mutation.
    ///
    /// The undirected graph is the pentagon, 2-regular on 5 vertices with 5
    /// edges, which is the exchange graph of the type A_2 cluster algebra.
    #[test]
    fn the_a2_walk_is_the_pentagon() {
        for field in fields() {
            let graph = walk(&linear_an(2, field));
            assert_eq!(graph.len(), 5);
            assert_eq!(graph.mutations().len(), 5);
            let mut parts: Vec<(Vec<Vec<usize>>, Vec<u32>)> = graph
                .pairs()
                .map(|pair| {
                    (
                        pair.module().dim_vectors(),
                        pair.projective().vertices().to_vec(),
                    )
                })
                .collect();
            parts.sort();
            assert_eq!(
                parts,
                vec![
                    (vec![], vec![0, 1]),
                    (vec![vec![0, 1]], vec![0]),
                    (vec![vec![0, 1], vec![1, 1]], vec![]),
                    (vec![vec![1, 0]], vec![1]),
                    (vec![vec![1, 0], vec![1, 1]], vec![]),
                ]
            );
            let fac: Vec<&FacWitness> = graph
                .vertices()
                .iter()
                .flat_map(|vertex| vertex.slots())
                .filter_map(SlotRecord::fac_witness)
                .collect();
            assert_eq!(fac.len(), 1);
            assert_eq!(fac[0].summand().dim_vector(), [1, 0]);
            assert_eq!(fac[0].module().dim_vector(), [1, 1]);
            // (A, 0) is the maximum, so both its slots mutate out and nothing
            // mutates into it. (0, A) is the minimum: no module slot at all.
            assert_eq!(graph.vertices()[0].slots().len(), 2);
            let minima = graph
                .vertices()
                .iter()
                .filter(|vertex| vertex.pair().module().is_empty())
                .count();
            assert_eq!(minima, 1);
            assert!(graph.mutations().iter().all(|edge| edge.target() != 0));
        }
    }

    /// The same algebra walked twice gives the same vertex order, the same
    /// edge order, and the same stored witnesses.
    #[test]
    fn two_runs_agree_on_order_and_witnesses() {
        for field in fields() {
            for algebra in [linear_an(3, field), radical_square_zero_cycle(3, field)] {
                let first = walk(&algebra);
                let second = walk(&algebra);
                assert_eq!(render(&first), render(&second));
                assert_eq!(first.work_units(), second.work_units());
            }
        }
    }

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
        assert_eq!(reachable_from_root(graph.len(), &all), graph.len());
        let cut: Vec<(usize, usize)> = all
            .iter()
            .copied()
            .filter(|(source, _)| *source != 0)
            .collect();
        assert!(reachable_from_root(graph.len(), &cut) < graph.len());
        assert_eq!(reachable_from_root(graph.len(), &[]), 1);
    }

    /// A Hom system wider than `max_matrix_entries` stops the walk before the
    /// allocation.
    #[test]
    fn a_matrix_budget_stops_the_walk_before_allocating() {
        let limits = MutationGraphLimits {
            max_matrix_entries: 1,
            ..MutationGraphLimits::default()
        };
        let outcome = support_tau_tilting_graph(&linear_an(3, f2()), &limits)
            .expect("A_3 walks without a defect");
        let graph = outcome.incomplete().expect("the budget stops the walk");
        match graph.reason() {
            IncompleteReason::BudgetExhausted(diagnostics) => {
                assert_eq!(diagnostics.limit(), GraphLimit::MatrixEntries);
            }
            IncompleteReason::CertificationBlocked(blocker) => {
                panic!("a matrix budget is no blocked certification: {blocker}")
            }
        }
    }

    /// A work-unit budget below the first step stops the walk with the typed
    /// limit.
    #[test]
    fn a_work_unit_budget_stops_the_walk() {
        let limits = MutationGraphLimits {
            max_work_units: 1,
            ..MutationGraphLimits::default()
        };
        let outcome = support_tau_tilting_graph(&linear_an(3, f2()), &limits)
            .expect("A_3 walks without a defect");
        let graph = outcome.incomplete().expect("the budget stops the walk");
        match graph.reason() {
            IncompleteReason::BudgetExhausted(diagnostics) => {
                assert_eq!(diagnostics.limit(), GraphLimit::WorkUnits);
                assert_eq!(diagnostics.vertices_found(), 1);
                assert_eq!(diagnostics.verified_slots(), 0);
            }
            IncompleteReason::CertificationBlocked(blocker) => {
                panic!("a work budget is no blocked certification: {blocker}")
            }
        }
    }

    /// A closed walk never charges more work units than its budget.
    ///
    /// The one-vertex algebra is the minimal case. `(A, 0)` has one slot and
    /// its left mutation lands on `(0, A)`, which has no slot at all, so the
    /// charges the walk makes after the slot precheck (the fingerprint, the
    /// isomorphism test, the new vertex) had no later precheck to catch them.
    /// Every budget from one unit up to the true count must truncate.
    #[test]
    fn a_closed_walk_never_charges_more_than_its_budget() {
        let algebra = semisimple(1, f2());
        let spent = walk(&algebra).work_units();
        for max_work_units in 1..spent {
            let limits = MutationGraphLimits {
                max_work_units,
                ..MutationGraphLimits::default()
            };
            let outcome = support_tau_tilting_graph(&algebra, &limits)
                .expect("the one-vertex walk runs without a defect");
            match outcome {
                SupportTauTiltingGraphOutcome::Closed(graph) => panic!(
                    "a budget of {max_work_units} closed at {} units",
                    graph.work_units()
                ),
                SupportTauTiltingGraphOutcome::Incomplete(graph) => match graph.reason() {
                    IncompleteReason::BudgetExhausted(diagnostics) => {
                        assert_eq!(diagnostics.limit(), GraphLimit::WorkUnits);
                    }
                    IncompleteReason::CertificationBlocked(blocker) => {
                        panic!("a work budget is no blocked certification: {blocker}")
                    }
                },
            }
        }
        // The true count still closes, so the gate is not off by one.
        let limits = MutationGraphLimits {
            max_work_units: spent,
            ..MutationGraphLimits::default()
        };
        let outcome = support_tau_tilting_graph(&algebra, &limits)
            .expect("the one-vertex walk runs without a defect");
        assert_eq!(
            outcome
                .closed()
                .expect("the true count closes")
                .work_units(),
            spent
        );
    }

    /// A mutation budget stops the walk when the next edge would exceed it.
    #[test]
    fn a_mutation_budget_stops_the_walk() {
        let limits = MutationGraphLimits {
            max_directed_mutations: 2,
            ..MutationGraphLimits::default()
        };
        let outcome = support_tau_tilting_graph(&linear_an(3, f2()), &limits)
            .expect("A_3 walks without a defect");
        let graph = outcome.incomplete().expect("the budget stops the walk");
        assert_eq!(graph.verified_mutations().len(), 2);
        match graph.reason() {
            IncompleteReason::BudgetExhausted(diagnostics) => {
                assert_eq!(diagnostics.limit(), GraphLimit::DirectedMutations);
            }
            IncompleteReason::CertificationBlocked(blocker) => {
                panic!("a mutation budget is no blocked certification: {blocker}")
            }
        }
    }

    /// An undetermined split or an undecided `tau` cross-check reads as a
    /// blocked certification, and a rejected input does not.
    ///
    /// No fixture in the suite produces either, since every split and every
    /// `tau` cross-check the walk runs certifies. The classification is tested
    /// here on constructed errors so the branch is covered: a blocked
    /// certification must reach [`IncompleteReason::CertificationBlocked`] and
    /// never [`IncompleteReason::BudgetExhausted`].
    #[test]
    fn blocked_certifications_never_read_as_budget_exhaustion() {
        let algebra = linear_an(2, f2());
        let blocked = BasicError::CertificationBlocked {
            reason: "a summand stayed undetermined after 8 split attempts".to_string(),
        };
        assert!(basic_blocker(&blocked).is_some());
        assert!(mutation_blocker(&MutationError::Basic(blocked.clone())).is_some());
        assert!(support_blocker(&SupportTauError::Basic(blocked)).is_some());
        assert!(
            mutation_blocker(&MutationError::Indec(IndecError::Undetermined {
                attempts: 8
            }))
            .is_some()
        );
        let undecided = SupportTauError::TauRigid(TauRigidError::Tau(TauError::AgreementUnknown {
            nakayama_kernel: Module::zero(&algebra),
            transpose_dual: Module::zero(&algebra),
            reason: "an undetermined summand".to_string(),
        }));
        assert!(support_blocker(&undecided).is_some());
        assert!(mutation_blocker(&MutationError::SupportTau(undecided)).is_some());
        // A rejected slot index is bad input, not a blocked certification.
        assert!(
            mutation_blocker(&MutationError::SlotOutOfRange {
                slot: 4,
                summands: 2
            })
            .is_none()
        );
        assert!(
            basic_blocker(&BasicError::NotBasic {
                first: 0,
                second: 1
            })
            .is_none()
        );
    }

    /// The Kronecker walk's mutations recheck.
    ///
    /// Ignored: rechecking the 16 mutations costs 183 ms in the dev profile,
    /// which is the exhaustive tier of `docs/v0.5-design.md` section 11. The
    /// always-on `the_kronecker_walk_truncates_with_a_typed_budget` rechecks
    /// the vertices.
    #[test]
    #[ignore = "exhaustive tier of docs/v0.5-design.md section 11"]
    fn the_kronecker_mutations_recheck() {
        let limits = MutationGraphLimits {
            max_vertices: 16,
            ..MutationGraphLimits::default()
        };
        let outcome = support_tau_tilting_graph(&kronecker(2, f2()), &limits)
            .expect("the Kronecker walk runs without a defect");
        let graph = outcome.incomplete().expect("the walk stopped short");
        assert!(graph.verify_parts());
    }

    /// The D_4 closure witness rechecks, and the D_4 walk agrees with the
    /// catalog route.
    ///
    /// Ignored: the walk, the gate's recheck, the second recheck here, and the
    /// catalog route cost more than a tenth of a second per field in the dev
    /// profile, which is the exhaustive tier of `docs/v0.5-design.md` section
    /// 11 rather than the always-on tier.
    #[test]
    #[ignore = "exhaustive tier of docs/v0.5-design.md section 11"]
    fn the_d4_closure_witness_and_the_catalog_route_agree() {
        for field in fields() {
            let algebra = d4(field);
            let graph = walk(&algebra);
            assert!(graph.verify());
            let catalog = IndecomposableCatalog::dynkin(&algebra).expect("D_4 is Dynkin");
            let enumeration = enumerate_over_catalog(&catalog).expect("the catalog route runs");
            let walked: Vec<&SupportTauTiltingPair> = graph.pairs().collect();
            let listed: Vec<&SupportTauTiltingPair> = enumeration.pairs().iter().collect();
            assert!(same_pair_set(&walked, &listed));
            assert!(same_pair_set(&listed, &walked));
        }
    }
}

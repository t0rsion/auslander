//! Left mutation of a support tau-tilting pair at a module summand slot.
//!
//! A vertex is a pair `(M, P)` with module summands `X_1, ..., X_m`. Slot `j`
//! addresses `X_j`. Only module summands have slots. Mutation at a summand of
//! the projective part is always a right mutation, so a walk that descends
//! from `(A, 0)` never performs one; `docs/v0.5-design.md` section 8 records
//! that as a deviation from the earlier signed-slot design.
//!
//! Exactly one of two branches holds at a slot, and [`mutate_at`] decides
//! which by computation, never by guessing.
//!
//! 1. `X_j` lies in `Fac(M/X_j)`. The mutation at slot `j` is then a right
//!    mutation and there is no left mutation. [`FacWitness`] proves the
//!    membership by one rank comparison per vertex.
//! 2. Otherwise the left mutation exists. [`Mutation`] carries the target pair
//!    and a [`MutationWitness`].
//!
//! # Adjacency is proved theorem-level
//!
//! The construction does not prove that the built pair is the mutation. The
//! proof runs through the almost complete pair:
//!
//! 1. `(U, Q) = (M/X_j, P)` is an almost complete support tau-tilting pair,
//!    certified by [`AlmostCompletePair`].
//! 2. `(M, P)` extends `(U, Q)`.
//! 3. `(M', P')` extends `(U, Q)`.
//! 4. The two completions are not isomorphic.
//! 5. `(M', P')` is a support tau-tilting pair, certified by
//!    [`SupportTauTiltingPair`].
//!
//! An almost complete support tau-tilting pair is a direct summand of exactly
//! two basic support tau-tilting pairs (Adachi, Iyama, and Reiten,
//! "tau-tilting theory", Compositio Math. 150 (2014), 415-452, Theorem 2.18,
//! two complements). With the five checks above, that theorem identifies
//! `(M', P')` as the mutation at slot `j`, and the `Fac` test of branch 1
//! identifies the direction (same paper, Definition-Proposition 2.28, and
//! Proposition 2.22: exactly one of `X in Fac U` and the containment
//! `perp(tau U) is inside perp(tau X)` holds).
//!
//! The theorem holds over an arbitrary field. Its hypothesis reads "let
//! `Lambda` be a finite dimensional `k`-algebra", and the algebraically closed
//! hypothesis of the paper's introduction is re-imposed at the head of section
//! 5, which would be pointless if it were already in force. Demonet, Iyama,
//! and Jasso, "tau-tilting finite algebras, bricks and g-vectors"
//! (arXiv:1503.00285), restate the same result over an arbitrary field for
//! right modules, which is this crate's setting. See
//! `docs/v0.5-design.md` section 8.
//!
//! The exchange sequence `X_j -> B -> Y -> 0` is stored as a construction
//! witness. It records how the target was built and it is not the proof of
//! adjacency.
//!
//! # Degenerate outputs are typed
//!
//! The two shapes of a left mutation are [`ExchangeShape`], and the
//! construction decides between them by comparing supports, as in AIR Theorem
//! 2.30(a) and (b):
//!
//! - `supp(U)` is smaller than `supp(M)`: the cokernel is zero, `X_j` leaves
//!   the module part, and the one vertex of `supp(M) \ supp(U)` joins the
//!   projective support.
//! - `supp(U)` equals `supp(M)`: the cokernel is a sum of copies of one
//!   indecomposable `Y_1`, and `M' = U + Y_1` with the projective support
//!   unchanged.
//!
//! Neither shape is an error, and neither is silent.

use std::fmt;
use std::sync::Arc;

use crate::approx::{ApproxError, MinimalLeftApproximation, left_approximation};
use crate::basic::{
    AddClosureWitness, BasicDecomposition, BasicError, ProjectiveSupport, SupportPairIsoOutcome,
    SupportPairObstruction, pair_iso,
};
use crate::decompose::{Certificate, decompose};
use crate::field::Fp;
use crate::hom::{HomError, Morphism, cokernel, hom};
use crate::indec::{IndecError, IndecomposableModule};
use crate::iso::indecomposable_iso;
use crate::linalg::DenseMat;
use crate::module::{Module, direct_sum};
use crate::quiver::ArrowId;
use crate::supporttau::{
    AlmostCompleteClassification, AlmostCompletePair, PairRejection, SupportTauError,
    SupportTauTiltingClassification, SupportTauTiltingPair,
};
use crate::taurigid::TauCache;

/// Which end of a mutation edge a report is about.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Endpoint {
    /// The pair the mutation starts from.
    Source,
    /// The pair the mutation lands on.
    Target,
}

impl fmt::Display for Endpoint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Source => f.write_str("source"),
            Self::Target => f.write_str("target"),
        }
    }
}

/// A failed internal cross-check of the mutation layer.
///
/// Every variant signals a crate defect: the hypotheses of AIR Theorem 2.18 or
/// Theorem 2.30 hold on the input, and a consequence the code checked did not.
/// None of these is a statement about the input pair.
#[derive(Clone, Debug)]
pub enum MutationDefect {
    /// Dropping the slot summand left a pair that is not almost complete. A
    /// direct summand of a tau-rigid pair is tau-rigid, and the summand count
    /// drops by exactly one, so this cannot happen.
    AlmostCompleteRejected(PairRejection),
    /// The built pair failed a support tau-tilting condition. AIR Theorem 2.30
    /// says it is one.
    TargetRejected(PairRejection),
    /// `supp(M) \ supp(U)` has a size other than one. AIR's proof of Theorem
    /// 2.30(a) forces a singleton.
    DroppedVertexCount {
        /// The vertices of `supp(M)` that `supp(U)` misses.
        dropped: Vec<u32>,
    },
    /// `supp(U)` is smaller than `supp(M)` and the cokernel of the
    /// approximation is not zero, against AIR Theorem 2.30(a).
    CokernelNonzero {
        /// The dimension vector of the cokernel.
        dim_vector: Vec<usize>,
    },
    /// `supp(U)` equals `supp(M)` and the cokernel is zero, against AIR
    /// Theorem 2.30(b).
    CokernelZero,
    /// The cokernel summand at this position is not isomorphic to the first
    /// one. AIR Theorem 2.30(b) makes the cokernel a sum of copies of one
    /// indecomposable.
    CokernelSummandsDiffer {
        /// Position of the summand in decomposition order.
        summand: usize,
    },
    /// The cokernel summand is isomorphic to summand `summand` of `M`, against
    /// AIR Theorem 2.30(b), which puts `Y` outside `add(T)`.
    ReplacementRepeatsSummand {
        /// Position of the summand in the module part of the source pair.
        summand: usize,
    },
    /// `U` is not a direct summand of the named endpoint's module part.
    AddClosureMissing {
        /// Which endpoint failed.
        endpoint: Endpoint,
    },
    /// The named endpoint's projective support does not contain `Q`.
    ProjectiveSupportNotExtended {
        /// Which endpoint failed.
        endpoint: Endpoint,
    },
    /// The two completions of the almost complete pair are isomorphic, against
    /// AIR Theorem 2.18.
    EndpointsIsomorphic,
}

impl fmt::Display for MutationDefect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::AlmostCompleteRejected(rejection) => write!(
                f,
                "dropping the slot summand left condition {} unmet: {rejection}; crate defect",
                rejection.condition()
            ),
            Self::TargetRejected(rejection) => write!(
                f,
                "the built pair left condition {} unmet: {rejection}; crate defect",
                rejection.condition()
            ),
            Self::DroppedVertexCount { dropped } => write!(
                f,
                "dropping the slot summand lost {} vertices, not one; crate defect",
                dropped.len()
            ),
            Self::CokernelNonzero { dim_vector } => write!(
                f,
                "the approximation has cokernel of dimension vector {dim_vector:?} where the \
                 support test says zero; crate defect"
            ),
            Self::CokernelZero => f.write_str(
                "the approximation has zero cokernel where the support test says nonzero; \
                 crate defect",
            ),
            Self::CokernelSummandsDiffer { summand } => write!(
                f,
                "cokernel summand {summand} is not isomorphic to the first one; crate defect"
            ),
            Self::ReplacementRepeatsSummand { summand } => write!(
                f,
                "the cokernel summand repeats summand {summand} of the module part; crate defect"
            ),
            Self::AddClosureMissing { endpoint } => {
                write!(f, "the {endpoint} pair does not contain U; crate defect")
            }
            Self::ProjectiveSupportNotExtended { endpoint } => write!(
                f,
                "the {endpoint} projective support does not contain Q; crate defect"
            ),
            Self::EndpointsIsomorphic => {
                f.write_str("the two completions are isomorphic; crate defect")
            }
        }
    }
}

impl std::error::Error for MutationDefect {}

/// Rejected input, a blocked certification, or a failed internal cross-check
/// of the mutation layer.
///
/// A slot with no left mutation is no error. It comes back as
/// [`SlotOutcome::NoLeftMutation`] with its witness.
#[derive(Clone, Debug)]
pub enum MutationError {
    /// The slot index is not a module summand of the pair.
    SlotOutOfRange {
        /// The requested slot.
        slot: usize,
        /// `|M|`, the number of module summands.
        summands: usize,
    },
    /// The caller's index list and the module summands have different lengths.
    SummandIndexCount {
        /// Number of indices supplied.
        indices: usize,
        /// `|M|`, the number of module summands.
        summands: usize,
    },
    /// The basic layer rejected an input or could not certify a summand.
    Basic(BasicError),
    /// The support tau-tilting layer rejected an input or could not run a
    /// check.
    SupportTau(SupportTauError),
    /// The approximation layer rejected the add-generators of `U`.
    Approx(ApproxError),
    /// A Hom computation rejected its input.
    Hom(HomError),
    /// A cokernel summand failed the indecomposability gate.
    /// [`IndecError::Undetermined`] is a blocked certification, not budget
    /// exhaustion, and it must poison any completeness claim built on it.
    Indec(IndecError),
    /// An internal cross-check failed.
    Defect(MutationDefect),
}

impl fmt::Display for MutationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SlotOutOfRange { slot, summands } => write!(
                f,
                "slot {slot} is out of range, the module part has {summands} summands"
            ),
            Self::SummandIndexCount { indices, summands } => {
                write!(f, "{indices} summand indices for {summands} summands")
            }
            Self::Basic(error) => write!(f, "basic layer: {error}"),
            Self::SupportTau(error) => write!(f, "support tau-tilting layer: {error}"),
            Self::Approx(error) => write!(f, "approximation layer: {error}"),
            Self::Hom(error) => write!(f, "hom: {error}"),
            Self::Indec(error) => write!(f, "cokernel summand: {error}"),
            Self::Defect(defect) => write!(f, "{defect}"),
        }
    }
}

impl std::error::Error for MutationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Basic(error) => Some(error),
            Self::SupportTau(error) => Some(error),
            Self::Approx(error) => Some(error),
            Self::Hom(error) => Some(error),
            Self::Indec(error) => Some(error),
            Self::Defect(defect) => Some(defect),
            Self::SlotOutOfRange { .. } | Self::SummandIndexCount { .. } => None,
        }
    }
}

impl From<BasicError> for MutationError {
    fn from(error: BasicError) -> MutationError {
        MutationError::Basic(error)
    }
}

impl From<SupportTauError> for MutationError {
    fn from(error: SupportTauError) -> MutationError {
        MutationError::SupportTau(error)
    }
}

impl From<HomError> for MutationError {
    fn from(error: HomError) -> MutationError {
        MutationError::Hom(error)
    }
}

fn defect(defect: MutationDefect) -> MutationError {
    MutationError::Defect(defect)
}

/// The vertices where `m` has positive dimension, ascending.
fn support(m: &Module) -> Vec<u32> {
    m.dim_vector()
        .iter()
        .enumerate()
        .filter(|&(_, &d)| d > 0)
        .map(|(v, _)| v as u32)
        .collect()
}

/// Whether `m` is the direct sum of `parts`, in that order, entry for entry.
///
/// Reassembles the sum and compares every arrow matrix. Dimension vectors
/// would not decide it: they are isomorphism invariants and not identifiers.
fn is_direct_sum(m: &Module, parts: &[Module]) -> bool {
    let refs: Vec<&Module> = parts.iter().collect();
    let rebuilt = if refs.is_empty() {
        Module::zero(m.algebra())
    } else {
        direct_sum(&refs).0
    };
    rebuilt.dim_vector() == m.dim_vector()
        && (0..m.algebra().quiver().num_arrows())
            .all(|i| rebuilt.map(ArrowId(i as u32)) == m.map(ArrowId(i as u32)))
}

/// The dimension of the sum of the images of `maps` at each vertex.
///
/// The images of a spanning set of `Hom(U, X)` sum to the trace submodule
/// `tr_U(X)`, and at one vertex that sum is the row span of the stacked vertex
/// matrices. So a rank per vertex decides `X in Fac U`.
fn trace_dims(maps: &[Morphism], x: &Module) -> Vec<usize> {
    let field = x.field();
    (0..x.algebra().quiver().num_vertices())
        .map(|v| {
            if x.dim_at(v) == 0 {
                return 0;
            }
            let mut rows: Vec<Vec<Fp>> = Vec::new();
            for f in maps {
                let block = f.map_at(v);
                for r in 0..block.rows() {
                    rows.push(block.row(r).to_vec());
                }
            }
            if rows.is_empty() {
                0
            } else {
                DenseMat::from_rows(&rows).rank(&field)
            }
        })
        .collect()
}

/// Whether `g` is a cokernel of `f`.
///
/// The checks are `f.then(g) = 0`, `g` onto at every vertex, and
/// `dim Y_v + rank f_v = dim B_v` at every vertex. Together those say
/// `im f = ker g` and `g` epi, which is the cokernel property.
fn is_cokernel(f: &Morphism, g: &Morphism) -> bool {
    if !g.source().ptr_eq(f.target()) {
        return false;
    }
    let Ok(composite) = f.then(g) else {
        return false;
    };
    if !composite.is_zero() {
        return false;
    }
    let field = f.source().field();
    (0..f.source().algebra().quiver().num_vertices()).all(|v| {
        let dim_y = g.target().dim_at(v);
        g.map_at(v).rank(&field) == dim_y
            && dim_y + f.map_at(v).rank(&field) == f.target().dim_at(v)
    })
}

/// A proof that `X_j` lies in `Fac(M/X_j)`, so slot `j` admits no left
/// mutation.
///
/// `X in Fac U` exactly when finitely many maps `f_i : U -> X` have images
/// summing to all of `X`, which is to say the induced `U^r -> X` is onto. The
/// witness is that family. It does not claim the family spans `Hom(U, X)`:
/// spanning is stronger than the definition of `Fac` and nothing here needs
/// it. Fields are private and the only constructor is [`mutate_at`].
///
/// By AIR Definition-Proposition 2.28 the mutation at this slot is then a right
/// mutation. This is a statement about the slot, not a failure.
#[derive(Clone, Debug)]
pub struct FacWitness {
    module: Module,
    // The summands of U, shared with the decomposition of the source pair.
    summands: Vec<Module>,
    summand: Module,
    maps: Vec<Morphism>,
}

impl FacWitness {
    /// `U = M/X_j`, the module part with the slot summand dropped.
    #[inline]
    pub fn module(&self) -> &Module {
        &self.module
    }

    /// The summands of `U`, in the order they hold in the source pair.
    ///
    /// These are the module values of the source decomposition, not copies,
    /// so a caller binds the witness to its pair by [`Module::ptr_eq`] on each
    /// one. A dimension vector does not bind: two non-isomorphic modules can
    /// share one, as three of the `kronecker(2)` indecomposables do.
    #[inline]
    pub fn summands(&self) -> &[Module] {
        &self.summands
    }

    /// `X_j`, the summand the slot addresses.
    #[inline]
    pub fn summand(&self) -> &Module {
        &self.summand
    }

    /// The maps `U -> X_j` whose images were summed.
    #[inline]
    pub fn maps(&self) -> &[Morphism] {
        &self.maps
    }

    /// The dimension of the sum of the images at each vertex, recomputed from
    /// the stored maps. On a witness that verifies it is the dimension vector
    /// of `X_j`.
    pub fn image_dims(&self) -> Vec<usize> {
        trace_dims(&self.maps, &self.summand)
    }

    /// Recomputes the rank equality from the stored maps.
    ///
    /// The checks: `U` is the direct sum of the stored summands in order,
    /// entry for entry; every stored map runs from `U` to `X_j`; and the
    /// images sum to the dimension vector of `X_j` at every vertex. A dropped
    /// map fails the rank check as soon as the remaining images stop covering
    /// `X_j`, and no [`crate::homspace::HomSpace`] is rebuilt.
    ///
    /// The first check is what binds `U` to the summands: a caller that also
    /// compares [`FacWitness::summands`] against its own pair by
    /// [`Module::ptr_eq`] knows which module the rank equality was proved
    /// over.
    pub fn verify(&self) -> bool {
        if !is_direct_sum(&self.module, &self.summands) {
            return false;
        }
        for f in &self.maps {
            if !f.source().ptr_eq(&self.module) || !f.target().ptr_eq(&self.summand) {
                return false;
            }
        }
        trace_dims(&self.maps, &self.summand) == self.summand.dim_vector()
    }
}

/// The shape of a left mutation at a module summand slot.
///
/// The two shapes are AIR Theorem 2.30(a) and (b). There is no third: a
/// projective summand is never exchanged for a projective, and a module summand
/// is never exchanged for two summands.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExchangeShape {
    /// `supp(U)` is smaller than `supp(M)`. The approximation has zero
    /// cokernel, the module part loses `X_j`, and `vertex` joins the projective
    /// support.
    MovesToProjective {
        /// The one vertex of `supp(M) \ supp(U)`.
        vertex: u32,
    },
    /// `supp(U)` equals `supp(M)`. The cokernel is `multiplicity` copies of one
    /// indecomposable, which enters the module part.
    ReplacedByModule {
        /// The number of summands of the cokernel.
        multiplicity: usize,
    },
}

/// The five checks that identify the target as the mutation, plus the exchange
/// sequence that built it.
///
/// Fields are private and the only constructor is [`mutate_at`], so a value of
/// this type carries a certified almost complete pair, an `add` closure witness
/// per endpoint, a proof that the endpoints differ, and a certified target
/// pair. [`MutationWitness::verify`] recomputes all of it.
///
/// The approximation and the cokernel map are construction data. They record
/// how the target was built. AIR Theorem 2.18 is what proves the target is the
/// mutation; see the module documentation.
#[derive(Debug)]
pub struct MutationWitness {
    slot: usize,
    exchanged: Module,
    almost_complete: AlmostCompletePair,
    source_module: Module,
    source_projective: Vec<u32>,
    source_extension: AddClosureWitness,
    target_module: Module,
    target_projective: Vec<u32>,
    target_extension: AddClosureWitness,
    distinct: SupportPairObstruction,
    approximation: MinimalLeftApproximation,
    // g: B -> Y, the cokernel of the approximation.
    exchange: Morphism,
    shape: ExchangeShape,
    // Y_1, present exactly for ExchangeShape::ReplacedByModule.
    replacement: Option<Module>,
}

impl MutationWitness {
    /// The slot the mutation was taken at.
    #[inline]
    pub fn slot(&self) -> usize {
        self.slot
    }

    /// `X_j`, the summand the slot addresses.
    #[inline]
    pub fn exchanged(&self) -> &Module {
        &self.exchanged
    }

    /// The almost complete pair `(U, Q) = (M/X_j, P)` both endpoints extend.
    #[inline]
    pub fn almost_complete(&self) -> &AlmostCompletePair {
        &self.almost_complete
    }

    /// The proof that `U` is a direct summand of the source module part.
    #[inline]
    pub fn source_extension(&self) -> &AddClosureWitness {
        &self.source_extension
    }

    /// The proof that `U` is a direct summand of the target module part.
    #[inline]
    pub fn target_extension(&self) -> &AddClosureWitness {
        &self.target_extension
    }

    /// The proof that the two completions are not isomorphic.
    #[inline]
    pub fn distinct(&self) -> &SupportPairObstruction {
        &self.distinct
    }

    /// The minimal left `add(U)`-approximation `f: X_j -> B`.
    #[inline]
    pub fn approximation(&self) -> &MinimalLeftApproximation {
        &self.approximation
    }

    /// The cokernel map `g: B -> Y` of the approximation.
    ///
    /// With [`MutationWitness::approximation`] this is the exchange sequence
    /// `X_j -> B -> Y -> 0`.
    #[inline]
    pub fn exchange(&self) -> &Morphism {
        &self.exchange
    }

    /// Which of the two shapes the mutation took.
    #[inline]
    pub fn shape(&self) -> &ExchangeShape {
        &self.shape
    }

    /// `Y_1`, the indecomposable that enters the module part, or `None` when
    /// the slot moved to the projective part.
    #[inline]
    pub fn replacement(&self) -> Option<&Module> {
        self.replacement.as_ref()
    }

    /// The module part of the source pair.
    #[inline]
    pub fn source_module(&self) -> &Module {
        &self.source_module
    }

    /// The projective support of the source pair.
    #[inline]
    pub fn source_projective(&self) -> &[u32] {
        &self.source_projective
    }

    /// The module part of the target pair.
    #[inline]
    pub fn target_module(&self) -> &Module {
        &self.target_module
    }

    /// The projective support of the target pair.
    #[inline]
    pub fn target_projective(&self) -> &[u32] {
        &self.target_projective
    }

    /// Recomputes every claim from the stored modules and maps.
    ///
    /// Nothing stored is taken on trust. Both endpoints are decomposed again,
    /// the almost complete pair reruns all four of its conditions, the `add`
    /// closures are rebuilt as well as rechecked, the endpoints are compared
    /// again, the target is classified again from its parts, and the exchange
    /// sequence is recomputed from the approximation. A witness borrowed from
    /// another slot fails, because its approximation does not start at the
    /// stored `X_j`.
    pub fn verify(&self) -> bool {
        if !self.almost_complete.verify() {
            return false;
        }
        let u = self.almost_complete.module();
        let algebra = u.module().algebra();
        if !Arc::ptr_eq(algebra, self.source_module.algebra())
            || !Arc::ptr_eq(algebra, self.target_module.algebra())
        {
            return false;
        }
        let (Ok(source_dec), Ok(target_dec)) = (
            BasicDecomposition::new(&self.source_module),
            BasicDecomposition::new(&self.target_module),
        ) else {
            return false;
        };
        let (Ok(source_proj), Ok(target_proj)) = (
            ProjectiveSupport::new(algebra, &self.source_projective),
            ProjectiveSupport::new(algebra, &self.target_projective),
        ) else {
            return false;
        };
        // Check 2. The source keeps the projective part of the almost complete
        // pair, since a left mutation at a module slot leaves it alone.
        if self.almost_complete.projective().vertices() != source_proj.vertices() {
            return false;
        }
        if !extends(u, &source_dec, &self.source_extension) {
            return false;
        }
        // Check 3.
        if !self
            .almost_complete
            .projective()
            .vertices()
            .iter()
            .all(|&v| target_proj.contains(v))
        {
            return false;
        }
        if !extends(u, &target_dec, &self.target_extension) {
            return false;
        }
        // Check 4.
        match pair_iso(&source_dec, &source_proj, &target_dec, &target_proj) {
            Ok(SupportPairIsoOutcome::NotIsomorphic(_)) => {}
            _ => return false,
        }
        // Check 5. The decomposition and the support are rebuilt once more,
        // because classification takes them by value.
        let (Ok(fresh_dec), Ok(fresh_proj)) = (
            BasicDecomposition::new(&self.target_module),
            ProjectiveSupport::new(algebra, &self.target_projective),
        ) else {
            return false;
        };
        match SupportTauTiltingPair::classify(fresh_dec, fresh_proj) {
            Ok(classification) if classification.is_pair() => {}
            _ => return false,
        }
        self.exchange_holds(u, &source_dec, &target_dec, &source_proj, &target_proj)
    }

    /// Rechecks the construction data: the approximation, the exchange
    /// sequence, and the shape.
    fn exchange_holds(
        &self,
        u: &BasicDecomposition,
        source_dec: &BasicDecomposition,
        target_dec: &BasicDecomposition,
        source_proj: &ProjectiveSupport,
        target_proj: &ProjectiveSupport,
    ) -> bool {
        let f = self.approximation.map();
        if !f.source().ptr_eq(&self.exchanged) {
            return false;
        }
        if self.approximation.summands().len() != u.len()
            || !self
                .approximation
                .summands()
                .iter()
                .zip(u.summands())
                .all(|(a, b)| a.module().ptr_eq(b.module()))
        {
            return false;
        }
        if !self.approximation.verify() || !is_cokernel(f, &self.exchange) {
            return false;
        }
        // The slot summand is a summand of the source module part, and the
        // slot is its position there.
        let Some(slot_summand) = source_dec.summands().get(self.slot) else {
            return false;
        };
        if indecomposable_iso(slot_summand.module(), &self.exchanged, slot_summand.endo()).is_none()
        {
            return false;
        }
        let y = self.exchange.target();
        match &self.shape {
            ExchangeShape::MovesToProjective { vertex } => {
                if !y.is_zero() || self.replacement.is_some() {
                    return false;
                }
                if source_proj.contains(*vertex) || !target_proj.contains(*vertex) {
                    return false;
                }
                let mut expected = source_proj.vertices().to_vec();
                expected.push(*vertex);
                expected.sort_unstable();
                expected == target_proj.vertices() && target_dec.len() == u.len()
            }
            ExchangeShape::ReplacedByModule { multiplicity } => {
                let Some(replacement) = &self.replacement else {
                    return false;
                };
                if y.is_zero() || source_proj.vertices() != target_proj.vertices() {
                    return false;
                }
                if target_dec.len() != u.len() + 1 {
                    return false;
                }
                let split = decompose(y);
                if split.summands().len() != *multiplicity
                    || split
                        .certificates()
                        .iter()
                        .any(|c| *c != Certificate::Indecomposable)
                {
                    return false;
                }
                let Ok(y1) = IndecomposableModule::new(replacement) else {
                    return false;
                };
                if !split
                    .summands()
                    .iter()
                    .all(|s| indecomposable_iso(y1.module(), s, y1.endo()).is_some())
                {
                    return false;
                }
                // AIR Theorem 2.30(b): Y_1 is outside add(T), so in particular
                // it repeats no summand of the source.
                if source_dec
                    .summands()
                    .iter()
                    .any(|s| indecomposable_iso(y1.module(), s.module(), y1.endo()).is_some())
                {
                    return false;
                }
                target_dec
                    .summands()
                    .iter()
                    .any(|s| indecomposable_iso(y1.module(), s.module(), y1.endo()).is_some())
            }
        }
    }
}

/// Whether `whole` contains `u` as a direct summand, both by a rebuilt match
/// and by the stored witness.
fn extends(u: &BasicDecomposition, whole: &BasicDecomposition, stored: &AddClosureWitness) -> bool {
    let Ok(Some(live)) = AddClosureWitness::new(u, whole) else {
        return false;
    };
    if live.matches().len() != stored.matches().len() {
        return false;
    }
    if !stored.module().ptr_eq(u.module()) || !stored.target().ptr_eq(whole.module()) {
        return false;
    }
    let mut seen: Vec<usize> = stored.matches().iter().map(|m| m.target_index()).collect();
    seen.sort_unstable();
    let distinct = seen.windows(2).all(|w| w[0] != w[1]);
    distinct && stored.verify()
}

/// A left mutation at one slot, with the pair it lands on.
#[derive(Debug)]
pub struct Mutation {
    slot: usize,
    target: SupportTauTiltingPair,
    witness: MutationWitness,
}

impl Mutation {
    /// The slot the mutation was taken at.
    #[inline]
    pub fn slot(&self) -> usize {
        self.slot
    }

    /// The pair the mutation lands on.
    #[inline]
    pub fn target(&self) -> &SupportTauTiltingPair {
        &self.target
    }

    /// The pair the mutation lands on, by value.
    #[inline]
    pub fn into_target(self) -> SupportTauTiltingPair {
        self.target
    }

    /// The five checks and the exchange sequence.
    #[inline]
    pub fn witness(&self) -> &MutationWitness {
        &self.witness
    }

    /// Which of the two shapes the mutation took.
    #[inline]
    pub fn shape(&self) -> &ExchangeShape {
        self.witness.shape()
    }

    /// Recomputes the witness and the target pair, and binds the two.
    ///
    /// The binding is [`Module::ptr_eq`] between the module part of the target
    /// pair and the target module the witness proves things about, plus
    /// equality of the two projective supports. Without it a witness for one
    /// target would pass next to a target pair for another.
    ///
    /// The slot is bound as well. The witness proves a statement about one
    /// slot, so a mutation carrying its own slot label could otherwise present
    /// a witness for a different one and still verify.
    pub fn verify(&self) -> bool {
        self.slot == self.witness.slot()
            && self
                .target
                .module()
                .module()
                .ptr_eq(self.witness.target_module())
            && self.target.projective().vertices() == self.witness.target_projective()
            && self.witness.verify()
            && self.target.verify()
    }
}

/// What slot `j` of a pair admits.
#[derive(Debug)]
pub enum SlotOutcome {
    /// `X_j` lies in `Fac(M/X_j)`, so the mutation at this slot is a right
    /// mutation and there is no left mutation.
    NoLeftMutation(FacWitness),
    /// The left mutation at this slot, with its target.
    ///
    /// The mutation is boxed because it carries the whole target pair and
    /// every witness, which is an order of magnitude larger than a
    /// [`FacWitness`].
    LeftMutation(Box<Mutation>),
}

impl SlotOutcome {
    /// Whether the slot admits a left mutation.
    #[inline]
    pub fn is_left_mutation(&self) -> bool {
        matches!(self, Self::LeftMutation(_))
    }

    /// The mutation, or `None` when the slot admits no left mutation.
    #[inline]
    pub fn mutation(&self) -> Option<&Mutation> {
        match self {
            Self::LeftMutation(mutation) => Some(mutation),
            Self::NoLeftMutation(_) => None,
        }
    }

    /// The `Fac` witness, or `None` when the slot admits a left mutation.
    #[inline]
    pub fn fac_witness(&self) -> Option<&FacWitness> {
        match self {
            Self::NoLeftMutation(witness) => Some(witness),
            Self::LeftMutation(_) => None,
        }
    }

    /// The mutation by value, or `None` when the slot admits no left mutation.
    #[inline]
    pub fn into_mutation(self) -> Option<Mutation> {
        match self {
            Self::LeftMutation(mutation) => Some(*mutation),
            Self::NoLeftMutation(_) => None,
        }
    }
}

/// The parts of the target pair the shape decision produces.
struct BuiltTarget {
    decomposition: BasicDecomposition,
    vertices: Vec<u32>,
    shape: ExchangeShape,
    // Y_1, present exactly for ExchangeShape::ReplacedByModule.
    replacement: Option<Module>,
}

/// The target parts, picked by the shape and cross-checked against AIR Theorem
/// 2.30.
///
/// `dropped` is `supp(M) \ supp(U)` and `y` is the cokernel of the
/// approximation. An empty `dropped` is the sincere case, where the cokernel
/// carries the exchange.
///
/// The target decomposition is built from `u_dec`, never decomposed again:
/// the module part is `U` itself, or `U` plus the one certified cokernel
/// summand `Y_1`.
fn build_target(
    pair: &SupportTauTiltingPair,
    u_dec: &BasicDecomposition,
    y: &Module,
    dropped: &[u32],
) -> Result<BuiltTarget, MutationError> {
    if !dropped.is_empty() {
        if dropped.len() != 1 {
            return Err(defect(MutationDefect::DroppedVertexCount {
                dropped: dropped.to_vec(),
            }));
        }
        if !y.is_zero() {
            return Err(defect(MutationDefect::CokernelNonzero {
                dim_vector: y.dim_vector().to_vec(),
            }));
        }
        let vertex = dropped[0];
        let mut vertices = pair.projective().vertices().to_vec();
        vertices.push(vertex);
        vertices.sort_unstable();
        return Ok(BuiltTarget {
            decomposition: u_dec.clone(),
            vertices,
            shape: ExchangeShape::MovesToProjective { vertex },
            replacement: None,
        });
    }
    if y.is_zero() {
        return Err(defect(MutationDefect::CokernelZero));
    }
    let split = decompose(y);
    for certificate in split.certificates() {
        if let Certificate::Undetermined { attempts } = certificate {
            return Err(MutationError::Basic(BasicError::CertificationBlocked {
                reason: format!(
                    "a cokernel summand stayed undetermined after {attempts} split attempts"
                ),
            }));
        }
    }
    let y1 =
        IndecomposableModule::from_endo(split.endos()[0].clone()).map_err(MutationError::Indec)?;
    for (position, other) in split.summands().iter().enumerate().skip(1) {
        if indecomposable_iso(y1.module(), other, y1.endo()).is_none() {
            return Err(defect(MutationDefect::CokernelSummandsDiffer {
                summand: position,
            }));
        }
    }
    // AIR Theorem 2.30(b) puts Y outside add(T). That covers the weaker
    // statement that Y_1 and X_j differ, since X_j is a summand of T.
    for (position, other) in pair.module().summands().iter().enumerate() {
        if indecomposable_iso(y1.module(), other.module(), y1.endo()).is_some() {
            return Err(defect(MutationDefect::ReplacementRepeatsSummand {
                summand: position,
            }));
        }
    }
    let replacement = y1.module().clone();
    Ok(BuiltTarget {
        decomposition: u_dec.with_new_summand(&y1).map_err(MutationError::Basic)?,
        vertices: pair.projective().vertices().to_vec(),
        shape: ExchangeShape::ReplacedByModule {
            multiplicity: split.summands().len(),
        },
        replacement: Some(replacement),
    })
}

/// The left mutation of `pair` at slot `slot`, over a cache of its own.
///
/// Summands are indexed by position and the cokernel summand gets the next
/// index, which is stable within this one call. Use
/// [`mutate_at_with_cache`] to share AR translates across several mutations.
///
/// # Errors
/// [`MutationError::SlotOutOfRange`] when the slot is not a module summand,
/// the wrapped errors of the layers a check runs through, and
/// [`MutationError::Defect`] on a failed internal cross-check.
pub fn mutate_at(pair: &SupportTauTiltingPair, slot: usize) -> Result<SlotOutcome, MutationError> {
    let count = pair.module().len();
    let indices: Vec<usize> = (0..count).collect();
    mutate_at_with_cache(pair, slot, &indices, count, None)
}

/// The left mutation of `pair` at slot `slot`, taking AR translates from
/// `cache`.
///
/// `summand_indices[i]` is the caller's stable label for summand `i` of the
/// module part, and `fresh_index` labels the cokernel summand of a
/// [`ExchangeShape::ReplacedByModule`] mutation. The labels travel to the
/// witnesses of the target pair and to
/// [`crate::taurigid::NonTauRigidWitness`]; they are not cache keys, so a
/// repeated label costs nothing but a confusing report. [`TauCache`] answers
/// from the identity of the module value.
///
/// The plain [`mutate_at`] labels summands by position because it builds and
/// drops its own cache. A caller that shares one cache usually has its own
/// numbering, which is why this entry point takes it.
///
/// With `cache` as `None` the call builds a cache, uses it, and drops it.
///
/// # Errors
/// As [`mutate_at`], plus [`MutationError::SummandIndexCount`] when the index
/// list and the summand list have different lengths.
pub fn mutate_at_with_cache(
    pair: &SupportTauTiltingPair,
    slot: usize,
    summand_indices: &[usize],
    fresh_index: usize,
    cache: Option<&mut TauCache>,
) -> Result<SlotOutcome, MutationError> {
    let m = pair.module();
    if slot >= m.len() {
        return Err(MutationError::SlotOutOfRange {
            slot,
            summands: m.len(),
        });
    }
    if summand_indices.len() != m.len() {
        return Err(MutationError::SummandIndexCount {
            indices: summand_indices.len(),
            summands: m.len(),
        });
    }
    let algebra = m.module().algebra().clone();
    let x = m.summands()[slot].module().clone();

    // Dropping one summand of a basic module leaves a basic module, so U comes
    // with its decomposition and no Krull-Schmidt runs here.
    let u_dec = m.without(slot).expect("the slot is a summand position");
    let u = u_dec.module().clone();

    // Step 2a of the case analysis: the Fac test decides the direction.
    let maps = hom(&u, &x)?;
    if trace_dims(&maps, &x) == x.dim_vector() {
        return Ok(SlotOutcome::NoLeftMutation(FacWitness {
            module: u,
            summands: u_dec
                .summands()
                .iter()
                .map(|s| s.module().clone())
                .collect(),
            summand: x,
            maps,
        }));
    }

    let u_indices: Vec<usize> = summand_indices
        .iter()
        .enumerate()
        .filter(|(i, _)| *i != slot)
        .map(|(_, &index)| index)
        .collect();
    let u_summands: Vec<Module> = u_dec
        .summands()
        .iter()
        .map(|s| s.module().clone())
        .collect();

    let mut owned = TauCache::new();
    let cache = cache.unwrap_or(&mut owned);
    let q = ProjectiveSupport::new(&algebra, pair.projective().vertices())?;
    let almost_complete = match AlmostCompletePair::classify_with_cache(
        u_dec.clone(),
        q,
        &u_indices,
        Some(&mut *cache),
    )? {
        AlmostCompleteClassification::Pair(almost) => almost,
        AlmostCompleteClassification::Rejected(rejection) => {
            return Err(defect(MutationDefect::AlmostCompleteRejected(rejection)));
        }
    };

    let approximation = left_approximation(&x, &u_summands).map_err(MutationError::Approx)?;
    let (y, exchange) = cokernel(approximation.map());

    // Step 2b: the sincerity test picks the shape. AIR Theorem 2.30 states it
    // as "U is sincere over Lambda/<e>", which is supp(U) = supp(M) here.
    let dropped: Vec<u32> = support(m.module())
        .into_iter()
        .filter(|&v| u.dim_at(v) == 0)
        .collect();

    let built = build_target(pair, &u_dec, &y, &dropped)?;

    let mut target_indices = u_indices.clone();
    if built.replacement.is_some() {
        target_indices.push(fresh_index);
    }
    let target_proj = ProjectiveSupport::new(&algebra, &built.vertices)?;
    let target = match SupportTauTiltingPair::classify_with_cache(
        built.decomposition,
        target_proj,
        &target_indices,
        Some(&mut *cache),
    )? {
        SupportTauTiltingClassification::Pair(target) => target,
        SupportTauTiltingClassification::Rejected(rejection) => {
            return Err(defect(MutationDefect::TargetRejected(rejection)));
        }
    };

    let Some(source_extension) = AddClosureWitness::new(almost_complete.module(), m)? else {
        return Err(defect(MutationDefect::AddClosureMissing {
            endpoint: Endpoint::Source,
        }));
    };
    let Some(target_extension) = AddClosureWitness::new(almost_complete.module(), target.module())?
    else {
        return Err(defect(MutationDefect::AddClosureMissing {
            endpoint: Endpoint::Target,
        }));
    };
    if almost_complete.projective().vertices() != pair.projective().vertices() {
        return Err(defect(MutationDefect::ProjectiveSupportNotExtended {
            endpoint: Endpoint::Source,
        }));
    }
    if !almost_complete
        .projective()
        .vertices()
        .iter()
        .all(|&v| target.projective().contains(v))
    {
        return Err(defect(MutationDefect::ProjectiveSupportNotExtended {
            endpoint: Endpoint::Target,
        }));
    }
    let distinct = match pair_iso(m, &pair.projective(), target.module(), &target.projective())? {
        SupportPairIsoOutcome::NotIsomorphic(obstruction) => obstruction,
        SupportPairIsoOutcome::Isomorphic(_) => {
            return Err(defect(MutationDefect::EndpointsIsomorphic));
        }
    };

    let witness = MutationWitness {
        slot,
        exchanged: x,
        almost_complete,
        source_module: m.module().clone(),
        source_projective: pair.projective().vertices().to_vec(),
        source_extension,
        target_module: target.module().module().clone(),
        target_projective: target.projective().vertices().to_vec(),
        target_extension,
        distinct,
        approximation,
        exchange,
        shape: built.shape,
        replacement: built.replacement,
    };
    Ok(SlotOutcome::LeftMutation(Box::new(Mutation {
        slot,
        target,
        witness,
    })))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{Algebra, linear_an, truncated_poly};
    use crate::dynkin::{DynkinType, dynkin_quiver};
    use crate::field::PrimeField;
    use crate::quiver::Quiver;

    /// The direct sum of `parts`, and the zero module when `parts` is empty.
    fn assemble(algebra: &Arc<Algebra>, parts: &[&Module]) -> Module {
        if parts.is_empty() {
            Module::zero(algebra)
        } else {
            direct_sum(parts).0
        }
    }

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

    fn pair_of(
        algebra: &Arc<Algebra>,
        parts: &[&Module],
        projective: &[u32],
    ) -> SupportTauTiltingPair {
        let module = assemble(algebra, parts);
        let decomposition =
            BasicDecomposition::new(&module).expect("the fixture module part is basic");
        let support =
            ProjectiveSupport::new(algebra, projective).expect("the fixture vertices are in range");
        match SupportTauTiltingPair::classify(decomposition, support)
            .expect("the fixture parts share one algebra")
        {
            SupportTauTiltingClassification::Pair(pair) => pair,
            SupportTauTiltingClassification::Rejected(rejection) => panic!(
                "the fixture is a pair, condition {} says otherwise: {rejection}",
                rejection.condition()
            ),
        }
    }

    /// The regular module `A = P_0 + ... + P_{n-1}`.
    fn regular_pair(algebra: &Arc<Algebra>) -> SupportTauTiltingPair {
        let parts: Vec<Module> = (0..algebra.quiver().num_vertices())
            .map(|v| Module::projective(algebra, v))
            .collect();
        let refs: Vec<&Module> = parts.iter().collect();
        pair_of(algebra, &refs, &[])
    }

    /// The slot addressing the summand with dimension vector `dim`.
    ///
    /// Every fixture below has module summands of pairwise distinct dimension
    /// vectors, so the lookup is unambiguous. Over the Dynkin fixtures the
    /// dimension vector also determines the indecomposable, since the
    /// indecomposables are the positive roots.
    fn slot_of(pair: &SupportTauTiltingPair, dim: &[usize]) -> usize {
        let hits: Vec<usize> = pair
            .module()
            .summands()
            .iter()
            .enumerate()
            .filter(|(_, s)| s.module().dim_vector() == dim)
            .map(|(i, _)| i)
            .collect();
        assert_eq!(hits.len(), 1, "one summand of dimension vector {dim:?}");
        hits[0]
    }

    fn sorted_dims(pair: &SupportTauTiltingPair) -> Vec<Vec<usize>> {
        let mut dims = pair.module().dim_vectors();
        dims.sort();
        dims
    }

    /// The mutation at the slot addressing `dim`, with both verifications run.
    fn left(pair: &SupportTauTiltingPair, dim: &[usize]) -> Mutation {
        let slot = slot_of(pair, dim);
        let outcome = mutate_at(pair, slot).expect("the fixture slot mutates");
        let mutation = match outcome {
            SlotOutcome::LeftMutation(mutation) => *mutation,
            SlotOutcome::NoLeftMutation(_) => {
                panic!("slot {slot} of dimension vector {dim:?} has a left mutation")
            }
        };
        assert!(mutation.witness().verify(), "the witness recomputes");
        assert!(mutation.verify(), "the mutation recomputes");
        mutation
    }

    fn no_left(pair: &SupportTauTiltingPair, dim: &[usize]) -> FacWitness {
        let slot = slot_of(pair, dim);
        match mutate_at(pair, slot).expect("the fixture slot classifies") {
            SlotOutcome::NoLeftMutation(witness) => {
                assert!(witness.verify(), "the Fac witness recomputes");
                witness
            }
            SlotOutcome::LeftMutation(_) => {
                panic!("slot {slot} of dimension vector {dim:?} has no left mutation")
            }
        }
    }

    fn assert_target(mutation: &Mutation, dims: &[&[usize]], projective: &[u32]) {
        let mut expected: Vec<Vec<usize>> = dims.iter().map(|d| d.to_vec()).collect();
        expected.sort();
        assert_eq!(sorted_dims(mutation.target()), expected);
        assert_eq!(mutation.target().projective().vertices(), projective);
    }

    // The pentagon of A_2, worked out by hand in the v0.5 mathematics spike,
    // section 3.2. Vertices in crate indexing (0-based, arrow 0 -> 1):
    //
    //   v1 = (P_0 + P_1, 0)      P_0 = (1,1), P_1 = (0,1) = S_1
    //   v2 = (P_0 + S_0, 0)      S_0 = (1,0)
    //   v3 = (S_0, P_1)
    //   v4 = (P_1, P_0)
    //   v5 = (0, P_0 + P_1)
    //
    // Left mutations, one line per slot:
    //
    //   v1 at P_0: U = P_1, Fac U = add P_1, so P_0 is outside it. supp U =
    //     {1} is smaller than supp M = {0,1}, so the slot moves to the
    //     projective part at vertex 0 and the target is v4. Hom(P_0, P_1) = 0,
    //     so the approximation is the zero map into the zero module.
    //   v1 at P_1: U = P_0. Every quotient of a sum of copies of P_0 has top a
    //     sum of S_0, and top P_1 = S_1, so P_1 is outside Fac U. supp U =
    //     {0,1} = supp M, so the cokernel carries the exchange: the minimal
    //     left add(P_0)-approximation is the socle inclusion P_1 -> P_0 and
    //     coker is S_0. Target v2.
    //   v2 at P_0: U = S_0, and P_0 is outside add S_0 = Fac S_0. supp U = {0}
    //     is smaller than {0,1}, so vertex 1 joins the projective part and the
    //     target is v3. The approximation P_0 -> S_0 is onto with kernel P_1,
    //     which the construction never touches.
    //   v2 at S_0: S_0 = top P_0 lies in Fac P_0, so there is no left mutation.
    //   v3 at S_0: U = 0 and Fac 0 = {0}, so S_0 is outside it. supp U = {} is
    //     smaller than {0}, so vertex 0 joins the projective part: target v5.
    //   v4 at P_1: as v3, with vertex 1: target v5.
    //   v5 has no module summand, so it has no slot.
    #[test]
    fn a2_pentagon_slot_by_slot() {
        for field in fields() {
            let algebra = linear_an(2, field);
            let p0 = Module::projective(&algebra, 0);
            let p1 = Module::projective(&algebra, 1);
            let s0 = Module::simple(&algebra, 0);

            let v1 = pair_of(&algebra, &[&p0, &p1], &[]);
            let v2 = pair_of(&algebra, &[&p0, &s0], &[]);
            let v3 = pair_of(&algebra, &[&s0], &[1]);
            let v4 = pair_of(&algebra, &[&p1], &[0]);
            let v5 = pair_of(&algebra, &[], &[0, 1]);

            let at_p0 = left(&v1, &[1, 1]);
            assert_target(&at_p0, &[&[0, 1]], &[0]);
            assert_eq!(
                *at_p0.shape(),
                ExchangeShape::MovesToProjective { vertex: 0 }
            );
            assert!(at_p0.witness().approximation().map().target().is_zero());

            let at_p1 = left(&v1, &[0, 1]);
            assert_target(&at_p1, &[&[1, 1], &[1, 0]], &[]);
            assert_eq!(
                *at_p1.shape(),
                ExchangeShape::ReplacedByModule { multiplicity: 1 }
            );
            assert_eq!(
                at_p1.witness().replacement().map(|y| y.dim_vector()),
                Some([1, 0].as_slice())
            );

            let v2_at_p0 = left(&v2, &[1, 1]);
            assert_target(&v2_at_p0, &[&[1, 0]], &[1]);
            assert_eq!(
                *v2_at_p0.shape(),
                ExchangeShape::MovesToProjective { vertex: 1 }
            );

            let fac = no_left(&v2, &[1, 0]);
            assert_eq!(fac.image_dims(), [1, 0]);
            assert_eq!(fac.maps().len(), 1);

            let v3_at_s0 = left(&v3, &[1, 0]);
            assert_target(&v3_at_s0, &[], &[0, 1]);
            assert_eq!(
                *v3_at_s0.shape(),
                ExchangeShape::MovesToProjective { vertex: 0 }
            );

            let v4_at_p1 = left(&v4, &[0, 1]);
            assert_target(&v4_at_p1, &[], &[0, 1]);
            assert_eq!(
                *v4_at_p1.shape(),
                ExchangeShape::MovesToProjective { vertex: 1 }
            );

            assert_eq!(v5.module().len(), 0);
            assert!(matches!(
                mutate_at(&v5, 0),
                Err(MutationError::SlotOutOfRange {
                    slot: 0,
                    summands: 0
                })
            ));
        }
    }

    // The semisimple algebra on two vertices, spike section 3.1. Every module
    // is projective, so tau is zero and a pair is any assignment of P_0 and
    // P_1 to the module part or the projective part: four vertices. Fac U is
    // add U here, so no module summand ever lies in Fac of the rest and every
    // slot mutates. Each mutation moves its summand to the projective part,
    // which makes the graph the 2-cube.
    #[test]
    fn semisimple_two_vertex_cube() {
        for field in fields() {
            let algebra = semisimple(2, field);
            let p0 = Module::projective(&algebra, 0);
            let p1 = Module::projective(&algebra, 1);

            let top = pair_of(&algebra, &[&p0, &p1], &[]);
            let left_side = pair_of(&algebra, &[&p1], &[0]);
            let right_side = pair_of(&algebra, &[&p0], &[1]);
            let bottom = pair_of(&algebra, &[], &[0, 1]);

            let drop_p0 = left(&top, &[1, 0]);
            assert_target(&drop_p0, &[&[0, 1]], &[0]);
            assert_eq!(
                *drop_p0.shape(),
                ExchangeShape::MovesToProjective { vertex: 0 }
            );

            let drop_p1 = left(&top, &[0, 1]);
            assert_target(&drop_p1, &[&[1, 0]], &[1]);

            let down_left = left(&left_side, &[0, 1]);
            assert_target(&down_left, &[], &[0, 1]);

            let down_right = left(&right_side, &[1, 0]);
            assert_target(&down_right, &[], &[0, 1]);

            assert_eq!(bottom.module().len(), 0);
        }
    }

    // Ten of the 21 edges of linear_an(3), spike section 3.3, with the
    // vertices named as in its table. Crate indexing is 0-based, so the
    // interval [i,j] of the spike is [i-1,j-1] here:
    //
    //   P_0 = (1,1,1)   P_1 = (0,1,1)   P_2 = (0,0,1)
    //   S_0 = (1,0,0)   S_1 = (0,1,0)   I_1 = (1,1,0)
    //
    //   A = (P_0 + S_0 + P_2, 0)   B = (A, 0)          C = (P_0 + P_1 + S_1, 0)
    //   E = (P_0 + I_1 + S_0, 0)   G = (P_1 + P_2, P_0)
    //   H = (S_0 + P_2, P_1)       K = (P_2, P_0 + P_1)
    //   M = (S_0, P_1 + P_2)       N = (0, A)
    //
    // Quotients of an interval module [a,b] are the intervals [a,c], so Fac
    // membership is a finite check by hand. Hom([a,b],[c,d]) is nonzero
    // exactly when c <= a <= d <= b, which fixes the approximations.
    //
    //   B at P_2: U = P_0 + P_1, whose quotients are [0,0], [0,1], [0,2],
    //     [1,1], [1,2]; P_2 = [2,2] is not among them. supp U = {0,1,2} is all
    //     of supp M, so the exchange runs through the cokernel. Hom(P_2, P_0)
    //     factors through Hom(P_2, P_1) . Hom(P_1, P_0), so the only generator
    //     is P_2 -> P_1 and coker is S_1. Target C.
    //   B at P_1: U = P_0 + P_2. Hom(P_0, P_1) = 0 and the image of
    //     Hom(P_2, P_1) is P_2, so the trace is P_2 and P_1 is outside Fac U.
    //     supp U is everything, the generator is P_1 -> P_0, and coker is S_0.
    //     Target A.
    //   B at P_0: U = P_1 + P_2 has support {1,2}, so P_0 is outside Fac U and
    //     vertex 0 moves to the projective part. Target G.
    //   A at P_2: U = P_0 + S_0. Hom(P_2, S_0) = 0 and Hom(P_2, P_0) is the
    //     socle inclusion, which is the one generator; coker is I_1. Target E.
    //   A at S_0: S_0 = top P_0 lies in Fac U, so no left mutation.
    //   A at P_0: U = S_0 + P_2 has support {0,2}, so vertex 1 moves to the
    //     projective part. Target H.
    //   H at P_2: U = S_0 has support {0}, so vertex 2 moves across. Target M.
    //   H at S_0: U = P_2 has support {2}, so vertex 0 moves across. Target K.
    //   K at P_2 and M at S_0: U = 0 in both, so the one support vertex moves
    //     across. Both land on N.
    #[test]
    fn linear_an_3_pinned_edges() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let p0 = Module::projective(&algebra, 0);
            let p1 = Module::projective(&algebra, 1);
            let p2 = Module::projective(&algebra, 2);
            let s0 = Module::simple(&algebra, 0);
            // I_1 is the interval module (1,1,0), which the targets below
            // reach as a cokernel rather than as a fixture.
            assert_eq!(Module::injective(&algebra, 1).dim_vector(), [1, 1, 0]);

            let vertex_a = pair_of(&algebra, &[&p0, &s0, &p2], &[]);
            let vertex_b = pair_of(&algebra, &[&p0, &p1, &p2], &[]);
            let vertex_h = pair_of(&algebra, &[&s0, &p2], &[1]);
            let vertex_k = pair_of(&algebra, &[&p2], &[0, 1]);
            let vertex_m = pair_of(&algebra, &[&s0], &[1, 2]);

            let b_at_p2 = left(&vertex_b, &[0, 0, 1]);
            assert_target(&b_at_p2, &[&[1, 1, 1], &[0, 1, 1], &[0, 1, 0]], &[]);
            assert_eq!(
                *b_at_p2.shape(),
                ExchangeShape::ReplacedByModule { multiplicity: 1 }
            );

            let b_at_p1 = left(&vertex_b, &[0, 1, 1]);
            assert_target(&b_at_p1, &[&[1, 1, 1], &[0, 0, 1], &[1, 0, 0]], &[]);

            let b_at_p0 = left(&vertex_b, &[1, 1, 1]);
            assert_target(&b_at_p0, &[&[0, 1, 1], &[0, 0, 1]], &[0]);
            assert_eq!(
                *b_at_p0.shape(),
                ExchangeShape::MovesToProjective { vertex: 0 }
            );

            let a_at_p2 = left(&vertex_a, &[0, 0, 1]);
            assert_target(&a_at_p2, &[&[1, 1, 1], &[1, 0, 0], &[1, 1, 0]], &[]);

            let fac = no_left(&vertex_a, &[1, 0, 0]);
            assert_eq!(fac.image_dims(), [1, 0, 0]);

            let a_at_p0 = left(&vertex_a, &[1, 1, 1]);
            assert_target(&a_at_p0, &[&[1, 0, 0], &[0, 0, 1]], &[1]);
            assert_eq!(
                *a_at_p0.shape(),
                ExchangeShape::MovesToProjective { vertex: 1 }
            );

            let h_at_p2 = left(&vertex_h, &[0, 0, 1]);
            assert_target(&h_at_p2, &[&[1, 0, 0]], &[1, 2]);

            let h_at_s0 = left(&vertex_h, &[1, 0, 0]);
            assert_target(&h_at_s0, &[&[0, 0, 1]], &[0, 1]);

            let k_at_p2 = left(&vertex_k, &[0, 0, 1]);
            assert_target(&k_at_p2, &[], &[0, 1, 2]);

            let m_at_s0 = left(&vertex_m, &[1, 0, 0]);
            assert_target(&m_at_s0, &[], &[0, 1, 2]);
        }
    }

    // `(A, 0)` is the maximum of the order, so no slot of it can be a right
    // mutation. Concretely: dropping P_j leaves U = sum of the other
    // projectives, every quotient of a sum of copies of U has top a sum of the
    // simples S_v with v not j, and top P_j = S_j, so P_j is outside Fac U.
    // The argument uses no property of the algebra, so it holds on both
    // fixtures.
    #[test]
    fn every_slot_of_the_regular_pair_mutates() {
        for field in fields() {
            for algebra in [linear_an(3, field), d4(field)] {
                let pair = regular_pair(&algebra);
                assert_eq!(pair.module().len(), pair.summand_count());
                for slot in 0..pair.module().len() {
                    let outcome = mutate_at(&pair, slot).expect("the regular pair mutates");
                    let mutation = match outcome {
                        SlotOutcome::LeftMutation(mutation) => *mutation,
                        SlotOutcome::NoLeftMutation(_) => {
                            panic!("slot {slot} of the regular pair has a left mutation")
                        }
                    };
                    assert!(mutation.witness().verify());
                    assert!(mutation.target().verify());
                }
            }
        }
    }

    // k[x]/(x^3) has one vertex and two pairs, `(A, 0)` and `(0, A)`. The one
    // slot drops the only summand, leaving U = 0 with empty support, so vertex
    // 0 moves to the projective part.
    #[test]
    fn truncated_poly_3_has_one_slot_to_the_zero_pair() {
        for field in fields() {
            let algebra = truncated_poly(3, field).expect("x^3 is admissible");
            let pair = regular_pair(&algebra);
            assert_eq!(pair.module().len(), 1);
            let mutation = left(&pair, &[3]);
            assert_target(&mutation, &[], &[0]);
            assert_eq!(
                *mutation.shape(),
                ExchangeShape::MovesToProjective { vertex: 0 }
            );
            assert!(mutation.target().module().is_empty());
        }
    }

    // One cache across several mutations answers repeated translates from the
    // store. The point here is only that the hit count rises, which is what
    // shows the cache is shared rather than rebuilt per call.
    #[test]
    fn one_cache_serves_several_mutations() {
        let algebra = linear_an(3, f5());
        let pair = regular_pair(&algebra);
        let indices: Vec<usize> = (0..pair.module().len()).collect();
        let mut cache = TauCache::new();
        let mut hits = Vec::new();
        for slot in 0..pair.module().len() {
            let outcome = mutate_at_with_cache(
                &pair,
                slot,
                &indices,
                indices.len() + slot,
                Some(&mut cache),
            )
            .expect("the regular pair mutates");
            assert!(outcome.is_left_mutation());
            hits.push(cache.hits());
        }
        assert!(hits[0] > 0, "the first call already reuses a translate");
        assert!(
            hits[2] > hits[0],
            "later calls keep hitting the shared store, got {hits:?}"
        );
        assert!(cache.misses() > 0);
    }

    // A witness whose target is another slot's target, which is a valid pair
    // in its own right. The stored almost complete pair no longer sits inside
    // it, so the extension check fails.
    #[test]
    fn a_swapped_target_fails_verification() {
        let algebra = linear_an(2, f2());
        let p0 = Module::projective(&algebra, 0);
        let p1 = Module::projective(&algebra, 1);
        let pair = pair_of(&algebra, &[&p0, &p1], &[]);

        let at_p0 = left(&pair, &[1, 1]);
        let at_p1 = left(&pair, &[0, 1]);
        let mut tampered = at_p0.witness;
        tampered.target_module = at_p1.witness.target_module.clone();
        tampered.target_projective = at_p1.witness.target_projective.clone();
        assert!(!tampered.verify());
    }

    // An approximation borrowed from the other slot of the same pair. It
    // starts at the wrong summand, which the witness catches before it
    // recomputes the exchange sequence.
    #[test]
    fn a_borrowed_approximation_fails_verification() {
        let algebra = linear_an(2, f2());
        let p0 = Module::projective(&algebra, 0);
        let p1 = Module::projective(&algebra, 1);
        let pair = pair_of(&algebra, &[&p0, &p1], &[]);

        let at_p0 = left(&pair, &[1, 1]);
        let at_p1 = left(&pair, &[0, 1]);
        let mut tampered = at_p1.witness;
        tampered.approximation = at_p0.witness.approximation;
        assert!(!tampered.verify());
    }

    // A witness whose target is the source pair, with the matching extension
    // witness moved over so that the add-closure checks pass. What is left is
    // the check that the two completions differ, and it fails: AIR Theorem
    // 2.18 gives two completions, not one taken twice.
    #[test]
    fn a_target_equal_to_the_source_fails_verification() {
        let algebra = linear_an(2, f2());
        let p0 = Module::projective(&algebra, 0);
        let p1 = Module::projective(&algebra, 1);
        let pair = pair_of(&algebra, &[&p0, &p1], &[]);

        let mut tampered = left(&pair, &[0, 1]).witness;
        tampered.target_module = tampered.source_module.clone();
        tampered.target_projective = tampered.source_projective.clone();
        tampered.target_extension = tampered.source_extension.clone();
        assert!(!tampered.verify());
    }

    // A Fac witness that lost a map. The remaining images no longer cover
    // X_j, which is the rank equality the witness exists to prove.
    #[test]
    fn a_truncated_fac_witness_fails_verification() {
        let algebra = linear_an(2, f2());
        let p0 = Module::projective(&algebra, 0);
        let s0 = Module::simple(&algebra, 0);
        let pair = pair_of(&algebra, &[&p0, &s0], &[]);

        let mut witness = no_left(&pair, &[1, 0]);
        assert!(witness.verify());
        witness.maps.pop();
        assert!(!witness.verify());
    }

    // A Fac witness whose summand list is not a decomposition of its stored
    // U. The rank equality is proved over U, so a caller reading the summand
    // list has to know it belongs to that U, and only the direct-sum check
    // says so.
    #[test]
    fn a_fac_witness_whose_summands_miss_u_fails_verification() {
        // Vertex A of the linear_an(3) table above. S_0 is the top of P_0, so
        // it lies in Fac(P_0 + P_2) and slot S_0 has no left mutation.
        let algebra = linear_an(3, f2());
        let p0 = Module::projective(&algebra, 0);
        let p2 = Module::projective(&algebra, 2);
        let s0 = Module::simple(&algebra, 0);
        let pair = pair_of(&algebra, &[&p0, &s0, &p2], &[]);

        let mut witness = no_left(&pair, &[1, 0, 0]);
        assert_eq!(witness.summands().len(), 2);
        witness.summands.pop();
        assert!(!witness.verify());
    }

    // A mutation carrying another slot's target pair. Both halves still pass
    // on their own, so only the binding between them catches the swap.
    #[test]
    fn a_mutation_with_another_slot_target_fails_verification() {
        let algebra = linear_an(2, f2());
        let p0 = Module::projective(&algebra, 0);
        let p1 = Module::projective(&algebra, 1);
        let pair = pair_of(&algebra, &[&p0, &p1], &[]);

        let mut at_p0 = left(&pair, &[1, 1]);
        let at_p1 = left(&pair, &[0, 1]);
        at_p0.target = at_p1.target;
        assert!(at_p0.witness.verify());
        assert!(at_p0.target.verify());
        assert!(!at_p0.verify());
    }

    // A witness proves a statement about ONE slot, so relabelling the
    // mutation must not survive verification. Both halves still pass alone.
    #[test]
    fn a_mutation_relabelled_to_another_slot_fails_verification() {
        let algebra = linear_an(2, f2());
        let p0 = Module::projective(&algebra, 0);
        let p1 = Module::projective(&algebra, 1);
        let pair = pair_of(&algebra, &[&p0, &p1], &[]);

        let mut at_p0 = left(&pair, &[1, 1]);
        let other = left(&pair, &[0, 1]);
        assert_ne!(at_p0.slot, other.slot, "the two slots must differ");
        at_p0.slot = other.slot;
        assert!(at_p0.witness.verify());
        assert!(at_p0.target.verify());
        assert!(!at_p0.verify());
    }

    // Every mutation of the A_2 pentagon leaves the source pair usable, since
    // mutate_at takes it by reference and builds fresh modules for the target.
    #[test]
    fn the_source_pair_survives_a_mutation() {
        let algebra = linear_an(2, f5());
        let p0 = Module::projective(&algebra, 0);
        let p1 = Module::projective(&algebra, 1);
        let pair = pair_of(&algebra, &[&p0, &p1], &[]);
        let _ = left(&pair, &[1, 1]);
        assert!(pair.verify());
    }
}

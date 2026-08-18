//! Support tau-tilting pairs, decided by support arithmetic, and a
//! definition-only enumerator over an exhaustive catalog.
//!
//! A pair is `(M, P)` with `M` basic and `P` a basic projective. It is a
//! support tau-tilting pair when `Hom(P, M) = 0`, `M` is tau-rigid, and
//! `|M| + |P| = n`, where `n` is the number of vertices and `|X|` counts
//! indecomposable summands. [`AlmostCompletePair`] takes the same conditions
//! with `|M| + |P| = n - 1`; mutation is defined through it.
//!
//! The projective part carries no information the module part does not
//! already fix. Take `M` tau-rigid and write `r = |M|`, `s` for the number of
//! vertices where `M` is nonzero, and `C` for the remaining vertices. Then a
//! support tau-tilting pair with module part `M` exists exactly when `r = s`,
//! and its projective part is forced to be the sum of `P_v` over `C`. An
//! almost complete pair with module part `M` has `P` equal to `C` when
//! `s = r + 1`, and to `C` minus one vertex when `s = r`; no other case is
//! possible. So [`SupportTauTiltingPair`] stores the module part and the
//! tau-rigidity witness alone, [`AlmostCompletePair`] adds the omitted
//! vertex, and both derive the support on request. The proofs sit on
//! `support_complement` and on the two `classify_with_cache` constructors.
//!
//! The projective part is a vertex subset because every algebra this crate
//! builds is a bound quiver algebra `kQ/I` with `I` admissible, which makes
//! it basic: the indecomposable projectives are the `n` modules
//! `P_v = e_v A`, pairwise non-isomorphic. Nothing here needs `Q` connected.
//!
//! Tau-rigidity is decided summandwise, through
//! [`is_tau_rigid_summandwise`] over a [`TauCache`]. `tau` never runs on an
//! assembled module. That rule is binding and follows from additivity of
//! `tau` and `Hom`: the summandwise calculation is EXACT, not an
//! approximation. Additivity says nothing about which part of `tau` dominates
//! its cost, so no claim about that is made here. Working per summand also
//! avoids the double-route cross-check decomposing both of its results.
//!
//! [`enumerate_over_catalog`] lists the pairs of one algebra from the
//! definition alone, with no mutation theory. Its completeness is the
//! classification theorem behind an [`IndecomposableCatalog`], so it runs only
//! over the algebras such a catalog covers.

use std::fmt;
use std::sync::Arc;

use crate::algebra::Algebra;
use crate::ar::TauError;
use crate::arquiver::{CatalogProvenance, IndecomposableCatalog};
use crate::basic::{
    BasicDecomposition, BasicError, PairFingerprint, ProjectiveSupport, SupportPairIsoOutcome,
    pair_iso,
};
use crate::hom::{HomError, hom_dim};
use crate::module::Module;
use crate::taurigid::{
    NonTauRigidWitness, TauCache, TauRigidError, TauRigidModule, TauRigidityOutcome,
    is_tau_rigid_summandwise,
};

/// Rejected input, a blocked certification, or a failed internal cross-check
/// of the support tau-tilting layer.
///
/// None of these is a mathematical answer about a pair. A pair that fails a
/// condition is a [`PairRejection`], never an error.
#[derive(Clone, Debug)]
pub enum SupportTauError {
    /// The basic layer rejected an input or could not certify a summand.
    Basic(BasicError),
    /// A tau-rigidity decision could not be reached.
    TauRigid(TauRigidError),
    /// A Hom space could not be built.
    Hom(HomError),
    /// The supplied summand indices do not match the module's summands one
    /// for one.
    SummandIndexCount {
        /// Number of indices supplied.
        indices: usize,
        /// Number of summands of the module part.
        summands: usize,
    },
    /// A failed internal cross-check: the tables and the certified route
    /// disagree, or a decomposition produced a summand outside the subset it
    /// was assembled from.
    Defect {
        /// What contradicted the check.
        reason: String,
    },
}

impl fmt::Display for SupportTauError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Basic(error) => write!(f, "the basic layer rejected an input: {error}"),
            Self::TauRigid(error) => write!(f, "tau-rigidity stayed undecided: {error}"),
            Self::Hom(error) => write!(f, "a Hom space failed: {error}"),
            Self::SummandIndexCount { indices, summands } => write!(
                f,
                "{indices} summand indices for {summands} summands; one index per summand"
            ),
            Self::Defect { reason } => write!(f, "internal cross-check failed: {reason}"),
        }
    }
}

impl std::error::Error for SupportTauError {}

impl From<BasicError> for SupportTauError {
    fn from(error: BasicError) -> SupportTauError {
        SupportTauError::Basic(error)
    }
}

impl From<TauRigidError> for SupportTauError {
    fn from(error: TauRigidError) -> SupportTauError {
        SupportTauError::TauRigid(error)
    }
}

impl From<TauError> for SupportTauError {
    fn from(error: TauError) -> SupportTauError {
        SupportTauError::TauRigid(TauRigidError::Tau(error))
    }
}

impl From<HomError> for SupportTauError {
    fn from(error: HomError) -> SupportTauError {
        SupportTauError::Hom(error)
    }
}

/// The condition a candidate pair failed, with the witness for that failure.
///
/// The conditions are numbered as in `docs/v0.5-design.md` section 6 and are
/// checked in that order, so the rejection names the first one that failed.
#[derive(Clone, Debug)]
pub enum PairRejection {
    /// Condition 1: the module part and the projective part do not share one
    /// algebra value (the same [`Arc`]).
    ///
    /// The rest of condition 1, that both parts are basic and certified, is
    /// carried by the argument types: [`BasicDecomposition`] and
    /// [`ProjectiveSupport`] have no other constructor.
    DifferentAlgebras,
    /// Condition 2: `Hom(P, M)` is not zero, at a support vertex of `P` where
    /// `M` does not vanish.
    ///
    /// `Hom(P_v, M) = M_v` for right modules, so the vertex and the dimension
    /// are the whole proof. No morphism is needed.
    HomFromProjectiveNonzero {
        /// A vertex in the support of `P` where `M` is nonzero.
        vertex: u32,
        /// `dim M_v`, which is `dim Hom(P_v, M)`.
        dim: usize,
    },
    /// Condition 3: `M` is not tau-rigid, with one nonzero morphism
    /// `X_i -> tau X_j`.
    NotTauRigid(NonTauRigidWitness),
    /// Condition 4: the summand counts do not add up to the expected total,
    /// which is `n` for a support tau-tilting pair and `n - 1` for an almost
    /// complete pair.
    SummandCount {
        /// `|M|`, the number of indecomposable summands of the module part.
        module: usize,
        /// `|P|`, the number of support vertices.
        projective: usize,
        /// The total the pair type requires.
        expected: usize,
    },
}

impl PairRejection {
    /// The number of the failed condition in `docs/v0.5-design.md` section 6,
    /// from 1 to 4.
    pub fn condition(&self) -> u32 {
        match self {
            Self::DifferentAlgebras => 1,
            Self::HomFromProjectiveNonzero { .. } => 2,
            Self::NotTauRigid(_) => 3,
            Self::SummandCount { .. } => 4,
        }
    }
}

impl fmt::Display for PairRejection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DifferentAlgebras => f.write_str("the two parts do not share one algebra"),
            Self::HomFromProjectiveNonzero { vertex, dim } => write!(
                f,
                "Hom(P, M) is not zero: dim Hom(P_{vertex}, M) = dim M_{vertex} = {dim}"
            ),
            Self::NotTauRigid(_) => f.write_str("M is not tau-rigid"),
            Self::SummandCount {
                module,
                projective,
                expected,
            } => write!(
                f,
                "|M| + |P| = {module} + {projective}, and the pair needs {expected}"
            ),
        }
    }
}

/// The result of [`check_conditions`]: the tau-rigidity witness both pair
/// types keep, or the first condition that failed.
enum Checked {
    Accepted(TauRigidModule),
    Rejected(PairRejection),
}

/// Runs conditions 1 to 4 in the order of `docs/v0.5-design.md` section 6.
///
/// `expected` is the required value of `|M| + |P|`. `summand_indices[i]` is
/// the caller's stable index for summand `i` of `module`. It is a LABEL only,
/// carried into witnesses and the bindings. It does NOT key `cache`, which
/// keys on nominal module identity.
fn check_conditions(
    module: &BasicDecomposition,
    projective: &ProjectiveSupport,
    expected: usize,
    summand_indices: &[usize],
    cache: Option<&mut TauCache>,
) -> Result<Checked, SupportTauError> {
    if summand_indices.len() != module.len() {
        return Err(SupportTauError::SummandIndexCount {
            indices: summand_indices.len(),
            summands: module.len(),
        });
    }
    if !Arc::ptr_eq(module.module().algebra(), projective.algebra()) {
        return Ok(Checked::Rejected(PairRejection::DifferentAlgebras));
    }
    // Condition 2 is arithmetic on the dimension vector, with no Hom space.
    // See `support_complement` for the identification Hom(P_v, M) = M_v.
    // ProjectiveSupport::new keeps its vertices below the vertex count of the
    // algebra the previous check just matched, so the index is in range.
    let dims = module.module().dim_vector();
    if let Some(&vertex) = projective
        .vertices()
        .iter()
        .find(|&&v| dims[v as usize] != 0)
    {
        return Ok(Checked::Rejected(PairRejection::HomFromProjectiveNonzero {
            vertex,
            dim: dims[vertex as usize],
        }));
    }
    let summands: Vec<(usize, Module)> = summand_indices
        .iter()
        .zip(module.summands())
        .map(|(&index, x)| (index, x.module().clone()))
        .collect();
    let mut owned = TauCache::new();
    let rigid = match is_tau_rigid_summandwise(&summands, cache.unwrap_or(&mut owned))? {
        TauRigidityOutcome::TauRigid(rigid) => rigid,
        TauRigidityOutcome::NotTauRigid(witness) => {
            return Ok(Checked::Rejected(PairRejection::NotTauRigid(witness)));
        }
    };
    if module.len() + projective.len() != expected {
        return Ok(Checked::Rejected(PairRejection::SummandCount {
            module: module.len(),
            projective: projective.len(),
            expected,
        }));
    }
    Ok(Checked::Accepted(rigid))
}

/// The number of vertices of the algebra the pair lives over.
fn vertex_count(module: &BasicDecomposition) -> usize {
    module.module().algebra().quiver().num_vertices() as usize
}

/// Positional indices, the indexing a caller with no stable one uses.
fn positional(module: &BasicDecomposition) -> Vec<usize> {
    (0..module.len()).collect()
}

/// The vertices outside the support of `module`, in increasing order.
///
/// These are exactly the vertices `v` with `Hom(P_v, module) = 0`. For right
/// modules `P_v = e_v A`, and evaluation at `e_v` is a bijection
/// `Hom(P_v, X) -> X e_v = X_v`: it is injective because `e_v A` is generated
/// by `e_v`, and surjective because every `m` in `X_v` gives the well defined
/// map `e_v a |-> m a`. So `dim Hom(P_v, X) = dim X_v`, and a basic
/// projective `P` has `Hom(P, module) = 0` exactly when its vertex set sits
/// inside this list.
fn support_complement(module: &BasicDecomposition) -> Vec<u32> {
    module
        .module()
        .dim_vector()
        .iter()
        .enumerate()
        .filter(|&(_, &dim)| dim == 0)
        .map(|(vertex, _)| vertex as u32)
        .collect()
}

/// `vertices` as a projective support over the algebra of `module`.
///
/// Every caller passes a subset of [`support_complement`], so the vertices are
/// in range for that algebra.
fn as_support(module: &BasicDecomposition, vertices: &[u32]) -> ProjectiveSupport {
    ProjectiveSupport::new(module.module().algebra(), vertices)
        .expect("the support complement lists vertices of the module's own algebra")
}

/// The vertices of the support complement of `module` that `projective` leaves
/// out, in increasing order.
///
/// Meaningful only after condition 2, which puts the vertex set of
/// `projective` inside the complement.
fn omitted_vertices(module: &BasicDecomposition, projective: &ProjectiveSupport) -> Vec<u32> {
    support_complement(module)
        .into_iter()
        .filter(|&v| !projective.contains(v))
        .collect()
}

/// Rechecks conditions 3 and 4 against the live parts, and that the stored
/// tau-rigidity witness covers the live summands.
///
/// Conditions 1 and 2 have nothing left to recheck. One algebra value carries
/// both parts, and the support is derived from the support complement of the
/// module part, so it cannot meet the support of `M`. The expensive half of
/// condition 3, [`TauRigidModule::verify`], stays with the caller, because
/// both pair types run it last.
fn recheck_shared(
    module: &BasicDecomposition,
    projective_len: usize,
    rigid: &TauRigidModule,
    expected: usize,
) -> bool {
    if module.len() + projective_len != expected {
        return false;
    }
    if rigid.summands().len() != module.len() {
        return false;
    }
    rigid
        .summands()
        .iter()
        .zip(module.summands())
        .all(|((_, stored), x)| stored.ptr_eq(x.module()))
}

/// A pair `(M, P)` certified to satisfy every condition of
/// `docs/v0.5-design.md` section 6.
///
/// Fields are private and every constructor runs all four checks, so a value
/// of this type is a proof: `M` is basic and certified, `Hom(P, M) = 0`, `M`
/// is tau-rigid with a [`TauRigidModule`], and `|M| + |P| = n`.
///
/// `P` is not stored. It is forced to be the sum of `P_v` over the vertices
/// where `M` vanishes, so [`SupportTauTiltingPair::projective`] derives it.
/// The proof is on [`SupportTauTiltingPair::classify_with_cache`].
///
/// Tau-rigidity is decided summandwise. `tau` runs once per indecomposable
/// summand, never on the assembled `M`.
pub struct SupportTauTiltingPair {
    module: BasicDecomposition,
    rigid: TauRigidModule,
}

impl fmt::Debug for SupportTauTiltingPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SupportTauTiltingPair")
            .field("module_dim_vectors", &self.module.dim_vectors())
            .field("projective_support", &support_complement(&self.module))
            .finish()
    }
}

/// Whether a candidate `(M, P)` is a support tau-tilting pair, and if not,
/// which condition failed.
#[derive(Debug)]
pub enum SupportTauTiltingClassification {
    /// Every condition holds.
    Pair(SupportTauTiltingPair),
    /// One condition failed, with its witness.
    Rejected(PairRejection),
}

impl SupportTauTiltingClassification {
    /// Whether the candidate is a pair.
    #[inline]
    pub fn is_pair(&self) -> bool {
        matches!(self, Self::Pair(_))
    }

    /// The pair, or `None` for a rejection.
    #[inline]
    pub fn pair(&self) -> Option<&SupportTauTiltingPair> {
        match self {
            Self::Pair(pair) => Some(pair),
            Self::Rejected(_) => None,
        }
    }

    /// The rejection, or `None` for a pair.
    #[inline]
    pub fn rejection(&self) -> Option<&PairRejection> {
        match self {
            Self::Pair(_) => None,
            Self::Rejected(rejection) => Some(rejection),
        }
    }

    /// Takes the pair out, or `None` for a rejection.
    #[inline]
    pub fn into_pair(self) -> Option<SupportTauTiltingPair> {
        match self {
            Self::Pair(pair) => Some(pair),
            Self::Rejected(_) => None,
        }
    }
}

impl SupportTauTiltingPair {
    /// Classifies `(module, projective)`, taking AR translates from `cache`.
    ///
    /// `summand_indices[i]` is the caller's stable label for summand `i` of
    /// `module`. It labels the entries of [`TauRigidModule::summands`] and
    /// [`TauRigidModule::vanishing_pairs`], nothing else;
    /// [`enumerate_over_catalog`] passes catalog positions.
    ///
    /// With `cache` as `None` the call builds a cache, uses it, and drops it.
    ///
    /// # Errors
    /// [`SupportTauError::SummandIndexCount`] when the index list and the
    /// summand list have different lengths, the wrapped errors of the Hom and
    /// tau layers when a check could not be run, and
    /// [`SupportTauError::Defect`] when an accepted candidate has a support
    /// strictly inside the support complement.
    pub fn classify_with_cache(
        module: BasicDecomposition,
        projective: ProjectiveSupport,
        summand_indices: &[usize],
        cache: Option<&mut TauCache>,
    ) -> Result<SupportTauTiltingClassification, SupportTauError> {
        let expected = vertex_count(&module);
        match check_conditions(&module, &projective, expected, summand_indices, cache)? {
            Checked::Accepted(rigid) => {
                // P is forced, which is why the pair does not store it.
                // Write r = |M|, s for the number of vertices where M is
                // nonzero, C for the other n - s vertices, and S for the
                // vertex set of P. Condition 2 puts S inside C, and
                // condition 4 gives |S| = n - r.
                //
                // Claim: r <= s. Let e be the sum of e_v over C, so M e = 0
                // and M is a module over B = A/AeA, an algebra whose simples
                // are indexed by the s vertices of the support. Condition 3
                // gives Hom_A(M, tau_A M) = 0, and that carries to B: Adachi,
                // Iyama, and Reiten, "tau-tilting theory", Compositio Math.
                // 150 (2014), Lemma 2.1(a), for an ideal inside the
                // annihilator. So M is tau-rigid over B, and Proposition 1.3
                // of the same paper bounds a tau-rigid module by the number
                // of simples: r <= s.
                //
                // Then |S| = n - r <= n - s = |C|, and S inside C forces
                // S = C and r = s.
                //
                // The check below is that bound, not decoration. A candidate
                // that passed every condition with S strictly inside C would
                // be a genuine pair with an underdetermined projective part,
                // so it is reported rather than stored.
                let omitted = omitted_vertices(&module, &projective);
                if !omitted.is_empty() {
                    return Err(SupportTauError::Defect {
                        reason: format!(
                            "a pair with module dimension vectors {:?} and support {:?} left the \
                             vertices {omitted:?} out of the support complement",
                            module.dim_vectors(),
                            projective.vertices()
                        ),
                    });
                }
                Ok(SupportTauTiltingClassification::Pair(
                    SupportTauTiltingPair { module, rigid },
                ))
            }
            Checked::Rejected(rejection) => {
                Ok(SupportTauTiltingClassification::Rejected(rejection))
            }
        }
    }

    /// Classifies `(module, projective)` over a cache of its own.
    ///
    /// Summands are indexed by position, which is stable within this one call.
    /// Use [`SupportTauTiltingPair::classify_with_cache`] to share translates
    /// across several pairs.
    pub fn classify(
        module: BasicDecomposition,
        projective: ProjectiveSupport,
    ) -> Result<SupportTauTiltingClassification, SupportTauError> {
        let indices = positional(&module);
        Self::classify_with_cache(module, projective, &indices, None)
    }

    /// The pair, or `Ok(None)` when a condition fails.
    ///
    /// `Ok(None)` names no condition. Call
    /// [`SupportTauTiltingPair::classify`] when the reason matters.
    pub fn new(
        module: BasicDecomposition,
        projective: ProjectiveSupport,
    ) -> Result<Option<SupportTauTiltingPair>, SupportTauError> {
        Ok(Self::classify(module, projective)?.into_pair())
    }

    /// The module part `M`.
    #[inline]
    pub fn module(&self) -> &BasicDecomposition {
        &self.module
    }

    /// The projective part `P`, derived as the sum of `P_v` over the vertices
    /// where `M` vanishes.
    ///
    /// The value is rebuilt on each call. It is not stored, because the four
    /// conditions force it.
    pub fn projective(&self) -> ProjectiveSupport {
        as_support(&self.module, &support_complement(&self.module))
    }

    /// The tau-rigidity witness of `M`, one certified translate per summand.
    #[inline]
    pub fn rigid(&self) -> &TauRigidModule {
        &self.rigid
    }

    /// Whether the projective part is empty, which makes `M` a tau-tilting
    /// module.
    ///
    /// The projective part is the support complement of `M`, so this is
    /// exactly sincerity of `M`.
    pub fn is_tau_tilting(&self) -> bool {
        self.module.module().dim_vector().iter().all(|&d| d > 0)
    }

    /// `|M| + |P|`, which equals the number of vertices.
    pub fn summand_count(&self) -> usize {
        self.module.len() + support_complement(&self.module).len()
    }

    /// Recomputes every condition against the live parts.
    ///
    /// Nothing stored is taken on trust. `P` is derived again from the module
    /// part, the counts are recomputed, and every summand's `tau` is
    /// recomputed through the certified double route inside
    /// [`TauRigidModule::verify`]. A tau-rigidity witness borrowed from
    /// another pair fails here.
    pub fn verify(&self) -> bool {
        recheck_shared(
            &self.module,
            support_complement(&self.module).len(),
            &self.rigid,
            vertex_count(&self.module),
        ) && self.rigid.verify()
    }
}

/// A pair `(M, P)` with every condition of a support tau-tilting pair except
/// that `|M| + |P| = n - 1`.
///
/// Mutation is defined through this type: an almost complete pair has exactly
/// two completions to a support tau-tilting pair (Adachi, Iyama, and Reiten,
/// "tau-tilting theory", Compositio Math. 150 (2014), Theorem 2.18), and the
/// two completions are the two ends of a mutation.
///
/// Fields are private and the constructors run the same checks as
/// [`SupportTauTiltingPair`] with the smaller total.
///
/// `P` is not stored either. With `r = |M|`, `s` the number of vertices where
/// `M` is nonzero, and `C` the other vertices, `P` is the sum of `P_v` over
/// `C` when `s = r + 1`, and over `C` minus one vertex when `s = r`. So the
/// only free datum is that one omitted vertex, and
/// [`AlmostCompletePair::projective`] rebuilds the rest. The proof is on
/// [`AlmostCompletePair::classify_with_cache`].
pub struct AlmostCompletePair {
    module: BasicDecomposition,
    rigid: TauRigidModule,
    // None when the support is the whole support complement, which is the
    // case s = r + 1.
    omitted: Option<u32>,
}

impl fmt::Debug for AlmostCompletePair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AlmostCompletePair")
            .field("module_dim_vectors", &self.module.dim_vectors())
            .field("projective_support", &self.support())
            .field("omitted_vertex", &self.omitted)
            .finish()
    }
}

/// Whether a candidate `(M, P)` is an almost complete pair, and if not, which
/// condition failed.
#[derive(Debug)]
pub enum AlmostCompleteClassification {
    /// Every condition holds.
    Pair(AlmostCompletePair),
    /// One condition failed, with its witness.
    Rejected(PairRejection),
}

impl AlmostCompleteClassification {
    /// Whether the candidate is an almost complete pair.
    #[inline]
    pub fn is_pair(&self) -> bool {
        matches!(self, Self::Pair(_))
    }

    /// The pair, or `None` for a rejection.
    #[inline]
    pub fn pair(&self) -> Option<&AlmostCompletePair> {
        match self {
            Self::Pair(pair) => Some(pair),
            Self::Rejected(_) => None,
        }
    }

    /// The rejection, or `None` for a pair.
    #[inline]
    pub fn rejection(&self) -> Option<&PairRejection> {
        match self {
            Self::Pair(_) => None,
            Self::Rejected(rejection) => Some(rejection),
        }
    }

    /// Takes the pair out, or `None` for a rejection.
    #[inline]
    pub fn into_pair(self) -> Option<AlmostCompletePair> {
        match self {
            Self::Pair(pair) => Some(pair),
            Self::Rejected(_) => None,
        }
    }
}

impl AlmostCompletePair {
    /// Classifies `(module, projective)` against `|M| + |P| = n - 1`, taking
    /// AR translates from `cache`.
    ///
    /// `summand_indices` and `cache` work as in
    /// [`SupportTauTiltingPair::classify_with_cache`].
    ///
    /// # Errors
    /// As [`SupportTauTiltingPair::classify_with_cache`], with
    /// [`SupportTauError::Defect`] when an accepted candidate leaves more than
    /// one vertex out of the support complement.
    pub fn classify_with_cache(
        module: BasicDecomposition,
        projective: ProjectiveSupport,
        summand_indices: &[usize],
        cache: Option<&mut TauCache>,
    ) -> Result<AlmostCompleteClassification, SupportTauError> {
        // Every algebra this crate builds has at least one vertex, so the
        // saturating step never fires; it keeps the arithmetic total anyway.
        let expected = vertex_count(&module).saturating_sub(1);
        match check_conditions(&module, &projective, expected, summand_indices, cache)? {
            Checked::Accepted(rigid) => {
                // At most one vertex of C is left out. Condition 2 puts the
                // vertex set S of P inside C, and condition 4 gives
                // |S| = n - 1 - r, so |C| - |S| = (n - s) - (n - 1 - r) =
                // r - s + 1. The bound r <= s proved on
                // SupportTauTiltingPair::classify_with_cache makes that at
                // most 1, and S inside C makes it at least 0. So s is r or
                // r + 1, and P is C or C minus one vertex.
                let omitted = omitted_vertices(&module, &projective);
                if omitted.len() > 1 {
                    return Err(SupportTauError::Defect {
                        reason: format!(
                            "an almost complete pair with module dimension vectors {:?} and \
                             support {:?} left the vertices {omitted:?} out of the support \
                             complement",
                            module.dim_vectors(),
                            projective.vertices()
                        ),
                    });
                }
                Ok(AlmostCompleteClassification::Pair(AlmostCompletePair {
                    module,
                    rigid,
                    omitted: omitted.first().copied(),
                }))
            }
            Checked::Rejected(rejection) => Ok(AlmostCompleteClassification::Rejected(rejection)),
        }
    }

    /// Classifies `(module, projective)` over a cache of its own, with
    /// summands indexed by position.
    pub fn classify(
        module: BasicDecomposition,
        projective: ProjectiveSupport,
    ) -> Result<AlmostCompleteClassification, SupportTauError> {
        let indices = positional(&module);
        Self::classify_with_cache(module, projective, &indices, None)
    }

    /// The pair, or `Ok(None)` when a condition fails.
    pub fn new(
        module: BasicDecomposition,
        projective: ProjectiveSupport,
    ) -> Result<Option<AlmostCompletePair>, SupportTauError> {
        Ok(Self::classify(module, projective)?.into_pair())
    }

    /// The module part `M`.
    #[inline]
    pub fn module(&self) -> &BasicDecomposition {
        &self.module
    }

    /// The vertex support of `P`: the support complement of `M`, minus the
    /// omitted vertex when there is one.
    fn support(&self) -> Vec<u32> {
        let mut vertices = support_complement(&self.module);
        if let Some(omitted) = self.omitted {
            vertices.retain(|&v| v != omitted);
        }
        vertices
    }

    /// The projective part `P`, as its vertex support.
    ///
    /// The value is rebuilt on each call from the module part and the omitted
    /// vertex.
    pub fn projective(&self) -> ProjectiveSupport {
        as_support(&self.module, &self.support())
    }

    /// The vertex of the support complement that `P` leaves out, and `None`
    /// when `P` is the whole complement.
    #[inline]
    pub fn omitted_vertex(&self) -> Option<u32> {
        self.omitted
    }

    /// The tau-rigidity witness of `M`.
    #[inline]
    pub fn rigid(&self) -> &TauRigidModule {
        &self.rigid
    }

    /// `|M| + |P|`, which equals the number of vertices minus one.
    pub fn summand_count(&self) -> usize {
        self.module.len() + self.support().len()
    }

    /// Recomputes every condition against the live parts, as
    /// [`SupportTauTiltingPair::verify`].
    ///
    /// The omitted vertex is rechecked against the live support complement, so
    /// an omitted vertex that is not in the complement fails here.
    pub fn verify(&self) -> bool {
        let complement = support_complement(&self.module);
        if let Some(omitted) = self.omitted
            && !complement.contains(&omitted)
        {
            return false;
        }
        recheck_shared(
            &self.module,
            self.support().len(),
            &self.rigid,
            vertex_count(&self.module).saturating_sub(1),
        ) && self.rigid.verify()
    }
}

/// The state of one [`enumerate_over_catalog`] run.
struct CatalogWalk<'a> {
    catalog: &'a IndecomposableCatalog,
    algebra: Arc<Algebra>,
    vertices: usize,
    // tau_hom[i][j] = dim Hom(X_i, tau X_j), and 0 when tau X_j is zero.
    tau_hom: Vec<Vec<usize>>,
    cache: TauCache,
    pairs: Vec<SupportTauTiltingPair>,
    nodes: usize,
}

impl CatalogWalk<'_> {
    /// Whether `chosen + [i]` is still tau-rigid, given that `chosen` is.
    ///
    /// Only the pairs involving `i` are new, so the test is incremental.
    fn extends_tau_rigid(&self, chosen: &[usize], i: usize) -> bool {
        self.tau_hom[i][i] == 0
            && chosen
                .iter()
                .all(|&j| self.tau_hom[i][j] == 0 && self.tau_hom[j][i] == 0)
    }

    fn walk(&mut self, chosen: &mut Vec<usize>, start: usize) -> Result<(), SupportTauError> {
        self.emit(chosen)?;
        // |M| + |P| = n with |P| >= 0 bounds |M| by n, so a longer subset can
        // never be the module part of a pair. The bound is checked on the
        // count, before any module is assembled.
        if chosen.len() == self.vertices {
            return Ok(());
        }
        for i in start..self.catalog.len() {
            if self.extends_tau_rigid(chosen, i) {
                chosen.push(i);
                self.nodes += 1;
                self.walk(chosen, i + 1)?;
                chosen.pop();
            }
        }
        Ok(())
    }

    /// Builds the pair whose module part is the subset `chosen`, when there is
    /// one.
    ///
    /// The subset admits a pair exactly when `|M|` equals the number of
    /// vertices where `M` is nonzero, and then the support of `P` is the
    /// complement of that set. So one subset yields at most one pair, and the
    /// test is a count.
    fn emit(&mut self, chosen: &[usize]) -> Result<(), SupportTauError> {
        let support: Vec<u32> = (0..self.vertices as u32)
            .filter(|&v| self.vanishes_at(chosen, v))
            .collect();
        if support.len() + chosen.len() != self.vertices {
            return Ok(());
        }
        // The catalog lists one entry per isomorphism class, so a subset of it
        // is already a certified basic decomposition. Reassembling and running
        // Krull-Schmidt would rediscover exactly what `chosen` names.
        let module = BasicDecomposition::from_catalog(self.catalog, chosen)?;
        let indices = chosen.to_vec();
        let projective = ProjectiveSupport::new(&self.algebra, &support)?;
        let classification = SupportTauTiltingPair::classify_with_cache(
            module,
            projective,
            &indices,
            Some(&mut self.cache),
        )?;
        match classification {
            SupportTauTiltingClassification::Pair(pair) => {
                self.pairs.push(pair);
                Ok(())
            }
            SupportTauTiltingClassification::Rejected(rejection) => Err(SupportTauError::Defect {
                reason: format!(
                    "the tables admitted the subset {chosen:?} with support {support:?} and the \
                     certified route rejected it: {rejection}"
                ),
            }),
        }
    }

    /// Whether every entry of `chosen` has dimension zero at `vertex`, which
    /// is `Hom(P_vertex, M) = 0` by the identification on `support_complement`.
    fn vanishes_at(&self, chosen: &[usize], vertex: u32) -> bool {
        chosen
            .iter()
            .all(|&i| self.catalog.entries()[i].module().dim_vector()[vertex as usize] == 0)
    }
}

/// Every support tau-tilting pair of one algebra, listed from the definition
/// over an exhaustive catalog.
///
/// Completeness comes from the catalog's classification theorem, and from
/// nothing else. An [`IndecomposableCatalog`] holds every indecomposable of
/// its algebra up to isomorphism, by the Nakayama classification or by
/// Gabriel's theorem ([`CatalogProvenance`]). The module part of a basic pair
/// is a direct sum of pairwise non-isomorphic indecomposables, so it is the
/// sum of a subset of the catalog, and walking the subsets reaches every pair.
///
/// The limit is the same theorem. Only algebras with a catalog can be
/// enumerated this way, so [`enumerate_over_catalog`] takes a catalog rather
/// than an algebra and there is no route from an arbitrary algebra to a value
/// of this type. The Kronecker algebra is tau-tilting infinite and has no
/// exhaustive catalog, so both catalog constructors reject it and no
/// enumeration is attempted.
///
/// This route is independent of the mutation-graph certificate. It uses no
/// mutation, no approximation, and no theorem about the support tau-tilting
/// quiver: only `Hom`, `tau`, and the four conditions of
/// [`SupportTauTiltingPair`]. When the two routes produce the same list, that
/// is evidence, not a restatement of one route by the other.
pub struct CatalogEnumeration {
    algebra: Arc<Algebra>,
    provenance: CatalogProvenance,
    catalog_len: usize,
    pairs: Vec<SupportTauTiltingPair>,
    nodes_visited: usize,
}

impl fmt::Debug for CatalogEnumeration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CatalogEnumeration")
            .field("provenance", &self.provenance)
            .field("catalog_len", &self.catalog_len)
            .field("pairs", &self.pairs.len())
            .field("nodes_visited", &self.nodes_visited)
            .finish()
    }
}

impl CatalogEnumeration {
    /// The algebra the pairs live over.
    #[inline]
    pub fn algebra(&self) -> &Arc<Algebra> {
        &self.algebra
    }

    /// The classification theorem the completeness of the list rests on.
    #[inline]
    pub fn provenance(&self) -> CatalogProvenance {
        self.provenance
    }

    /// The number of catalog entries the walk ran over.
    #[inline]
    pub fn catalog_len(&self) -> usize {
        self.catalog_len
    }

    /// The pairs, in walk order: module subsets in lexicographic order over
    /// catalog positions, one pair per subset that admits one.
    #[inline]
    pub fn pairs(&self) -> &[SupportTauTiltingPair] {
        &self.pairs
    }

    /// The number of pairs.
    #[inline]
    pub fn len(&self) -> usize {
        self.pairs.len()
    }

    /// Whether the list is empty. It never is: `(A, 0)` is a pair over every
    /// algebra.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.pairs.is_empty()
    }

    /// The number of subsets the depth-first search visited, counting the
    /// empty subset.
    ///
    /// Tau-rigidity is inherited by subsets, so the walk visits exactly the
    /// tau-rigid subsets of at most `n` entries and tests each remaining entry
    /// once per visit. The count is deterministic and profile-independent, so
    /// a test can assert it.
    #[inline]
    pub fn nodes_visited(&self) -> usize {
        self.nodes_visited
    }

    /// Pair counts by `|M|`, indexed from zero to the number of vertices.
    pub fn histogram(&self) -> Vec<usize> {
        let vertices = self.algebra.quiver().num_vertices() as usize;
        let mut out = vec![0; vertices + 1];
        for pair in &self.pairs {
            out[pair.module().len()] += 1;
        }
        out
    }

    /// Rechecks every pair, and that the pairs are pairwise non-isomorphic.
    ///
    /// Each pair goes through [`SupportTauTiltingPair::verify`], which
    /// recomputes all four conditions. Distinctness runs
    /// [`PairFingerprint`] as a prefilter and [`pair_iso`] inside a bucket, so
    /// a duplicated entry fails even when the two copies were built
    /// separately.
    ///
    /// This rechecks the list. It does not recheck completeness, which is the
    /// catalog's classification theorem and is not a computation.
    pub fn verify(&self) -> bool {
        let mut fingerprints = Vec::with_capacity(self.pairs.len());
        for pair in &self.pairs {
            if !Arc::ptr_eq(pair.module().module().algebra(), &self.algebra) || !pair.verify() {
                return false;
            }
            match PairFingerprint::new(pair.module(), &pair.projective()) {
                Ok(fingerprint) => fingerprints.push(fingerprint),
                Err(_) => return false,
            }
        }
        for (i, left) in self.pairs.iter().enumerate() {
            for (j, right) in self.pairs.iter().enumerate().skip(i + 1) {
                if fingerprints[i] != fingerprints[j] {
                    continue;
                }
                match pair_iso(
                    left.module(),
                    &left.projective(),
                    right.module(),
                    &right.projective(),
                ) {
                    Ok(SupportPairIsoOutcome::NotIsomorphic(_)) => {}
                    _ => return false,
                }
            }
        }
        true
    }
}

/// Lists every support tau-tilting pair of the catalog's algebra, from the
/// definition alone.
///
/// The algorithm is the one `docs/v0.5-design.md` section 10 fixes, and the
/// cost spike measured the naive alternative at 36 times slower:
///
/// 1. Compute `tau X_i` once per catalog entry, through one [`TauCache`].
/// 2. Build the table `hom_dim(X_i, tau X_j)`.
/// 3. Walk the subsets depth first, extending only sets that stay tau-rigid.
/// 4. Keep the subsets whose support complement has exactly `n - |M|`
///    vertices, which is the whole projective condition.
///
/// The subset walk reads the table and the dimension vectors, so no linear
/// algebra runs inside it. `Hom(P_v, X) = X_v`, so the second table the design
/// calls for is the dimension vectors themselves. The count bound `|M| <= n`
/// cuts a branch before any module is assembled.
///
/// Every kept candidate still goes through
/// [`SupportTauTiltingPair::classify_with_cache`], so each listed pair carries
/// the same witnesses as one built by hand. A candidate the tables admit and
/// the certified route rejects is a [`SupportTauError::Defect`].
///
/// Completeness is the catalog's, and only the catalog's: see
/// [`CatalogEnumeration`].
///
/// # Errors
/// The wrapped errors of the basic, Hom, and tau layers when a check could not
/// be run, and [`SupportTauError::Defect`] when the tables and the certified
/// route disagree.
pub fn enumerate_over_catalog(
    catalog: &IndecomposableCatalog,
) -> Result<CatalogEnumeration, SupportTauError> {
    let algebra = catalog.algebra().clone();
    let vertices = algebra.quiver().num_vertices() as usize;
    let mut cache = TauCache::new();
    let mut translates = Vec::with_capacity(catalog.len());
    for entry in catalog.entries() {
        translates.push(cache.tau_of(entry.module())?.clone());
    }
    let mut tau_hom = vec![vec![0usize; catalog.len()]; catalog.len()];
    for (i, x) in catalog.entries().iter().enumerate() {
        for (j, translate) in translates.iter().enumerate() {
            // Hom(X_i, 0) is zero, so a projective X_j needs no Hom system.
            if !translate.is_zero() {
                tau_hom[i][j] = hom_dim(x.module(), translate)?;
            }
        }
    }
    let mut walk = CatalogWalk {
        catalog,
        algebra: algebra.clone(),
        vertices,
        tau_hom,
        cache,
        pairs: Vec::new(),
        nodes: 1,
    };
    walk.walk(&mut Vec::with_capacity(vertices), 0)?;
    Ok(CatalogEnumeration {
        algebra,
        provenance: catalog.provenance(),
        catalog_len: catalog.len(),
        pairs: walk.pairs,
        nodes_visited: walk.nodes,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{
        commutative_square, kronecker, linear_an, linear_nakayama, radical_square_zero_cycle,
        truncated_poly,
    };
    use crate::ar::tau;
    use crate::dynkin::{DynkinError, DynkinType, dynkin_quiver};
    use crate::enumerate::EnumerateError;
    use crate::field::PrimeField;
    use crate::iso::{IsoOutcome, is_isomorphic};
    use crate::linalg::DenseMat;
    use crate::quiver::Quiver;

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

    // D_4 as dynkin_quiver builds it: vertex 0 is the center, arrows 0 -> 1,
    // 0 -> 2, 0 -> 3.
    fn d4(field: PrimeField) -> Arc<Algebra> {
        path_algebra(
            dynkin_quiver(DynkinType::D(4)).expect("D_4 has a quiver"),
            field,
        )
    }

    // The semisimple algebra on n vertices: n vertices, no arrows. Every
    // vertex has no incoming and no outgoing arrow, so the quiver is Nakayama
    // and the catalog is the n simples.
    fn semisimple(n: u32, field: PrimeField) -> Arc<Algebra> {
        path_algebra(
            Quiver::new(n, &[]).expect("no arrow is out of range"),
            field,
        )
    }

    fn basic(m: &Module) -> BasicDecomposition {
        BasicDecomposition::new(m).expect("the fixture module is basic")
    }

    fn support(algebra: &Arc<Algebra>, vertices: &[u32]) -> ProjectiveSupport {
        ProjectiveSupport::new(algebra, vertices).expect("the fixture vertices are in range")
    }

    fn all_vertices(algebra: &Arc<Algebra>) -> Vec<u32> {
        (0..algebra.quiver().num_vertices()).collect()
    }

    /// The regular module `A = P_0 + ... + P_{n-1}`, basic over a basic
    /// algebra.
    fn regular(algebra: &Arc<Algebra>) -> Module {
        let parts: Vec<Module> = all_vertices(algebra)
            .iter()
            .map(|&v| Module::projective(algebra, v))
            .collect();
        let refs: Vec<&Module> = parts.iter().collect();
        sum(algebra, &refs)
    }

    /// The direct sum of `parts`, and the zero module when `parts` is empty.
    /// Production code builds its decompositions from the catalog instead.
    fn sum(algebra: &Arc<Algebra>, parts: &[&Module]) -> Module {
        if parts.is_empty() {
            Module::zero(algebra)
        } else {
            crate::module::direct_sum(parts).0
        }
    }

    fn expect_pair(classification: SupportTauTiltingClassification) -> SupportTauTiltingPair {
        match classification {
            SupportTauTiltingClassification::Pair(pair) => pair,
            SupportTauTiltingClassification::Rejected(rejection) => {
                panic!(
                    "expected a pair, got condition {} : {rejection}",
                    rejection.condition()
                )
            }
        }
    }

    fn expect_rejection(classification: SupportTauTiltingClassification) -> PairRejection {
        match classification {
            SupportTauTiltingClassification::Rejected(rejection) => rejection,
            SupportTauTiltingClassification::Pair(pair) => {
                panic!("expected a rejection, got {pair:?}")
            }
        }
    }

    /// The fixture algebras that carry an exhaustive catalog, named for
    /// failure messages.
    fn catalog_fixtures(field: PrimeField) -> Vec<(String, IndecomposableCatalog)> {
        let modulus = field.modulus();
        let mut out = Vec::new();
        for n in [2u32, 3, 4] {
            let algebra = semisimple(n, field);
            out.push((
                format!("semisimple({n}) over F_{modulus}"),
                IndecomposableCatalog::nakayama(&algebra).expect("no arrow means Nakayama"),
            ));
        }
        for n in [2usize, 3] {
            let algebra = linear_an(n, field);
            out.push((
                format!("linear_an({n}) over F_{modulus}"),
                IndecomposableCatalog::dynkin(&algebra).expect("A_n is Dynkin"),
            ));
        }
        let tp = truncated_poly(3, field).expect("k[x]/(x^3) is admissible");
        out.push((
            format!("truncated_poly(3) over F_{modulus}"),
            IndecomposableCatalog::nakayama(&tp).expect("one loop is Nakayama"),
        ));
        let cycle = radical_square_zero_cycle(3, field);
        out.push((
            format!("radical_square_zero_cycle(3) over F_{modulus}"),
            IndecomposableCatalog::nakayama(&cycle).expect("a cycle is Nakayama"),
        ));
        let nakayama = linear_nakayama(&[2, 2, 1], field).expect("[2, 2, 1] is a Kupisch series");
        out.push((
            format!("linear_nakayama([2, 2, 1]) over F_{modulus}"),
            IndecomposableCatalog::nakayama(&nakayama).expect("a linear quiver is Nakayama"),
        ));
        out
    }

    /// An independent count of the pairs, by brute force over every subset of
    /// the catalog and every vertex subset.
    ///
    /// Nothing here is shared with [`enumerate_over_catalog`]: `tau` runs
    /// uncached through the double route, the supports come from dimension
    /// vectors rather than from a Hom table, and the subsets are enumerated by
    /// bitmask with no pruning at all. It returns the pair count, the
    /// histogram by `|M|`, and the number of tau-rigid subsets of at most `n`
    /// entries, which is what the walk counts as nodes.
    fn brute_force(catalog: &IndecomposableCatalog) -> (usize, Vec<usize>, usize) {
        let algebra = catalog.algebra();
        let vertices = algebra.quiver().num_vertices() as usize;
        let k = catalog.len();
        assert!(k < 20, "the bitmask walk needs a small catalog");
        let translates: Vec<Module> = catalog
            .entries()
            .iter()
            .map(|x| tau(x.module()).expect("the fixture translates"))
            .collect();
        let mut tau_hom = vec![vec![0usize; k]; k];
        for (i, x) in catalog.entries().iter().enumerate() {
            for (j, translate) in translates.iter().enumerate() {
                if !translate.is_zero() {
                    tau_hom[i][j] = hom_dim(x.module(), translate).expect("one algebra");
                }
            }
        }
        let mut pairs = 0;
        let mut histogram = vec![0usize; vertices + 1];
        let mut nodes = 0;
        for mask in 0..(1u32 << k) {
            let chosen: Vec<usize> = (0..k).filter(|&i| mask & (1 << i) != 0).collect();
            let rigid = chosen
                .iter()
                .all(|&i| chosen.iter().all(|&j| tau_hom[i][j] == 0));
            if !rigid {
                continue;
            }
            if chosen.len() <= vertices {
                nodes += 1;
            }
            if chosen.len() > vertices {
                continue;
            }
            // Hom(P_v, M) is zero exactly when M vanishes at v.
            let zero_support = (0..vertices)
                .filter(|&v| {
                    chosen
                        .iter()
                        .all(|&i| catalog.entries()[i].module().dim_vector()[v] == 0)
                })
                .count();
            let want = vertices - chosen.len();
            if zero_support < want {
                continue;
            }
            let choices = (0..want).fold(1usize, |acc, t| acc * (zero_support - t) / (t + 1));
            pairs += choices;
            histogram[chosen.len()] += choices;
        }
        (pairs, histogram, nodes)
    }

    // (A, 0) is a support tau-tilting pair over every algebra: A is basic over
    // a basic algebra with one summand per vertex, tau of a projective is
    // zero so A is tau-rigid, Hom(0, A) is zero, and |A| + |0| = n. The
    // fixtures include kronecker(2), which has no catalog: pair verification
    // is general even where enumeration is impossible.
    #[test]
    fn the_regular_pair_is_a_support_tau_tilting_pair() {
        for field in fields() {
            for algebra in [
                linear_an(2, field),
                linear_an(3, field),
                d4(field),
                truncated_poly(3, field).unwrap(),
                linear_nakayama(&[2, 2, 1], field).unwrap(),
                radical_square_zero_cycle(3, field),
                commutative_square(field),
                kronecker(2, field),
                semisimple(3, field),
            ] {
                let n = algebra.quiver().num_vertices() as usize;
                let pair = expect_pair(
                    SupportTauTiltingPair::classify(
                        basic(&regular(&algebra)),
                        support(&algebra, &[]),
                    )
                    .expect("the fixture translates"),
                );
                assert_eq!(pair.module().len(), n);
                assert_eq!(pair.summand_count(), n);
                assert!(pair.is_tau_tilting(), "the projective part is empty");
                assert!(pair.projective().is_empty());
                assert!(pair.rigid().vanishing_pairs().is_empty(), "tau A is zero");
                assert!(pair.verify(), "over F_{}", field.modulus());
            }
        }
    }

    // (0, A) is a support tau-tilting pair: the zero module is tau-rigid with
    // no summand, Hom(A, 0) is zero, and 0 + n = n. It is the pair the design
    // calls a legitimate vertex with an empty module part.
    #[test]
    fn the_zero_module_over_the_full_support_is_a_support_tau_tilting_pair() {
        for field in fields() {
            for algebra in [
                linear_an(2, field),
                d4(field),
                truncated_poly(3, field).unwrap(),
                kronecker(2, field),
            ] {
                let n = algebra.quiver().num_vertices() as usize;
                let pair = expect_pair(
                    SupportTauTiltingPair::classify(
                        basic(&Module::zero(&algebra)),
                        support(&algebra, &all_vertices(&algebra)),
                    )
                    .expect("the zero module needs no translate"),
                );
                assert!(pair.module().is_empty());
                assert_eq!(pair.projective().len(), n);
                assert_eq!(pair.summand_count(), n);
                assert!(!pair.is_tau_tilting(), "the projective part is all of A");
                assert!(pair.rigid().is_zero_module());
                assert!(pair.verify(), "over F_{}", field.modulus());
            }
        }
    }

    // One rejection per condition, over linearly oriented A_2 (arrow 0 -> 1)
    // except for the algebra check. The indecomposables are S_0 = (1, 0),
    // S_1 = P_1 = (0, 1), and P_0 = (1, 1), and tau S_0 = S_1 is the only
    // nonzero translate.
    //
    // 1. Two algebra values built from the same presentation are different
    //    values, so the module part and the support do not share one Arc.
    // 2. (P_0, {1}): Hom(P_1, P_0) has dimension dim (P_0)_1 = 1. The other
    //    three conditions hold, so this isolates condition 2.
    // 3. (S_0 + S_1, {}): Hom(0, M) is zero and 2 + 0 = 2, so the first
    //    failure is Hom(S_1, tau S_0) = End(S_1), of dimension 1.
    // 4. (0, {}): the zero module is tau-rigid and Hom(0, 0) is zero, so the
    //    first failure is 0 + 0 != 2.
    #[test]
    fn each_condition_has_its_own_rejection() {
        for field in fields() {
            let algebra = linear_an(2, field);
            let other = linear_an(2, field);
            let s0 = Module::simple(&algebra, 0);
            let s1 = Module::simple(&algebra, 1);
            let p0 = Module::projective(&algebra, 0);

            let mismatched = expect_rejection(
                SupportTauTiltingPair::classify(basic(&p0), support(&other, &[]))
                    .expect("the algebra check runs before any Hom space"),
            );
            assert_eq!(mismatched.condition(), 1);
            assert!(matches!(mismatched, PairRejection::DifferentAlgebras));

            let hom = expect_rejection(
                SupportTauTiltingPair::classify(basic(&p0), support(&algebra, &[1]))
                    .expect("A_2 translates"),
            );
            assert_eq!(hom.condition(), 2);
            assert!(matches!(
                hom,
                PairRejection::HomFromProjectiveNonzero { vertex: 1, dim: 1 }
            ));

            let rigid = expect_rejection(
                SupportTauTiltingPair::classify(
                    basic(&sum(&algebra, &[&s0, &s1])),
                    support(&algebra, &[]),
                )
                .expect("A_2 translates"),
            );
            assert_eq!(rigid.condition(), 3);
            match &rigid {
                PairRejection::NotTauRigid(witness) => {
                    assert_eq!(witness.translate().dim_vector(), &[0, 1]);
                    assert!(witness.verify());
                }
                other => panic!("expected a tau-rigidity failure, got {other}"),
            }

            let count = expect_rejection(
                SupportTauTiltingPair::classify(
                    basic(&Module::zero(&algebra)),
                    support(&algebra, &[]),
                )
                .expect("the zero module needs no translate"),
            );
            assert_eq!(count.condition(), 4);
            assert!(matches!(
                count,
                PairRejection::SummandCount {
                    module: 0,
                    projective: 0,
                    expected: 2
                }
            ));
        }
    }

    // The sharpest regression test for the right-module convention in this
    // release. Over A_2 with the arrow 0 -> 1 the candidate (P_0, {1}) has
    // |M| + |P| = 2 = n and a tau-rigid module part, so only condition 2
    // separates it from a pair. Under the right-module convention
    // Hom(P_v, X) = X_v, so Hom(P_1, P_0) has dimension (P_0)_1 = 1 and the
    // candidate is rejected. The left-module formula pairs P_1 with the other
    // side and would admit it, which would turn the pentagon into a hexagon.
    #[test]
    fn the_a2_near_miss_is_rejected_by_the_right_module_hom_condition() {
        for field in fields() {
            let algebra = linear_an(2, field);
            let p0 = Module::projective(&algebra, 0);
            // Condition 4 holds on its own.
            assert_eq!(basic(&p0).len() + support(&algebra, &[1]).len(), 2);
            // Condition 3 holds on its own: P_0 is projective, so tau P_0 = 0.
            let alone = expect_pair(
                SupportTauTiltingPair::classify(
                    basic(&sum(&algebra, &[&p0, &Module::simple(&algebra, 0)])),
                    support(&algebra, &[]),
                )
                .expect("A_2 translates"),
            );
            assert!(alone.verify());
            let rejection = expect_rejection(
                SupportTauTiltingPair::classify(basic(&p0), support(&algebra, &[1]))
                    .expect("A_2 translates"),
            );
            assert_eq!(rejection.condition(), 2);
            match rejection {
                PairRejection::HomFromProjectiveNonzero { vertex, dim } => {
                    assert_eq!((vertex, dim), (1, 1));
                    // The stored dimension is the live Hom dimension.
                    assert_eq!(
                        hom_dim(&Module::projective(&algebra, vertex), &p0).unwrap(),
                        dim,
                        "over F_{}",
                        field.modulus()
                    );
                }
                other => panic!("the right-module condition must fire here, got {other}"),
            }
        }
    }

    // The A_2 pentagon, listed by hand. The catalog is S_0 = (1, 0),
    // S_1 = P_1 = (0, 1), P_0 = (1, 1), with tau S_0 = S_1 the only nonzero
    // translate. A subset is tau-rigid unless it holds both S_0 and S_1, and
    // Hom(P_v, M) = 0 forces the support of P to avoid the support of M, so
    // P is the complement of supp M and exists only when its size is n - |M|:
    //
    //   |M| = 0: M = 0,            P = {0, 1}
    //   |M| = 1: M = S_0,          P = {1}
    //   |M| = 1: M = S_1,          P = {0}
    //   |M| = 1: M = P_0,          supp M = {0, 1} leaves no room for P
    //   |M| = 2: M = S_0 + P_0,    P = {}
    //   |M| = 2: M = S_1 + P_0,    P = {}
    //   |M| = 2: M = S_0 + S_1,    not tau-rigid
    //
    // Five pairs, with the histogram [1, 2, 2] by module-summand count.
    #[test]
    fn the_a2_pentagon_lists_five_pairs_by_dimension_vector() {
        for field in fields() {
            let algebra = linear_an(2, field);
            let catalog = IndecomposableCatalog::dynkin(&algebra).expect("A_2 is Dynkin");
            let enumeration = enumerate_over_catalog(&catalog).expect("A_2 enumerates");
            let mut listed: Vec<(Vec<Vec<usize>>, Vec<u32>)> = enumeration
                .pairs()
                .iter()
                .map(|pair| {
                    (
                        pair.module().dim_vectors(),
                        pair.projective().vertices().to_vec(),
                    )
                })
                .collect();
            listed.sort();
            assert_eq!(
                listed,
                vec![
                    (vec![], vec![0, 1]),
                    (vec![vec![0, 1]], vec![0]),
                    (vec![vec![0, 1], vec![1, 1]], vec![]),
                    (vec![vec![1, 0]], vec![1]),
                    (vec![vec![1, 0], vec![1, 1]], vec![]),
                ],
                "over F_{}",
                field.modulus()
            );
            assert_eq!(enumeration.len(), 5);
            assert_eq!(enumeration.histogram(), vec![1, 2, 2]);
            // Two of the five have an empty projective part.
            assert_eq!(
                enumeration
                    .pairs()
                    .iter()
                    .filter(|pair| pair.is_tau_tilting())
                    .count(),
                2
            );
            assert!(enumeration.verify());
        }
    }

    // The counts three independent sources agree on: the mathematics spike by
    // hand, the cost spike by brute force, and the QPA capability spike in
    // GAP. `docs/v0.5-design.md` section 10 records them.
    //
    // Hand derivations for the small fixtures:
    //
    // Semisimple on n vertices. Every indecomposable is a simple, which is
    // also projective, so tau is zero and every subset is tau-rigid. The
    // support of M is the set of chosen vertices, so P is forced to be its
    // complement and always has the required size n - |M|. Pairs correspond
    // to subsets: 2^n, that is 4, 8, and 16 on 2, 3, and 4 vertices.
    //
    // truncated_poly(3) = k[x]/(x^3). The indecomposables are the uniserials
    // U_1, U_2, U_3 = A, and tau U_m = U_m for m = 1, 2, with
    // dim Hom(U_m, U_m) = m > 0, so U_1 and U_2 are not tau-rigid alone. The
    // tau-rigid subsets are {} and {A}, giving (0, A) and (A, 0): 2 pairs.
    //
    // linear_an(2) is the pentagon derived in
    // `the_a2_pentagon_lists_five_pairs_by_dimension_vector`.
    //
    // linear_an(3): the Catalan number C_4 = 14. Writing the interval module
    // on vertices a to b as [a, b], the six indecomposables are [0,0], [1,1],
    // [2,2], [0,1], [1,2], [0,2], with Hom([a,b],[c,d]) nonzero exactly when
    // c <= a <= d <= b, and tau [a,b] = [a+1, b+1] except at b = 2, where the
    // module is projective. The five forbidden co-occurrences are
    // {[1,1],[0,0]}, {[1,2],[0,0]}, {[2,2],[1,1]}, {[1,2],[0,1]},
    // {[2,2],[0,1]}, a 5-cycle on the five non-regular entries with [0,2]
    // isolated. Counting independent sets against the room left for P gives
    // 1 + 3 + 5 + 5 = 14 by module-summand count.
    //
    // linear_nakayama([2, 2, 1]) is kA_3/(ab), with the five intervals [0,0],
    // [1,1], [2,2], [0,1], [1,2]. Here tau [0,0] = [1,1] and tau [1,1] =
    // [2,2], so the forbidden co-occurrences are {[1,1],[0,0]},
    // {[1,2],[0,0]}, {[2,2],[1,1]}: a path with [0,1] isolated. The counts by
    // module-summand count are 1 + 3 + 5 + 3 = 12.
    //
    // radical_square_zero_cycle(3) has the three simples S_v and the three
    // projectives P_v of dimension vector supported on {v, v+1}. It is
    // self-injective with tau S_v = S_{v+1}, and Hom(X, S_w) is nonzero
    // exactly when top X = S_w, so the forbidden co-occurrences are
    // {S_v, S_{v+1}} and {S_v, P_{v+1}}. The counts by module-summand count
    // are 1 + 3 + 6 + 4 = 14.
    //
    // D_4 with zero relations is the W-Catalan number 50, with the histogram
    // [1, 4, 9, 16, 20]. Its own test keeps it separate.
    #[test]
    fn the_enumerated_counts_are_pinned() {
        let expected: Vec<(&str, usize, Vec<usize>)> = vec![
            ("semisimple(2)", 4, vec![1, 2, 1]),
            ("semisimple(3)", 8, vec![1, 3, 3, 1]),
            ("semisimple(4)", 16, vec![1, 4, 6, 4, 1]),
            ("linear_an(2)", 5, vec![1, 2, 2]),
            ("linear_an(3)", 14, vec![1, 3, 5, 5]),
            ("truncated_poly(3)", 2, vec![1, 1]),
            ("radical_square_zero_cycle(3)", 14, vec![1, 3, 6, 4]),
            ("linear_nakayama([2, 2, 1])", 12, vec![1, 3, 5, 3]),
        ];
        for field in fields() {
            let fixtures = catalog_fixtures(field);
            assert_eq!(fixtures.len(), expected.len());
            for ((name, catalog), (short, count, histogram)) in fixtures.iter().zip(&expected) {
                assert!(name.starts_with(short), "{name} is not {short}");
                let enumeration = enumerate_over_catalog(catalog).expect("the fixture enumerates");
                assert_eq!(enumeration.len(), *count, "{name}");
                assert_eq!(&enumeration.histogram(), histogram, "{name}");
                assert_eq!(enumeration.provenance(), catalog.provenance());
                assert_eq!(enumeration.catalog_len(), catalog.len());
                assert!(!enumeration.is_empty());
                assert!(enumeration.verify(), "{name}");
            }
        }
    }

    // The walk visits exactly the tau-rigid subsets of at most n entries,
    // because tau-rigidity is inherited by subsets: every prefix of a
    // tau-rigid subset in index order is tau-rigid, so the subset is reached,
    // and the count bound stops the descent at n. The brute-force count is
    // computed with an uncached tau and no pruning, so it shares nothing with
    // the walk.
    #[test]
    fn the_dfs_node_count_is_the_number_of_tau_rigid_subsets() {
        let expected = [
            ("semisimple(2)", 4usize),
            ("semisimple(3)", 8),
            ("semisimple(4)", 16),
            ("linear_an(2)", 6),
            ("linear_an(3)", 22),
            ("truncated_poly(3)", 2),
            ("radical_square_zero_cycle(3)", 20),
            ("linear_nakayama([2, 2, 1])", 16),
        ];
        for field in fields() {
            for ((name, catalog), (short, nodes)) in catalog_fixtures(field).iter().zip(&expected) {
                assert!(name.starts_with(short), "{name} is not {short}");
                let enumeration = enumerate_over_catalog(catalog).expect("the fixture enumerates");
                let (count, histogram, brute_nodes) = brute_force(catalog);
                assert_eq!(enumeration.nodes_visited(), *nodes, "{name}");
                assert_eq!(enumeration.nodes_visited(), brute_nodes, "{name}");
                assert_eq!(enumeration.len(), count, "{name}");
                assert_eq!(enumeration.histogram(), histogram, "{name}");
            }
        }
    }

    // D_4 with zero relations: 50 pairs with the histogram [1, 4, 9, 16, 20]
    // by module-summand count, from the three sources of section 10. The
    // catalog has 12 entries, one per positive root of D_4. The node count is
    // the number of tau-rigid subsets of at most four entries, cross-checked
    // here against the brute-force walk over all 4096 subsets.
    #[test]
    fn the_d4_enumeration_has_fifty_pairs() {
        for field in fields() {
            let algebra = d4(field);
            let catalog = IndecomposableCatalog::dynkin(&algebra).expect("D_4 is Dynkin");
            assert_eq!(catalog.len(), 12);
            let enumeration = enumerate_over_catalog(&catalog).expect("D_4 enumerates");
            assert_eq!(enumeration.len(), 50, "over F_{}", field.modulus());
            assert_eq!(enumeration.histogram(), vec![1, 4, 9, 16, 20]);
            let (count, histogram, nodes) = brute_force(&catalog);
            assert_eq!(count, 50);
            assert_eq!(histogram, vec![1, 4, 9, 16, 20]);
            // 120 tau-rigid subsets of at most four entries, which is what the
            // walk visits. The brute-force run recounts them over all 4096
            // subsets, so the literal is pinned by two routes.
            assert_eq!(enumeration.nodes_visited(), 120);
            assert_eq!(enumeration.nodes_visited(), nodes);
            assert_eq!(enumeration.provenance(), CatalogProvenance::DynkinZeroIdeal);
            // Every pair recomputes all four conditions, and no two of the 50
            // are isomorphic.
            assert!(enumeration.verify(), "over F_{}", field.modulus());
        }
    }

    // Both catalog constructors reject the Kronecker algebra, which is
    // tau-tilting infinite, so no enumeration is attempted over it. There is
    // no route from an algebra to a CatalogEnumeration that skips a catalog.
    #[test]
    fn the_kronecker_algebra_has_no_catalog() {
        for field in fields() {
            let algebra = kronecker(2, field);
            assert_eq!(
                IndecomposableCatalog::nakayama(&algebra).unwrap_err(),
                EnumerateError::NotNakayama {
                    vertex: 0,
                    incoming: 0,
                    outgoing: 2
                }
            );
            assert!(matches!(
                IndecomposableCatalog::dynkin(&algebra).unwrap_err(),
                DynkinError::NotDynkin { .. }
            ));
        }
    }

    // The almost complete pairs over A_2, listed by hand. The condition is
    // |M| + |P| = 1, so either M is one tau-rigid indecomposable with an empty
    // support, or M is zero and P is a single vertex. All three
    // indecomposables are tau-rigid alone, and Hom(P_v, 0) is zero for both
    // vertices, so there are 5 almost complete pairs. That is the edge count
    // of the pentagon, as it must be: each edge is one almost complete pair
    // with its two completions.
    #[test]
    fn the_a2_almost_complete_pairs_are_the_five_edges() {
        for field in fields() {
            let algebra = linear_an(2, field);
            let modules = [
                Module::simple(&algebra, 0),
                Module::simple(&algebra, 1),
                Module::projective(&algebra, 0),
            ];
            let mut found = 0;
            for m in &modules {
                let pair = AlmostCompletePair::new(basic(m), support(&algebra, &[]))
                    .expect("A_2 translates")
                    .expect("a tau-rigid indecomposable with no support is almost complete");
                assert_eq!(pair.summand_count(), 1);
                assert!(pair.verify());
                found += 1;
            }
            for v in [0u32, 1] {
                let pair = AlmostCompletePair::new(
                    basic(&Module::zero(&algebra)),
                    support(&algebra, &[v]),
                )
                .expect("the zero module needs no translate")
                .expect("(0, P_v) is almost complete");
                assert!(pair.module().is_empty());
                assert_eq!(pair.projective().len(), 1);
                assert!(pair.verify());
                found += 1;
            }
            assert_eq!(found, 5, "over F_{}", field.modulus());
        }
    }

    // The two totals separate the two types: a support tau-tilting pair has
    // n summands and an almost complete pair has n - 1, so neither is the
    // other and the rejection names condition 4 both ways.
    #[test]
    fn the_two_pair_types_reject_each_other_on_the_count() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let a = regular(&algebra);
            let full = SupportTauTiltingPair::new(basic(&a), support(&algebra, &[]))
                .expect("A_3 translates")
                .expect("(A, 0) is a pair");
            assert_eq!(full.summand_count(), 3);
            let as_almost = AlmostCompletePair::classify(basic(&a), support(&algebra, &[]))
                .expect("A_3 translates");
            match as_almost {
                AlmostCompleteClassification::Rejected(PairRejection::SummandCount {
                    module,
                    projective,
                    expected,
                }) => assert_eq!((module, projective, expected), (3, 0, 2)),
                other => panic!("expected a count rejection, got {other:?}"),
            }
            // P_0 + P_1 is tau-rigid with two summands, which is n - 1 over
            // A_3, and Hom(0, M) is zero.
            let two = sum(
                &algebra,
                &[
                    &Module::projective(&algebra, 0),
                    &Module::projective(&algebra, 1),
                ],
            );
            let almost = AlmostCompletePair::new(basic(&two), support(&algebra, &[]))
                .expect("A_3 translates")
                .expect("(P_0 + P_1, 0) is almost complete");
            assert_eq!(almost.summand_count(), 2);
            assert!(almost.verify());
            let as_full = SupportTauTiltingPair::classify(basic(&two), support(&algebra, &[]))
                .expect("A_3 translates");
            assert_eq!(
                expect_rejection(as_full).condition(),
                4,
                "over F_{}",
                field.modulus()
            );
        }
    }

    // Every accepted pair verifies, and the one tamper the type still admits
    // fails. The support is derived from the module part, so there is no
    // support field to tamper with and no vanishing witness to borrow: the
    // tau-rigidity witness is the only stored claim left.
    #[test]
    fn a_tampered_pair_fails_verification() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let a = regular(&algebra);
            let pair = SupportTauTiltingPair::new(basic(&a), support(&algebra, &[]))
                .expect("A_3 translates")
                .expect("(A, 0) is a pair");
            assert!(pair.verify());
            assert!(pair.projective().is_empty(), "A is sincere");

            // A tau-rigidity witness borrowed from another pair with the same
            // summand count. S_1 + P_1 + P_0 is a pair with three summands, so
            // the length check passes and the summand identity check is what
            // fails.
            let s1 = Module::simple(&algebra, 1);
            let p1 = Module::projective(&algebra, 1);
            let mut forged = SupportTauTiltingPair::new(basic(&a), support(&algebra, &[]))
                .expect("A_3 translates")
                .expect("(A, 0) is a pair");
            let donor = SupportTauTiltingPair::new(
                basic(&sum(
                    &algebra,
                    &[&s1, &p1, &Module::projective(&algebra, 0)],
                )),
                support(&algebra, &[]),
            )
            .expect("A_3 translates")
            .expect("(S_1 + P_1 + P_0, 0) is a pair");
            assert!(donor.rigid().verify(), "the donor witness is honest");
            assert_eq!(
                donor.rigid().summands().len(),
                forged.rigid.summands().len()
            );
            forged.rigid = donor.rigid().clone();
            assert!(!forged.verify(), "over F_{}", field.modulus());
        }
    }

    // The projective part is forced, so a candidate that passes conditions 1
    // to 4 with a support strictly inside the support complement cannot exist.
    // Over A_3 the closest a caller gets is (S_1 + P_1, {0}), where the
    // complement of the support (0, 2, 1) is exactly {0}: dropping vertex 0
    // breaks the count instead of producing a second pair on the same module.
    #[test]
    fn the_projective_part_of_a_pair_is_the_whole_support_complement() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let m = sum(
                &algebra,
                &[
                    &Module::simple(&algebra, 1),
                    &Module::projective(&algebra, 1),
                ],
            );
            assert_eq!(basic(&m).module().dim_vector(), &[0, 2, 1]);
            let pair = SupportTauTiltingPair::new(basic(&m), support(&algebra, &[0]))
                .expect("A_3 translates")
                .expect("(S_1 + P_1, P_0) is a pair");
            assert_eq!(pair.projective().vertices(), [0]);
            let short = expect_rejection(
                SupportTauTiltingPair::classify(basic(&m), support(&algebra, &[]))
                    .expect("A_3 translates"),
            );
            assert_eq!(short.condition(), 4, "over F_{}", field.modulus());
        }
    }

    // A shared cache computes one translate per catalog entry across a whole
    // run. Over A_3 that is six translates for the six catalog entries, one
    // miss each and no hit, because each entry is classified once and the
    // cache is keyed by module identity.
    #[test]
    fn a_shared_cache_serves_a_whole_enumeration() {
        let field = f5();
        let algebra = linear_an(3, field);
        let catalog = IndecomposableCatalog::dynkin(&algebra).expect("A_3 is Dynkin");
        let mut cache = TauCache::new();
        for (i, entry) in catalog.entries().iter().enumerate() {
            let pair = SupportTauTiltingPair::classify_with_cache(
                basic(entry.module()),
                support(&algebra, &[]),
                &[i],
                Some(&mut cache),
            )
            .expect("A_3 translates");
            // A single indecomposable is never a pair over A_3: 1 + |P| = 3
            // needs two support vertices outside its support, and an empty
            // support leaves |M| + |P| = 1. Every entry is tau-rigid alone and
            // Hom(0, X) is zero, so the rejection is condition 4 every time.
            assert_eq!(expect_rejection(pair).condition(), 4);
        }
        assert_eq!(cache.len(), catalog.len());
        assert_eq!(cache.misses(), catalog.len() as u64);
    }

    // One index per summand, or the call is rejected before any work.
    #[test]
    fn a_wrong_index_count_is_rejected() {
        let algebra = linear_an(3, f5());
        let error = SupportTauTiltingPair::classify_with_cache(
            basic(&regular(&algebra)),
            support(&algebra, &[]),
            &[0, 1],
            None,
        )
        .unwrap_err();
        assert!(matches!(
            error,
            SupportTauError::SummandIndexCount {
                indices: 2,
                summands: 3
            }
        ));
    }

    /// The Kronecker representation `(I_3, C)` over F_2 with `C` the companion
    /// matrix of x^3 + x + 1, irreducible over F_2, so `End(W)` is the field
    /// F_8 and the residue degree is 3. Same module as
    /// `arquiver::tests::f8_module`, `indec.rs`, and `approx.rs`.
    fn f8_module(algebra: &Arc<Algebra>, field: PrimeField) -> Module {
        let mut companion = DenseMat::zero(3, 3);
        companion.set(0, 1, field.one());
        companion.set(1, 2, field.one());
        companion.set(2, 0, field.one());
        companion.set(2, 1, field.one());
        Module::new(
            algebra.clone(),
            vec![3, 3],
            vec![DenseMat::identity(3), companion],
        )
        .expect("a Kronecker representation is a module")
    }

    // Residue degree above 1 at the pair layer. `docs/v0.5-design.md` section
    // 8 rests field generality on residue division rings larger than the prime
    // field, and the tau-rigidity condition is where they enter: it runs
    // Hom(X_i, tau X_j) over the summands.
    //
    // W is the F_8 module, of dimension vector [3, 3] over kronecker(2, F_2).
    // It is regular of defect zero, so tau W is isomorphic to W, and the
    // condition-3 Hom system is Hom(W, W) = F_8, of F_2 dimension 3. The
    // candidate (W + P_0, {}) has |M| + |P| = 2 = n and passes conditions 1
    // and 2, so it reaches condition 3 with the F_8 system and is rejected
    // there.
    //
    // No tau-rigid pair over kronecker(2) can hold W, and none can hold any
    // other module of residue degree above 1 either: over a path algebra a
    // tau-rigid indecomposable is exceptional, and an exceptional module has
    // dim End = q(dim M) = 1. So the rejection is the only route residue
    // degree 3 has to this layer, not a weaker version of a positive test.
    #[test]
    fn the_f8_module_reaches_the_tau_rigidity_condition() {
        let field = f2();
        let algebra = kronecker(2, field);
        let w = f8_module(&algebra, field);
        let decomposition = basic(&w);
        assert_eq!(decomposition.len(), 1);
        assert_eq!(decomposition.summands()[0].residue_degree(), 3);
        assert_eq!(decomposition.summands()[0].endo().dim(), 3);

        let translate = tau(&w).expect("kronecker translates");
        assert!(!translate.is_zero(), "W is not projective");
        assert_eq!(translate.dim_vector(), &[3, 3]);
        assert!(matches!(
            is_isomorphic(&w, &translate),
            Ok(IsoOutcome::Isomorphic(_))
        ));
        // The Hom system condition 3 runs is End(W) = F_8, of F_2 dimension 3.
        assert_eq!(hom_dim(&w, &translate).unwrap(), 3);

        // (W, {}) alone: the summand list is W, so the only Hom system the
        // condition runs is Hom(W, tau W) = End(W) = F_8. Condition 3 is
        // checked before the count, so the rejection names it even though
        // |M| + |P| = 1 is short of n = 2.
        let alone = expect_rejection(
            SupportTauTiltingPair::classify(basic(&w), support(&algebra, &[]))
                .expect("kronecker translates"),
        );
        assert_eq!(alone.condition(), 3);
        match &alone {
            PairRejection::NotTauRigid(witness) => {
                assert_eq!(witness.source().dim_vector(), &[3, 3]);
                assert_eq!(witness.translate().dim_vector(), &[3, 3]);
                assert!(witness.verify());
            }
            other => panic!("expected a tau-rigidity failure, got {other}"),
        }

        // (W + P_0, {}) has the count of a pair, |M| + |P| = 2 = n, and
        // Hom(0, M) = 0, so it passes conditions 1, 2, and 4 and is rejected
        // on tau-rigidity alone. tau P_0 = 0, so tau W is the only translate
        // any Hom system in the check can end at.
        let p0 = Module::projective(&algebra, 0);
        let candidate = sum(&algebra, &[&w, &p0]);
        assert_eq!(basic(&candidate).len() + support(&algebra, &[]).len(), 2);
        let rejection = expect_rejection(
            SupportTauTiltingPair::classify(basic(&candidate), support(&algebra, &[]))
                .expect("kronecker translates"),
        );
        assert_eq!(rejection.condition(), 3);
        match &rejection {
            PairRejection::NotTauRigid(witness) => {
                assert_eq!(witness.translate().dim_vector(), &[3, 3]);
                assert!(witness.verify());
            }
            other => panic!("expected a tau-rigidity failure, got {other}"),
        }
    }

    // A duplicated vertex must not pass verification, which is clause 2 of the
    // closure obligations in `docs/v0.5-design.md` section 8. The duplicate is
    // built separately through the checking constructor, so every pair in the
    // list verifies on its own and only the pairwise-distinctness loop can
    // catch it.
    //
    // The two indices are the ends of the A_2 pentagon in the walk order
    // `CatalogEnumeration::pairs` documents, module subsets in lexicographic
    // order over catalog positions and supports lexicographic within a subset.
    // The empty subset comes first, so pair 0 is (0, {0, 1}), and the last
    // subset gives pair 4, which is (S_0 + P_0, {}). Both shapes are asserted
    // below. The empty module part exercises the distinctness loop where
    // pair_iso has no summand to match.
    #[test]
    fn a_duplicated_pair_fails_verification() {
        let field = f5();
        let algebra = linear_an(2, field);
        let catalog = IndecomposableCatalog::dynkin(&algebra).expect("A_2 is Dynkin");
        for (index, dim_vectors, vertices) in [
            (0usize, Vec::new(), vec![0u32, 1]),
            (4, vec![vec![1, 0], vec![1, 1]], Vec::new()),
        ] {
            let mut enumeration = enumerate_over_catalog(&catalog).expect("A_2 enumerates");
            assert_eq!(enumeration.len(), 5);
            assert!(enumeration.verify());
            let duplicate = {
                let pair = &enumeration.pairs()[index];
                assert_eq!(pair.module().dim_vectors(), dim_vectors);
                assert_eq!(pair.projective().vertices(), vertices);
                let module = BasicDecomposition::new(pair.module().module())
                    .expect("the module part of a pair is basic");
                let projective = ProjectiveSupport::new(&algebra, pair.projective().vertices())
                    .expect("the support of a pair is in range");
                SupportTauTiltingPair::new(module, projective)
                    .expect("A_2 translates")
                    .expect("a rebuilt pair is a pair")
            };
            assert!(duplicate.verify(), "the duplicate is honest on its own");
            enumeration.pairs.push(duplicate);
            assert_eq!(enumeration.len(), 6);
            assert!(!enumeration.verify(), "a duplicate of pair {index} passed");
        }
    }

    // The almost complete side of `a_tampered_pair_fails_verification`, on the
    // (P_0 + P_1, 0) fixture of
    // `the_two_pair_types_reject_each_other_on_the_count`.
    #[test]
    fn a_tampered_almost_complete_pair_fails_verification() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let p0 = Module::projective(&algebra, 0);
            let p1 = Module::projective(&algebra, 1);
            let p2 = Module::projective(&algebra, 2);
            let two = sum(&algebra, &[&p0, &p1]);
            let almost = |m: &Module| {
                AlmostCompletePair::new(basic(m), support(&algebra, &[]))
                    .expect("A_3 translates")
                    .expect("a sum of two projectives is almost complete")
            };
            let pair = almost(&two);
            assert!(pair.verify());
            // P_0 + P_1 has dimension vector (1, 2, 2), so s = 3 = r + 1 and
            // the support complement is empty. P is the whole complement, and
            // no vertex is omitted.
            assert_eq!(pair.module().module().dim_vector(), &[1, 2, 2]);
            assert_eq!(pair.omitted_vertex(), None);
            assert!(pair.projective().is_empty());

            // P_1 + P_2 has dimension vector (0, 1, 2), so s = 2 = r and the
            // complement is {0}. P is the complement minus one vertex, which
            // leaves it empty and records the omission.
            let donor = almost(&sum(&algebra, &[&p1, &p2]));
            assert!(donor.verify(), "the donor is honest");
            assert_eq!(donor.module().module().dim_vector(), &[0, 1, 2]);
            assert_eq!(donor.omitted_vertex(), Some(0));
            assert!(donor.projective().is_empty());

            // An omitted vertex outside the support complement. Vertex 1 is in
            // the support of P_1 + P_2, so it is not the crate's to omit, and
            // claiming it leaves the derived support one vertex too long.
            let mut moved = almost(&sum(&algebra, &[&p1, &p2]));
            moved.omitted = Some(1);
            assert!(!moved.verify());

            // A tau-rigidity witness from the same donor. Both parts have two
            // summands, so the length check passes and the summand identity
            // check is what fails.
            let mut forged = almost(&two);
            assert_eq!(
                donor.rigid().summands().len(),
                forged.rigid.summands().len()
            );
            forged.rigid = donor.rigid().clone();
            assert!(!forged.verify(), "over F_{}", field.modulus());
        }
    }
}

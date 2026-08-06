//! Bound quiver algebras `kQ/I` with a certificate-verified normal-word basis.
//!
//! Two types live here. [`MonomialPresentation`] is the field-free analysis
//! type for monomial ideals: forbidden words, the standard-path automaton, and
//! the exact finiteness decision. [`Algebra`] is the sole runtime algebra
//! type: it owns a prime field, the reduced Groebner basis of its ideal, the
//! normal-word basis, and per-arrow multiplication tables. Every `Algebra`
//! comes from one pipeline: completion emits a certificate, the independent
//! verifier checks the certificate bytes, and the constructor builds the
//! tables from the verified data. Nothing in this module truncates silently.

use std::fmt;
use std::sync::Arc;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::certificate::Certificate;
use crate::completion::{CompletionLimits, Outcome, TruncationDiagnostics, complete};
use crate::field::{Fp, PrimeField};
use crate::linalg::DenseMat;
use crate::order::word_cmp;
use crate::quiver::{ArrowId, PathWord, Quiver, QuiverError};
use crate::relation::{Presentation, Relation, RelationError};
use crate::verify::{CycleWitness, VerifiedCompletion, VerifyError, verify};

/// Index into [`Algebra::basis`] (and [`MonomialPresentation::basis`]).
pub type BasisIdx = usize;

/// Rejected monomial presentation input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AlgebraError {
    /// Forbidden word `index` has length < 2. Admissibility needs `I ⊆ J²`.
    ForbiddenWordTooShort { index: usize, len: usize },
    /// Forbidden word `index` is not a path in the quiver.
    ForbiddenWordInvalid { index: usize, error: QuiverError },
    /// The standard-path language is infinite; this crate supports
    /// finite-dimensional algebras only.
    InfiniteDimensional,
    /// The Kupisch series violates the conditions documented on the
    /// constructor.
    InvalidKupisch { reason: String },
    /// No path with this start and length exists in the linear quiver.
    ZeroPathOutOfRange { start: usize, len: usize },
}

impl fmt::Display for AlgebraError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ForbiddenWordTooShort { index, len } => write!(
                f,
                "forbidden word {index} has length {len}; admissibility needs length >= 2"
            ),
            Self::ForbiddenWordInvalid { index, error } => {
                write!(f, "forbidden word {index} is not a path: {error}")
            }
            Self::InfiniteDimensional => f.write_str(
                "the standard-path language is infinite; this crate supports finite-dimensional algebras only",
            ),
            Self::InvalidKupisch { reason } => write!(f, "invalid Kupisch series: {reason}"),
            Self::ZeroPathOutOfRange { start, len } => write!(
                f,
                "no path of length {len} starting at vertex {start} in the linear quiver"
            ),
        }
    }
}

impl std::error::Error for AlgebraError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::ForbiddenWordInvalid { error, .. } => Some(error),
            _ => None,
        }
    }
}

/// Rejected [`Algebra`] construction input, or an exhausted or defective
/// pipeline run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AlgebraBuildError {
    /// A monomial presentation was rejected before the pipeline ran.
    Monomial(AlgebraError),
    /// A relation or presentation was rejected before the pipeline ran.
    Relation(RelationError),
    /// The verifier proved the quotient infinite dimensional. This variant
    /// carries the certificate of the completed basis alongside the cycle
    /// witness.
    InfiniteDimensional {
        certificate: Box<Certificate>,
        witness: CycleWitness,
    },
    /// Completion ran out of budget; no certificate exists.
    Truncated(TruncationDiagnostics),
    /// The verifier rejected the engine's own certificate for a reason other
    /// than infinite dimension. This is an engine defect, still typed.
    Verification(VerifyError),
}

impl fmt::Display for AlgebraBuildError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Monomial(error) => write!(f, "monomial presentation rejected: {error}"),
            Self::Relation(error) => write!(f, "relation rejected: {error}"),
            Self::InfiniteDimensional { witness, .. } => write!(
                f,
                "the quotient is infinite dimensional: prefix {:?}, cycle {:?}",
                witness.prefix, witness.cycle
            ),
            Self::Truncated(diagnostics) => write!(
                f,
                "completion ran out of budget ({:?}): basis {}, pending ambiguities {}, steps {}",
                diagnostics.reason,
                diagnostics.basis_len,
                diagnostics.pending_ambiguities,
                diagnostics.steps_used
            ),
            Self::Verification(error) => {
                write!(f, "the engine's certificate failed verification: {error}")
            }
        }
    }
}

impl std::error::Error for AlgebraBuildError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Monomial(error) => Some(error),
            Self::Relation(error) => Some(error),
            Self::Verification(error) => Some(error),
            _ => None,
        }
    }
}

/// The field-free combinatorics of a monomial ideal: `kQ/(forbidden)` as an
/// analysis object, not a runtime algebra.
///
/// The basis consists of all standard paths: paths containing no forbidden
/// word as a contiguous factor. Construction either certifies that the basis
/// is finite or fails. The basis order is fixed: `basis[v]` is the trivial
/// path `e_v` for `v < num_vertices`; the remaining entries are sorted by
/// length, then source vertex, then lexicographic arrow word. Build a runtime
/// [`Algebra`] from it with [`Algebra::from_monomial`].
///
/// ```
/// use auslander::algebra::MonomialPresentation;
/// use auslander::quiver::{ArrowId, Quiver};
/// let loop_x = Quiver::new(1, &[(0, 0)]).unwrap();
/// let m = MonomialPresentation::new(loop_x, vec![vec![ArrowId(0); 2]]).unwrap();
/// assert_eq!(m.dim(), 2); // k[x]/(x²): basis e, x
/// ```
#[derive(Debug)]
pub struct MonomialPresentation {
    quiver: Quiver,
    forbidden: Vec<Vec<ArrowId>>,
    basis: Vec<PathWord>,
    index_of: FxHashMap<Vec<ArrowId>, BasisIdx>,
    from: Vec<Vec<BasisIdx>>,
    to: Vec<Vec<BasisIdx>>,
    between: Vec<Vec<Vec<BasisIdx>>>,
}

impl MonomialPresentation {
    /// Builds `kQ/(forbidden)` with a certified finite standard-path basis.
    ///
    /// Forbidden words must be composable paths of length >= 2. This
    /// constructor drops any word that contains another forbidden word as a
    /// factor; the generated ideal is unchanged. Errors with
    /// [`AlgebraError::InfiniteDimensional`] when the standard-path language
    /// is infinite. Cycle detection on the forbidden-prefix automaton decides
    /// this exactly.
    pub fn new(
        quiver: Quiver,
        forbidden: Vec<Vec<ArrowId>>,
    ) -> Result<MonomialPresentation, AlgebraError> {
        for (index, word) in forbidden.iter().enumerate() {
            if word.len() < 2 {
                return Err(AlgebraError::ForbiddenWordTooShort {
                    index,
                    len: word.len(),
                });
            }
            if let Err(error) = PathWord::from_arrows(&quiver, word) {
                return Err(AlgebraError::ForbiddenWordInvalid { index, error });
            }
        }
        let forbidden = minimal_words(forbidden);
        let automaton = Automaton::build(&quiver, &forbidden);
        if automaton.has_cycle() {
            return Err(AlgebraError::InfiniteDimensional);
        }

        let n = quiver.num_vertices() as usize;
        let mut basis: Vec<PathWord> = (0..quiver.num_vertices())
            .map(PathWord::trivial_unchecked)
            .collect();
        let mut state: Vec<usize> = (0..n).collect();
        let mut level_start = 0;
        while level_start < basis.len() {
            let level_end = basis.len();
            for i in level_start..level_end {
                let word = basis[i].arrows().to_vec();
                let target = basis[i].target();
                let s = state[i];
                for &a in quiver.arrows_from(target) {
                    if let Some(next) = automaton.step(s, a) {
                        let mut extended = word.clone();
                        extended.push(a);
                        basis.push(PathWord::from_arrows_unchecked(&quiver, extended));
                        state.push(next);
                    }
                }
            }
            level_start = level_end;
        }

        let (index_of, from, to, between) = index_basis(&quiver, &basis);
        Ok(MonomialPresentation {
            quiver,
            forbidden,
            basis,
            index_of,
            from,
            to,
            between,
        })
    }

    /// `dim_k A` = number of standard paths.
    #[inline]
    pub fn dim(&self) -> usize {
        self.basis.len()
    }

    #[inline]
    pub fn quiver(&self) -> &Quiver {
        &self.quiver
    }

    /// The standard-path basis, in the order documented on the type.
    #[inline]
    pub fn basis(&self) -> &[PathWord] {
        &self.basis
    }

    /// The minimal forbidden words, sorted by length then arrow word.
    #[inline]
    pub fn forbidden(&self) -> &[Vec<ArrowId>] {
        &self.forbidden
    }

    /// Basis index of `path`: `Ok(Some(i))` when the path is standard,
    /// `Ok(None)` when it is a valid path of the quiver but zero in the algebra
    /// (contains a forbidden factor), and `Err` when it is not a path of this
    /// presentation's quiver at all (see [`PathWord::validate_in`]).
    pub fn path_index(&self, path: &PathWord) -> Result<Option<BasisIdx>, QuiverError> {
        path.validate_in(&self.quiver)?;
        if path.is_trivial() {
            Ok(Some(path.source() as usize))
        } else {
            Ok(self.index_of.get(path.arrows()).copied())
        }
    }

    /// Basis index of `e_v`; equals `v`. Panics if `v >= num_vertices`.
    pub fn vertex_idempotent(&self, v: u32) -> BasisIdx {
        assert!(v < self.quiver.num_vertices());
        v as usize
    }

    /// Basis indices of paths with source `v`, the basis of `e_v A = P_v`.
    /// Panics if `v >= num_vertices`.
    #[inline]
    pub fn paths_from(&self, v: u32) -> &[BasisIdx] {
        &self.from[v as usize]
    }

    /// Basis indices of paths with target `v`, the basis of `A e_v`.
    /// Panics if `v >= num_vertices`.
    #[inline]
    pub fn paths_to(&self, v: u32) -> &[BasisIdx] {
        &self.to[v as usize]
    }

    /// Basis indices of paths from `u` to `v`, the basis of `e_u A e_v`.
    /// Panics if either vertex is out of range.
    #[inline]
    pub fn paths_between(&self, u: u32, v: u32) -> &[BasisIdx] {
        &self.between[u as usize][v as usize]
    }

    /// Cartan matrix: `c[i][j] = dim e_i A e_j`, the number of standard
    /// paths from `i` to `j`; row `i` is the dimension vector of the
    /// projective `P_i = e_i A`.
    pub fn cartan_matrix(&self) -> Vec<Vec<usize>> {
        self.between
            .iter()
            .map(|row| row.iter().map(Vec::len).collect())
            .collect()
    }
}

/// Index maps shared by both basis-carrying types: word to index for the
/// non-trivial words, plus the source, target, and component partitions.
type BasisIndexes = (
    FxHashMap<Vec<ArrowId>, BasisIdx>,
    Vec<Vec<BasisIdx>>,
    Vec<Vec<BasisIdx>>,
    Vec<Vec<Vec<BasisIdx>>>,
);

fn index_basis(quiver: &Quiver, basis: &[PathWord]) -> BasisIndexes {
    let n = quiver.num_vertices() as usize;
    let mut index_of = FxHashMap::default();
    for (i, p) in basis.iter().enumerate() {
        if !p.is_trivial() {
            index_of.insert(p.arrows().to_vec(), i);
        }
    }
    let mut from = vec![Vec::new(); n];
    let mut to = vec![Vec::new(); n];
    let mut between = vec![vec![Vec::new(); n]; n];
    for (i, p) in basis.iter().enumerate() {
        from[p.source() as usize].push(i);
        to[p.target() as usize].push(i);
        between[p.source() as usize][p.target() as usize].push(i);
    }
    (index_of, from, to, between)
}

/// The runtime algebra `kQ/I` over a checked prime field.
///
/// Construction runs the full pipeline: completion of the relations into the
/// reduced Groebner basis, certificate emission, and independent verification
/// of the certificate bytes. The basis consists of the normal words (words
/// irreducible by the Groebner leading words) in the fixed order: `basis[v]`
/// is the trivial path `e_v` for `v < num_vertices`; the remaining entries
/// are sorted by length, then source vertex, then lexicographic arrow word.
/// Multiplication tables store normal forms, so every product is exact.
///
/// ```
/// use auslander::algebra::dual_numbers;
/// use auslander::field::PrimeField;
/// let a = dual_numbers(PrimeField::new(5).unwrap());
/// assert_eq!(a.dim(), 2); // k[x]/(x²): basis e, x
/// ```
#[derive(Debug)]
pub struct Algebra {
    quiver: Quiver,
    field: PrimeField,
    relations: Vec<Relation>,
    certificate: Certificate,
    limits: CompletionLimits,
    basis: Vec<PathWord>,
    index_of: FxHashMap<Vec<ArrowId>, BasisIdx>,
    from: Vec<Vec<BasisIdx>>,
    to: Vec<Vec<BasisIdx>>,
    between: Vec<Vec<Vec<BasisIdx>>>,
    // right_mul[i][a]: NF(basis[i]·a); left_mul[a][i]: NF(a·basis[i]).
    // Rows are sorted by basis index. Every entry of a row shares the source
    // of basis[i] (resp. the source of a) and the target of a (resp. of
    // basis[i]).
    right_mul: Vec<Vec<Vec<(BasisIdx, Fp)>>>,
    left_mul: Vec<Vec<Vec<(BasisIdx, Fp)>>>,
}

impl Algebra {
    /// Runs the full pipeline on `presentation`: completion, certificate
    /// serialization, verification of the bytes, and table construction from
    /// the verified data.
    ///
    /// Errors: [`AlgebraBuildError::Truncated`] when a budget of `limits`
    /// runs out, [`AlgebraBuildError::InfiniteDimensional`] when the verifier
    /// proves the quotient infinite dimensional, and
    /// [`AlgebraBuildError::Verification`] when the verifier rejects the
    /// certificate for any other reason (an engine defect).
    ///
    /// The algebra stores `limits` as its effective completion limits, and
    /// every derived completion, [`crate::opposite::opposite`] included,
    /// runs with them.
    pub fn new(
        presentation: Presentation,
        limits: &CompletionLimits,
    ) -> Result<Arc<Algebra>, AlgebraBuildError> {
        let certificate = match complete(&presentation, limits) {
            Outcome::Complete(certificate) => certificate,
            Outcome::Truncated(diagnostics) => {
                return Err(AlgebraBuildError::Truncated(diagnostics));
            }
        };
        match verify(&certificate.to_canonical_json()) {
            Ok(verified) => Ok(Algebra::from_verified_with_limits(verified, limits)),
            Err(VerifyError::InfiniteDimensional { witness }) => {
                Err(AlgebraBuildError::InfiniteDimensional {
                    certificate: Box::new(certificate),
                    witness,
                })
            }
            Err(error) => Err(AlgebraBuildError::Verification(error)),
        }
    }

    /// Builds the algebra from an already verified completion. This is the
    /// dump, reload, and reverify path: serialize with
    /// [`Algebra::certificate`], later call [`crate::verify::verify`] on the
    /// bytes, and rebuild from the token. Infallible because verification
    /// already proved the quotient finite dimensional.
    ///
    /// The rebuilt algebra uses [`CompletionLimits::default`] as its
    /// effective limits. This is policy: certificate bytes are untrusted
    /// input, and untrusted input must never carry or select downstream
    /// resource budgets. Use [`Algebra::from_verified_with_limits`] when a
    /// reload flow wants to preserve the budgets of the original build.
    pub fn from_verified(verified: VerifiedCompletion) -> Arc<Algebra> {
        Algebra::from_verified_with_limits(verified, &CompletionLimits::default())
    }

    /// [`Algebra::from_verified`] with explicit effective completion
    /// limits. The limits come from the caller, never from the certificate
    /// bytes; downstream completions such as
    /// [`crate::opposite::opposite`] run with them.
    pub fn from_verified_with_limits(
        verified: VerifiedCompletion,
        limits: &CompletionLimits,
    ) -> Arc<Algebra> {
        let quiver = verified.quiver().clone();
        let field = verified.field();
        let relations: Vec<Relation> = verified
            .basis()
            .iter()
            .map(|element| {
                let terms = element
                    .iter()
                    .map(|(coeff, word)| (*coeff, word.arrows().to_vec()))
                    .collect();
                Relation::new(&quiver, field, terms)
                    .expect("a verified basis element is a valid relation")
            })
            .collect();
        let basis = verified.normal_words().to_vec();
        let (index_of, from, to, between) = index_basis(&quiver, &basis);
        let mut algebra = Algebra {
            quiver,
            field,
            relations,
            certificate: verified.certificate().clone(),
            limits: limits.clone(),
            basis,
            index_of,
            from,
            to,
            between,
            right_mul: Vec::new(),
            left_mul: Vec::new(),
        };
        let num_arrows = algebra.quiver.num_arrows();
        let mut right_mul = vec![vec![Vec::new(); num_arrows]; algebra.basis.len()];
        let mut left_mul = vec![vec![Vec::new(); algebra.basis.len()]; num_arrows];
        for (i, p) in algebra.basis.iter().enumerate() {
            for &a in algebra.quiver.arrows_from(p.target()) {
                let mut word = p.arrows().to_vec();
                word.push(a);
                right_mul[i][a.index()] = algebra.nf_arrow_word(word);
            }
            for &a in algebra.quiver.arrows_to(p.source()) {
                let mut word = vec![a];
                word.extend_from_slice(p.arrows());
                left_mul[a.index()][i] = algebra.nf_arrow_word(word);
            }
        }
        algebra.right_mul = right_mul;
        algebra.left_mul = left_mul;
        Arc::new(algebra)
    }

    /// Routes a monomial presentation through the same pipeline: each
    /// forbidden word becomes a one-term relation, then [`Algebra::new`]
    /// runs with `limits`. The resulting basis equals the standard-path
    /// basis of `presentation` word for word.
    /// [`monomial_completion_limits`] derives limits that are always
    /// adequate for a monomial presentation.
    pub fn from_monomial(
        field: PrimeField,
        presentation: &MonomialPresentation,
        limits: &CompletionLimits,
    ) -> Result<Arc<Algebra>, AlgebraBuildError> {
        let quiver = presentation.quiver().clone();
        let relations = presentation
            .forbidden()
            .iter()
            .map(|word| Relation::new(&quiver, field, vec![(field.one(), word.clone())]))
            .collect::<Result<Vec<Relation>, RelationError>>()
            .map_err(AlgebraBuildError::Relation)?;
        let bundled =
            Presentation::new(quiver, field, relations).map_err(AlgebraBuildError::Relation)?;
        let algebra = Algebra::new(bundled, limits)?;
        debug_assert_eq!(
            algebra.basis(),
            presentation.basis(),
            "the normal words of a monomial ideal are its standard paths"
        );
        Ok(algebra)
    }

    /// The verified certificate this algebra was built from. Serialize it
    /// with [`Certificate::to_canonical_json`] for dumping.
    #[inline]
    pub fn certificate(&self) -> &Certificate {
        &self.certificate
    }

    /// The effective completion limits of this algebra. Derived
    /// completions, [`crate::opposite::opposite`] included, run with
    /// them.
    #[inline]
    pub fn completion_limits(&self) -> &CompletionLimits {
        &self.limits
    }

    /// `dim_k A` = number of normal words.
    #[inline]
    pub fn dim(&self) -> usize {
        self.basis.len()
    }

    #[inline]
    pub fn quiver(&self) -> &Quiver {
        &self.quiver
    }

    #[inline]
    pub fn field(&self) -> PrimeField {
        self.field
    }

    /// The normal-word basis, in the order documented on the type.
    #[inline]
    pub fn basis(&self) -> &[PathWord] {
        &self.basis
    }

    /// The reduced Groebner basis of the ideal, each element a monic
    /// [`Relation`] with terms in descending order.
    #[inline]
    pub fn relations(&self) -> &[Relation] {
        &self.relations
    }

    /// Basis index of `path`: `Ok(Some(i))` when the path is a normal word,
    /// `Ok(None)` when it is a valid path of the quiver but not a normal
    /// word, and `Err` when it is not a path of this algebra's quiver at all
    /// (see [`PathWord::validate_in`]).
    ///
    /// A non-normal path is not zero in general: it equals its normal form,
    /// a combination of normal words that [`Algebra::nf_word`] computes. For
    /// a monomial ideal the two notions coincide and `Ok(None)` does mean
    /// zero.
    pub fn path_index(&self, path: &PathWord) -> Result<Option<BasisIdx>, QuiverError> {
        path.validate_in(&self.quiver)?;
        if path.is_trivial() {
            Ok(Some(path.source() as usize))
        } else {
            Ok(self.index_of.get(path.arrows()).copied())
        }
    }

    /// Basis index of `e_v`; equals `v`. Panics if `v >= num_vertices`.
    pub fn vertex_idempotent(&self, v: u32) -> BasisIdx {
        assert!(v < self.quiver.num_vertices());
        v as usize
    }

    /// Basis indices of normal words with source `v`, the basis of
    /// `e_v A = P_v`. Panics if `v >= num_vertices`.
    #[inline]
    pub fn paths_from(&self, v: u32) -> &[BasisIdx] {
        &self.from[v as usize]
    }

    /// Basis indices of normal words with target `v`, the basis of `A e_v`.
    /// Panics if `v >= num_vertices`.
    #[inline]
    pub fn paths_to(&self, v: u32) -> &[BasisIdx] {
        &self.to[v as usize]
    }

    /// Basis indices of normal words from `u` to `v`, the basis of
    /// `e_u A e_v`. Panics if either vertex is out of range.
    #[inline]
    pub fn paths_between(&self, u: u32, v: u32) -> &[BasisIdx] {
        &self.between[u as usize][v as usize]
    }

    /// Cartan matrix: `c[i][j] = dim e_i A e_j`, the number of normal words
    /// from `i` to `j`; row `i` is the dimension vector of the projective
    /// `P_i = e_i A`.
    pub fn cartan_matrix(&self) -> Vec<Vec<usize>> {
        self.between
            .iter()
            .map(|row| row.iter().map(Vec::len).collect())
            .collect()
    }

    /// `basis[i] · a` as a sparse coefficient row over the basis, sorted by
    /// basis index. The row is empty when the product is zero, and has at
    /// most one entry over a monomial ideal. Panics on out-of-range `i` or
    /// `a`.
    #[inline]
    pub fn right_mul(&self, i: BasisIdx, a: ArrowId) -> &[(BasisIdx, Fp)] {
        &self.right_mul[i][a.index()]
    }

    /// `a · basis[i]`, as [`Self::right_mul`].
    #[inline]
    pub fn left_mul(&self, a: ArrowId, i: BasisIdx) -> &[(BasisIdx, Fp)] {
        &self.left_mul[a.index()][i]
    }

    /// The normal form of `word` as a sparse coefficient row over the basis,
    /// sorted by basis index. Errors when `word` is not a path of this
    /// algebra's quiver.
    pub fn nf_word(&self, word: &PathWord) -> Result<Vec<(BasisIdx, Fp)>, QuiverError> {
        word.validate_in(&self.quiver)?;
        if word.is_trivial() {
            return Ok(vec![(word.source() as usize, self.field.one())]);
        }
        Ok(self.nf_arrow_word(word.arrows().to_vec()))
    }

    /// `basis[p] · basis[q]` as a sparse coefficient row over the basis,
    /// sorted by basis index. The row is empty when the endpoints do not
    /// compose or the product reduces to zero. Panics on out-of-range
    /// indices.
    pub fn mul_basis(&self, p: BasisIdx, q: BasisIdx) -> Vec<(BasisIdx, Fp)> {
        let (left, right) = (&self.basis[p], &self.basis[q]);
        if left.target() != right.source() {
            return Vec::new();
        }
        if left.is_trivial() {
            return vec![(q, self.field.one())];
        }
        if right.is_trivial() {
            return vec![(p, self.field.one())];
        }
        let mut word = left.arrows().to_vec();
        word.extend_from_slice(right.arrows());
        self.nf_arrow_word(word)
    }

    /// Division against the reduced Groebner basis. `word` is nonempty and
    /// composable in the quiver. Correctness of the result rests on the
    /// verified diamond property: any reduction order gives the same normal
    /// form, so the leftmost factor of the first matching basis element is
    /// as good as any.
    fn nf_arrow_word(&self, word: Vec<ArrowId>) -> Vec<(BasisIdx, Fp)> {
        let mut poly: Vec<(Fp, Vec<ArrowId>)> = vec![(self.field.one(), word)];
        let mut out: Vec<(BasisIdx, Fp)> = Vec::new();
        while let Some((coeff, word)) = poly.first().cloned() {
            match self.leftmost_reduction(&word) {
                None => {
                    let index = *self
                        .index_of
                        .get(&word)
                        .expect("the verifier enumerated every irreducible word");
                    out.push((index, coeff));
                    poly.remove(0);
                }
                Some((relation, position)) => {
                    let lead_len = relation.leading().1.len();
                    let left = &word[..position];
                    let right = &word[position + lead_len..];
                    let scale = self.field.neg(coeff);
                    poly = add_scaled(self.field, &poly, scale, left, relation.terms(), right);
                }
            }
        }
        out.sort_unstable_by_key(|&(index, _)| index);
        out
    }

    /// The first Groebner element whose leading word is a factor of `word`,
    /// with the leftmost factor position.
    fn leftmost_reduction(&self, word: &[ArrowId]) -> Option<(&Relation, usize)> {
        self.relations.iter().find_map(|relation| {
            let lead = relation.leading().1.arrows();
            if lead.len() > word.len() {
                return None;
            }
            (0..=word.len() - lead.len())
                .find(|&at| &word[at..at + lead.len()] == lead)
                .map(|at| (relation, at))
        })
    }

    /// A row-reduced basis of `e_u · J^k · e_v` in the coordinates of
    /// [`Self::paths_between`]`(u, v)`. `J^0` is the algebra itself, so
    /// `k = 0` gives the identity. Panics if either vertex is out of range.
    ///
    /// Row-space iteration computes `J^k`: `J^1` is the span of the
    /// non-trivial basis words and `J^{k+1}` is the span of `x·a` over `x`
    /// spanning `J^k` and arrows `a`. Word length decides nothing here: an
    /// inhomogeneous relation can place a short normal word inside a deep
    /// radical power.
    pub fn radical_power_component(&self, u: u32, v: u32, k: usize) -> Vec<Vec<Fp>> {
        assert!(u < self.quiver.num_vertices() && v < self.quiver.num_vertices());
        let power = self.radical_power(k);
        let component = &power[u as usize][v as usize];
        (0..component.rows())
            .map(|r| component.row(r).to_vec())
            .collect()
    }

    /// The least `k` with `J^k = 0`. Finite for every constructed algebra:
    /// the radical of a finite-dimensional algebra is nilpotent.
    pub fn nilpotency_degree(&self) -> usize {
        let mut k = 0;
        let mut power = self.radical_power(0);
        loop {
            let total: usize = power.iter().flatten().map(DenseMat::rows).sum();
            if total == 0 {
                return k;
            }
            let next = self.radical_step(&power);
            let next_total: usize = next.iter().flatten().map(DenseMat::rows).sum();
            assert!(
                next_total < total,
                "radical iteration stalled on a nonzero power; this is a bug in auslander"
            );
            power = next;
            k += 1;
        }
    }

    /// Row-reduced component matrices of `J^k`, indexed `[u][v]` with columns
    /// over `paths_between(u, v)`.
    fn radical_power(&self, k: usize) -> Vec<Vec<DenseMat>> {
        let n = self.quiver.num_vertices() as usize;
        let mut power: Vec<Vec<DenseMat>> = (0..n)
            .map(|u| {
                (0..n)
                    .map(|v| DenseMat::identity(self.between[u][v].len()))
                    .collect()
            })
            .collect();
        for _ in 0..k {
            power = self.radical_step(&power);
        }
        power
    }

    /// `J^{k+1}` from `J^k`: right-multiply every spanning row by every
    /// arrow and row-reduce each component. For `J^0` (identity components)
    /// this yields `J^1`, the span of the non-trivial basis words, because
    /// every non-trivial normal word is a normal word times its last arrow.
    fn radical_step(&self, power: &[Vec<DenseMat>]) -> Vec<Vec<DenseMat>> {
        let n = self.quiver.num_vertices() as usize;
        let positions = self.component_positions();
        let mut rows: Vec<Vec<Vec<Vec<Fp>>>> = vec![vec![Vec::new(); n]; n];
        for u in 0..n {
            for (w, component) in power[u].iter().enumerate() {
                let word_indices = &self.between[u][w];
                for r in 0..component.rows() {
                    let row = component.row(r);
                    for &a in self.quiver.arrows_from(w as u32) {
                        let v = self.quiver.target(a) as usize;
                        let mut image = vec![self.field.zero(); self.between[u][v].len()];
                        for (pos, &c) in row.iter().enumerate() {
                            if c.is_zero() {
                                continue;
                            }
                            for &(q, qc) in self.right_mul(word_indices[pos], a) {
                                let slot = &mut image[positions[q]];
                                *slot = self.field.add(*slot, self.field.mul(c, qc));
                            }
                        }
                        if image.iter().any(|c| !c.is_zero()) {
                            rows[u][v].push(image);
                        }
                    }
                }
            }
        }
        (0..n)
            .map(|u| {
                (0..n)
                    .map(|v| {
                        let cols = self.between[u][v].len();
                        let mut mat = DenseMat::zero(rows[u][v].len(), cols);
                        for (r, row) in rows[u][v].iter().enumerate() {
                            for (c, &value) in row.iter().enumerate() {
                                mat.set(r, c, value);
                            }
                        }
                        mat.row_space_basis(&self.field)
                    })
                    .collect()
            })
            .collect()
    }

    /// Position of each basis word within `paths_between` of its own
    /// endpoints.
    fn component_positions(&self) -> Vec<usize> {
        let mut positions = vec![usize::MAX; self.basis.len()];
        for row in &self.between {
            for component in row {
                for (i, &b) in component.iter().enumerate() {
                    positions[b] = i;
                }
            }
        }
        positions
    }
}

/// `poly + scale · left · terms · right`, merged into strictly descending
/// order. `terms` is descending, and concatenation with a fixed context
/// preserves the order.
fn add_scaled(
    field: PrimeField,
    poly: &[(Fp, Vec<ArrowId>)],
    scale: Fp,
    left: &[ArrowId],
    terms: &[(Fp, PathWord)],
    right: &[ArrowId],
) -> Vec<(Fp, Vec<ArrowId>)> {
    let addend: Vec<(Fp, Vec<ArrowId>)> = terms
        .iter()
        .map(|(c, w)| {
            let mut word = left.to_vec();
            word.extend_from_slice(w.arrows());
            word.extend_from_slice(right);
            (field.mul(scale, *c), word)
        })
        .collect();
    let mut merged = Vec::with_capacity(poly.len() + addend.len());
    let mut i = 0;
    let mut j = 0;
    while i < poly.len() && j < addend.len() {
        match word_cmp(&poly[i].1, &addend[j].1) {
            std::cmp::Ordering::Greater => {
                merged.push(poly[i].clone());
                i += 1;
            }
            std::cmp::Ordering::Less => {
                merged.push(addend[j].clone());
                j += 1;
            }
            std::cmp::Ordering::Equal => {
                let sum = field.add(poly[i].0, addend[j].0);
                if !sum.is_zero() {
                    merged.push((sum, poly[i].1.clone()));
                }
                i += 1;
                j += 1;
            }
        }
    }
    merged.extend_from_slice(&poly[i..]);
    merged.extend(addend.into_iter().skip(j));
    merged
}

/// Drops duplicate words and words containing another as a contiguous factor;
/// the generated ideal is unchanged. The result is sorted by length, then
/// lexicographically.
fn minimal_words(mut words: Vec<Vec<ArrowId>>) -> Vec<Vec<ArrowId>> {
    words.sort();
    words.dedup();
    words.sort_by_key(Vec::len);
    let mut minimal: Vec<Vec<ArrowId>> = Vec::new();
    for word in words {
        let contains_kept = minimal
            .iter()
            .any(|v| word.windows(v.len()).any(|w| w == v.as_slice()));
        if !contains_kept {
            minimal.push(word);
        }
    }
    minimal
}

/// Deterministic automaton recognizing standard paths.
///
/// States `v < num_vertices`: "at vertex `v`, no forbidden-word progress".
/// Remaining states: the nonempty proper prefixes of the (minimal) forbidden
/// words. The state after reading a standard path is its longest suffix that
/// is such a prefix. A transition is absent exactly when the arrow does not
/// start at the state's vertex, or when appending it completes a forbidden
/// word. Minimality of the forbidden set guarantees that no prefix state
/// contains a forbidden factor, so every state is reachable from a start
/// state. Any cycle then proves the standard-path language infinite.
struct Automaton {
    trans: Vec<Vec<Option<usize>>>,
}

impl Automaton {
    fn build(quiver: &Quiver, forbidden: &[Vec<ArrowId>]) -> Automaton {
        let n = quiver.num_vertices() as usize;
        let mut prefixes: Vec<Vec<ArrowId>> = Vec::new();
        let mut prefix_index: FxHashMap<Vec<ArrowId>, usize> = FxHashMap::default();
        for word in forbidden {
            for len in 1..word.len() {
                let prefix = word[..len].to_vec();
                if !prefix_index.contains_key(&prefix) {
                    prefix_index.insert(prefix.clone(), prefixes.len());
                    prefixes.push(prefix);
                }
            }
        }
        let forbidden_set: FxHashSet<&[ArrowId]> = forbidden.iter().map(Vec::as_slice).collect();

        let num_states = n + prefixes.len();
        let mut trans = vec![vec![None; quiver.num_arrows()]; num_states];
        for (s, row) in trans.iter_mut().enumerate() {
            let (word, vertex): (&[ArrowId], u32) = if s < n {
                (&[], s as u32)
            } else {
                let w = prefixes[s - n].as_slice();
                (w, quiver.target(w[w.len() - 1]))
            };
            for &a in quiver.arrows_from(vertex) {
                let mut extended = word.to_vec();
                extended.push(a);
                // Longest suffix in (forbidden ∪ prefixes) decides; minimality makes
                // the two sets disjoint and rules out shorter forbidden suffixes
                // hiding under a prefix match.
                let mut next = Some(quiver.target(a) as usize);
                for start in 0..extended.len() {
                    let suffix = &extended[start..];
                    if forbidden_set.contains(suffix) {
                        next = None;
                        break;
                    }
                    if let Some(&k) = prefix_index.get(suffix) {
                        next = Some(n + k);
                        break;
                    }
                }
                row[a.index()] = next;
            }
        }
        Automaton { trans }
    }

    /// Kahn's algorithm; every state is reachable, so any cycle means
    /// infinitely many standard paths.
    fn has_cycle(&self) -> bool {
        let m = self.trans.len();
        let mut indegree = vec![0usize; m];
        for row in &self.trans {
            for &t in row.iter().flatten() {
                indegree[t] += 1;
            }
        }
        let mut stack: Vec<usize> = (0..m).filter(|&s| indegree[s] == 0).collect();
        let mut visited = 0;
        while let Some(s) = stack.pop() {
            visited += 1;
            for &t in self.trans[s].iter().flatten() {
                indegree[t] -= 1;
                if indegree[t] == 0 {
                    stack.push(t);
                }
            }
        }
        visited < m
    }

    #[inline]
    fn step(&self, s: usize, a: ArrowId) -> Option<usize> {
        self.trans[s][a.index()]
    }
}

/// Completion limits that are always adequate for `presentation`, each
/// the default or a bound derived from the presentation, whichever is
/// larger. `max_word_len` covers the longest self-overlap superposition,
/// `2·L - 1` for the longest forbidden word length `L`. `max_basis`
/// covers the forbidden words. `max_steps` covers one reduction step per
/// forbidden word plus one work unit per emitted standard path. The named
/// monomial constructors use these limits, so a long forbidden word does
/// not truncate.
pub fn monomial_completion_limits(presentation: &MonomialPresentation) -> CompletionLimits {
    let defaults = CompletionLimits::default();
    let longest = presentation
        .forbidden()
        .iter()
        .map(Vec::len)
        .max()
        .unwrap_or(0);
    CompletionLimits {
        max_basis: defaults.max_basis.max(presentation.forbidden().len()),
        max_word_len: defaults
            .max_word_len
            .max(longest.saturating_mul(2).saturating_sub(1)),
        max_steps: defaults.max_steps.max(
            presentation
                .dim()
                .saturating_add(presentation.forbidden().len()),
        ),
    }
}

fn from_monomial_derived(
    field: PrimeField,
    presentation: &MonomialPresentation,
) -> Result<Arc<Algebra>, AlgebraBuildError> {
    Algebra::from_monomial(
        field,
        presentation,
        &monomial_completion_limits(presentation),
    )
}

fn linear_quiver(n: usize) -> Quiver {
    let n = u32::try_from(n).expect("vertex count fits in u32");
    let arrows: Vec<(u32, u32)> = (0..n.saturating_sub(1)).map(|i| (i, i + 1)).collect();
    Quiver::new(n, &arrows).expect("endpoints in range by construction")
}

fn cyclic_quiver(n: usize) -> Quiver {
    let arrows: Vec<(u32, u32)> = (0..n).map(|i| (i as u32, ((i + 1) % n) as u32)).collect();
    Quiver::new(u32::try_from(n).expect("vertex count fits in u32"), &arrows)
        .expect("endpoints in range by construction")
}

/// The [`MonomialPresentation`] of linearly oriented `A_n`: vertices `0..n`,
/// arrows `i → i+1`, no relations.
pub fn linear_an_presentation(n: usize) -> MonomialPresentation {
    MonomialPresentation::new(linear_quiver(n), Vec::new())
        .expect("acyclic quiver without relations is finite-dimensional")
}

/// Path algebra of linearly oriented `A_n` over `field`.
pub fn linear_an(n: usize, field: PrimeField) -> Arc<Algebra> {
    from_monomial_derived(field, &linear_an_presentation(n))
        .expect("the zero ideal over an acyclic quiver completes")
}

/// The [`MonomialPresentation`] of the Kronecker-type algebra: vertices
/// `0, 1` and `m` parallel arrows `0 → 1`, no relations.
pub fn kronecker_presentation(m: usize) -> MonomialPresentation {
    let arrows = vec![(0u32, 1u32); m];
    let quiver = Quiver::new(2, &arrows).expect("endpoints in range by construction");
    MonomialPresentation::new(quiver, Vec::new())
        .expect("acyclic quiver without relations is finite-dimensional")
}

/// Kronecker-type algebra over `field`. Hereditary; `dim = m + 2`.
pub fn kronecker(m: usize, field: PrimeField) -> Arc<Algebra> {
    from_monomial_derived(field, &kronecker_presentation(m))
        .expect("the zero ideal over an acyclic quiver completes")
}

/// `k[x]/(x²)` over `field`: one vertex, one loop `x`, forbidden word `xx`.
pub fn dual_numbers(field: PrimeField) -> Arc<Algebra> {
    truncated_poly(2, field).expect("x² is an admissible relation")
}

/// The [`MonomialPresentation`] of `k[x]/(xⁿ)`: one vertex, one loop `x`,
/// forbidden word `xⁿ`. Errors for `n < 2` (the ideal would not be
/// admissible).
pub fn truncated_poly_presentation(n: usize) -> Result<MonomialPresentation, AlgebraError> {
    let quiver = Quiver::new(1, &[(0, 0)]).expect("endpoints in range by construction");
    MonomialPresentation::new(quiver, vec![vec![ArrowId(0); n]])
}

/// `k[x]/(xⁿ)` over `field`, as [`truncated_poly_presentation`].
pub fn truncated_poly(n: usize, field: PrimeField) -> Result<Arc<Algebra>, AlgebraBuildError> {
    let presentation = truncated_poly_presentation(n).map_err(AlgebraBuildError::Monomial)?;
    from_monomial_derived(field, &presentation)
}

/// The [`MonomialPresentation`] of the linear Nakayama algebra over linearly
/// oriented `A_n` with `dim P_i = kupisch[i]`.
///
/// Valid series `c`: nonempty; `c[n-1] == 1`; `c[i] >= 2` for `i < n-1`
/// (admissibility); `c[i+1] >= c[i] - 1` (rad `P_i` is a quotient of
/// `P_{i+1}`). Anything else errors; for example `[3, 3, 2]`, where no
/// admissible ideal gives the prescribed projective dimensions.
pub fn linear_nakayama_presentation(
    kupisch: &[usize],
) -> Result<MonomialPresentation, AlgebraError> {
    let n = kupisch.len();
    if n == 0 {
        return Err(AlgebraError::InvalidKupisch {
            reason: "series is empty".to_string(),
        });
    }
    if kupisch[n - 1] != 1 {
        return Err(AlgebraError::InvalidKupisch {
            reason: format!(
                "linear series must end with 1, got c[{}] = {}",
                n - 1,
                kupisch[n - 1]
            ),
        });
    }
    for i in 0..n - 1 {
        if kupisch[i] < 2 {
            return Err(AlgebraError::InvalidKupisch {
                reason: format!("c[{i}] = {} but interior entries need c >= 2", kupisch[i]),
            });
        }
        if kupisch[i + 1] < kupisch[i] - 1 {
            return Err(AlgebraError::InvalidKupisch {
                reason: format!(
                    "c[{}] = {} violates c[i+1] >= c[i] - 1 = {}",
                    i + 1,
                    kupisch[i + 1],
                    kupisch[i] - 1
                ),
            });
        }
    }
    let mut forbidden = Vec::new();
    for (i, &c) in kupisch.iter().enumerate() {
        // Forbid the path from i of length c; it exists only when
        // i + c <= n - 1.
        if i + c <= n - 1 {
            forbidden.push((i..i + c).map(|j| ArrowId(j as u32)).collect());
        }
    }
    MonomialPresentation::new(linear_quiver(n), forbidden)
}

/// Linear Nakayama algebra over `field`, as [`linear_nakayama_presentation`].
pub fn linear_nakayama(
    kupisch: &[usize],
    field: PrimeField,
) -> Result<Arc<Algebra>, AlgebraBuildError> {
    let presentation =
        linear_nakayama_presentation(kupisch).map_err(AlgebraBuildError::Monomial)?;
    from_monomial_derived(field, &presentation)
}

/// The [`MonomialPresentation`] of the cyclic Nakayama algebra over the cycle
/// `0 → 1 → … → n-1 → 0` with `dim P_i = kupisch[i]`.
///
/// Valid series `c`: nonempty; `c[i] >= 2` for all `i` (admissibility);
/// cyclically `c[(i+1) % n] >= c[i] - 1`. Anything else errors.
pub fn cyclic_nakayama_presentation(
    kupisch: &[usize],
) -> Result<MonomialPresentation, AlgebraError> {
    let n = kupisch.len();
    if n == 0 {
        return Err(AlgebraError::InvalidKupisch {
            reason: "series is empty".to_string(),
        });
    }
    for (i, &c) in kupisch.iter().enumerate() {
        if c < 2 {
            return Err(AlgebraError::InvalidKupisch {
                reason: format!("c[{i}] = {c} but cyclic entries need c >= 2"),
            });
        }
        if kupisch[(i + 1) % n] < c - 1 {
            return Err(AlgebraError::InvalidKupisch {
                reason: format!(
                    "c[{}] = {} violates cyclic c[i+1] >= c[i] - 1 = {}",
                    (i + 1) % n,
                    kupisch[(i + 1) % n],
                    c - 1
                ),
            });
        }
    }
    let forbidden: Vec<Vec<ArrowId>> = (0..n)
        .map(|i| {
            (0..kupisch[i])
                .map(|j| ArrowId(((i + j) % n) as u32))
                .collect()
        })
        .collect();
    MonomialPresentation::new(cyclic_quiver(n), forbidden)
}

/// Cyclic Nakayama algebra over `field`, as [`cyclic_nakayama_presentation`].
pub fn cyclic_nakayama(
    kupisch: &[usize],
    field: PrimeField,
) -> Result<Arc<Algebra>, AlgebraBuildError> {
    let presentation =
        cyclic_nakayama_presentation(kupisch).map_err(AlgebraBuildError::Monomial)?;
    from_monomial_derived(field, &presentation)
}

/// The [`MonomialPresentation`] of the cyclic quiver on `n` vertices with
/// `rad² = 0`: every length-2 path forbidden. `dim = 2n`.
pub fn radical_square_zero_cycle_presentation(n: usize) -> MonomialPresentation {
    let forbidden: Vec<Vec<ArrowId>> = (0..n)
        .map(|i| vec![ArrowId(i as u32), ArrowId(((i + 1) % n) as u32)])
        .collect();
    MonomialPresentation::new(cyclic_quiver(n), forbidden)
        .expect("rad² = 0 leaves only vertices and arrows")
}

/// Cyclic quiver with `rad² = 0` over `field`, as
/// [`radical_square_zero_cycle_presentation`].
pub fn radical_square_zero_cycle(n: usize, field: PrimeField) -> Arc<Algebra> {
    from_monomial_derived(field, &radical_square_zero_cycle_presentation(n))
        .expect("rad² = 0 leaves only vertices and arrows")
}

/// The [`MonomialPresentation`] of linearly oriented `A_n` with zero
/// relations: each `(start, len)` in `zero_paths` kills the unique path of
/// length `len` from vertex `start` (arrows `start, …, start + len - 1`).
/// `kA_3/(ab)` is `an_with_relations_presentation(3, &[(0, 2)])`.
///
/// Errors when a zero path runs past vertex `n - 1` or has length < 2.
pub fn an_with_relations_presentation(
    n: usize,
    zero_paths: &[(usize, usize)],
) -> Result<MonomialPresentation, AlgebraError> {
    for &(start, len) in zero_paths {
        if n == 0 || start + len > n - 1 {
            return Err(AlgebraError::ZeroPathOutOfRange { start, len });
        }
    }
    let forbidden = zero_paths
        .iter()
        .map(|&(start, len)| (start..start + len).map(|j| ArrowId(j as u32)).collect())
        .collect();
    MonomialPresentation::new(linear_quiver(n), forbidden)
}

/// Linearly oriented `A_n` with zero relations over `field`, as
/// [`an_with_relations_presentation`].
pub fn an_with_relations(
    n: usize,
    zero_paths: &[(usize, usize)],
    field: PrimeField,
) -> Result<Arc<Algebra>, AlgebraBuildError> {
    let presentation =
        an_with_relations_presentation(n, zero_paths).map_err(AlgebraBuildError::Monomial)?;
    from_monomial_derived(field, &presentation)
}

/// The commutative square over `field`: vertices `0..4`, arrows `a: 0 → 1`,
/// `b: 1 → 3`, `c: 0 → 2`, `d: 2 → 3`, and the relation `ab - cd`.
/// `dim = 9`; the two length-2 paths share one basis class.
pub fn commutative_square(field: PrimeField) -> Arc<Algebra> {
    let quiver = Quiver::new(4, &[(0, 1), (1, 3), (0, 2), (2, 3)]).expect("endpoints in range");
    let relation = Relation::new(
        &quiver,
        field,
        vec![
            (field.one(), vec![ArrowId(0), ArrowId(1)]),
            (field.elem(-1), vec![ArrowId(2), ArrowId(3)]),
        ],
    )
    .expect("ab - cd is a valid uniform relation");
    let presentation = Presentation::new(quiver, field, vec![relation])
        .expect("the relation was built over this quiver and field");
    // Every limit derived from this presentation sits below the default,
    // so the defaults are the derived limits.
    Algebra::new(presentation, &CompletionLimits::default())
        .expect("the commutative square is finite dimensional")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f5() -> PrimeField {
        PrimeField::new(5).unwrap()
    }

    fn word(algebra: &Algebra, arrows: &[u32]) -> PathWord {
        let ids: Vec<ArrowId> = arrows.iter().copied().map(ArrowId).collect();
        PathWord::from_arrows(algebra.quiver(), &ids).unwrap()
    }

    #[test]
    fn dual_numbers_has_basis_e_x() {
        let a = dual_numbers(f5());
        assert_eq!(a.dim(), 2);
        assert!(a.basis()[0].is_trivial());
        assert_eq!(a.basis()[1].arrows(), &[ArrowId(0)]);
    }

    #[test]
    fn truncated_poly_3_has_dim_3() {
        let a = truncated_poly(3, f5()).unwrap();
        assert_eq!(a.dim(), 3);
        assert_eq!(a.basis()[2].len(), 2);
    }

    /// Regression pin: x^65 needs `max_word_len = 129` for its
    /// self-overlap superpositions, above the default 64. The named
    /// constructor derives adequate limits; the defaults truncate.
    #[test]
    fn truncated_poly_65_succeeds_with_derived_limits() {
        let a = truncated_poly(65, f5()).unwrap();
        assert_eq!(a.dim(), 65);
        assert_eq!(a.completion_limits().max_word_len, 129);
        let presentation = truncated_poly_presentation(65).unwrap();
        assert!(matches!(
            Algebra::from_monomial(f5(), &presentation, &CompletionLimits::default()),
            Err(AlgebraBuildError::Truncated(diagnostics))
                if diagnostics.reason == crate::completion::TruncationReason::WordLenBudget
        ));
    }

    #[test]
    fn monomial_completion_limits_never_fall_below_the_defaults() {
        let presentation = truncated_poly_presentation(3).unwrap();
        assert_eq!(
            monomial_completion_limits(&presentation),
            CompletionLimits::default()
        );
        let long = truncated_poly_presentation(100).unwrap();
        let limits = monomial_completion_limits(&long);
        assert_eq!(limits.max_word_len, 199);
        assert_eq!(limits.max_basis, CompletionLimits::default().max_basis);
        assert_eq!(limits.max_steps, CompletionLimits::default().max_steps);
    }

    #[test]
    fn from_verified_keeps_default_limits_and_with_limits_stores_them() {
        let a = truncated_poly(65, f5()).unwrap();
        let bytes = a.certificate().to_canonical_json();
        let reloaded = Algebra::from_verified(verify(&bytes).unwrap());
        assert_eq!(reloaded.completion_limits(), &CompletionLimits::default());
        let raised = CompletionLimits {
            max_word_len: 129,
            ..CompletionLimits::default()
        };
        let preserved = Algebra::from_verified_with_limits(verify(&bytes).unwrap(), &raised);
        assert_eq!(preserved.completion_limits(), &raised);
    }

    #[test]
    fn truncated_poly_rejects_n_below_2() {
        assert!(matches!(
            truncated_poly(1, f5()),
            Err(AlgebraBuildError::Monomial(
                AlgebraError::ForbiddenWordTooShort { index: 0, len: 1 }
            ))
        ));
    }

    #[test]
    fn linear_a3_dim_and_cartan() {
        let a = linear_an(3, f5());
        assert_eq!(a.dim(), 6);
        // Row i = dimension vector of P_i; upper triangular under left-to-right
        // composition since paths run from lower to higher vertices.
        assert_eq!(
            a.cartan_matrix(),
            vec![vec![1, 1, 1], vec![0, 1, 1], vec![0, 0, 1]]
        );
    }

    #[test]
    fn linear_a3_paths_between_counts() {
        let a = linear_an(3, f5());
        for u in 0..3 {
            for v in 0..3 {
                let expected = usize::from(u <= v);
                assert_eq!(a.paths_between(u, v).len(), expected, "({u}, {v})");
            }
        }
    }

    #[test]
    fn a3_mod_ab_has_basis_without_ab() {
        let a = an_with_relations(3, &[(0, 2)], f5()).unwrap();
        assert_eq!(a.dim(), 5);
        for v in 0..3 {
            assert!(a.basis()[v as usize].is_trivial());
        }
        assert_eq!(a.path_index(&word(&a, &[0])), Ok(Some(3)));
        assert_eq!(a.path_index(&word(&a, &[1])), Ok(Some(4)));
        assert_eq!(a.path_index(&word(&a, &[0, 1])), Ok(None));
        assert_eq!(a.nf_word(&word(&a, &[0, 1])), Ok(Vec::new()));
    }

    #[test]
    fn kronecker_2_has_dim_4() {
        let a = kronecker(2, f5());
        assert_eq!(a.dim(), 4);
        assert_eq!(a.cartan_matrix(), vec![vec![1, 2], vec![0, 1]]);
    }

    #[test]
    fn linear_nakayama_3_2_1_is_path_algebra_a3() {
        let a = linear_nakayama(&[3, 2, 1], f5()).unwrap();
        assert_eq!(a.dim(), 6);
        assert!(a.relations().is_empty());
    }

    #[test]
    fn linear_nakayama_2_2_1_is_a3_mod_ab() {
        let a = linear_nakayama(&[2, 2, 1], f5()).unwrap();
        assert_eq!(a.dim(), 5);
        assert_eq!(a.relations().len(), 1);
        assert_eq!(a.relations()[0].terms(), &[(f5().one(), word(&a, &[0, 1]))]);
    }

    #[test]
    fn cyclic_nakayama_2_2_2_has_dim_6() {
        let a = cyclic_nakayama(&[2, 2, 2], f5()).unwrap();
        assert_eq!(a.dim(), 6);
    }

    #[test]
    fn cyclic_nakayama_3_3_3_has_dim_9() {
        let a = cyclic_nakayama(&[3, 3, 3], f5()).unwrap();
        assert_eq!(a.dim(), 9);
    }

    #[test]
    fn linear_kupisch_3_3_2_rejected() {
        assert!(matches!(
            linear_nakayama(&[3, 3, 2], f5()),
            Err(AlgebraBuildError::Monomial(
                AlgebraError::InvalidKupisch { .. }
            ))
        ));
    }

    #[test]
    fn linear_kupisch_drop_violation_rejected() {
        assert!(matches!(
            linear_nakayama(&[4, 2, 1], f5()),
            Err(AlgebraBuildError::Monomial(
                AlgebraError::InvalidKupisch { .. }
            ))
        ));
    }

    #[test]
    fn cyclic_kupisch_entry_below_2_rejected() {
        assert!(matches!(
            cyclic_nakayama(&[2, 1, 2], f5()),
            Err(AlgebraBuildError::Monomial(
                AlgebraError::InvalidKupisch { .. }
            ))
        ));
    }

    #[test]
    fn cyclic_kupisch_drop_violation_rejected() {
        assert!(matches!(
            cyclic_nakayama(&[4, 2, 2], f5()),
            Err(AlgebraBuildError::Monomial(
                AlgebraError::InvalidKupisch { .. }
            ))
        ));
    }

    #[test]
    fn loop_without_relations_is_infinite_dimensional() {
        let quiver = Quiver::new(1, &[(0, 0)]).unwrap();
        assert_eq!(
            MonomialPresentation::new(quiver, Vec::new()).unwrap_err(),
            AlgebraError::InfiniteDimensional
        );
    }

    #[test]
    fn cycle_without_relations_is_infinite_dimensional() {
        let quiver = Quiver::new(3, &[(0, 1), (1, 2), (2, 0)]).unwrap();
        assert_eq!(
            MonomialPresentation::new(quiver, Vec::new()).unwrap_err(),
            AlgebraError::InfiniteDimensional
        );
    }

    #[test]
    fn pipeline_reports_infinite_dimension_with_a_witness() {
        let quiver = Quiver::new(1, &[(0, 0)]).unwrap();
        let presentation = Presentation::new(quiver, f5(), Vec::new()).unwrap();
        match Algebra::new(presentation, &CompletionLimits::default()) {
            Err(AlgebraBuildError::InfiniteDimensional { witness, .. }) => {
                assert!(!witness.cycle.is_empty());
            }
            other => panic!("expected InfiniteDimensional, got {other:?}"),
        }
    }

    #[test]
    fn forbidden_words_reduced_to_minimal() {
        // A4 with both ab and abc: abc contains ab, so only ab survives.
        let quiver = Quiver::new(4, &[(0, 1), (1, 2), (2, 3)]).unwrap();
        let m = MonomialPresentation::new(
            quiver,
            vec![
                vec![ArrowId(0), ArrowId(1), ArrowId(2)],
                vec![ArrowId(0), ArrowId(1)],
            ],
        )
        .unwrap();
        assert_eq!(m.forbidden(), &[vec![ArrowId(0), ArrowId(1)]]);
        assert_eq!(m.dim(), 8); // e0..e3, a, b, c, bc
    }

    #[test]
    fn loop_with_x_cubed_forbidden_is_finite() {
        let quiver = Quiver::new(1, &[(0, 0)]).unwrap();
        let m = MonomialPresentation::new(quiver, vec![vec![ArrowId(0); 3]]).unwrap();
        assert_eq!(m.dim(), 3);
        let a = Algebra::from_monomial(f5(), &m, &CompletionLimits::default()).unwrap();
        assert_eq!(a.dim(), 3);
    }

    #[test]
    fn two_loops_with_xx_yy_forbidden_is_infinite() {
        // xyxyxy… never contains xx or yy; the automaton fallback must find the cycle.
        let quiver = Quiver::new(1, &[(0, 0), (0, 0)]).unwrap();
        let result = MonomialPresentation::new(
            quiver,
            vec![vec![ArrowId(0), ArrowId(0)], vec![ArrowId(1), ArrowId(1)]],
        );
        assert_eq!(result.unwrap_err(), AlgebraError::InfiniteDimensional);
    }

    #[test]
    fn two_loops_with_rad_square_zero_has_dim_3() {
        let quiver = Quiver::new(1, &[(0, 0), (0, 0)]).unwrap();
        let forbidden = vec![
            vec![ArrowId(0), ArrowId(0)],
            vec![ArrowId(0), ArrowId(1)],
            vec![ArrowId(1), ArrowId(0)],
            vec![ArrowId(1), ArrowId(1)],
        ];
        let m = MonomialPresentation::new(quiver, forbidden).unwrap();
        assert_eq!(m.dim(), 3);
    }

    #[test]
    fn radical_square_zero_cycle_3_has_dim_6() {
        let a = radical_square_zero_cycle(3, f5());
        assert_eq!(a.dim(), 6);
        assert_eq!(a.paths_from(0).len(), 2); // e_0 and the arrow out of 0
    }

    #[test]
    fn multiplication_tables_match_path_composition() {
        let a = linear_an(3, f5());
        let one = f5().one();
        let (ia, ib) = (ArrowId(0), ArrowId(1));
        let a_idx = a.path_index(&word(&a, &[0])).unwrap().unwrap();
        let ab_idx = a.path_index(&word(&a, &[0, 1])).unwrap().unwrap();
        assert_eq!(a.right_mul(a.vertex_idempotent(0), ia), &[(a_idx, one)]);
        assert_eq!(a.right_mul(a_idx, ib), &[(ab_idx, one)]);
        assert_eq!(
            a.left_mul(ia, a.path_index(&word(&a, &[1])).unwrap().unwrap()),
            &[(ab_idx, one)]
        );
        assert!(a.right_mul(a_idx, ia).is_empty()); // target(a) != source(a)
    }

    #[test]
    fn multiplication_by_forbidden_extension_is_zero() {
        let a = an_with_relations(3, &[(0, 2)], f5()).unwrap();
        let a_idx = a.path_index(&word(&a, &[0])).unwrap().unwrap();
        assert!(a.right_mul(a_idx, ArrowId(1)).is_empty());
        let b_idx = a.path_index(&word(&a, &[1])).unwrap().unwrap();
        assert!(a.left_mul(ArrowId(0), b_idx).is_empty());
    }

    #[test]
    fn basis_starts_with_trivial_paths_then_lengths_ascend() {
        let a = linear_an(3, f5());
        for v in 0..3u32 {
            let p = &a.basis()[a.vertex_idempotent(v)];
            assert!(p.is_trivial());
            assert_eq!(p.source(), v);
        }
        let lengths: Vec<usize> = a.basis().iter().map(PathWord::len).collect();
        assert_eq!(lengths, vec![0, 0, 0, 1, 1, 2]);
    }

    #[test]
    fn forbidden_word_too_short_rejected() {
        let quiver = Quiver::new(2, &[(0, 1)]).unwrap();
        assert!(matches!(
            MonomialPresentation::new(quiver, vec![vec![ArrowId(0)]]),
            Err(AlgebraError::ForbiddenWordTooShort { index: 0, len: 1 })
        ));
    }

    #[test]
    fn forbidden_word_not_composable_rejected() {
        let quiver = Quiver::new(3, &[(0, 1), (1, 2)]).unwrap();
        assert!(matches!(
            MonomialPresentation::new(quiver, vec![vec![ArrowId(1), ArrowId(0)]]),
            Err(AlgebraError::ForbiddenWordInvalid {
                index: 0,
                error: QuiverError::NotComposable { position: 0 },
            })
        ));
    }

    #[test]
    fn an_zero_path_out_of_range_rejected() {
        assert!(matches!(
            an_with_relations(3, &[(1, 2)], f5()),
            Err(AlgebraBuildError::Monomial(
                AlgebraError::ZeroPathOutOfRange { start: 1, len: 2 }
            ))
        ));
    }

    #[test]
    fn paths_from_lists_projective_basis() {
        let a = an_with_relations(3, &[(0, 2)], f5()).unwrap();
        assert_eq!(a.paths_from(0), &[0, 3]); // P_0: e_0, a
        assert_eq!(a.paths_from(1), &[1, 4]); // P_1: e_1, b
        assert_eq!(a.paths_from(2), &[2]); // P_2: e_2
        assert_eq!(a.paths_to(2), &[2, 4]); // A e_2: e_2, b
    }

    #[test]
    fn from_monomial_basis_equals_the_standard_path_basis() {
        let quiver = Quiver::new(4, &[(0, 1), (1, 2), (1, 3)]).unwrap();
        let m = MonomialPresentation::new(quiver, vec![vec![ArrowId(0), ArrowId(1)]]).unwrap();
        let a = Algebra::from_monomial(f5(), &m, &CompletionLimits::default()).unwrap();
        assert_eq!(a.basis(), m.basis());
        assert_eq!(a.cartan_matrix(), m.cartan_matrix());
    }

    #[test]
    fn commutative_square_identifies_the_two_diagonals() {
        let a = commutative_square(f5());
        assert_eq!(a.dim(), 9);
        // The larger word cd reduces to ab, the unique length-2 normal word.
        let ab = a.path_index(&word(&a, &[0, 1])).unwrap().unwrap();
        assert_eq!(a.path_index(&word(&a, &[2, 3])), Ok(None));
        assert_eq!(a.nf_word(&word(&a, &[2, 3])), Ok(vec![(ab, f5().one())]));
        let c_idx = a.path_index(&word(&a, &[2])).unwrap().unwrap();
        assert_eq!(a.right_mul(c_idx, ArrowId(3)), &[(ab, f5().one())]);
    }

    #[test]
    fn mul_basis_composes_and_respects_endpoints() {
        let a = commutative_square(f5());
        let c_idx = a.path_index(&word(&a, &[2])).unwrap().unwrap();
        let d_idx = a.path_index(&word(&a, &[3])).unwrap().unwrap();
        let ab = a.path_index(&word(&a, &[0, 1])).unwrap().unwrap();
        assert_eq!(a.mul_basis(c_idx, d_idx), vec![(ab, f5().one())]);
        assert_eq!(a.mul_basis(d_idx, c_idx), Vec::new());
        assert_eq!(
            a.mul_basis(a.vertex_idempotent(0), c_idx),
            vec![(c_idx, f5().one())]
        );
        assert_eq!(a.mul_basis(c_idx, a.vertex_idempotent(3)), Vec::new());
    }

    #[test]
    fn certificate_round_trips_through_verify() {
        let a = commutative_square(f5());
        let bytes = a.certificate().to_canonical_json();
        let verified = verify(&bytes).expect("the stored certificate verifies");
        let rebuilt = Algebra::from_verified(verified);
        assert_eq!(rebuilt.dim(), a.dim());
        assert_eq!(rebuilt.basis(), a.basis());
        assert_eq!(rebuilt.relations(), a.relations());
    }

    #[test]
    fn nilpotency_degree_matches_loewy_structure() {
        let f = f5();
        assert_eq!(linear_an(3, f).nilpotency_degree(), 3);
        assert_eq!(dual_numbers(f).nilpotency_degree(), 2);
        assert_eq!(truncated_poly(4, f).unwrap().nilpotency_degree(), 4);
        assert_eq!(radical_square_zero_cycle(3, f).nilpotency_degree(), 2);
        assert_eq!(commutative_square(f).nilpotency_degree(), 3);
    }

    #[test]
    fn radical_power_components_descend_by_row_space_iteration() {
        let f = f5();
        let a = linear_an(3, f);
        // e_0 A e_2 is one-dimensional (the word ab), which lies in J and J².
        assert_eq!(a.radical_power_component(0, 2, 0).len(), 1);
        assert_eq!(a.radical_power_component(0, 2, 1).len(), 1);
        assert_eq!(a.radical_power_component(0, 2, 2).len(), 1);
        assert_eq!(a.radical_power_component(0, 2, 3).len(), 0);
        // e_0 A e_1 is the arrow a: in J but not in J².
        assert_eq!(a.radical_power_component(0, 1, 1).len(), 1);
        assert_eq!(a.radical_power_component(0, 1, 2).len(), 0);
        // The trivial component at a vertex leaves J immediately.
        assert_eq!(a.radical_power_component(0, 0, 0).len(), 1);
        assert_eq!(a.radical_power_component(0, 0, 1).len(), 0);
    }
}

//! Bound quiver algebras `kQ/I` with a certificate-verified normal-word basis.
//!
//! [`Algebra`] is the sole runtime algebra type: it owns a prime field, the
//! reduced Groebner basis of its ideal, the normal-word basis, and per-arrow
//! multiplication tables. Every `Algebra` comes from one pipeline: completion
//! emits a certificate, the independent verifier checks it, and the
//! constructor builds the tables from the verified data. Nothing in this
//! module truncates silently.
//!
//! Monomial input takes the same pipeline. [`monomial_presentation`] turns a
//! [`crate::monomial::MonomialIdeal`] into a [`Presentation`] of one-term
//! relations, and [`monomial_limits`] derives budgets adequate for it. The
//! named constructors ([`linear_an`], [`kronecker`], and the rest) are that
//! pair applied to the families of [`crate::monomial`].

use std::fmt;
use std::sync::Arc;

use rustc_hash::FxHashMap;

use crate::certificate::{Certificate, FinitenessData, RelationData};
use crate::completion::{CompletionLimits, Outcome, TruncationDiagnostics, complete};
use crate::field::{Fp, PrimeField};
use crate::linalg::DenseMat;
use crate::monomial::{
    MonomialError, MonomialIdeal, an_with_relations_ideal, cyclic_nakayama_ideal, kronecker_ideal,
    linear_an_ideal, linear_nakayama_ideal, radical_square_zero_cycle_ideal, truncated_poly_ideal,
};
use crate::order::word_cmp;
use crate::profile::{Site, hit};
use crate::quiver::{ArrowId, PathWord, Quiver, QuiverError};
use crate::relation::{Presentation, Relation, RelationError};
use crate::verify::{CycleWitness, VerifiedCompletion, VerifyError, verify_certificate};

/// Index into [`Algebra::basis`].
pub type BasisIdx = usize;

/// Rejected [`Algebra`] construction input, or an exhausted or defective
/// pipeline run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AlgebraBuildError {
    /// A monomial family parameter was rejected before the pipeline ran.
    Monomial(MonomialError),
    /// A relation or presentation was rejected before the pipeline ran.
    Relation(RelationError),
    /// The ideal is not admissible: the arrow ideal `J` is not nilpotent.
    /// `J^stable_power` has dimension `dimension` and equals every higher
    /// power. Only the subspace chain decides this. Leading words cannot:
    /// for one loop `x`, the ideals `(x³)` and `(x³ - x²)` share every
    /// leading word, and the second has `J² = J³ = span(x²)`.
    NonAdmissible {
        stable_power: usize,
        dimension: usize,
    },
    /// The verified certificate's `input_relations` differ from the
    /// relations of the presentation, first at `index`. Nothing else in the
    /// certificate ties it to the caller's request.
    InputRelationsMismatch { index: usize },
    /// The verifier proved the quotient infinite dimensional. It carries the
    /// certificate of the completed basis and the cycle witness.
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
            Self::Monomial(error) => write!(f, "monomial input rejected: {error}"),
            Self::Relation(error) => write!(f, "relation rejected: {error}"),
            Self::NonAdmissible {
                stable_power,
                dimension,
            } => write!(
                f,
                "the ideal is not admissible: J^{stable_power} has dimension {dimension} \
                 and equals every higher power, so J is not nilpotent"
            ),
            Self::InputRelationsMismatch { index } => write!(
                f,
                "the certificate's input relations differ from the presentation at index {index}"
            ),
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

/// Rejects a certificate whose `input_relations` are not the relations of
/// `presentation`, term for term in stored order.
///
/// The certificate chain ties `origin` to `input_relations` and
/// `input_relations` to the ideal through `membership`. This comparison is
/// the one link that ties `input_relations` to what the caller asked for.
fn check_input_relations(
    presentation: &Presentation,
    certificate: &Certificate,
) -> Result<(), AlgebraBuildError> {
    let asked = presentation.relations();
    let found = &certificate.input_relations;
    let differs =
        |index: &usize| asked.get(*index).map(relation_data).as_ref() != found.get(*index);
    match (0..asked.len().max(found.len())).find(differs) {
        Some(index) => Err(AlgebraBuildError::InputRelationsMismatch { index }),
        None => Ok(()),
    }
}

/// A relation as certificate data: raw coefficients and arrow-id words, in
/// the stored descending order.
fn relation_data(relation: &Relation) -> RelationData {
    relation
        .terms()
        .iter()
        .map(|(coeff, word)| (coeff.raw(), word.arrows().iter().map(|a| a.0).collect()))
        .collect()
}

/// The index maps of a normal-word basis: word to index for the
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
/// reduced Groebner basis, certificate emission, independent verification of
/// the certificate, and the admissibility decision. The ideal is
/// admissible: `I ⊆ J²` holds term by term, and the arrow ideal `J` is
/// nilpotent, which every construction path decides by iterating the radical
/// step. The basis consists of the normal words (words
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
    // right_mul[i][a] is NF(basis[i]·a) and left_mul[a][i] is NF(a·basis[i]),
    // each row sorted by basis index. Every word in a right_mul row runs from
    // the source of basis[i] to the target of a; every word in a left_mul row
    // runs from the source of a to the target of basis[i].
    right_mul: Vec<Vec<Vec<(BasisIdx, Fp)>>>,
    left_mul: Vec<Vec<Vec<(BasisIdx, Fp)>>>,
    // The chain J^0 ⊇ J^1 ⊇ ... ⊇ J^d = 0, one entry per power, built once at
    // construction by radical_chain. The last index d is the nilpotency
    // degree. An Algebra is immutable and lives behind an Arc, so every reader
    // shares this one copy.
    radical_powers: Vec<Vec<Vec<DenseMat>>>,
}

impl Algebra {
    /// Runs the full pipeline on `presentation`: completion, independent
    /// verification of the emitted certificate, and table construction from
    /// the verified data.
    ///
    /// Verification goes through [`crate::verify::verify_certificate`], which
    /// is the same verifier [`crate::verify::verify`] runs after parsing
    /// bytes. The engine shares no algorithm with it.
    ///
    /// Errors: [`AlgebraBuildError::Truncated`] when a budget of `limits`
    /// runs out, [`AlgebraBuildError::InfiniteDimensional`] when the verifier
    /// proves the quotient infinite dimensional,
    /// [`AlgebraBuildError::InputRelationsMismatch`] when the verified
    /// certificate is not about `presentation`,
    /// [`AlgebraBuildError::NonAdmissible`] when the arrow ideal is not
    /// nilpotent, and [`AlgebraBuildError::Verification`] when the verifier
    /// rejects the certificate for any other reason (an engine defect).
    ///
    /// The algebra stores `limits` as its effective completion limits, and
    /// every derived completion, [`crate::opposite::opposite`] included,
    /// runs with them.
    pub fn new(
        presentation: Presentation,
        limits: &CompletionLimits,
    ) -> Result<Arc<Algebra>, AlgebraBuildError> {
        hit(Site::AlgebraNew);
        let certificate = match complete(&presentation, limits) {
            Outcome::Complete(certificate) => certificate,
            Outcome::Truncated(diagnostics) => {
                return Err(AlgebraBuildError::Truncated(diagnostics));
            }
        };
        // verify_certificate consumes the certificate, and the infinite case
        // has to hand it back. The verifier returns InfiniteDimensional only
        // for a certificate whose own finiteness claim is Infinite (a Finite
        // claim over a cyclic automaton is FinitenessClaim instead), so a copy
        // taken in exactly that case covers the error path and the finite path
        // copies nothing.
        let spare = match certificate.finiteness {
            FinitenessData::Infinite { .. } => Some(certificate.clone()),
            FinitenessData::Finite => None,
        };
        match verify_certificate(certificate) {
            Ok(verified) => {
                check_input_relations(&presentation, verified.certificate())?;
                Algebra::from_verified_with_limits(verified, limits)
            }
            Err(VerifyError::InfiniteDimensional { witness }) => {
                Err(AlgebraBuildError::InfiniteDimensional {
                    certificate: Box::new(
                        spare.expect("only an infinite finiteness claim yields this error"),
                    ),
                    witness,
                })
            }
            Err(error) => Err(AlgebraBuildError::Verification(error)),
        }
    }

    /// Builds the algebra from an already verified completion. This is the
    /// dump, reload, and reverify path: serialize with
    /// [`Algebra::certificate`], later call [`crate::verify::verify`] on the
    /// bytes, and rebuild from the token.
    ///
    /// Errors with [`AlgebraBuildError::NonAdmissible`] when the arrow ideal
    /// of the verified quotient is not nilpotent. Verification proves the
    /// quotient finite dimensional, which is weaker: it decides that from
    /// the leading words alone.
    ///
    /// The rebuilt algebra uses [`CompletionLimits::default`] as its
    /// effective limits. This is policy: certificate bytes are untrusted
    /// input, and untrusted input must never carry or select downstream
    /// resource budgets. Use [`Algebra::from_verified_with_limits`] when a
    /// reload flow wants to preserve the budgets of the original build.
    pub fn from_verified(verified: VerifiedCompletion) -> Result<Arc<Algebra>, AlgebraBuildError> {
        Algebra::from_verified_with_limits(verified, &CompletionLimits::default())
    }

    /// [`Algebra::from_verified`] with explicit effective completion
    /// limits. The limits come from the caller, never from the certificate
    /// bytes; downstream completions such as
    /// [`crate::opposite::opposite`] run with them.
    pub fn from_verified_with_limits(
        verified: VerifiedCompletion,
        limits: &CompletionLimits,
    ) -> Result<Arc<Algebra>, AlgebraBuildError> {
        hit(Site::AlgebraFromVerified);
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
            radical_powers: Vec::new(),
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
        // radical_chain needs right_mul and between, and nothing after it, so
        // it is the last field filled.
        algebra.radical_powers = algebra.radical_chain()?;
        Ok(Arc::new(algebra))
    }

    /// The chain `J^0 ⊇ J^1 ⊇ ... ⊇ J^d = 0`, entry `k` holding `J^k`, or a
    /// rejection when no `d` with `J^d = 0` exists.
    ///
    /// The chain is descending, so within `dim` steps it either reaches zero
    /// or repeats a nonzero dimension. A repeat means `J^k = J^{k+1}`, hence
    /// `J^k = J^m` for every `m >= k`, so `J` is not nilpotent and the ideal
    /// is not admissible. Multiplication tables are the only input: leading
    /// words alone cannot decide this, because `(x³)` and `(x³ - x²)` share
    /// every leading word and only the first is admissible.
    ///
    /// The walk runs once, at construction. Every reader of a radical power
    /// indexes the stored chain, so the cost is paid one time per algebra
    /// rather than once per query.
    fn radical_chain(&self) -> Result<Vec<Vec<Vec<DenseMat>>>, AlgebraBuildError> {
        let total =
            |power: &[Vec<DenseMat>]| -> usize { power.iter().flatten().map(DenseMat::rows).sum() };
        let n = self.quiver.num_vertices() as usize;
        // J^0 is A itself, and paths_between(u, v) is a basis of e_u A e_v, so
        // the component of J^0 at (u, v) is the identity.
        let identity: Vec<Vec<DenseMat>> = (0..n)
            .map(|u| {
                (0..n)
                    .map(|v| DenseMat::identity(self.between[u][v].len()))
                    .collect()
            })
            .collect();
        let mut chain = vec![identity];
        for _ in 0..=self.dim() {
            let dimension = total(chain.last().expect("the chain starts at J^0"));
            if dimension == 0 {
                return Ok(chain);
            }
            let next = self.radical_step(chain.last().expect("the chain starts at J^0"));
            let next_dimension = total(&next);
            debug_assert!(next_dimension <= dimension, "J^{{k+1}} is contained in J^k");
            if next_dimension == dimension {
                return Err(AlgebraBuildError::NonAdmissible {
                    stable_power: chain.len() - 1,
                    dimension,
                });
            }
            chain.push(next);
        }
        unreachable!("a strictly descending chain of subspaces of A reaches zero within dim steps")
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
        hit(Site::NfWord);
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
        hit(Site::MulBasis);
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

    /// Divides `word` against the reduced Groebner basis. Requires `word`
    /// nonempty and composable in the quiver.
    ///
    /// The verified diamond property makes every reduction order give the
    /// same normal form, so reducing the first matching basis element at its
    /// leftmost factor is as good as any other choice.
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

    /// The stored component of `e_u · J^k · e_v`, one spanning vector per
    /// row, in the coordinates of [`Self::paths_between`]`(u, v)`. `J^0` is
    /// the algebra itself, so `k = 0` gives the identity. Panics if either
    /// vertex is out of range.
    ///
    /// Row-space iteration computes `J^k`: `J^1` is the span of the
    /// non-trivial basis words and `J^{k+1}` is the span of `x·a` over `x`
    /// spanning `J^k` and arrows `a`. Word length does not decide radical
    /// depth: an inhomogeneous relation can place a short normal word inside
    /// a deep radical power.
    ///
    /// The iteration runs at construction, not here, and the matrix is
    /// borrowed, so this method costs one index.
    pub fn radical_power_matrix(&self, u: u32, v: u32, k: usize) -> &DenseMat {
        assert!(u < self.quiver.num_vertices() && v < self.quiver.num_vertices());
        &self.radical_power(k)[u as usize][v as usize]
    }

    /// The least `k` with `J^k = 0`, read off the chain construction built.
    /// Finite for every constructed algebra: an `Algebra` exists only when its
    /// arrow ideal `J` is nilpotent. The Jacobson radical of a
    /// finite-dimensional algebra is always nilpotent, but `J` is the arrow
    /// ideal, and a quotient can be finite dimensional with `J` not nilpotent.
    #[inline]
    pub fn nilpotency_degree(&self) -> usize {
        self.radical_powers.len() - 1
    }

    /// Row-reduced component matrices of `J^k`, indexed `[u][v]` with columns
    /// over `paths_between(u, v)`.
    ///
    /// The stored chain stops at `J^d = 0`, and `J^k = 0` for every `k >= d`,
    /// so an index past the end reads the last entry.
    fn radical_power(&self, k: usize) -> &[Vec<DenseMat>] {
        &self.radical_powers[k.min(self.nilpotency_degree())]
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
                        mat.into_row_space_basis(&self.field)
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

/// `ideal` as a [`Presentation`] over `field`: one monic one-term relation
/// per forbidden word, in the ideal's own order.
///
/// [`MonomialIdeal::new`] already checked that every forbidden word is a
/// path of length >= 2, which is what [`Relation::new`] asks for, so nothing
/// here can be rejected.
pub fn monomial_presentation(ideal: &MonomialIdeal, field: PrimeField) -> Presentation {
    let quiver = ideal.quiver().clone();
    let relations = ideal
        .forbidden()
        .iter()
        .map(|word| {
            Relation::new(&quiver, field, vec![(field.one(), word.clone())])
                .expect("a forbidden word is a path of length >= 2")
        })
        .collect();
    Presentation::new(quiver, field, relations).expect("the relations were built over this quiver")
}

/// Completion limits adequate for `ideal`: each entry is the default or a
/// bound derived from the forbidden words, whichever is larger.
///
/// `max_word_len` covers the longest self-overlap superposition, `2·L - 1`
/// for the longest forbidden word length `L`. `max_basis` covers the
/// forbidden words. `max_ambiguities` covers `2·L` keys for each ordered
/// pair of forbidden words. `max_origin_terms` keeps the default: a monomial
/// completion never combines provenance, because every composition reduces to
/// zero, so each origin keeps the one term its forbidden word started with.
///
/// `max_steps` keeps the default as well, and that is the one budget these
/// limits do not derive. Each emitted normal word costs one step, so a
/// monomial algebra of dimension above `max_steps` truncates. The truncation
/// is typed, so the caller sees it.
pub fn monomial_limits(ideal: &MonomialIdeal) -> CompletionLimits {
    let defaults = CompletionLimits::default();
    let words = ideal.forbidden().len();
    let longest = ideal.forbidden().iter().map(Vec::len).max().unwrap_or(0);
    CompletionLimits {
        max_basis: defaults.max_basis.max(words),
        max_word_len: defaults
            .max_word_len
            .max(longest.saturating_mul(2).saturating_sub(1)),
        max_steps: defaults.max_steps,
        max_origin_terms: defaults.max_origin_terms,
        max_ambiguities: defaults.max_ambiguities.max(
            words
                .saturating_mul(words)
                .saturating_mul(longest.saturating_mul(2)),
        ),
    }
}

/// The runtime algebra of `ideal` over `field`, built with
/// [`monomial_limits`].
pub fn monomial_algebra(
    ideal: &MonomialIdeal,
    field: PrimeField,
) -> Result<Arc<Algebra>, AlgebraBuildError> {
    Algebra::new(monomial_presentation(ideal, field), &monomial_limits(ideal))
}

/// The path algebra `kQ` over `field`, with no relations.
///
/// Errors with [`AlgebraBuildError::InfiniteDimensional`] when `quiver` has a
/// cycle, since then `kQ` has infinitely many paths. The default completion
/// limits are adequate: with no relation there is no superposition word.
pub fn path_algebra(quiver: Quiver, field: PrimeField) -> Result<Arc<Algebra>, AlgebraBuildError> {
    let presentation =
        Presentation::new(quiver, field, Vec::new()).expect("there is no relation to reject");
    Algebra::new(presentation, &CompletionLimits::default())
}

/// Path algebra of linearly oriented `A_n` over `field`.
pub fn linear_an(n: usize, field: PrimeField) -> Arc<Algebra> {
    monomial_algebra(&linear_an_ideal(n), field)
        .expect("the zero ideal over an acyclic quiver completes")
}

/// Kronecker-type algebra over `field`: vertices `0, 1` and `m` parallel
/// arrows `0 → 1`. Hereditary; `dim = m + 2`.
pub fn kronecker(m: usize, field: PrimeField) -> Arc<Algebra> {
    monomial_algebra(&kronecker_ideal(m), field)
        .expect("the zero ideal over an acyclic quiver completes")
}

/// `k[x]/(x²)` over `field`: one vertex, one loop `x`, forbidden word `xx`.
pub fn dual_numbers(field: PrimeField) -> Arc<Algebra> {
    truncated_poly(2, field).expect("x² is an admissible relation")
}

/// `k[x]/(xⁿ)` over `field`, as [`crate::monomial::truncated_poly_ideal`].
pub fn truncated_poly(n: usize, field: PrimeField) -> Result<Arc<Algebra>, AlgebraBuildError> {
    let ideal = truncated_poly_ideal(n).map_err(AlgebraBuildError::Monomial)?;
    monomial_algebra(&ideal, field)
}

/// Linear Nakayama algebra over `field`, as
/// [`crate::monomial::linear_nakayama_ideal`].
pub fn linear_nakayama(
    kupisch: &[usize],
    field: PrimeField,
) -> Result<Arc<Algebra>, AlgebraBuildError> {
    let ideal = linear_nakayama_ideal(kupisch).map_err(AlgebraBuildError::Monomial)?;
    monomial_algebra(&ideal, field)
}

/// Cyclic Nakayama algebra over `field`, as
/// [`crate::monomial::cyclic_nakayama_ideal`].
pub fn cyclic_nakayama(
    kupisch: &[usize],
    field: PrimeField,
) -> Result<Arc<Algebra>, AlgebraBuildError> {
    let ideal = cyclic_nakayama_ideal(kupisch).map_err(AlgebraBuildError::Monomial)?;
    monomial_algebra(&ideal, field)
}

/// Cyclic quiver on `n` vertices with `rad² = 0` over `field`, as
/// [`crate::monomial::radical_square_zero_cycle_ideal`]. `dim = 2n`.
pub fn radical_square_zero_cycle(n: usize, field: PrimeField) -> Arc<Algebra> {
    monomial_algebra(&radical_square_zero_cycle_ideal(n), field)
        .expect("rad² = 0 leaves only vertices and arrows")
}

/// Linearly oriented `A_n` with zero relations over `field`, as
/// [`crate::monomial::an_with_relations_ideal`].
pub fn an_with_relations(
    n: usize,
    zero_paths: &[(usize, usize)],
    field: PrimeField,
) -> Result<Arc<Algebra>, AlgebraBuildError> {
    let ideal = an_with_relations_ideal(n, zero_paths).map_err(AlgebraBuildError::Monomial)?;
    monomial_algebra(&ideal, field)
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
    // The one relation has length 2, so completion needs word length 3 at
    // most and a handful of steps. The defaults cover that.
    Algebra::new(presentation, &CompletionLimits::default())
        .expect("the commutative square is finite dimensional")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::monomial::MonomialPresentation;
    use crate::verify::verify;

    fn f5() -> PrimeField {
        PrimeField::new(5).unwrap()
    }

    fn word(algebra: &Algebra, arrows: &[u32]) -> PathWord {
        let ids: Vec<ArrowId> = arrows.iter().copied().map(ArrowId).collect();
        PathWord::from_arrows(algebra.quiver(), &ids).unwrap()
    }

    /// One vertex, one loop `x`, and the relation given as
    /// `(coefficient, exponent)` terms.
    fn loop_presentation(field: PrimeField, terms: &[(i64, usize)]) -> Presentation {
        let quiver = Quiver::new(1, &[(0, 0)]).unwrap();
        let relation = Relation::new(
            &quiver,
            field,
            terms
                .iter()
                .map(|&(c, n)| (field.elem(c), vec![ArrowId(0); n]))
                .collect(),
        )
        .expect("the terms are parallel words of length >= 2");
        Presentation::new(quiver, field, vec![relation]).expect("built over this quiver and field")
    }

    /// The witness of the admissibility defect. `x³ - x²` passes every
    /// relation check and completes: the leading word is `x³`, its
    /// automaton is acyclic, and the verifier reports a finite quotient of
    /// dimension 3. The quotient is `k[x]/(x²) × k`, where the arrow ideal
    /// `J = span(x, x²)` has `J² = J³ = span(x²)` and never reaches zero.
    #[test]
    fn a_stable_nonzero_arrow_ideal_is_rejected_as_non_admissible() {
        let presentation = loop_presentation(f5(), &[(1, 3), (-1, 2)]);
        assert_eq!(
            Algebra::new(presentation.clone(), &CompletionLimits::default()).unwrap_err(),
            AlgebraBuildError::NonAdmissible {
                stable_power: 2,
                dimension: 1,
            }
        );
        // The completion and the verifier both accept, so the reload path
        // needs the same check as `Algebra::new`.
        let certificate = match complete(&presentation, &CompletionLimits::default()) {
            Outcome::Complete(certificate) => certificate,
            Outcome::Truncated(diagnostics) => panic!("unexpected truncation: {diagnostics:?}"),
        };
        let verified = verify(&certificate.to_canonical_json()).expect("the certificate verifies");
        assert_eq!(verified.normal_words().len(), 3);
        assert_eq!(
            Algebra::from_verified(verified).unwrap_err(),
            AlgebraBuildError::NonAdmissible {
                stable_power: 2,
                dimension: 1,
            }
        );
    }

    /// Arrows `a: 0 → 1`, `b: 1 → 3`, `c: 0 → 2`, `d: 2 → 4`, `e: 4 → 3`,
    /// and the relation `cde - ab`. The ideal is admissible, so the algebra
    /// builds. Its nilpotency degree is 4 while the longest normal word has
    /// length 2: `J³ = span(ab)` because `cd·e` rewrites to `ab`.
    #[test]
    fn an_admissible_inhomogeneous_presentation_builds() {
        let field = f5();
        let quiver = Quiver::new(5, &[(0, 1), (1, 3), (0, 2), (2, 4), (4, 3)]).unwrap();
        let relation = Relation::new(
            &quiver,
            field,
            vec![
                (field.one(), vec![ArrowId(2), ArrowId(3), ArrowId(4)]),
                (field.elem(-1), vec![ArrowId(0), ArrowId(1)]),
            ],
        )
        .unwrap();
        let presentation = Presentation::new(quiver, field, vec![relation]).unwrap();
        let a = Algebra::new(presentation, &CompletionLimits::default()).unwrap();
        assert_eq!(a.dim(), 13);
        assert_eq!(a.basis().iter().map(PathWord::len).max(), Some(2));
        assert_eq!(a.nilpotency_degree(), 4);
    }

    #[test]
    fn a_certificate_about_another_presentation_is_rejected() {
        let field = f5();
        let a = loop_presentation(field, &[(1, 3)]);
        let b = loop_presentation(field, &[(1, 4)]);
        let built = Algebra::new(a.clone(), &CompletionLimits::default()).unwrap();
        assert_eq!(check_input_relations(&a, built.certificate()), Ok(()));
        assert_eq!(
            check_input_relations(&b, built.certificate()),
            Err(AlgebraBuildError::InputRelationsMismatch { index: 0 })
        );
        let empty =
            Presentation::new(Quiver::new(1, &[(0, 0)]).unwrap(), field, Vec::new()).unwrap();
        assert_eq!(
            check_input_relations(&empty, built.certificate()),
            Err(AlgebraBuildError::InputRelationsMismatch { index: 0 })
        );
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
        let ideal = truncated_poly_ideal(65).unwrap();
        assert!(matches!(
            Algebra::new(
                monomial_presentation(&ideal, f5()),
                &CompletionLimits::default()
            ),
            Err(AlgebraBuildError::Truncated(diagnostics))
                if diagnostics.reason == crate::completion::TruncationReason::WordLenBudget
        ));
    }

    #[test]
    fn monomial_limits_never_fall_below_the_defaults() {
        let ideal = truncated_poly_ideal(3).unwrap();
        assert_eq!(monomial_limits(&ideal), CompletionLimits::default());
        let long = truncated_poly_ideal(100).unwrap();
        let limits = monomial_limits(&long);
        assert_eq!(limits.max_word_len, 199);
        assert_eq!(limits.max_basis, CompletionLimits::default().max_basis);
        assert_eq!(limits.max_steps, CompletionLimits::default().max_steps);
    }

    #[test]
    fn from_verified_keeps_default_limits_and_with_limits_stores_them() {
        let a = truncated_poly(65, f5()).unwrap();
        let bytes = a.certificate().to_canonical_json();
        let reloaded = Algebra::from_verified(verify(&bytes).unwrap()).unwrap();
        assert_eq!(reloaded.completion_limits(), &CompletionLimits::default());
        let raised = CompletionLimits {
            max_word_len: 129,
            ..CompletionLimits::default()
        };
        let preserved =
            Algebra::from_verified_with_limits(verify(&bytes).unwrap(), &raised).unwrap();
        assert_eq!(preserved.completion_limits(), &raised);
    }

    #[test]
    fn truncated_poly_rejects_n_below_2() {
        assert!(matches!(
            truncated_poly(1, f5()),
            Err(AlgebraBuildError::Monomial(
                MonomialError::ForbiddenWordTooShort { index: 0, len: 1 }
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
                MonomialError::InvalidKupisch { .. }
            ))
        ));
    }

    #[test]
    fn linear_kupisch_drop_violation_rejected() {
        assert!(matches!(
            linear_nakayama(&[4, 2, 1], f5()),
            Err(AlgebraBuildError::Monomial(
                MonomialError::InvalidKupisch { .. }
            ))
        ));
    }

    #[test]
    fn cyclic_kupisch_entry_below_2_rejected() {
        assert!(matches!(
            cyclic_nakayama(&[2, 1, 2], f5()),
            Err(AlgebraBuildError::Monomial(
                MonomialError::InvalidKupisch { .. }
            ))
        ));
    }

    #[test]
    fn cyclic_kupisch_drop_violation_rejected() {
        assert!(matches!(
            cyclic_nakayama(&[4, 2, 2], f5()),
            Err(AlgebraBuildError::Monomial(
                MonomialError::InvalidKupisch { .. }
            ))
        ));
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
    fn an_zero_path_out_of_range_rejected() {
        assert!(matches!(
            an_with_relations(3, &[(1, 2)], f5()),
            Err(AlgebraBuildError::Monomial(
                MonomialError::ZeroPathOutOfRange { start: 1, len: 2 }
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

    /// The runtime pipeline and the field-free analysis agree on a monomial
    /// ideal: normal words are standard paths, in the same order.
    #[test]
    fn normal_words_equal_the_standard_paths() {
        let quiver = Quiver::new(4, &[(0, 1), (1, 2), (1, 3)]).unwrap();
        let ideal = MonomialIdeal::new(quiver, vec![vec![ArrowId(0), ArrowId(1)]]).unwrap();
        let m = MonomialPresentation::new(ideal.clone()).unwrap();
        let a = monomial_algebra(&ideal, f5()).unwrap();
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
        let rebuilt = Algebra::from_verified(verified).expect("the ideal is admissible");
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
    fn radical_power_matrices_descend_by_row_space_iteration() {
        let f = f5();
        let a = linear_an(3, f);
        let rank = |u, v, k| a.radical_power_matrix(u, v, k).rows();
        // e_0 A e_2 is one-dimensional (the word ab), which lies in J and J².
        assert_eq!(rank(0, 2, 0), 1);
        assert_eq!(rank(0, 2, 1), 1);
        assert_eq!(rank(0, 2, 2), 1);
        assert_eq!(rank(0, 2, 3), 0);
        // e_0 A e_1 is the arrow a: in J but not in J².
        assert_eq!(rank(0, 1, 1), 1);
        assert_eq!(rank(0, 1, 2), 0);
        // The trivial component at a vertex leaves J immediately.
        assert_eq!(rank(0, 0, 0), 1);
        assert_eq!(rank(0, 0, 1), 0);
    }
}

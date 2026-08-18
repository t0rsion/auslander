//! Independent verification of completion certificates.
//!
//! The verifier accepts a certificate only when it reproduces every claim
//! itself, from the certificate and nothing else. It reuses four modules:
//! [`crate::field`] arithmetic, [`crate::quiver`] paths, the sealed
//! comparison of [`crate::order`], and the [`crate::certificate`] data
//! model. Every replay routine, the ambiguity enumeration, and the
//! normal-word automaton are written here from the definitions, so a
//! defect in the completion engine cannot make a bad certificate pass.
//!
//! Two entry points, one verifier. [`verify`] takes untrusted bytes and
//! parses them strictly before anything else. [`verify_certificate`] takes
//! a parsed [`Certificate`] and runs every check listed on it. The engine
//! calls the typed one, so building an algebra does not serialize and
//! reparse its own certificate. Transport is the only difference: the
//! checks are the same function on the same data either way.
//!
//! Conventions this module fixes:
//!
//! - A trace replays over a polynomial, a map from word to coefficient.
//!   A step eliminates one word: the step coefficient must equal the
//!   current coefficient of that word, so the subtraction leaves zero
//!   there.
//! - The composition of an overlap `(i, j, offset)` is `g_i·v - u·g_j`,
//!   where `u` is the first `offset` arrows of `leading(g_i)` and `v` is
//!   the tail of `leading(g_j)` past the shared part. The composition of
//!   an inclusion `(i, j, offset)` is `g_i - u·g_j·v` with
//!   `leading(g_i) = u·leading(g_j)·v`. A trace start must equal the
//!   composition or its negation. Accepting both signs keeps the check
//!   free of any producer's sign convention.
//! - A composition that is exactly zero takes the empty trace: empty
//!   start, no steps.
//! - The ambiguity list must equal the enumeration of `(i, j, kind,
//!   offset)` keys in canonical order: `i`, then `j`, then overlap before
//!   inclusion, then offset. The verifier walks a lazy key generator in
//!   lockstep with the list, so it never materializes the full set. A
//!   duplicate key, an extra key, a missing key, and an out-of-order key
//!   are four distinct errors.
//! - The certificate's `automaton` section must equal the verifier's own
//!   automaton state for state and transition for transition, in the
//!   canonical order. The `finiteness` claim must match the verifier's
//!   own cycle decision; an infinite claim must carry a witness the
//!   verifier replays in full.
//! - Normal words are compared in lockstep against a lazy enumeration in
//!   the fixed basis order. The verifier requests at most one word past
//!   the certificate list, so its memory stays bounded by the automaton
//!   size.
//!
//! [`VerifiedCompletion`] has no public constructor. Holding one proves
//! the bytes passed every check in this module.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt;

use crate::certificate::{
    AmbiguityKind, CERT_SCHEMA, CertParseError, Certificate, FinitenessData, RelationData,
    TraceStep,
};
use crate::field::{FieldError, Fp, PrimeField};
use crate::order::{ORDER_ID, word_cmp};
use crate::quiver::{ArrowId, PathWord, Quiver, QuiverError};

/// A witness for an infinite-dimensional quotient: `prefix` reaches a
/// state on a cycle of the normal-word automaton and `cycle` returns to
/// that state. Every word `prefix·cycle^k` is a normal word.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CycleWitness {
    pub prefix: Vec<u32>,
    pub cycle: Vec<u32>,
}

/// Where a trace under replay lives in the certificate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TraceSite {
    /// `membership[input]`.
    Membership { input: usize },
    /// `ambiguities[index].trace`.
    Ambiguity { index: usize },
}

impl fmt::Display for TraceSite {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Membership { input } => write!(f, "membership trace {input}"),
            Self::Ambiguity { index } => write!(f, "ambiguity trace {index}"),
        }
    }
}

/// A defect in one term of relation data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TermDefect {
    /// The relation has no terms.
    Empty,
    /// The coefficient is zero.
    ZeroCoefficient,
    /// The coefficient is not in `0..p`.
    NonCanonicalCoefficient { coeff: u64 },
    /// The word has length below 2.
    WordTooShort { len: usize },
    /// The word is not a path of the quiver.
    InvalidWord(QuiverError),
    /// The word starts at a different vertex than term 0.
    MixedSource,
    /// The word ends at a different vertex than term 0.
    MixedTarget,
    /// The word is not strictly below the word before it.
    NotDescending,
}

impl fmt::Display for TermDefect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => f.write_str("relation has no terms"),
            Self::ZeroCoefficient => f.write_str("coefficient is zero"),
            Self::NonCanonicalCoefficient { coeff } => {
                write!(f, "coefficient {coeff} is not in 0..p")
            }
            Self::WordTooShort { len } => write!(f, "word has length {len}, below 2"),
            Self::InvalidWord(error) => write!(f, "word is not a path: {error}"),
            Self::MixedSource => f.write_str("word starts at a different vertex than term 0"),
            Self::MixedTarget => f.write_str("word ends at a different vertex than term 0"),
            Self::NotDescending => f.write_str("word is not strictly below the word before it"),
        }
    }
}

/// A defect in the witness of an infinite-dimensional claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WitnessDefect {
    /// The cycle word is empty.
    EmptyCycle,
    /// `prefix·cycle·cycle` is not a path of the quiver.
    NotAPath(QuiverError),
    /// The leading word of `basis[lead]` occurs in `prefix·cycle·cycle`
    /// at `position`.
    ContainsLeadingWord { lead: usize, position: usize },
    /// The prefix leaves the automaton at position `at`. Unreachable once
    /// the factor check passes; the check guards the definition.
    PrefixLeaves { at: usize },
    /// The cycle leaves the automaton at position `at`. Unreachable once
    /// the factor check passes; the check guards the definition.
    CycleLeaves { at: usize },
    /// Reading the cycle from the state the prefix reaches does not
    /// return to that state.
    CycleDoesNotReturn { reached: usize, back: usize },
}

impl fmt::Display for WitnessDefect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyCycle => f.write_str("the cycle word is empty"),
            Self::NotAPath(error) => {
                write!(f, "prefix and two cycles do not spell a path: {error}")
            }
            Self::ContainsLeadingWord { lead, position } => write!(
                f,
                "the leading word of basis element {lead} occurs at position {position}"
            ),
            Self::PrefixLeaves { at } => {
                write!(f, "the prefix leaves the automaton at position {at}")
            }
            Self::CycleLeaves { at } => {
                write!(f, "the cycle leaves the automaton at position {at}")
            }
            Self::CycleDoesNotReturn { reached, back } => write!(
                f,
                "the cycle starts at state {reached} but ends at state {back}"
            ),
        }
    }
}

/// A rejected certificate. Each variant names one failed check and carries
/// the indices needed to locate the defect.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    /// The bytes do not parse as a certificate.
    Parse(CertParseError),
    /// The schema string is not [`CERT_SCHEMA`].
    Schema { found: String },
    /// The order string is not [`ORDER_ID`].
    Order { found: String },
    /// The field modulus is rejected.
    Field(FieldError),
    /// The quiver data is rejected.
    Quiver(QuiverError),
    /// `input_relations[index]` has a defect at term `term`.
    InputRelation {
        index: usize,
        term: usize,
        defect: TermDefect,
    },
    /// `basis[index]` has a defect at term `term`.
    BasisRelation {
        index: usize,
        term: usize,
        defect: TermDefect,
    },
    /// `basis[index]` has leading coefficient `coeff`, not 1.
    BasisNotMonic { index: usize, coeff: u64 },
    /// The leading word of `basis[lead]` occurs in word `term` of
    /// `basis[element]` at `position`.
    BasisNotReduced {
        lead: usize,
        element: usize,
        term: usize,
        position: usize,
    },
    /// `origin` does not have one entry per basis element.
    OriginCount { basis: usize, origin: usize },
    /// An origin term of `basis[element]` has a zero or non-canonical
    /// coefficient.
    OriginCoefficient {
        element: usize,
        term: usize,
        coeff: u64,
    },
    /// An origin term of `basis[element]` names an input index out of range.
    OriginInputIndex {
        element: usize,
        term: usize,
        input_index: usize,
        inputs: usize,
    },
    /// An origin term of `basis[element]` expands to a non-path word.
    OriginNotComposable {
        element: usize,
        term: usize,
        error: QuiverError,
    },
    /// The origin of `basis[element]` does not expand to it; `word` is a
    /// word where the two sides differ.
    OriginMismatch { element: usize, word: Vec<u32> },
    /// `membership` does not have one trace per input relation.
    MembershipCount { inputs: usize, traces: usize },
    /// `membership[input].start` is not `input_relations[input]`.
    MembershipStart { input: usize },
    /// A trace step names a basis index out of range.
    TraceStepBasisIndex {
        site: TraceSite,
        step: usize,
        basis_index: usize,
        basis: usize,
    },
    /// A trace step's word is not `left · leading word · right`.
    TraceStepWord { site: TraceSite, step: usize },
    /// A trace step's word or one of its expansions is not a path.
    TraceStepPath {
        site: TraceSite,
        step: usize,
        error: QuiverError,
    },
    /// A trace step names a word the current polynomial does not contain.
    TraceStepAbsent {
        site: TraceSite,
        step: usize,
        word: Vec<u32>,
    },
    /// A trace step's coefficient does not eliminate the named word.
    TraceStepCoefficient {
        site: TraceSite,
        step: usize,
        expected: u64,
        found: u64,
    },
    /// A trace step expands to a word that is not strictly below the
    /// eliminated word.
    TraceStepAscending {
        site: TraceSite,
        step: usize,
        word: Vec<u32>,
    },
    /// The polynomial is not zero after the last step; `word` is the
    /// largest remaining word.
    TraceRemainder { site: TraceSite, word: Vec<u32> },
    /// The basis has this ambiguity but the certificate does not list it.
    AmbiguityMissing {
        i: usize,
        j: usize,
        kind: AmbiguityKind,
        offset: usize,
    },
    /// The certificate lists an entry that is not an ambiguity of the basis.
    AmbiguityExtra {
        i: usize,
        j: usize,
        kind: AmbiguityKind,
        offset: usize,
    },
    /// The certificate lists the same ambiguity twice.
    AmbiguityDuplicate {
        i: usize,
        j: usize,
        kind: AmbiguityKind,
        offset: usize,
    },
    /// `ambiguities[index]` skips this ambiguity: the list must follow
    /// the canonical `(i, j, kind, offset)` order, overlap before
    /// inclusion.
    AmbiguityOrder {
        index: usize,
        i: usize,
        j: usize,
        kind: AmbiguityKind,
        offset: usize,
    },
    /// `ambiguities[index].trace.start` has a defect at term `term`.
    AmbiguityStart {
        index: usize,
        term: usize,
        defect: TermDefect,
    },
    /// `ambiguities[index].trace.start` is not the composition or its
    /// negation.
    AmbiguityStartMismatch { index: usize },
    /// The automaton declares fewer states than the quiver has vertices.
    /// Checked before the quiver is built, so a huge declared vertex
    /// count cannot force a large allocation.
    AutomatonStateCount { vertices: u32, states: usize },
    /// The automaton state lists differ first at `position`. `None` means
    /// the list ends there.
    AutomatonStates {
        position: usize,
        expected: Option<Vec<u32>>,
        found: Option<Vec<u32>>,
    },
    /// The automaton transition lists differ first at `position`. `None`
    /// means the list ends there.
    AutomatonTransitions {
        position: usize,
        expected: Option<(usize, u32, usize)>,
        found: Option<(usize, u32, usize)>,
    },
    /// The finiteness claim contradicts the verifier's own cycle
    /// decision.
    FinitenessClaim { claimed_finite: bool },
    /// The witness of an infinite claim fails a check.
    InfiniteWitness { defect: WitnessDefect },
    /// The normal-word lists differ first at `position`. `None` means the
    /// list ends there.
    NormalWords {
        position: usize,
        expected: Option<Vec<u32>>,
        found: Option<Vec<u32>>,
    },
    /// The set of normal words is infinite. The witness is the
    /// certificate's own, fully verified.
    InfiniteDimensional { witness: CycleWitness },
}

impl fmt::Display for VerifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Parse(error) => write!(f, "certificate rejected: {error}"),
            Self::Schema { found } => {
                write!(f, "schema is {found:?}, expected {CERT_SCHEMA:?}")
            }
            Self::Order { found } => write!(f, "order is {found:?}, expected {ORDER_ID:?}"),
            Self::Field(error) => write!(f, "field rejected: {error}"),
            Self::Quiver(error) => write!(f, "quiver rejected: {error}"),
            Self::InputRelation {
                index,
                term,
                defect,
            } => write!(f, "input relation {index}, term {term}: {defect}"),
            Self::BasisRelation {
                index,
                term,
                defect,
            } => write!(f, "basis element {index}, term {term}: {defect}"),
            Self::BasisNotMonic { index, coeff } => write!(
                f,
                "basis element {index} has leading coefficient {coeff}, not 1"
            ),
            Self::BasisNotReduced {
                lead,
                element,
                term,
                position,
            } => write!(
                f,
                "leading word of basis element {lead} occurs in word {term} of \
                 basis element {element} at position {position}"
            ),
            Self::OriginCount { basis, origin } => {
                write!(f, "origin has {origin} entries for {basis} basis elements")
            }
            Self::OriginCoefficient {
                element,
                term,
                coeff,
            } => write!(
                f,
                "origin of basis element {element}, term {term}: coefficient {coeff} \
                 is zero or not in 0..p"
            ),
            Self::OriginInputIndex {
                element,
                term,
                input_index,
                inputs,
            } => write!(
                f,
                "origin of basis element {element}, term {term}: input index \
                 {input_index} outside 0..{inputs}"
            ),
            Self::OriginNotComposable {
                element,
                term,
                error,
            } => write!(
                f,
                "origin of basis element {element}, term {term}: expansion is not \
                 a path: {error}"
            ),
            Self::OriginMismatch { element, word } => write!(
                f,
                "origin of basis element {element} does not expand to it; the \
                 sides differ at word {word:?}"
            ),
            Self::MembershipCount { inputs, traces } => {
                write!(f, "membership has {traces} traces for {inputs} inputs")
            }
            Self::MembershipStart { input } => write!(
                f,
                "membership trace {input} does not start at input relation {input}"
            ),
            Self::TraceStepBasisIndex {
                site,
                step,
                basis_index,
                basis,
            } => write!(
                f,
                "{site}, step {step}: basis index {basis_index} outside 0..{basis}"
            ),
            Self::TraceStepWord { site, step } => write!(
                f,
                "{site}, step {step}: word is not left, leading word, right \
                 concatenated"
            ),
            Self::TraceStepPath { site, step, error } => {
                write!(f, "{site}, step {step}: not a path: {error}")
            }
            Self::TraceStepAbsent { site, step, word } => {
                write!(f, "{site}, step {step}: word {word:?} has coefficient zero")
            }
            Self::TraceStepCoefficient {
                site,
                step,
                expected,
                found,
            } => write!(
                f,
                "{site}, step {step}: the word has coefficient {expected}, the \
                 step says {found}"
            ),
            Self::TraceStepAscending { site, step, word } => write!(
                f,
                "{site}, step {step}: expanded word {word:?} is not strictly \
                 below the eliminated word"
            ),
            Self::TraceRemainder { site, word } => write!(
                f,
                "{site}: not zero after the last step; largest remaining word {word:?}"
            ),
            Self::AmbiguityMissing { i, j, kind, offset } => write!(
                f,
                "ambiguity ({i}, {j}, {}, {offset}) is missing",
                kind.as_str()
            ),
            Self::AmbiguityExtra { i, j, kind, offset } => write!(
                f,
                "({i}, {j}, {}, {offset}) is not an ambiguity of the basis",
                kind.as_str()
            ),
            Self::AmbiguityDuplicate { i, j, kind, offset } => write!(
                f,
                "ambiguity ({i}, {j}, {}, {offset}) is listed twice",
                kind.as_str()
            ),
            Self::AmbiguityOrder {
                index,
                i,
                j,
                kind,
                offset,
            } => write!(
                f,
                "ambiguity entry {index} skips ({i}, {j}, {}, {offset}); the list \
                 must follow the canonical key order",
                kind.as_str()
            ),
            Self::AmbiguityStart {
                index,
                term,
                defect,
            } => write!(f, "ambiguity {index}, start term {term}: {defect}"),
            Self::AmbiguityStartMismatch { index } => write!(
                f,
                "ambiguity {index}: start is not the composition or its negation"
            ),
            Self::AutomatonStateCount { vertices, states } => write!(
                f,
                "the automaton has {states} states for {vertices} vertices"
            ),
            Self::AutomatonStates {
                position,
                expected,
                found,
            } => write!(
                f,
                "automaton states differ at position {position}: expected \
                 {expected:?}, found {found:?}"
            ),
            Self::AutomatonTransitions {
                position,
                expected,
                found,
            } => write!(
                f,
                "automaton transitions differ at position {position}: expected \
                 {expected:?}, found {found:?}"
            ),
            Self::FinitenessClaim { claimed_finite } => {
                if *claimed_finite {
                    f.write_str(
                        "the certificate claims a finite language but the automaton has a cycle",
                    )
                } else {
                    f.write_str(
                        "the certificate claims an infinite language but the automaton is acyclic",
                    )
                }
            }
            Self::InfiniteWitness { defect } => {
                write!(f, "the infinite-dimension witness is rejected: {defect}")
            }
            Self::NormalWords {
                position,
                expected,
                found,
            } => write!(
                f,
                "normal words differ at position {position}: expected {expected:?}, \
                 found {found:?}"
            ),
            Self::InfiniteDimensional { witness } => write!(
                f,
                "the quotient is infinite dimensional: prefix {:?}, cycle {:?}",
                witness.prefix, witness.cycle
            ),
        }
    }
}

impl std::error::Error for VerifyError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Parse(error) => Some(error),
            Self::Field(error) => Some(error),
            Self::Quiver(error) => Some(error),
            _ => None,
        }
    }
}

/// A certificate that passed every check. Only [`verify`] builds one, and
/// the fields stay private, so holding the value is proof the bytes
/// verified. Every constructor of [`crate::algebra::Algebra`] consumes
/// one, so verification is the only route to an algebra.
#[derive(Clone, Debug)]
pub struct VerifiedCompletion {
    certificate: Certificate,
    quiver: Quiver,
    field: PrimeField,
    basis: Vec<Vec<(Fp, PathWord)>>,
    normal_words: Vec<PathWord>,
}

impl VerifiedCompletion {
    /// The verified certificate.
    #[inline]
    pub fn certificate(&self) -> &Certificate {
        &self.certificate
    }

    /// The quiver rebuilt from the certificate.
    #[inline]
    pub fn quiver(&self) -> &Quiver {
        &self.quiver
    }

    /// The prime field of the certificate.
    #[inline]
    pub fn field(&self) -> PrimeField {
        self.field
    }

    /// The reduced Groebner basis, each element as descending
    /// `(coefficient, word)` terms.
    #[inline]
    pub fn basis(&self) -> &[Vec<(Fp, PathWord)>] {
        &self.basis
    }

    /// The normal words in the fixed basis order: trivial paths by vertex,
    /// then by length, source, and lexicographic arrow word.
    #[inline]
    pub fn normal_words(&self) -> &[PathWord] {
        &self.normal_words
    }
}

type Poly = BTreeMap<Vec<u32>, Fp>;

fn ids(word: &[u32]) -> Vec<ArrowId> {
    word.iter().copied().map(ArrowId).collect()
}

fn cmp_words(a: &[u32], b: &[u32]) -> Ordering {
    word_cmp(&ids(a), &ids(b))
}

fn is_suffix(needle: &[u32], hay: &[u32]) -> bool {
    needle.len() <= hay.len() && hay[hay.len() - needle.len()..] == *needle
}

fn find_factor(hay: &[u32], needle: &[u32]) -> Option<usize> {
    if needle.is_empty() || needle.len() > hay.len() {
        return None;
    }
    (0..=hay.len() - needle.len()).find(|&at| hay[at..at + needle.len()] == *needle)
}

fn poly_add(field: PrimeField, poly: &mut Poly, word: Vec<u32>, value: Fp) {
    use std::collections::btree_map::Entry;
    match poly.entry(word) {
        Entry::Vacant(entry) => {
            if !value.is_zero() {
                entry.insert(value);
            }
        }
        Entry::Occupied(mut entry) => {
            let sum = field.add(*entry.get(), value);
            if sum.is_zero() {
                entry.remove();
            } else {
                *entry.get_mut() = sum;
            }
        }
    }
}

/// Caller guarantees the data is validated: distinct words, canonical
/// nonzero coefficients.
fn poly_from_data(field: PrimeField, data: &RelationData) -> Poly {
    let mut poly = Poly::new();
    for (coeff, word) in data {
        poly_add(field, &mut poly, word.clone(), field.elem(*coeff as i64));
    }
    poly
}

fn poly_neg(field: PrimeField, poly: &Poly) -> Poly {
    poly.iter()
        .map(|(word, coeff)| (word.clone(), field.neg(*coeff)))
        .collect()
}

fn first_difference(a: &Poly, b: &Poly) -> Vec<u32> {
    a.iter()
        .find(|(word, coeff)| b.get(*word) != Some(*coeff))
        .map(|(word, _)| word.clone())
        .or_else(|| b.keys().find(|word| !a.contains_key(*word)).cloned())
        .unwrap_or_default()
}

fn validate_relation_data(
    quiver: &Quiver,
    modulus: u64,
    data: &RelationData,
) -> Result<(), (usize, TermDefect)> {
    if data.is_empty() {
        return Err((0, TermDefect::Empty));
    }
    let mut endpoints = None;
    for (index, (coeff, word)) in data.iter().enumerate() {
        if *coeff == 0 {
            return Err((index, TermDefect::ZeroCoefficient));
        }
        if *coeff >= modulus {
            return Err((index, TermDefect::NonCanonicalCoefficient { coeff: *coeff }));
        }
        if word.len() < 2 {
            return Err((index, TermDefect::WordTooShort { len: word.len() }));
        }
        let path = PathWord::from_arrows(quiver, &ids(word))
            .map_err(|error| (index, TermDefect::InvalidWord(error)))?;
        match endpoints {
            None => endpoints = Some((path.source(), path.target())),
            Some((source, target)) => {
                if path.source() != source {
                    return Err((index, TermDefect::MixedSource));
                }
                if path.target() != target {
                    return Err((index, TermDefect::MixedTarget));
                }
            }
        }
        if index > 0 && cmp_words(&data[index - 1].1, word) != Ordering::Greater {
            return Err((index, TermDefect::NotDescending));
        }
    }
    Ok(())
}

fn check_basis(quiver: &Quiver, modulus: u64, basis: &[RelationData]) -> Result<(), VerifyError> {
    for (index, element) in basis.iter().enumerate() {
        validate_relation_data(quiver, modulus, element).map_err(|(term, defect)| {
            VerifyError::BasisRelation {
                index,
                term,
                defect,
            }
        })?;
        if element[0].0 != 1 {
            return Err(VerifyError::BasisNotMonic {
                index,
                coeff: element[0].0,
            });
        }
    }
    for (lead_index, leader) in basis.iter().enumerate() {
        let lead = &leader[0].1;
        for (element, other) in basis.iter().enumerate() {
            for (term, (_, word)) in other.iter().enumerate() {
                if element == lead_index && term == 0 {
                    continue;
                }
                if let Some(position) = find_factor(word, lead) {
                    return Err(VerifyError::BasisNotReduced {
                        lead: lead_index,
                        element,
                        term,
                        position,
                    });
                }
            }
        }
    }
    Ok(())
}

fn check_origin(
    field: PrimeField,
    quiver: &Quiver,
    certificate: &Certificate,
) -> Result<(), VerifyError> {
    if certificate.origin.len() != certificate.basis.len() {
        return Err(VerifyError::OriginCount {
            basis: certificate.basis.len(),
            origin: certificate.origin.len(),
        });
    }
    for (element, terms) in certificate.origin.iter().enumerate() {
        let mut sum = Poly::new();
        for (term_index, origin_term) in terms.iter().enumerate() {
            if origin_term.coeff == 0 || origin_term.coeff >= field.modulus() {
                return Err(VerifyError::OriginCoefficient {
                    element,
                    term: term_index,
                    coeff: origin_term.coeff,
                });
            }
            let Some(relation) = certificate.input_relations.get(origin_term.input_index) else {
                return Err(VerifyError::OriginInputIndex {
                    element,
                    term: term_index,
                    input_index: origin_term.input_index,
                    inputs: certificate.input_relations.len(),
                });
            };
            let scale = field.elem(origin_term.coeff as i64);
            for (coeff, word) in relation {
                let mut expanded = origin_term.left.clone();
                expanded.extend_from_slice(word);
                expanded.extend_from_slice(&origin_term.right);
                PathWord::from_arrows(quiver, &ids(&expanded)).map_err(|error| {
                    VerifyError::OriginNotComposable {
                        element,
                        term: term_index,
                        error,
                    }
                })?;
                let value = field.mul(scale, field.elem(*coeff as i64));
                poly_add(field, &mut sum, expanded, value);
            }
        }
        let target = poly_from_data(field, &certificate.basis[element]);
        if sum != target {
            return Err(VerifyError::OriginMismatch {
                element,
                word: first_difference(&sum, &target),
            });
        }
    }
    Ok(())
}

fn replay(
    field: PrimeField,
    quiver: &Quiver,
    basis: &[RelationData],
    site: TraceSite,
    mut poly: Poly,
    steps: &[TraceStep],
) -> Result<(), VerifyError> {
    for (step_index, step) in steps.iter().enumerate() {
        let Some(element) = basis.get(step.basis_index) else {
            return Err(VerifyError::TraceStepBasisIndex {
                site,
                step: step_index,
                basis_index: step.basis_index,
                basis: basis.len(),
            });
        };
        let lead = &element[0].1;
        let mut factored = step.left.clone();
        factored.extend_from_slice(lead);
        factored.extend_from_slice(&step.right);
        if step.word != factored {
            return Err(VerifyError::TraceStepWord {
                site,
                step: step_index,
            });
        }
        PathWord::from_arrows(quiver, &ids(&step.word)).map_err(|error| {
            VerifyError::TraceStepPath {
                site,
                step: step_index,
                error,
            }
        })?;
        let Some(&current) = poly.get(&step.word) else {
            return Err(VerifyError::TraceStepAbsent {
                site,
                step: step_index,
                word: step.word.clone(),
            });
        };
        if step.coeff != current.raw() {
            return Err(VerifyError::TraceStepCoefficient {
                site,
                step: step_index,
                expected: current.raw(),
                found: step.coeff,
            });
        }
        for (term, (coeff, word)) in element.iter().enumerate() {
            let mut expanded = step.left.clone();
            expanded.extend_from_slice(word);
            expanded.extend_from_slice(&step.right);
            PathWord::from_arrows(quiver, &ids(&expanded)).map_err(|error| {
                VerifyError::TraceStepPath {
                    site,
                    step: step_index,
                    error,
                }
            })?;
            // The sealed order is compatible with concatenation, so this
            // branch cannot fire once the factorization check above and the
            // basis checks pass. The check guards the definition, not a
            // known failure mode.
            if term > 0 && cmp_words(&expanded, &step.word) != Ordering::Less {
                return Err(VerifyError::TraceStepAscending {
                    site,
                    step: step_index,
                    word: expanded,
                });
            }
            let delta = field.neg(field.mul(current, field.elem(*coeff as i64)));
            poly_add(field, &mut poly, expanded, delta);
        }
    }
    if let Some(word) = poly.keys().max_by(|a, b| cmp_words(a, b)) {
        return Err(VerifyError::TraceRemainder {
            site,
            word: word.clone(),
        });
    }
    Ok(())
}

fn check_membership(
    field: PrimeField,
    quiver: &Quiver,
    certificate: &Certificate,
) -> Result<(), VerifyError> {
    if certificate.membership.len() != certificate.input_relations.len() {
        return Err(VerifyError::MembershipCount {
            inputs: certificate.input_relations.len(),
            traces: certificate.membership.len(),
        });
    }
    for (input, trace) in certificate.membership.iter().enumerate() {
        if trace.start != certificate.input_relations[input] {
            return Err(VerifyError::MembershipStart { input });
        }
        replay(
            field,
            quiver,
            &certificate.basis,
            TraceSite::Membership { input },
            poly_from_data(field, &trace.start),
            &trace.steps,
        )?;
    }
    Ok(())
}

fn kind_tag(kind: AmbiguityKind) -> u8 {
    match kind {
        AmbiguityKind::Overlap => 0,
        AmbiguityKind::Inclusion => 1,
    }
}

fn tag_kind(tag: u8) -> AmbiguityKind {
    if tag == 0 {
        AmbiguityKind::Overlap
    } else {
        AmbiguityKind::Inclusion
    }
}

type AmbKey = (usize, usize, u8, usize);

/// All ambiguity keys of the ordered pair `(i, j)`, in canonical order:
/// overlap keys by ascending offset, then inclusion keys by ascending
/// offset.
fn pair_ambiguity_keys(i: usize, j: usize, leads: &[&Vec<u32>], out: &mut Vec<AmbKey>) {
    let lead_i = leads[i];
    let lead_j = leads[j];
    for offset in 1..lead_i.len() {
        let shared = lead_i.len() - offset;
        if shared < lead_j.len() && lead_i[offset..] == lead_j[..shared] {
            out.push((i, j, kind_tag(AmbiguityKind::Overlap), offset));
        }
    }
    if i != j && lead_j.len() < lead_i.len() {
        for offset in 0..=lead_i.len() - lead_j.len() {
            if lead_i[offset..offset + lead_j.len()] == **lead_j {
                out.push((i, j, kind_tag(AmbiguityKind::Inclusion), offset));
            }
        }
    }
}

/// Yields every ambiguity key of `leads` in canonical order without
/// materializing the full set: memory stays bounded by one pair's keys.
struct AmbiguityKeyGen<'a> {
    leads: &'a [&'a Vec<u32>],
    i: usize,
    j: usize,
    buffer: Vec<AmbKey>,
    buffer_at: usize,
}

impl<'a> AmbiguityKeyGen<'a> {
    fn new(leads: &'a [&'a Vec<u32>]) -> AmbiguityKeyGen<'a> {
        AmbiguityKeyGen {
            leads,
            i: 0,
            j: 0,
            buffer: Vec::new(),
            buffer_at: 0,
        }
    }

    fn next(&mut self) -> Option<AmbKey> {
        loop {
            if self.buffer_at < self.buffer.len() {
                self.buffer_at += 1;
                return Some(self.buffer[self.buffer_at - 1]);
            }
            if self.i >= self.leads.len() {
                return None;
            }
            self.buffer.clear();
            self.buffer_at = 0;
            pair_ambiguity_keys(self.i, self.j, self.leads, &mut self.buffer);
            self.j += 1;
            if self.j == self.leads.len() {
                self.j = 0;
                self.i += 1;
            }
        }
    }
}

/// Whether `(i, j, kind, offset)` names an ambiguity of `leads`. The test
/// reads the two leading words directly, so it stays independent of the
/// enumeration order that [`AmbiguityKeyGen`] follows.
fn is_ambiguity(leads: &[&Vec<u32>], key: AmbKey) -> bool {
    let (i, j, kind, offset) = key;
    let (Some(lead_i), Some(lead_j)) = (leads.get(i), leads.get(j)) else {
        return false;
    };
    if kind == kind_tag(AmbiguityKind::Overlap) {
        if offset == 0 || offset >= lead_i.len() {
            return false;
        }
        let shared = lead_i.len() - offset;
        shared < lead_j.len() && lead_i[offset..] == lead_j[..shared]
    } else {
        i != j
            && lead_j.len() < lead_i.len()
            && offset <= lead_i.len() - lead_j.len()
            && lead_i[offset..offset + lead_j.len()] == **lead_j
    }
}

/// Caller guarantees `(i, j, kind, offset)` is an enumerated ambiguity of
/// the validated basis, so every concatenation composes.
fn composition(
    field: PrimeField,
    basis: &[RelationData],
    i: usize,
    j: usize,
    kind: AmbiguityKind,
    offset: usize,
) -> Poly {
    let lead_i = &basis[i][0].1;
    let lead_j = &basis[j][0].1;
    let mut poly = Poly::new();
    match kind {
        AmbiguityKind::Overlap => {
            let left = &lead_i[..offset];
            let tail = &lead_j[lead_i.len() - offset..];
            for (coeff, word) in &basis[i] {
                let mut expanded = word.clone();
                expanded.extend_from_slice(tail);
                poly_add(field, &mut poly, expanded, field.elem(*coeff as i64));
            }
            for (coeff, word) in &basis[j] {
                let mut expanded = left.to_vec();
                expanded.extend_from_slice(word);
                let value = field.neg(field.elem(*coeff as i64));
                poly_add(field, &mut poly, expanded, value);
            }
        }
        AmbiguityKind::Inclusion => {
            let left = &lead_i[..offset];
            let tail = &lead_i[offset + lead_j.len()..];
            for (coeff, word) in &basis[i] {
                poly_add(field, &mut poly, word.clone(), field.elem(*coeff as i64));
            }
            for (coeff, word) in &basis[j] {
                let mut expanded = left.to_vec();
                expanded.extend_from_slice(word);
                expanded.extend_from_slice(tail);
                let value = field.neg(field.elem(*coeff as i64));
                poly_add(field, &mut poly, expanded, value);
            }
        }
    }
    poly
}

/// Lockstep comparison of the listed keys against the lazy canonical
/// enumeration. A listed key that differs from the expected one splits
/// three ways. A key that is not an ambiguity of the basis is extra. A
/// genuine key above the expected one skips it, so the list is out of
/// order. A genuine key below the expected one was already consumed in
/// lockstep, so it is a duplicate. Keys the list never reaches are
/// missing.
fn check_ambiguity_keys(certificate: &Certificate) -> Result<(), VerifyError> {
    let leads: Vec<&Vec<u32>> = certificate.basis.iter().map(|g| &g[0].1).collect();
    let mut generator = AmbiguityKeyGen::new(&leads);
    let mut next_expected = generator.next();
    for (index, entry) in certificate.ambiguities.iter().enumerate() {
        let found = (entry.i, entry.j, kind_tag(entry.kind), entry.offset);
        match next_expected {
            Some(expected) if expected == found => {
                next_expected = generator.next();
            }
            _ => {
                if !is_ambiguity(&leads, found) {
                    return Err(VerifyError::AmbiguityExtra {
                        i: entry.i,
                        j: entry.j,
                        kind: entry.kind,
                        offset: entry.offset,
                    });
                }
                match next_expected {
                    Some(expected) if found > expected => {
                        return Err(VerifyError::AmbiguityOrder {
                            index,
                            i: expected.0,
                            j: expected.1,
                            kind: tag_kind(expected.2),
                            offset: expected.3,
                        });
                    }
                    _ => {
                        return Err(VerifyError::AmbiguityDuplicate {
                            i: entry.i,
                            j: entry.j,
                            kind: entry.kind,
                            offset: entry.offset,
                        });
                    }
                }
            }
        }
    }
    if let Some((i, j, tag, offset)) = next_expected {
        return Err(VerifyError::AmbiguityMissing {
            i,
            j,
            kind: tag_kind(tag),
            offset,
        });
    }
    Ok(())
}

fn check_ambiguities(
    field: PrimeField,
    quiver: &Quiver,
    certificate: &Certificate,
) -> Result<(), VerifyError> {
    check_ambiguity_keys(certificate)?;
    for (index, entry) in certificate.ambiguities.iter().enumerate() {
        if !entry.trace.start.is_empty() {
            validate_relation_data(quiver, field.modulus(), &entry.trace.start).map_err(
                |(term, defect)| VerifyError::AmbiguityStart {
                    index,
                    term,
                    defect,
                },
            )?;
        }
        let start = poly_from_data(field, &entry.trace.start);
        let composed = composition(
            field,
            &certificate.basis,
            entry.i,
            entry.j,
            entry.kind,
            entry.offset,
        );
        if start != composed && start != poly_neg(field, &composed) {
            return Err(VerifyError::AmbiguityStartMismatch { index });
        }
        replay(
            field,
            quiver,
            &certificate.basis,
            TraceSite::Ambiguity { index },
            start,
            &entry.trace.steps,
        )?;
    }
    Ok(())
}

/// The normal-word automaton. State `v < starts` is the start state at
/// vertex `v`. Every other state is a proper nonempty prefix of a basis
/// leading word, and those states are sorted lexicographically. After
/// reading a word the automaton sits in the state of that word's longest
/// suffix that is still a proper prefix of a leading word.
struct Automaton {
    /// The word of each state; empty for the start states.
    words: Vec<Vec<u32>>,
    /// Outgoing edges `(arrow, target state)` in arrow order.
    edges: Vec<Vec<(u32, usize)>>,
    starts: usize,
}

fn build_automaton(quiver: &Quiver, leads: &[Vec<u32>]) -> Automaton {
    let starts = quiver.num_vertices() as usize;
    let mut prefixes = BTreeSet::new();
    for lead in leads {
        for len in 1..lead.len() {
            prefixes.insert(lead[..len].to_vec());
        }
    }
    let mut words: Vec<Vec<u32>> = vec![Vec::new(); starts];
    let mut vertices: Vec<u32> = (0..quiver.num_vertices()).collect();
    let mut index_of = BTreeMap::new();
    for prefix in &prefixes {
        index_of.insert(prefix.clone(), words.len());
        vertices.push(quiver.target(ArrowId(prefix[prefix.len() - 1])));
        words.push(prefix.clone());
    }
    let mut edges = vec![Vec::new(); words.len()];
    for state in 0..words.len() {
        for &arrow in quiver.arrows_from(vertices[state]) {
            let mut candidate = words[state].clone();
            candidate.push(arrow.0);
            if leads.iter().any(|lead| is_suffix(lead, &candidate)) {
                continue;
            }
            let mut next = quiver.target(arrow) as usize;
            for cut in 0..candidate.len() {
                if let Some(&found) = index_of.get(&candidate[cut..]) {
                    next = found;
                    break;
                }
            }
            edges[state].push((arrow.0, next));
        }
    }
    Automaton {
        words,
        edges,
        starts,
    }
}

/// The certificate's automaton section must equal the verifier's own
/// automaton state for state and transition for transition, in canonical
/// order: states are the vertices then the sorted prefixes; transitions
/// are sorted by state then arrow.
fn check_automaton(own: &Automaton, certificate: &Certificate) -> Result<(), VerifyError> {
    let found_states = &certificate.automaton.states;
    for position in 0..own.words.len().max(found_states.len()) {
        if own.words.get(position) != found_states.get(position) {
            return Err(VerifyError::AutomatonStates {
                position,
                expected: own.words.get(position).cloned(),
                found: found_states.get(position).cloned(),
            });
        }
    }
    let found = &certificate.automaton.transitions;
    let mut position = 0;
    for (state, row) in own.edges.iter().enumerate() {
        for &(arrow, next) in row {
            let expected = (state, arrow, next);
            if found.get(position) != Some(&expected) {
                return Err(VerifyError::AutomatonTransitions {
                    position,
                    expected: Some(expected),
                    found: found.get(position).copied(),
                });
            }
            position += 1;
        }
    }
    if let Some(&extra) = found.get(position) {
        return Err(VerifyError::AutomatonTransitions {
            position,
            expected: None,
            found: Some(extra),
        });
    }
    Ok(())
}

/// Whether the reachable part of the automaton has a cycle. Repeatedly
/// removing states with no outgoing edge leaves exactly the states that
/// start an infinite walk, so a survivor means a cycle.
fn automaton_has_cycle(automaton: &Automaton) -> bool {
    let n = automaton.edges.len();
    let mut reachable = vec![false; n];
    let mut queue: VecDeque<usize> = (0..automaton.starts).collect();
    reachable[..automaton.starts].fill(true);
    while let Some(state) = queue.pop_front() {
        for &(_, next) in &automaton.edges[state] {
            if !reachable[next] {
                reachable[next] = true;
                queue.push_back(next);
            }
        }
    }
    let mut out_degree = vec![0usize; n];
    let mut predecessors: Vec<Vec<usize>> = vec![Vec::new(); n];
    for state in 0..n {
        if !reachable[state] {
            continue;
        }
        out_degree[state] = automaton.edges[state].len();
        for &(_, next) in &automaton.edges[state] {
            predecessors[next].push(state);
        }
    }
    let mut removed = 0usize;
    let total = reachable.iter().filter(|&&r| r).count();
    let mut ready: VecDeque<usize> = (0..n)
        .filter(|&state| reachable[state] && out_degree[state] == 0)
        .collect();
    while let Some(state) = ready.pop_front() {
        removed += 1;
        for &before in &predecessors[state] {
            out_degree[before] -= 1;
            if out_degree[before] == 0 {
                ready.push_back(before);
            }
        }
    }
    removed < total
}

/// Reads `word` from `start` along automaton edges. Returns the reached
/// state, or the position of the first arrow without an edge.
fn replay_word(automaton: &Automaton, start: usize, word: &[u32]) -> Result<usize, usize> {
    let mut state = start;
    for (at, &arrow) in word.iter().enumerate() {
        match automaton.edges[state].iter().find(|&&(a, _)| a == arrow) {
            Some(&(_, next)) => state = next,
            None => return Err(at),
        }
    }
    Ok(state)
}

/// Full verification of an infinite-dimension witness: the cycle is
/// nonempty, `prefix·cycle·cycle` is a path free of every leading word,
/// the prefix reads to a state `s`, and one cycle from `s` returns to
/// exactly `s`. State return proves arbitrary repetition, so every
/// `prefix·cycle^k` is a normal word.
fn check_witness(
    quiver: &Quiver,
    automaton: &Automaton,
    leads: &[Vec<u32>],
    prefix: &[u32],
    cycle: &[u32],
) -> Result<CycleWitness, VerifyError> {
    let defect = |defect: WitnessDefect| VerifyError::InfiniteWitness { defect };
    if cycle.is_empty() {
        return Err(defect(WitnessDefect::EmptyCycle));
    }
    let mut word = prefix.to_vec();
    word.extend_from_slice(cycle);
    word.extend_from_slice(cycle);
    let path = PathWord::from_arrows(quiver, &ids(&word))
        .map_err(|error| defect(WitnessDefect::NotAPath(error)))?;
    for (lead, lead_word) in leads.iter().enumerate() {
        if let Some(position) = find_factor(&word, lead_word) {
            return Err(defect(WitnessDefect::ContainsLeadingWord {
                lead,
                position,
            }));
        }
    }
    let start = path.source() as usize;
    let reached = replay_word(automaton, start, prefix)
        .map_err(|at| defect(WitnessDefect::PrefixLeaves { at }))?;
    let back = replay_word(automaton, reached, cycle)
        .map_err(|at| defect(WitnessDefect::CycleLeaves { at }))?;
    if back != reached {
        return Err(defect(WitnessDefect::CycleDoesNotReturn { reached, back }));
    }
    Ok(CycleWitness {
        prefix: prefix.to_vec(),
        cycle: cycle.to_vec(),
    })
}

/// Longest walk length from each state. The caller guarantees the
/// automaton is acyclic. Every walk prefix is a walk, so a walk of length
/// `k` exists from a state exactly when `k <= longest[state]`.
fn longest_walks(automaton: &Automaton) -> Vec<usize> {
    let n = automaton.edges.len();
    let mut indegree = vec![0usize; n];
    for row in &automaton.edges {
        for &(_, next) in row {
            indegree[next] += 1;
        }
    }
    let mut order = Vec::with_capacity(n);
    let mut queue: VecDeque<usize> = (0..n).filter(|&state| indegree[state] == 0).collect();
    while let Some(state) = queue.pop_front() {
        order.push(state);
        for &(_, next) in &automaton.edges[state] {
            indegree[next] -= 1;
            if indegree[next] == 0 {
                queue.push_back(next);
            }
        }
    }
    debug_assert_eq!(order.len(), n, "the caller checked acyclicity");
    let mut longest = vec![0usize; n];
    for &state in order.iter().rev() {
        longest[state] = automaton.edges[state]
            .iter()
            .map(|&(_, next)| longest[next] + 1)
            .max()
            .unwrap_or(0);
    }
    longest
}

/// Yields the normal words in the fixed basis order without materializing
/// the list: trivial words in vertex order, then words by length, then by
/// source vertex, then in lexicographic arrow order. Each length comes
/// from a depth-first walk that `longest` prunes, so memory stays bounded
/// by the automaton size.
struct NormalWordGen<'a> {
    automaton: &'a Automaton,
    longest: Vec<usize>,
    max_length: usize,
    trivial_emitted: usize,
    length: usize,
    source: usize,
    stack: Vec<(usize, usize)>,
    word: Vec<u32>,
    dfs_active: bool,
}

impl<'a> NormalWordGen<'a> {
    fn new(automaton: &'a Automaton) -> NormalWordGen<'a> {
        let longest = longest_walks(automaton);
        let max_length = (0..automaton.starts).map(|s| longest[s]).max().unwrap_or(0);
        NormalWordGen {
            automaton,
            longest,
            max_length,
            trivial_emitted: 0,
            length: 1,
            source: 0,
            stack: Vec::new(),
            word: Vec::new(),
            dfs_active: false,
        }
    }

    fn next(&mut self) -> Option<Vec<u32>> {
        if self.trivial_emitted < self.automaton.starts {
            self.trivial_emitted += 1;
            return Some(Vec::new());
        }
        loop {
            if !self.dfs_active {
                if self.length > self.max_length {
                    return None;
                }
                if self.source >= self.automaton.starts {
                    self.source = 0;
                    self.length += 1;
                    continue;
                }
                let source = self.source;
                self.source += 1;
                if self.longest[source] < self.length {
                    continue;
                }
                self.stack.clear();
                self.stack.push((source, 0));
                self.word.clear();
                self.dfs_active = true;
            }
            while let Some(&(state, edge_at)) = self.stack.last() {
                if self.word.len() == self.length {
                    let emitted = self.word.clone();
                    self.stack.pop();
                    self.word.pop();
                    return Some(emitted);
                }
                let remaining = self.length - self.word.len();
                let row = &self.automaton.edges[state];
                let mut advanced = false;
                let mut edge_at = edge_at;
                while edge_at < row.len() {
                    let (arrow, next) = row[edge_at];
                    edge_at += 1;
                    if self.longest[next] + 1 >= remaining {
                        self.stack.last_mut().expect("stack is nonempty").1 = edge_at;
                        self.word.push(arrow);
                        self.stack.push((next, 0));
                        advanced = true;
                        break;
                    }
                }
                if !advanced {
                    self.stack.pop();
                    self.word.pop();
                }
            }
            self.dfs_active = false;
        }
    }
}

/// Lockstep comparison of the certificate's normal words against the lazy
/// enumeration. After the certificate list is exhausted the generator is
/// asked for at most one more word; its existence is the extra-word error.
fn check_normal_words_lockstep(
    automaton: &Automaton,
    found: &[Vec<u32>],
) -> Result<(), VerifyError> {
    let mut generator = NormalWordGen::new(automaton);
    for (position, found_word) in found.iter().enumerate() {
        match generator.next() {
            Some(expected) if expected == *found_word => {}
            expected => {
                return Err(VerifyError::NormalWords {
                    position,
                    expected,
                    found: Some(found_word.clone()),
                });
            }
        }
    }
    if let Some(extra) = generator.next() {
        return Err(VerifyError::NormalWords {
            position: found.len(),
            expected: Some(extra),
            found: None,
        });
    }
    Ok(())
}

/// Checks the automaton section, the finiteness claim, and the normal
/// words. A verified infinite claim returns
/// [`VerifyError::InfiniteDimensional`] carrying the certificate's own
/// witness.
fn check_finiteness_and_normal_words(
    quiver: &Quiver,
    certificate: &Certificate,
) -> Result<(), VerifyError> {
    let leads: Vec<Vec<u32>> = certificate.basis.iter().map(|g| g[0].1.clone()).collect();
    let automaton = build_automaton(quiver, &leads);
    check_automaton(&automaton, certificate)?;
    let cyclic = automaton_has_cycle(&automaton);
    match &certificate.finiteness {
        FinitenessData::Finite => {
            if cyclic {
                return Err(VerifyError::FinitenessClaim {
                    claimed_finite: true,
                });
            }
            check_normal_words_lockstep(&automaton, &certificate.normal_words)
        }
        FinitenessData::Infinite { prefix, cycle } => {
            if !cyclic {
                return Err(VerifyError::FinitenessClaim {
                    claimed_finite: false,
                });
            }
            let witness = check_witness(quiver, &automaton, &leads, prefix, cycle)?;
            if let Some(first) = certificate.normal_words.first() {
                return Err(VerifyError::NormalWords {
                    position: 0,
                    expected: None,
                    found: Some(first.clone()),
                });
            }
            Err(VerifyError::InfiniteDimensional { witness })
        }
    }
}

/// Parses certificate bytes and verifies the parsed certificate.
///
/// This is the entry point for untrusted bytes. Parsing is strict:
/// [`Certificate::from_json`] rejects an unknown field, a missing field,
/// a wrong JSON type, and trailing input, each as [`VerifyError::Parse`].
/// Everything after the parse is [`verify_certificate`], which is where
/// the mathematics lives.
pub fn verify(bytes: &str) -> Result<VerifiedCompletion, VerifyError> {
    verify_certificate(Certificate::from_json(bytes).map_err(VerifyError::Parse)?)
}

/// Verifies a parsed certificate and returns the trust token.
///
/// The checks read `certificate` and nothing else, so a caller that
/// already holds a typed certificate skips the serialization round trip
/// without weakening anything. Byte-level input goes through [`verify`],
/// which adds the strict parse.
///
/// Checks run in this order. The first failure returns its typed error:
///
/// 1. Schema, order, field.
/// 2. The automaton declares at least one state per vertex. This binds
///    the declared vertex count to serialized data before the quiver is
///    built, so allocation stays proportional to the certificate size.
/// 3. Quiver.
/// 4. Input relations: valid uniform descending relation data.
/// 5. Basis: the same relation checks, monic, fully reduced.
/// 6. Origin: each basis element expands from the input relations.
/// 7. Membership: each input relation reduces to zero by the basis.
/// 8. Ambiguities: the list equals the lazy re-enumeration in canonical
///    key order, and every composition reduces to zero.
/// 9. Automaton: the certificate's states and transitions equal the
///    verifier's own automaton in canonical order.
/// 10. Finiteness: the claim matches the verifier's own cycle decision.
///     A finite claim requires the normal words to match the lazy
///     enumeration in lockstep. An infinite claim requires a fully
///     verified witness and an empty normal-word list, and returns
///     [`VerifyError::InfiniteDimensional`] with the certificate's
///     witness.
pub fn verify_certificate(certificate: Certificate) -> Result<VerifiedCompletion, VerifyError> {
    if certificate.schema != CERT_SCHEMA {
        return Err(VerifyError::Schema {
            found: certificate.schema,
        });
    }
    if certificate.order != ORDER_ID {
        return Err(VerifyError::Order {
            found: certificate.order,
        });
    }
    let field = PrimeField::new(certificate.field).map_err(VerifyError::Field)?;
    if certificate.automaton.states.len() < certificate.quiver.vertices as usize {
        return Err(VerifyError::AutomatonStateCount {
            vertices: certificate.quiver.vertices,
            states: certificate.automaton.states.len(),
        });
    }
    let quiver = Quiver::new(certificate.quiver.vertices, &certificate.quiver.arrows)
        .map_err(VerifyError::Quiver)?;
    for (index, relation) in certificate.input_relations.iter().enumerate() {
        validate_relation_data(&quiver, field.modulus(), relation).map_err(|(term, defect)| {
            VerifyError::InputRelation {
                index,
                term,
                defect,
            }
        })?;
    }
    check_basis(&quiver, field.modulus(), &certificate.basis)?;
    check_origin(field, &quiver, &certificate)?;
    check_membership(field, &quiver, &certificate)?;
    check_ambiguities(field, &quiver, &certificate)?;
    check_finiteness_and_normal_words(&quiver, &certificate)?;
    let basis = certificate
        .basis
        .iter()
        .map(|element| {
            element
                .iter()
                .map(|(coeff, word)| {
                    let path = PathWord::from_arrows(&quiver, &ids(word))
                        .expect("basis words were validated");
                    (field.elem(*coeff as i64), path)
                })
                .collect()
        })
        .collect();
    let starts = quiver.num_vertices() as usize;
    let normal_words = certificate
        .normal_words
        .iter()
        .enumerate()
        .map(|(index, word)| {
            if index < starts {
                PathWord::trivial(&quiver, index as u32).expect("vertex index is in range")
            } else {
                PathWord::from_arrows(&quiver, &ids(word))
                    .expect("normal words matched the enumeration")
            }
        })
        .collect();
    Ok(VerifiedCompletion {
        certificate,
        quiver,
        field,
        basis,
        normal_words,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::certificate::{AmbiguityEntry, AutomatonData, OriginTerm, QuiverData, Trace};

    fn check(certificate: &Certificate) -> Result<VerifiedCompletion, VerifyError> {
        verify(&certificate.to_canonical_json())
    }

    fn empty_trace() -> Trace {
        Trace {
            start: vec![],
            steps: vec![],
        }
    }

    /// k[x]/(x^3) over F_5: one loop, one monomial relation. Both
    /// self-overlap compositions are exactly zero, so their traces are
    /// empty.
    fn x3_certificate() -> Certificate {
        Certificate {
            schema: CERT_SCHEMA.to_string(),
            field: 5,
            quiver: QuiverData {
                vertices: 1,
                arrows: vec![(0, 0)],
            },
            order: ORDER_ID.to_string(),
            input_relations: vec![vec![(1, vec![0, 0, 0])]],
            basis: vec![vec![(1, vec![0, 0, 0])]],
            origin: vec![vec![OriginTerm {
                coeff: 1,
                left: vec![],
                input_index: 0,
                right: vec![],
            }]],
            membership: vec![Trace {
                start: vec![(1, vec![0, 0, 0])],
                steps: vec![TraceStep {
                    word: vec![0, 0, 0],
                    basis_index: 0,
                    left: vec![],
                    right: vec![],
                    coeff: 1,
                }],
            }],
            ambiguities: vec![
                AmbiguityEntry {
                    i: 0,
                    j: 0,
                    kind: AmbiguityKind::Overlap,
                    offset: 1,
                    trace: empty_trace(),
                },
                AmbiguityEntry {
                    i: 0,
                    j: 0,
                    kind: AmbiguityKind::Overlap,
                    offset: 2,
                    trace: empty_trace(),
                },
            ],
            normal_words: vec![vec![], vec![0], vec![0, 0]],
            automaton: AutomatonData {
                states: vec![vec![], vec![0], vec![0, 0]],
                transitions: vec![(0, 0, 1), (1, 0, 2)],
            },
            finiteness: FinitenessData::Finite,
        }
    }

    /// The commutative square over F_5. Arrows: a = 0, b = 1, c = 2,
    /// d = 3. The input is ab - cd. The word cd = [2, 3] is the larger
    /// one, so the input stores as 4·[2, 3] + 1·[0, 1] and the monic
    /// basis element is 1·[2, 3] + 4·[0, 1]. The origin scales the input
    /// by 4. The membership trace eliminates [2, 3] with coefficient 4 in
    /// one step.
    fn square_certificate() -> Certificate {
        Certificate {
            schema: CERT_SCHEMA.to_string(),
            field: 5,
            quiver: QuiverData {
                vertices: 4,
                arrows: vec![(0, 1), (1, 3), (0, 2), (2, 3)],
            },
            order: ORDER_ID.to_string(),
            input_relations: vec![vec![(4, vec![2, 3]), (1, vec![0, 1])]],
            basis: vec![vec![(1, vec![2, 3]), (4, vec![0, 1])]],
            origin: vec![vec![OriginTerm {
                coeff: 4,
                left: vec![],
                input_index: 0,
                right: vec![],
            }]],
            membership: vec![Trace {
                start: vec![(4, vec![2, 3]), (1, vec![0, 1])],
                steps: vec![TraceStep {
                    word: vec![2, 3],
                    basis_index: 0,
                    left: vec![],
                    right: vec![],
                    coeff: 4,
                }],
            }],
            ambiguities: vec![],
            normal_words: vec![
                vec![],
                vec![],
                vec![],
                vec![],
                vec![0],
                vec![2],
                vec![1],
                vec![3],
                vec![0, 1],
            ],
            // States: the four vertices, then the prefix [2] of the leading
            // word cd. Reading c enters the prefix state; d from there
            // completes cd, so that transition is absent.
            automaton: AutomatonData {
                states: vec![vec![], vec![], vec![], vec![], vec![2]],
                transitions: vec![(0, 0, 1), (0, 2, 4), (1, 1, 3), (2, 3, 3)],
            },
            finiteness: FinitenessData::Finite,
        }
    }

    /// One loop, no relations: the normal-word language is infinite.
    fn loop_certificate() -> Certificate {
        Certificate {
            schema: CERT_SCHEMA.to_string(),
            field: 5,
            quiver: QuiverData {
                vertices: 1,
                arrows: vec![(0, 0)],
            },
            order: ORDER_ID.to_string(),
            input_relations: vec![],
            basis: vec![],
            origin: vec![],
            membership: vec![],
            ambiguities: vec![],
            normal_words: vec![],
            automaton: AutomatonData {
                states: vec![vec![]],
                transitions: vec![(0, 0, 0)],
            },
            finiteness: FinitenessData::Infinite {
                prefix: vec![],
                cycle: vec![0],
            },
        }
    }

    #[test]
    fn truncated_polynomial_certificate_accepted() {
        let verified = check(&x3_certificate()).unwrap();
        assert_eq!(verified.field().modulus(), 5);
        assert_eq!(verified.quiver().num_arrows(), 1);
        assert_eq!(verified.basis().len(), 1);
        assert_eq!(verified.basis()[0].len(), 1);
        let lengths: Vec<usize> = verified.normal_words().iter().map(PathWord::len).collect();
        assert_eq!(lengths, [0, 1, 2]);
        assert!(verified.normal_words()[0].is_trivial());
        assert_eq!(verified.certificate(), &x3_certificate());
    }

    #[test]
    fn commutative_square_certificate_accepted() {
        let verified = check(&square_certificate()).unwrap();
        assert_eq!(verified.quiver().num_vertices(), 4);
        assert_eq!(verified.normal_words().len(), 9);
        assert!(
            verified.normal_words()[..4]
                .iter()
                .all(PathWord::is_trivial)
        );
        assert_eq!(
            verified.normal_words()[8].arrows(),
            &[ArrowId(0), ArrowId(1)][..]
        );
        assert_eq!(verified.basis()[0][0].0, verified.field().one());
    }

    #[test]
    fn one_loop_without_relations_is_infinite_dimensional() {
        let certificate = loop_certificate();
        let witness = match check(&certificate) {
            Err(VerifyError::InfiniteDimensional { witness }) => witness,
            other => panic!("expected InfiniteDimensional, got {other:?}"),
        };
        assert!(!witness.cycle.is_empty());
        let mut word = witness.prefix.clone();
        word.extend_from_slice(&witness.cycle);
        word.extend_from_slice(&witness.cycle);
        let quiver = Quiver::new(1, &[(0, 0)]).unwrap();
        assert!(PathWord::from_arrows(&quiver, &ids(&word)).is_ok());
        for element in &certificate.basis {
            assert!(find_factor(&word, &element[0].1).is_none());
        }
    }

    #[test]
    fn unparsable_bytes_rejected() {
        assert!(matches!(
            verify("not a certificate"),
            Err(VerifyError::Parse(_))
        ));
    }

    /// The two entry points differ only in transport. The byte path adds the
    /// strict parse and nothing else, so it accepts and rejects exactly what
    /// the typed path does.
    #[test]
    fn the_typed_entry_and_the_byte_entry_agree() {
        for certificate in [x3_certificate(), square_certificate()] {
            let bytes = certificate.to_canonical_json();
            let typed = verify_certificate(certificate.clone()).expect("the certificate verifies");
            assert_eq!(verify(&bytes).unwrap().normal_words(), typed.normal_words());
            let mut tampered = certificate;
            tampered.order = "wrong".to_string();
            assert_eq!(
                verify(&tampered.to_canonical_json()).unwrap_err(),
                verify_certificate(tampered).unwrap_err()
            );
        }
    }

    #[test]
    fn wrong_schema_rejected() {
        let mut tampered = square_certificate();
        tampered.schema = "wrong".to_string();
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::Schema {
                found: "wrong".to_string(),
            }
        );
    }

    #[test]
    fn non_prime_field_rejected() {
        let mut tampered = square_certificate();
        tampered.field = 6;
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::Field(FieldError::NotPrime(6))
        );
    }

    #[test]
    fn arrow_endpoint_out_of_range_rejected() {
        let mut tampered = square_certificate();
        tampered.quiver.arrows[3] = (2, 7);
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::Quiver(QuiverError::EndpointOutOfRange {
                arrow: 3,
                vertex: 7,
                num_vertices: 4,
            })
        );
    }

    #[test]
    fn non_canonical_coefficient_rejected() {
        let mut tampered = square_certificate();
        tampered.input_relations[0][0].0 = 9;
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::InputRelation {
                index: 0,
                term: 0,
                defect: TermDefect::NonCanonicalCoefficient { coeff: 9 },
            }
        );
    }

    #[test]
    fn non_monic_basis_rejected() {
        let mut tampered = square_certificate();
        tampered.basis[0][0].0 = 2;
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::BasisNotMonic { index: 0, coeff: 2 }
        );
    }

    #[test]
    fn non_reduced_basis_rejected() {
        let mut tampered = x3_certificate();
        tampered.basis.push(vec![(1, vec![0, 0, 0, 0])]);
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::BasisNotReduced {
                lead: 0,
                element: 1,
                term: 0,
                position: 0,
            }
        );
    }

    #[test]
    fn origin_expanding_to_wrong_value_rejected() {
        let mut tampered = square_certificate();
        tampered.origin[0][0].coeff = 3;
        assert!(matches!(
            check(&tampered).unwrap_err(),
            VerifyError::OriginMismatch { element: 0, .. }
        ));
    }

    #[test]
    fn origin_with_non_composable_concatenation_rejected() {
        let mut tampered = square_certificate();
        tampered.origin[0][0].left = vec![1];
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::OriginNotComposable {
                element: 0,
                term: 0,
                error: QuiverError::NotComposable { position: 0 },
            }
        );
    }

    #[test]
    fn membership_trace_with_dropped_step_rejected() {
        let mut tampered = square_certificate();
        tampered.membership[0].steps.clear();
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::TraceRemainder {
                site: TraceSite::Membership { input: 0 },
                word: vec![2, 3],
            }
        );
    }

    /// Forged contexts cannot make a step ascend. The step word must
    /// equal `left · leading word · right`, and the sealed order is
    /// compatible with concatenation. A forged context instead names a
    /// word the polynomial does not contain.
    #[test]
    fn membership_step_with_forged_context_rejected() {
        let mut tampered = x3_certificate();
        tampered.membership[0].steps[0] = TraceStep {
            word: vec![0, 0, 0, 0],
            basis_index: 0,
            left: vec![0],
            right: vec![],
            coeff: 1,
        };
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::TraceStepAbsent {
                site: TraceSite::Membership { input: 0 },
                step: 0,
                word: vec![0, 0, 0, 0],
            }
        );
    }

    #[test]
    fn membership_step_naming_absent_word_rejected() {
        let mut tampered = square_certificate();
        let step = tampered.membership[0].steps[0].clone();
        tampered.membership[0].steps.push(step);
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::TraceStepAbsent {
                site: TraceSite::Membership { input: 0 },
                step: 1,
                word: vec![2, 3],
            }
        );
    }

    #[test]
    fn membership_step_with_non_eliminating_coefficient_rejected() {
        let mut tampered = square_certificate();
        tampered.membership[0].steps[0].coeff = 3;
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::TraceStepCoefficient {
                site: TraceSite::Membership { input: 0 },
                step: 0,
                expected: 4,
                found: 3,
            }
        );
    }

    #[test]
    fn missing_ambiguity_rejected() {
        let mut tampered = x3_certificate();
        tampered.ambiguities.remove(1);
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::AmbiguityMissing {
                i: 0,
                j: 0,
                kind: AmbiguityKind::Overlap,
                offset: 2,
            }
        );
    }

    #[test]
    fn extra_ambiguity_rejected() {
        let mut tampered = square_certificate();
        tampered.ambiguities.push(AmbiguityEntry {
            i: 0,
            j: 0,
            kind: AmbiguityKind::Overlap,
            offset: 1,
            trace: empty_trace(),
        });
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::AmbiguityExtra {
                i: 0,
                j: 0,
                kind: AmbiguityKind::Overlap,
                offset: 1,
            }
        );
    }

    #[test]
    fn duplicated_ambiguity_rejected() {
        let mut tampered = x3_certificate();
        let entry = tampered.ambiguities[0].clone();
        tampered.ambiguities.push(entry);
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::AmbiguityDuplicate {
                i: 0,
                j: 0,
                kind: AmbiguityKind::Overlap,
                offset: 1,
            }
        );
    }

    #[test]
    fn wrong_ambiguity_offset_rejected() {
        let mut tampered = x3_certificate();
        tampered.ambiguities[1].offset = 0;
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::AmbiguityExtra {
                i: 0,
                j: 0,
                kind: AmbiguityKind::Overlap,
                offset: 0,
            }
        );
    }

    #[test]
    fn normal_words_with_missing_word_rejected() {
        let mut tampered = x3_certificate();
        tampered.normal_words.remove(2);
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::NormalWords {
                position: 2,
                expected: Some(vec![0, 0]),
                found: None,
            }
        );
    }

    #[test]
    fn normal_words_with_extra_word_rejected() {
        let mut tampered = x3_certificate();
        tampered.normal_words.push(vec![0, 0, 0]);
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::NormalWords {
                position: 3,
                expected: None,
                found: Some(vec![0, 0, 0]),
            }
        );
    }

    #[test]
    fn normal_words_in_wrong_order_rejected() {
        let mut tampered = x3_certificate();
        tampered.normal_words.swap(1, 2);
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::NormalWords {
                position: 1,
                expected: Some(vec![0]),
                found: Some(vec![0, 0]),
            }
        );
    }

    #[test]
    fn ambiguities_out_of_order_rejected() {
        let mut tampered = x3_certificate();
        tampered.ambiguities.swap(0, 1);
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::AmbiguityOrder {
                index: 0,
                i: 0,
                j: 0,
                kind: AmbiguityKind::Overlap,
                offset: 1,
            }
        );
    }

    #[test]
    fn automaton_false_edge_rejected() {
        let mut tampered = square_certificate();
        tampered.automaton.transitions[3] = (4, 3, 3);
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::AutomatonTransitions {
                position: 3,
                expected: Some((2, 3, 3)),
                found: Some((4, 3, 3)),
            }
        );
    }

    #[test]
    fn automaton_missing_state_rejected() {
        let mut tampered = x3_certificate();
        tampered.automaton.states.pop();
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::AutomatonStates {
                position: 2,
                expected: Some(vec![0, 0]),
                found: None,
            }
        );
    }

    #[test]
    fn automaton_reordered_states_rejected() {
        let mut tampered = x3_certificate();
        tampered.automaton.states.swap(1, 2);
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::AutomatonStates {
                position: 1,
                expected: Some(vec![0]),
                found: Some(vec![0, 0]),
            }
        );
    }

    #[test]
    fn automaton_duplicate_transition_rejected() {
        let mut tampered = x3_certificate();
        tampered.automaton.transitions.insert(1, (0, 0, 1));
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::AutomatonTransitions {
                position: 1,
                expected: Some((1, 0, 2)),
                found: Some((0, 0, 1)),
            }
        );
    }

    #[test]
    fn automaton_out_of_order_transitions_rejected() {
        let mut tampered = x3_certificate();
        tampered.automaton.transitions.swap(0, 1);
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::AutomatonTransitions {
                position: 0,
                expected: Some((0, 0, 1)),
                found: Some((1, 0, 2)),
            }
        );
    }

    #[test]
    fn false_finite_claim_on_an_infinite_language_rejected() {
        let mut tampered = loop_certificate();
        tampered.finiteness = FinitenessData::Finite;
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::FinitenessClaim {
                claimed_finite: true,
            }
        );
    }

    #[test]
    fn false_infinite_claim_on_a_finite_language_rejected() {
        let mut tampered = x3_certificate();
        tampered.normal_words.clear();
        tampered.finiteness = FinitenessData::Infinite {
            prefix: vec![],
            cycle: vec![0],
        };
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::FinitenessClaim {
                claimed_finite: false,
            }
        );
    }

    /// Two loops x = 0 and y = 1 over F_2 with the single relation y².
    /// The normal-word language is infinite; the automaton has the vertex
    /// state and the prefix state [1], and the witness loops on x.
    fn two_loop_certificate() -> Certificate {
        Certificate {
            schema: CERT_SCHEMA.to_string(),
            field: 2,
            quiver: QuiverData {
                vertices: 1,
                arrows: vec![(0, 0), (0, 0)],
            },
            order: ORDER_ID.to_string(),
            input_relations: vec![vec![(1, vec![1, 1])]],
            basis: vec![vec![(1, vec![1, 1])]],
            origin: vec![vec![OriginTerm {
                coeff: 1,
                left: vec![],
                input_index: 0,
                right: vec![],
            }]],
            membership: vec![Trace {
                start: vec![(1, vec![1, 1])],
                steps: vec![TraceStep {
                    word: vec![1, 1],
                    basis_index: 0,
                    left: vec![],
                    right: vec![],
                    coeff: 1,
                }],
            }],
            ambiguities: vec![AmbiguityEntry {
                i: 0,
                j: 0,
                kind: AmbiguityKind::Overlap,
                offset: 1,
                trace: empty_trace(),
            }],
            normal_words: vec![],
            automaton: AutomatonData {
                states: vec![vec![], vec![1]],
                transitions: vec![(0, 0, 0), (0, 1, 1), (1, 0, 0)],
            },
            finiteness: FinitenessData::Infinite {
                prefix: vec![],
                cycle: vec![0],
            },
        }
    }

    #[test]
    fn honest_infinite_certificate_yields_its_own_witness() {
        assert_eq!(
            check(&two_loop_certificate()).unwrap_err(),
            VerifyError::InfiniteDimensional {
                witness: CycleWitness {
                    prefix: vec![],
                    cycle: vec![0],
                },
            }
        );
    }

    #[test]
    fn forged_witness_with_bad_prefix_rejected() {
        let mut tampered = two_loop_certificate();
        tampered.finiteness = FinitenessData::Infinite {
            prefix: vec![7],
            cycle: vec![0],
        };
        assert!(matches!(
            check(&tampered).unwrap_err(),
            VerifyError::InfiniteWitness {
                defect: WitnessDefect::NotAPath(_),
            }
        ));
    }

    #[test]
    fn forged_witness_with_bad_cycle_rejected() {
        let mut tampered = two_loop_certificate();
        tampered.finiteness = FinitenessData::Infinite {
            prefix: vec![],
            cycle: vec![1],
        };
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::InfiniteWitness {
                defect: WitnessDefect::ContainsLeadingWord {
                    lead: 0,
                    position: 0,
                },
            }
        );
    }

    #[test]
    fn forged_witness_with_empty_cycle_rejected() {
        let mut tampered = two_loop_certificate();
        tampered.finiteness = FinitenessData::Infinite {
            prefix: vec![0],
            cycle: vec![],
        };
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::InfiniteWitness {
                defect: WitnessDefect::EmptyCycle,
            }
        );
    }

    #[test]
    fn forged_witness_with_non_returning_cycle_rejected() {
        let mut tampered = two_loop_certificate();
        tampered.finiteness = FinitenessData::Infinite {
            prefix: vec![1],
            cycle: vec![0],
        };
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::InfiniteWitness {
                defect: WitnessDefect::CycleDoesNotReturn {
                    reached: 1,
                    back: 0,
                },
            }
        );
    }

    #[test]
    fn infinite_claim_with_nonempty_normal_words_rejected() {
        let mut tampered = two_loop_certificate();
        tampered.normal_words.push(vec![]);
        assert_eq!(
            check(&tampered).unwrap_err(),
            VerifyError::NormalWords {
                position: 0,
                expected: None,
                found: Some(vec![]),
            }
        );
    }

    #[test]
    fn huge_declared_vertex_count_rejected_before_allocation() {
        let started = std::time::Instant::now();
        let certificate = Certificate {
            schema: CERT_SCHEMA.to_string(),
            field: 5,
            quiver: QuiverData {
                vertices: 4_294_967_295,
                arrows: vec![],
            },
            order: ORDER_ID.to_string(),
            input_relations: vec![],
            basis: vec![],
            origin: vec![],
            membership: vec![],
            ambiguities: vec![],
            normal_words: vec![],
            automaton: AutomatonData {
                states: vec![],
                transitions: vec![],
            },
            finiteness: FinitenessData::Finite,
        };
        assert_eq!(
            check(&certificate).unwrap_err(),
            VerifyError::AutomatonStateCount {
                vertices: 4_294_967_295,
                states: 0,
            }
        );
        assert!(
            started.elapsed() < std::time::Duration::from_secs(5),
            "the rejection must not allocate per declared vertex"
        );
    }

    /// Forty layers of two parallel arrows and no relations give a finite
    /// language with more than 2^40 words. The lockstep comparison must
    /// reject the empty normal-word list at position 0 without
    /// enumerating the language.
    #[test]
    fn huge_finite_language_certificate_rejected_fast() {
        let layers = 40u32;
        let mut arrows = Vec::new();
        let mut transitions = Vec::new();
        for v in 0..layers {
            arrows.push((v, v + 1));
            arrows.push((v, v + 1));
            transitions.push((v as usize, 2 * v, (v + 1) as usize));
            transitions.push((v as usize, 2 * v + 1, (v + 1) as usize));
        }
        let certificate = Certificate {
            schema: CERT_SCHEMA.to_string(),
            field: 2,
            quiver: QuiverData {
                vertices: layers + 1,
                arrows,
            },
            order: ORDER_ID.to_string(),
            input_relations: vec![],
            basis: vec![],
            origin: vec![],
            membership: vec![],
            ambiguities: vec![],
            normal_words: vec![],
            automaton: AutomatonData {
                states: vec![vec![]; (layers + 1) as usize],
                transitions,
            },
            finiteness: FinitenessData::Finite,
        };
        let started = std::time::Instant::now();
        assert_eq!(
            check(&certificate).unwrap_err(),
            VerifyError::NormalWords {
                position: 0,
                expected: Some(vec![]),
                found: None,
            }
        );
        assert!(
            started.elapsed() < std::time::Duration::from_secs(5),
            "the lockstep comparison must fail fast"
        );
    }

    /// The zero-vertex quiver is legal, its language is finite, and the
    /// empty normal-word list is the honest enumeration.
    #[test]
    fn zero_vertex_certificate_accepted() {
        let certificate = Certificate {
            schema: CERT_SCHEMA.to_string(),
            field: 5,
            quiver: QuiverData {
                vertices: 0,
                arrows: vec![],
            },
            order: ORDER_ID.to_string(),
            input_relations: vec![],
            basis: vec![],
            origin: vec![],
            membership: vec![],
            ambiguities: vec![],
            normal_words: vec![],
            automaton: AutomatonData {
                states: vec![],
                transitions: vec![],
            },
            finiteness: FinitenessData::Finite,
        };
        let verified = check(&certificate).unwrap();
        assert_eq!(verified.normal_words().len(), 0);
    }
}

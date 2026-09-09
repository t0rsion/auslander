use crate::certificate::{AmbiguityKind, CERT_SCHEMA, CertParseError, Certificate};
use crate::field::{FieldError, Fp, PrimeField};
use crate::order::ORDER_ID;
use crate::quiver::{PathWord, Quiver, QuiverError};

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

display_error! { TraceSite {
    Self::Membership { input } => "membership trace {input}";
    Self::Ambiguity { index } => "ambiguity trace {index}";
} }

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

display_error! { TermDefect {
    Self::Empty => "relation has no terms";
    Self::ZeroCoefficient => "coefficient is zero";
    Self::NonCanonicalCoefficient { coeff } => "coefficient {coeff} is not in 0..p";
    Self::WordTooShort { len } => "word has length {len}, below 2";
    Self::InvalidWord(error) => "word is not a path: {error}";
    Self::MixedSource => "word starts at a different vertex than term 0";
    Self::MixedTarget => "word ends at a different vertex than term 0";
    Self::NotDescending => "word is not strictly below the word before it";
} }

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

display_error! { WitnessDefect {
    Self::EmptyCycle => "the cycle word is empty";
    Self::NotAPath(error) => "prefix and two cycles do not spell a path: {error}";
    Self::ContainsLeadingWord { lead, position } => "the leading word of basis element {lead} occurs at position {position}";
    Self::PrefixLeaves { at } => "the prefix leaves the automaton at position {at}";
    Self::CycleLeaves { at } => "the cycle leaves the automaton at position {at}";
    Self::CycleDoesNotReturn { reached, back } => "the cycle starts at state {reached} but ends at state {back}";
} }

macro_rules! verify_error_enum {
    (
        $(#[$enum_meta:meta])*
        $name:ident {
            $(
                $(#[$meta:meta])*
                $variant:ident $(($inner:ty))?
                $( { $($field:ident : $ty:ty),* $(,)? } )? ;
            )*
        }
    ) => {
        $(#[$enum_meta])*
        #[derive(Clone, Debug, PartialEq, Eq)]
        pub enum $name {
            $(
                $(#[$meta])*
                $variant $(($inner))? $( { $($field : $ty),* } )?,
            )*
        }
    };
}

verify_error_enum! {
    /// A rejected certificate. Each variant names one failed check and carries
    /// the indices needed to locate the defect.
    VerifyError {
        /// The bytes do not parse as a certificate.
        Parse(CertParseError);
        /// The schema string is not [`CERT_SCHEMA`].
        Schema { found: String };
        /// The order string is not [`ORDER_ID`].
        Order { found: String };
        /// The field modulus is rejected.
        Field(FieldError);
        /// The quiver data is rejected.
        Quiver(QuiverError);
        /// `input_relations[index]` has a defect at term `term`.
        InputRelation { index: usize, term: usize, defect: TermDefect };
        /// `basis[index]` has a defect at term `term`.
        BasisRelation { index: usize, term: usize, defect: TermDefect };
        /// `basis[index]` has leading coefficient `coeff`, not 1.
        BasisNotMonic { index: usize, coeff: u64 };
        /// The leading word of `basis[lead]` occurs in word `term` of
        /// `basis[element]` at `position`.
        BasisNotReduced { lead: usize, element: usize, term: usize, position: usize };
        /// `origin` does not have one entry per basis element.
        OriginCount { basis: usize, origin: usize };
        /// An origin term of `basis[element]` has a zero or non-canonical
        /// coefficient.
        OriginCoefficient { element: usize, term: usize, coeff: u64 };
        /// An origin term of `basis[element]` names an input index out of range.
        OriginInputIndex { element: usize, term: usize, input_index: usize, inputs: usize };
        /// An origin term of `basis[element]` expands to a non-path word.
        OriginNotComposable { element: usize, term: usize, error: QuiverError };
        /// The origin of `basis[element]` does not expand to it; `word` is a
        /// word where the two sides differ.
        OriginMismatch { element: usize, word: Vec<u32> };
        /// `membership` does not have one trace per input relation.
        MembershipCount { inputs: usize, traces: usize };
        /// `membership[input].start` is not `input_relations[input]`.
        MembershipStart { input: usize };
        /// A trace step names a basis index out of range.
        TraceStepBasisIndex { site: TraceSite, step: usize, basis_index: usize, basis: usize };
        /// A trace step's word is not `left · leading word · right`.
        TraceStepWord { site: TraceSite, step: usize };
        /// A trace step's word or one of its expansions is not a path.
        TraceStepPath { site: TraceSite, step: usize, error: QuiverError };
        /// A trace step names a word the current polynomial does not contain.
        TraceStepAbsent { site: TraceSite, step: usize, word: Vec<u32> };
        /// A trace step's coefficient does not eliminate the named word.
        TraceStepCoefficient { site: TraceSite, step: usize, expected: u64, found: u64 };
        /// A trace step expands to a word that is not strictly below the
        /// eliminated word.
        TraceStepAscending { site: TraceSite, step: usize, word: Vec<u32> };
        /// The polynomial is not zero after the last step; `word` is the
        /// largest remaining word.
        TraceRemainder { site: TraceSite, word: Vec<u32> };
        /// The basis has this ambiguity but the certificate does not list it.
        AmbiguityMissing { i: usize, j: usize, kind: AmbiguityKind, offset: usize };
        /// The certificate lists an entry that is not an ambiguity of the basis.
        AmbiguityExtra { i: usize, j: usize, kind: AmbiguityKind, offset: usize };
        /// The certificate lists the same ambiguity twice.
        AmbiguityDuplicate { i: usize, j: usize, kind: AmbiguityKind, offset: usize };
        /// `ambiguities[index]` skips this ambiguity: the list must follow
        /// the canonical `(i, j, kind, offset)` order, overlap before
        /// inclusion.
        AmbiguityOrder { index: usize, i: usize, j: usize, kind: AmbiguityKind, offset: usize };
        /// `ambiguities[index].trace.start` has a defect at term `term`.
        AmbiguityStart { index: usize, term: usize, defect: TermDefect };
        /// `ambiguities[index].trace.start` is not the composition or its
        /// negation.
        AmbiguityStartMismatch { index: usize };
        /// The automaton declares fewer states than the quiver has vertices.
        /// Checked before the quiver is built, so a huge declared vertex
        /// count cannot force a large allocation.
        AutomatonStateCount { vertices: u32, states: usize };
        /// The automaton state lists differ first at `position`. `None` means
        /// the list ends there.
        AutomatonStates { position: usize, expected: Option<Vec<u32>>, found: Option<Vec<u32>> };
        /// The automaton transition lists differ first at `position`. `None`
        /// means the list ends there.
        AutomatonTransitions {
            position: usize,
            expected: Option<(usize, u32, usize)>,
            found: Option<(usize, u32, usize)>,
        };
        /// The finiteness claim contradicts the verifier's own cycle
        /// decision.
        FinitenessClaim { claimed_finite: bool };
        /// The witness of an infinite claim fails a check.
        InfiniteWitness { defect: WitnessDefect };
        /// The normal-word lists differ first at `position`. `None` means the
        /// list ends there.
        NormalWords {
            position: usize,
            expected: Option<Vec<u32>>,
            found: Option<Vec<u32>>,
        };
        /// The set of normal words is infinite. The witness is the
        /// certificate's own, fully verified.
        InfiniteDimensional { witness: CycleWitness };
    }
}

display_error! { VerifyError {
    Self::Parse(error) => "certificate rejected: {error}";
    Self::Schema { found } => "schema is {found:?}, expected {CERT_SCHEMA:?}";
    Self::Order { found } => "order is {found:?}, expected {ORDER_ID:?}";
    Self::Field(error) => "field rejected: {error}";
    Self::Quiver(error) => "quiver rejected: {error}";
    Self::InputRelation { index, term, defect } => "input relation {index}, term {term}: {defect}";
    Self::BasisRelation { index, term, defect } => "basis element {index}, term {term}: {defect}";
    Self::BasisNotMonic { index, coeff } => "basis element {index} has leading coefficient {coeff}, not 1";
    Self::BasisNotReduced { lead, element, term, position } => "leading word of basis element {lead} occurs in word {term} of basis element {element} at position {position}";
    Self::OriginCount { basis, origin } => "origin has {origin} entries for {basis} basis elements";
    Self::OriginCoefficient { element, term, coeff } => "origin of basis element {element}, term {term}: coefficient {coeff} is zero or not in 0..p";
    Self::OriginInputIndex { element, term, input_index, inputs } => "origin of basis element {element}, term {term}: input index {input_index} outside 0..{inputs}";
    Self::OriginNotComposable { element, term, error } => "origin of basis element {element}, term {term}: expansion is not a path: {error}";
    Self::OriginMismatch { element, word } => "origin of basis element {element} does not expand to it; the sides differ at word {word:?}";
    Self::MembershipCount { inputs, traces } => "membership has {traces} traces for {inputs} inputs";
    Self::MembershipStart { input } => "membership trace {input} does not start at input relation {input}";
    Self::TraceStepBasisIndex { site, step, basis_index, basis } => "{site}, step {step}: basis index {basis_index} outside 0..{basis}";
    Self::TraceStepWord { site, step } => "{site}, step {step}: word is not left, leading word, right concatenated";
    Self::TraceStepPath { site, step, error } => "{site}, step {step}: not a path: {error}";
    Self::TraceStepAbsent { site, step, word } => "{site}, step {step}: word {word:?} has coefficient zero";
    Self::TraceStepCoefficient { site, step, expected, found } => "{site}, step {step}: the word has coefficient {expected}, the step says {found}";
    Self::TraceStepAscending { site, step, word } => "{site}, step {step}: expanded word {word:?} is not strictly below the eliminated word";
    Self::TraceRemainder { site, word } => "{site}: not zero after the last step; largest remaining word {word:?}";
    Self::AmbiguityMissing { i, j, kind, offset } => "ambiguity ({i}, {j}, {}, {offset}) is missing", kind.as_str();
    Self::AmbiguityExtra { i, j, kind, offset } => "({i}, {j}, {}, {offset}) is not an ambiguity of the basis", kind.as_str();
    Self::AmbiguityDuplicate { i, j, kind, offset } => "ambiguity ({i}, {j}, {}, {offset}) is listed twice", kind.as_str();
    Self::AmbiguityOrder { index, i, j, kind, offset } => "ambiguity entry {index} skips ({i}, {j}, {}, {offset}); the list must follow the canonical key order", kind.as_str();
    Self::AmbiguityStart { index, term, defect } => "ambiguity {index}, start term {term}: {defect}";
    Self::AmbiguityStartMismatch { index } => "ambiguity {index}: start is not the composition or its negation";
    Self::AutomatonStateCount { vertices, states } => "the automaton has {states} states for {vertices} vertices";
    Self::AutomatonStates { position, expected, found } => "automaton states differ at position {position}: expected {expected:?}, found {found:?}";
    Self::AutomatonTransitions { position, expected, found } => "automaton transitions differ at position {position}: expected {expected:?}, found {found:?}";
    Self::FinitenessClaim { claimed_finite: true } => "the certificate claims a finite language but the automaton has a cycle";
    Self::FinitenessClaim { claimed_finite: false } => "the certificate claims an infinite language but the automaton is acyclic";
    Self::InfiniteWitness { defect } => "the infinite-dimension witness is rejected: {defect}";
    Self::NormalWords { position, expected, found } => "normal words differ at position {position}: expected {expected:?}, found {found:?}";
    Self::InfiniteDimensional { witness } => "the quotient is infinite dimensional: prefix {:?}, cycle {:?}", witness.prefix, witness.cycle;
} }

error_source!(VerifyError {
    Self::Parse(error) => Some(error),
    Self::Field(error) => Some(error),
    Self::Quiver(error) => Some(error),
    _ => None,
});

/// A certificate that passed every check.
///
/// Only [`super::verify`] and [`super::verify_certificate`] build one, and
/// the fields stay private, so holding the value is proof the certificate
/// verified.
/// Every constructor of [`crate::algebra::Algebra`] consumes one, so
/// verification is the only route to an algebra.
#[derive(Clone, Debug)]
pub struct VerifiedCompletion {
    pub(super) certificate: Certificate,
    pub(super) quiver: Quiver,
    pub(super) field: PrimeField,
    pub(super) basis: Vec<Vec<(Fp, PathWord)>>,
    pub(super) normal_words: Vec<PathWord>,
}

impl VerifiedCompletion {
    accessor_methods! {
        /// The verified certificate.
        pub certificate() -> &Certificate = |this| &this.certificate;
        /// The quiver rebuilt from the certificate.
        pub quiver() -> &Quiver = |this| &this.quiver;
        /// The prime field of the certificate.
        pub field() -> PrimeField = |this| this.field;
        /// The reduced Groebner basis, each element as descending
        /// `(coefficient, word)` terms.
        pub basis() -> &[Vec<(Fp, PathWord)>] = |this| &this.basis;
        /// The normal words in the fixed basis order: trivial paths by vertex,
        /// then by length, source, and lexicographic arrow word.
        pub normal_words() -> &[PathWord] = |this| &this.normal_words;
    }
}

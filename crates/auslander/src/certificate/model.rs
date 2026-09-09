/// A relation as certificate data: terms `(coefficient, word)` with the
/// coefficient as its canonical representative in `0..p` and the word as
/// arrow indices. Terms descend strictly under the sealed order.
pub type RelationData = Vec<(u64, Vec<u32>)>;

/// The quiver as certificate data: vertex count and `(source, target)` arrow
/// pairs in [`crate::quiver::ArrowId`] order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuiverData {
    pub vertices: u32,
    pub arrows: Vec<(u32, u32)>,
}

/// One term of a provenance expression: `coeff · left · r_{input_index} · right`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OriginTerm {
    pub coeff: u64,
    pub left: Vec<u32>,
    pub input_index: usize,
    pub right: Vec<u32>,
}

/// One reduction step: the element under reduction contains `word` as
/// `left · leading(basis[basis_index]) · right`, and the step subtracts
/// `coeff · left · basis[basis_index] · right`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraceStep {
    pub word: Vec<u32>,
    pub basis_index: usize,
    pub left: Vec<u32>,
    pub right: Vec<u32>,
    pub coeff: u64,
}

/// A reduction trace: the start element and the steps that take it to zero.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Trace {
    pub start: RelationData,
    pub steps: Vec<TraceStep>,
}

/// How two leading words form an ambiguity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AmbiguityKind {
    /// A proper suffix of `leading(basis[i])` equals a proper prefix of
    /// `leading(basis[j])`.
    Overlap,
    /// `leading(basis[j])` is a proper factor of `leading(basis[i])`.
    Inclusion,
}

impl AmbiguityKind {
    /// The identifier stored in JSON: `"overlap"` or `"inclusion"`.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Overlap => "overlap",
            Self::Inclusion => "inclusion",
        }
    }
}

/// One ambiguity of the basis leading words, keyed `(i, j, kind, offset)`,
/// with a reduction trace of its composition ending at zero.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AmbiguityEntry {
    pub i: usize,
    pub j: usize,
    pub kind: AmbiguityKind,
    pub offset: usize,
    pub trace: Trace,
}

/// The normal-word automaton as certificate data. `states[v]` is the empty
/// word for each vertex `v` in vertex order; the remaining states are the
/// proper nonempty prefixes of the basis leading words, sorted
/// lexicographically, each stored as its arrow-id word. `transitions` holds
/// sparse `(state, arrow, next state)` triples sorted by state then arrow;
/// a missing pair is noncomposable or completes a leading word.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AutomatonData {
    pub states: Vec<Vec<u32>>,
    pub transitions: Vec<(usize, u32, usize)>,
}

/// The finiteness claim of the certificate. `Infinite` carries a witness:
/// `prefix` reads from the start state of its source vertex to a state on a
/// cycle, and `cycle` returns to exactly that state, so every
/// `prefix·cycle^k` is a normal word.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FinitenessData {
    Finite,
    Infinite { prefix: Vec<u32>, cycle: Vec<u32> },
}

/// A completion certificate. The engine emits it. The verifier checks it
/// from bytes. See the certified bound quiver design, sections 4 and 5.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Certificate {
    pub schema: String,
    pub field: u64,
    pub quiver: QuiverData,
    pub order: String,
    pub input_relations: Vec<RelationData>,
    pub basis: Vec<RelationData>,
    /// `origin[j]` expands to `basis[j]` as a two-sided combination of the
    /// input relations.
    pub origin: Vec<Vec<OriginTerm>>,
    /// `membership[i]` reduces `input_relations[i]` to zero by `basis`.
    pub membership: Vec<Trace>,
    pub ambiguities: Vec<AmbiguityEntry>,
    /// The claimed normal-word basis of the quotient, in the fixed basis
    /// order of the design, section 6. Empty when `finiteness` claims an
    /// infinite quotient.
    pub normal_words: Vec<Vec<u32>>,
    /// The normal-word automaton over the basis leading words.
    pub automaton: AutomatonData,
    /// Whether the normal-word language is finite, with a cycle witness
    /// when it is not.
    pub finiteness: FinitenessData,
}

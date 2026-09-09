#[derive(Clone, Debug, PartialEq)]
enum DimOutcome {
    Finite(usize),
    AtLeast(usize),
}

#[derive(Clone, Debug, PartialEq)]
enum TauOutcome {
    Projective,
    Dimvec(Vec<usize>),
}

/// How a designated module is named. A module is named by kind and index and
/// never looked up by its dimension vector: on `kronecker-2` the dimension
/// vector `[1, 1]` belongs to `field + 1` pairwise non-isomorphic modules.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ModuleKind {
    Simple,
    Projective,
    Injective,
}

impl ModuleKind {
    fn name(self) -> &'static str {
        match self {
            ModuleKind::Simple => "simple",
            ModuleKind::Projective => "projective",
            ModuleKind::Injective => "injective",
        }
    }

    fn label(self) -> char {
        match self {
            ModuleKind::Simple => 'S',
            ModuleKind::Projective => 'P',
            ModuleKind::Injective => 'I',
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ModuleRef {
    kind: ModuleKind,
    index: usize,
}

impl ModuleRef {
    fn label(&self) -> String {
        format!("{}_{}", self.kind.label(), self.index)
    }
}

/// The designated module list of a quiver with `n` vertices: every simple,
/// then every indecomposable projective, then every indecomposable
/// injective, in vertex order. A module that is both simple and projective
/// appears once per kind and carries the same results in both entries.
fn designated_refs(n: usize) -> Vec<ModuleRef> {
    [
        ModuleKind::Simple,
        ModuleKind::Projective,
        ModuleKind::Injective,
    ]
    .into_iter()
    .flat_map(|kind| (0..n).map(move |index| ModuleRef { kind, index }))
    .collect()
}

/// The almost-split sequence ending at one designated module, or
/// [`ArSequence::Projective`].
#[derive(Clone, Debug, PartialEq)]
enum ArSequence {
    Projective,
    Sequence {
        tau: Vec<usize>,
        middle_dimvec: Vec<usize>,
        middle: Vec<(Vec<usize>, usize)>,
        num_middle_summands: usize,
    },
}

#[derive(Clone, Debug, PartialEq)]
struct ArEntry {
    module: ModuleRef,
    sequence: ArSequence,
}

/// One direction of the irreducible morphisms at a designated module.
/// `present` is false exactly where there is no such morphism: nothing is
/// irreducible into a projective with zero radical, and nothing is
/// irreducible out of an injective that equals its socle.
#[derive(Clone, Debug, PartialEq)]
struct IrrSide {
    present: bool,
    total: usize,
    endpoints: Vec<(Vec<usize>, usize)>,
}

#[derive(Clone, Debug, PartialEq)]
struct IrrEntry {
    module: ModuleRef,
    into: IrrSide,
    out_of: IrrSide,
}

/// The Yoneda algebra of the sum of all simples, degree by degree.
/// `min_generators` is the elementwise difference `dims - product_rank`.
#[derive(Clone, Debug, PartialEq)]
struct ExtAlgebra {
    dims: Vec<usize>,
    min_generators: Vec<usize>,
    product_rank: Vec<usize>,
}

/// The rank of the image of
/// `Ext^1(S_i, S_j) x Ext^1(S_j, S_k) -> Ext^2(S_i, S_k)`, with the three
/// factor dimensions that `ext` already stores.
#[derive(Clone, Debug, PartialEq)]
struct YonedaProduct {
    i: usize,
    j: usize,
    k: usize,
    dim_ext1_ij: usize,
    dim_ext1_jk: usize,
    dim_ext2_ik: usize,
    yoneda_map_rank: usize,
}

#[derive(Clone, Debug, PartialEq)]
enum TauPeriod {
    Period(usize),
    NoneUpTo(usize),
}

/// Whether GAP's AR-quiver walk closed. A closed walk certifies the
/// indecomposable list, because a finite AR component over a connected
/// algebra forces representation-finiteness. `NotClosed` records the budget it
/// spent, which is no claim about the algebra.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Closure {
    Closed { count: usize },
    NotClosed { cap: usize },
}

/// GAP's own cross-check of the walk against `AllIndecModulesOfLengthAtMost`.
/// It has no library counterpart, so the harness validates it and never
/// compares it.
#[derive(Clone, Debug, PartialEq, Eq)]
enum BruteAgreement {
    Available { max_length: usize, agrees: bool },
    Unavailable { reason: String },
}

/// A support tau-tilting pair as the schema stores it: the module summand
/// dimension vectors, sorted, and the projective support as a sorted 0-based
/// vertex subset.
///
/// This is a WEAK identity. Repetitions in `module_dimvecs` are preserved and
/// are never multiplicity: `cyclic-nakayama-3-3-3` has three pairwise
/// non-isomorphic projectives of dimension vector `[1, 1, 1]`. Two distinct
/// pairs can share one record, so comparisons run over multisets of records
/// and never key a lookup on one.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct PairRecord {
    module_dimvecs: Vec<Vec<usize>>,
    projective_support: Vec<u32>,
}

impl PairRecord {
    fn summand_count(&self) -> usize {
        self.module_dimvecs.len()
    }
}

/// The invariants of `MinimalLeftApproximation(X, M/X)` at one (pair, module
/// summand) slot. Invariants only: no mutated pair is claimed, because QPA
/// realizes the exchange only when the approximation is injective with a
/// nonzero cokernel.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ApproxRecord {
    pair: PairRecord,
    summand_dimvec: Vec<usize>,
    invariants: ApproxInvariants,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ApproxInvariants {
    source_dimvec: Vec<usize>,
    target_dimvec: Vec<usize>,
    rank: usize,
    kernel_dimvec: Vec<usize>,
    cokernel_dimvec: Vec<usize>,
}

/// Shape of the graph on the enumerated pairs, adjacent when they share
/// `n - 1` of their `n` labels. Computed from the enumerated set on both
/// sides, so it is a self-consistency check and never external truth.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ExchangeShape {
    degree_histogram: Vec<usize>,
    edges: usize,
    connected: bool,
}

/// The v8 `support_tau_tilting` block of one fixture.
#[derive(Clone, Debug, PartialEq)]
struct SupportTauTilting {
    indecomposables: Closure,
    brute: BruteAgreement,
    tau_rigid_designated: Vec<bool>,
    body: SttBody,
}

#[derive(Clone, Debug, PartialEq)]
enum SttBody {
    /// Everything gated on the closure marker.
    Enumerated(Box<SttValues>),
    /// The typed refusal, with the reason the generator recorded.
    NotComputed { reason: String },
}

#[derive(Clone, Debug, PartialEq)]
struct SttValues {
    total: usize,
    histogram: Vec<usize>,
    pairs: Vec<PairRecord>,
    approximation_slots: usize,
    approximations: Vec<ApproxRecord>,
    exchange: ExchangeShape,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ClassicalTiltingRecord {
    id: String,
    construction: String,
    bound: usize,
    module_dimvec: Vec<usize>,
    qpa_tilting: bool,
    projective_dimension: Option<usize>,
    coresolutions: Vec<Vec<Vec<usize>>>,
    coresolutions_exact: Vec<bool>,
    target: Option<TargetOracle>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TargetOracle {
    Computed(TargetInvariants),
    Skipped { reason: TargetSkipReason },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TargetSkipReason {
    OperationUnavailable,
    EndomorphismPresentationFailed,
    OppositeAlgebraFailed,
    InvariantComputationFailed,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TargetInvariants {
    dimension: usize,
    cartan: Vec<Vec<usize>>,
    radical_layers: Vec<usize>,
    simple_ext1: Vec<Vec<usize>>,
}

#[derive(Clone, Debug, PartialEq)]
struct ArrowSpec {
    name: String,
    source: u32,
    target: u32,
}

#[derive(Clone, Debug, PartialEq)]
struct QuiverSpec {
    num_vertices: u32,
    arrows: Vec<ArrowSpec>,
}

/// One relation term as written: an integer coefficient and a path of arrow
/// indices. Coefficients stay raw here; the documented mod-p reduction runs
/// when the algebra is built.
#[derive(Clone, Debug, PartialEq)]
struct TermSpec {
    coeff: i64,
    path: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq)]
struct Fixture {
    family: String,
    case: String,
    field: u64,
    presentation_id: String,
    ideal_id: String,
    quiver: QuiverSpec,
    relations: Vec<Vec<TermSpec>>,
    dim: usize,
    cartan: Vec<Vec<usize>>,
    injectives: Vec<Vec<usize>>,
    projdim: Vec<DimOutcome>,
    injdim: Vec<DimOutcome>,
    tau: Vec<TauOutcome>,
    tau_injectives: Vec<TauOutcome>,
    decomposition: Vec<(Vec<usize>, usize)>,
    ext: Vec<Vec<Vec<usize>>>,
    designated: Vec<ModuleRef>,
    ar_sequences: Vec<ArEntry>,
    irreducible_maps: Vec<IrrEntry>,
    ext_algebra: ExtAlgebra,
    yoneda_products: Vec<YonedaProduct>,
    stable_hom: Vec<Vec<usize>>,
    tau_rigid: Vec<bool>,
    rigid: Vec<bool>,
    tau_period: Vec<TauPeriod>,
    /// The v8 block, absent from the v6 snapshot projection.
    stt: Option<SupportTauTilting>,
    /// Designated schema v8 classical-tilting candidates.
    classical_tilting: Vec<ClassicalTiltingRecord>,
    /// The tau-orbit search bound the `tau_period` list was computed with,
    /// read back from its `none_up_to` entries. Derived, so it never widens
    /// document equality.
    tau_period_bound: usize,
}

struct FixtureHeader<'a> {
    pairs: &'a [(String, json::Value)],
    family: String,
    case: String,
    field: u64,
    presentation_id: String,
    ideal_id: String,
    quiver: QuiverSpec,
    relations: Vec<Vec<TermSpec>>,
}

struct FixtureDetails {
    cartan: Vec<Vec<usize>>,
    designated: Vec<ModuleRef>,
    tau_period: Vec<TauPeriod>,
    tau_period_bound: usize,
    tau_rigid: Vec<bool>,
    stt: Option<SupportTauTilting>,
    classical_tilting: Vec<ClassicalTiltingRecord>,
}

struct FixtureCoreValues {
    dim: usize,
    injectives: Vec<Vec<usize>>,
    projdim: Vec<DimOutcome>,
    injdim: Vec<DimOutcome>,
    tau: Vec<TauOutcome>,
    tau_injectives: Vec<TauOutcome>,
    decomposition: Vec<(Vec<usize>, usize)>,
    ext: Vec<Vec<Vec<usize>>>,
}

struct FixtureArValues {
    ar_sequences: Vec<ArEntry>,
    irreducible_maps: Vec<IrrEntry>,
    ext_algebra: ExtAlgebra,
    yoneda_products: Vec<YonedaProduct>,
    stable_hom: Vec<Vec<usize>>,
    rigid: Vec<bool>,
}

/// A validated oracle document. Provenance is kept as key/value pairs so the
/// live mode's whole-document equality covers it.
#[derive(Clone, Debug, PartialEq)]
struct Document {
    left_convention: bool,
    provenance: Vec<(String, String)>,
    fixtures: Vec<Fixture>,
}

type ExtAlgebraRows = (Vec<usize>, Vec<usize>, Vec<usize>);
type SttHeader<'a> = (
    &'a [(String, json::Value)],
    Closure,
    BruteAgreement,
    Vec<bool>,
);
type CoresolutionValues = (Vec<Vec<Vec<usize>>>, Vec<bool>);
type FixtureDimensionValues = (usize, Vec<Vec<usize>>, Vec<DimOutcome>, Vec<DimOutcome>);
type FixtureTranslateValues = (
    Vec<TauOutcome>,
    Vec<TauOutcome>,
    Vec<(Vec<usize>, usize)>,
    Vec<Vec<Vec<usize>>>,
);
type FixtureArStructures = (Vec<ArEntry>, Vec<IrrEntry>, ExtAlgebra, Vec<YonedaProduct>);
type DocumentMetadata = (bool, bool, Vec<(String, String)>);
type TauValues = (Vec<bool>, Vec<bool>, Vec<TauPeriod>);

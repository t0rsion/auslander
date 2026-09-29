use crate::certificate::Certificate;
use crate::derived_artifact::{ArtifactMutation, ArtifactVerifyLimits};
use crate::derived_invariant::{
    DerivedInvariantKind, InvariantReading, InvariantStop, InvariantValue,
};
use crate::gentle::WindingClass;

use super::super::{ClassificationLimits, ClassificationStatus, MutationWalk, UnresolvedPair};

/// Limits that the atlas parser checks before it allocates.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DerivedAtlasParseLimits {
    /// The greatest input byte count.
    pub max_input_bytes: usize,
    /// The greatest byte count of one member certificate.
    pub max_certificate_bytes: usize,
    /// The maximum number of members.
    pub max_members: usize,
    /// The greatest length of any other array.
    pub max_entries: usize,
    /// The maximum number of integers in the document.
    pub max_numeric_values: usize,
    /// The maximum number of array elements in the document.
    pub max_array_elements: usize,
    /// The greatest digit count of one integer. An `i128` has at most 39.
    pub max_integer_digits: usize,
}

impl Default for DerivedAtlasParseLimits {
    fn default() -> Self {
        DerivedAtlasParseLimits {
            max_input_bytes: 67_108_864,
            max_certificate_bytes: 4_194_304,
            max_members: 100_000,
            max_entries: 16_777_216,
            max_numeric_values: 50_000_000,
            max_array_elements: 50_000_000,
            max_integer_digits: 39,
        }
    }
}

/// Ceilings for one atlas verification.
///
/// A declared limit above its ceiling stops verification with
/// [`crate::derived_artifact::ArtifactVerificationCut::DeclaredLimit`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DerivedAtlasVerifyLimits {
    /// Parser and allocation ceilings.
    pub parse: DerivedAtlasParseLimits,
    /// The tilting and target ceilings of each merge replay, as for a
    /// derived-equivalence artifact. `max_work_units` bounds the mutations
    /// replayed over all merges. `replay.parse` is not used.
    pub replay: ArtifactVerifyLimits,
    /// The greatest declared last Hochschild degree.
    pub max_hochschild_degree: u64,
    /// The greatest declared bar tensor-tuple limit.
    pub max_tensor_tuples: u64,
    /// The greatest declared bar cochain-dimension limit.
    pub max_cochain_dim: u64,
    /// The greatest declared bar matrix-entry limit.
    pub max_bar_matrix_entries: u64,
    /// The greatest declared bar work-unit limit.
    pub max_bar_work_units: u64,
    /// The greatest dimension of one member, read from its certificate
    /// before verification. It bounds the vertex count, which sets the cost
    /// of the Cartan invariants, and the cost of each product in an
    /// isomorphism check.
    pub max_member_dimension: u64,
}

impl Default for DerivedAtlasVerifyLimits {
    fn default() -> Self {
        DerivedAtlasVerifyLimits {
            parse: DerivedAtlasParseLimits::default(),
            replay: ArtifactVerifyLimits::default(),
            max_hochschild_degree: 16,
            max_tensor_tuples: 1_000_000,
            max_cochain_dim: 1_000_000,
            max_bar_matrix_entries: 100_000_000,
            max_bar_work_units: 10_000_000_000,
            max_member_dimension: 256,
        }
    }
}

/// Why a stored invariant did not finish.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AtlasStop {
    /// An intermediate integer left the `i128` range.
    Overflow,
    /// The bar computation hit a limit before the value finished.
    BarCut,
}

/// One stored invariant reading.
///
/// A finished value is a list of integers: a count or a determinant as one
/// entry; invariant factors, pencil coefficients, or Hochschild dimensions
/// in order; an AAG function as `n_1, m_1, n_2, m_2, ...`; a winding class
/// as `[0]` planar, `[1, g]` gcd, `[2]` odd, `[3]` even, or `[4, a]` Arf.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AtlasReading {
    /// The finished value.
    Finished(Vec<i128>),
    /// The computation stopped without a value.
    Stopped(AtlasStop),
    /// The invariant is not defined for this presentation.
    NotApplicable,
}

impl AtlasReading {
    /// The stored form of `reading`. `None` for a cancelled reading, which a
    /// replay cannot reproduce.
    pub fn from_reading(reading: &InvariantReading) -> Option<AtlasReading> {
        Some(match reading {
            InvariantReading::Finished(value) => AtlasReading::Finished(encode_value(value)),
            InvariantReading::Stopped(InvariantStop::Overflow) => {
                AtlasReading::Stopped(AtlasStop::Overflow)
            }
            InvariantReading::Stopped(InvariantStop::BarCut(_)) => {
                AtlasReading::Stopped(AtlasStop::BarCut)
            }
            InvariantReading::Stopped(InvariantStop::Cancelled) => return None,
            InvariantReading::NotApplicable(_) => AtlasReading::NotApplicable,
        })
    }
}

/// The integers of one finished value, as [`AtlasReading::Finished`] stores
/// them.
pub(super) fn encode_value(value: &InvariantValue) -> Vec<i128> {
    let widen = |values: &[usize]| values.iter().map(|&v| v as i128).collect();
    match value {
        InvariantValue::Count(count) => vec![*count as i128],
        InvariantValue::Integer(integer) => vec![*integer],
        InvariantValue::Factors(values) | InvariantValue::Polynomial(values) => values.clone(),
        InvariantValue::AagFunction(function) => function
            .pairs()
            .iter()
            .flat_map(|&(n, m)| [n as i128, m as i128])
            .collect(),
        InvariantValue::WindingClass(class) => encode_winding(*class),
        InvariantValue::Dimensions(dimensions) => widen(dimensions),
    }
}

fn encode_winding(class: WindingClass) -> Vec<i128> {
    match class {
        WindingClass::Planar => vec![0],
        WindingClass::Gcd(gcd) => vec![1, i128::from(gcd)],
        WindingClass::Odd => vec![2],
        WindingClass::Even => vec![3],
        WindingClass::Arf(arf) => vec![4, i128::from(arf)],
    }
}

/// The portable name of each kind, in [`DerivedInvariantKind::ALL`] order.
pub(super) const KIND_NAMES: [&str; 10] = [
    "vertex_count",
    "cartan_determinant",
    "cartan_factors",
    "symmetric_factors",
    "skew_factors",
    "cartan_pencil",
    "aag_function",
    "winding_class",
    "hochschild_dimensions",
    "center_dimension",
];

pub(super) fn kind_name(kind: DerivedInvariantKind) -> &'static str {
    KIND_NAMES[kind as usize]
}

pub(super) fn kind_from_name(name: &str) -> Option<DerivedInvariantKind> {
    let position = KIND_NAMES.iter().position(|known| *known == name)?;
    Some(DerivedInvariantKind::ALL[position])
}

/// One stored merge: the recipe from member `source` and the isomorphism
/// from the recovered target onto member `member`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtlasMerge {
    pub(super) source: usize,
    pub(super) member: usize,
    pub(super) recipe: Vec<ArtifactMutation>,
    pub(super) vertex_map: Vec<u32>,
    pub(super) arrow_images: Vec<Vec<u64>>,
}

impl AtlasMerge {
    accessor_methods! {
        /// The walked member, where the recipe starts.
        pub source() -> usize = |this| this.source;
        /// The matched member.
        pub member() -> usize = |this| this.member;
        /// The mutations from the regular complex of `source`. Empty for a
        /// duplicate, whose target is `source` itself.
        pub recipe() -> &[ArtifactMutation] = |this| &this.recipe;
        /// The vertex map of the isomorphism onto `member`.
        pub vertex_map() -> &[u32] = |this| &this.vertex_map;
        /// Each arrow image over the normal-word basis of `member`, as
        /// residues in `0..p`.
        pub arrow_images() -> &[Vec<u64>] = |this| &this.arrow_images;
    }
}

/// One stored class: its members, increasing, and its merges.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtlasClass {
    pub(super) members: Vec<usize>,
    pub(super) merges: Vec<AtlasMerge>,
}

impl AtlasClass {
    accessor_methods! {
        /// The members, increasing.
        pub members() -> &[usize] = |this| &this.members;
        /// The merges, a spanning tree of the members.
        pub merges() -> &[AtlasMerge] = |this| &this.merges;
    }
}

/// One stored separation: a member of each class and the two values of the
/// separating invariant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtlasSeparation {
    pub(super) classes: (usize, usize),
    pub(super) members: (usize, usize),
    pub(super) kind: DerivedInvariantKind,
    pub(super) left: Vec<i128>,
    pub(super) right: Vec<i128>,
}

impl AtlasSeparation {
    accessor_methods! {
        /// The class indices, the first one smaller.
        pub classes() -> (usize, usize) = |this| this.classes;
        /// The witnessed member of each class.
        pub members() -> (usize, usize) = |this| this.members;
        /// The separating invariant.
        pub kind() -> DerivedInvariantKind = |this| this.kind;
        /// The value for the first member, encoded as in [`AtlasReading`].
        pub left() -> &[i128] = |this| &this.left;
        /// The value for the second member.
        pub right() -> &[i128] = |this| &this.right;
    }
}

/// A canonical portable derived classification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DerivedAtlasArtifact {
    pub(super) field: u64,
    pub(super) limits: ClassificationLimits,
    pub(super) members: Vec<Certificate>,
    pub(super) invariants: Vec<Vec<AtlasReading>>,
    pub(super) classes: Vec<AtlasClass>,
    pub(super) separations: Vec<AtlasSeparation>,
    pub(super) unresolved: Vec<UnresolvedPair>,
    pub(super) walks: Vec<MutationWalk>,
    pub(super) status: ClassificationStatus,
    pub(super) fingerprint: String,
}

impl DerivedAtlasArtifact {
    accessor_methods! {
        /// The prime `p` of the field `GF(p)`.
        pub field() -> u64 = |this| this.field;
        /// The limits of the classification.
        pub limits() -> &ClassificationLimits = |this| &this.limits;
        /// The member certificates, in family order.
        pub members() -> &[Certificate] = |this| &this.members;
        /// The readings of each member, in [`DerivedInvariantKind::ALL`] order.
        pub invariants() -> &[Vec<AtlasReading>] = |this| &this.invariants;
        /// The classes, ordered by representative.
        pub classes() -> &[AtlasClass] = |this| &this.classes;
        /// One separation per separated pair of classes, in pair order.
        pub separations() -> &[AtlasSeparation] = |this| &this.separations;
        /// Every unresolved pair of classes, in pair order.
        pub unresolved() -> &[UnresolvedPair] = |this| &this.unresolved;
        /// Every mutation walk, in the order it ran.
        pub walks() -> &[MutationWalk] = |this| &this.walks;
        /// `Complete` exactly when no pair is unresolved.
        pub status() -> ClassificationStatus = |this| this.status;
        /// The FNV-1a fingerprint of the preceding canonical fields.
        pub fingerprint() -> &str = |this| &this.fingerprint;
    }
}

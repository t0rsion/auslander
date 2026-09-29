//! Certified derived classification of a finite family of algebras over one
//! prime field.
//!
//! [`classify_derived`] partitions a family into classes. A class is joined
//! by merges, and each [`DerivedMerge`] carries a replayable tilting recipe,
//! a [`DerivedEquivalencePath`], and an [`AlgebraIsomorphism`]. Each pair of
//! classes is either separated by a [`DerivedInequivalenceWitness`] or listed
//! as an [`UnresolvedPair`] with the walks that left it open. A resource
//! limit or cancellation never turns an unresolved pair into a merge or a
//! separation.
//!
//! The classification runs in three stages.
//!
//! 1. [`DerivedInvariants::compute`] reads every invariant of every member.
//! 2. [`first_difference`] compares every pair of members. The groups are
//!    the connected components of the pairs it does not separate.
//! 3. Mutation walks run from members whose class still has an unresolved
//!    partner in its group. Every certified vertex gives a recovered target,
//!    and [`FamilyIndex::match_member`] matches it against the whole family.
//!
//! A merge joins the walked member and the matched member. The merges of a
//! class form a spanning tree of its members. A merge path starts at the
//! walked member, not at the class representative: a path continues only
//! from an identical certificate, and an isomorphic target is not one.
//!
//! A match whose classes are separated contradicts Rickard's theorem, and a
//! match outside the group is a special case of it. Both give
//! [`ClassificationError::Contradiction`], an internal defect.
//!
//! Members with equal [`crate::gentle::GentleKey`], or equal certificates
//! when not gentle, are duplicates. Each merges into the first such member
//! with an identity path and is never walked.
//!
//! [`DerivedClassification::to_artifact`] writes the portable
//! `derived-atlas-v1` artifact, and [`verify_derived_atlas_artifact`]
//! replays it.

mod atlas;
mod stages;
mod verify;

pub use atlas::{
    AtlasClass, AtlasMerge, AtlasReading, AtlasSeparation, AtlasStop,
    DERIVED_ATLAS_ARTIFACT_ENGINE, DERIVED_ATLAS_ARTIFACT_KIND, DERIVED_ATLAS_ARTIFACT_SCHEMA,
    DerivedAtlasArtifact, DerivedAtlasError, DerivedAtlasParseLimits, DerivedAtlasVerification,
    DerivedAtlasVerifyLimits, VerifiedDerivedAtlas, verify_derived_atlas_artifact,
};

use std::sync::Arc;

use crate::algebra::Algebra;
use crate::algebra_isomorphism::{AlgebraIsomorphism, FamilyFieldError, FamilyIndex};
use crate::complex_target::ComplexTargetError;
use crate::control::ComputationControl;
use crate::derived_artifact::ArtifactMutation;
use crate::derived_invariant::{
    DerivedInequivalenceWitness, DerivedInvariantKind, DerivedInvariants, InvariantLimits,
    first_difference,
};
use crate::equivalence_discovery::{DiscoveryLimits, DiscoveryStop};
use crate::equivalence_edge::DerivedEquivalencePath;
use crate::hochschild::{BarLimits, HochschildError};
use crate::target::TargetLimits;
use crate::tilting_complex::TiltingComplexError;

use stages::{Context, Partition, SeparationTable, assemble};

/// Caller-owned limits for one classification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassificationLimits {
    /// The limits of every invariant computation.
    pub invariants: InvariantLimits,
    /// The limits of each mutation walk. Every walk gets the whole budget.
    pub discovery: DiscoveryLimits,
    /// The limits of each target recovery.
    pub target: TargetLimits,
}

impl ClassificationLimits {
    /// The limits of the committed classification study, with at most
    /// `walk_vertices` stored complexes per walk.
    ///
    /// The invariants use Hochschild degree 2 and at most 10000 tensor
    /// tuples, 100000 cochain coordinates, 10000000 matrix entries, and
    /// 1000000000 work units. A walk attempts at most `4 * walk_vertices`
    /// mutations and stores at most `32 * walk_vertices` terms and
    /// `2048 * walk_vertices` matrix entries. Each product saturates at
    /// `u64::MAX`. Targets use [`TargetLimits::default`], and
    /// `through_silting` is off.
    pub fn with_walk_vertices(walk_vertices: u64) -> ClassificationLimits {
        let bar = BarLimits {
            max_tensor_tuples: 10_000,
            max_cochain_dim: 100_000,
            max_matrix_entries: 10_000_000,
            max_work_units: 1_000_000_000,
        };
        let scaled = |factor: u64| walk_vertices.saturating_mul(factor);
        ClassificationLimits {
            invariants: InvariantLimits {
                hochschild_degree: 2,
                bar,
            },
            discovery: DiscoveryLimits {
                max_vertices: walk_vertices,
                max_directed_mutations: scaled(4),
                max_total_terms: scaled(32),
                max_matrix_entries: scaled(2_048),
                ..DiscoveryLimits::default()
            },
            target: TargetLimits::default(),
        }
    }
}

/// Why a classification produced no result.
#[derive(Clone, Debug)]
pub enum ClassificationError {
    /// Two members live over different fields.
    FieldMismatch(FamilyFieldError),
    /// The bar computation of one member failed, an internal defect.
    Invariant {
        member: usize,
        error: HochschildError,
    },
    /// A tilting check in the walk from `member` failed structurally.
    Discovery {
        member: usize,
        error: TiltingComplexError,
    },
    /// Target recovery failed at one vertex of the walk from `member`.
    Target {
        member: usize,
        vertex: usize,
        error: ComplexTargetError,
    },
    /// A merge from `source` to `member` joins classes that `kind`
    /// separates at members `separated`. `vertex` is the walk vertex, or
    /// `None` for a duplicate. This is an internal defect.
    Contradiction {
        source: usize,
        vertex: Option<usize>,
        member: usize,
        separated: (usize, usize),
        kind: DerivedInvariantKind,
    },
}

display_error! { error ClassificationError {
    Self::FieldMismatch(error) => "{error}";
    Self::Invariant { member, error } => "invariants of member {member} failed: {error}";
    Self::Discovery { member, error } => "the walk from member {member} failed: {error}";
    Self::Target { member, vertex, error } => "target recovery at vertex {vertex} of the walk from member {member} failed: {error}";
    Self::Contradiction { source, vertex, member, separated, kind } => "a merge from member {source} to member {member} at vertex {vertex:?} contradicts {kind:?}, which separates members {} and {}; library bug", separated.0, separated.1;
} }

/// One certified derived equivalence between two family members.
///
/// `recipe` mutates the regular complex of member `source` to a tilting
/// complex `T`. `path` runs from `source` to the recovered target
/// `End(T)^op`, and `isomorphism` maps that target onto member `member`. A
/// duplicate merge has an empty recipe and the identity path on `source`.
#[derive(Clone, Debug)]
pub struct DerivedMerge {
    pub(crate) source: usize,
    pub(crate) member: usize,
    pub(crate) recipe: Vec<ArtifactMutation>,
    pub(crate) path: DerivedEquivalencePath,
    pub(crate) isomorphism: AlgebraIsomorphism,
}

impl DerivedMerge {
    accessor_methods! {
        /// The walked member, where the recipe starts.
        pub source() -> usize = |this| this.source;
        /// The matched member.
        pub member() -> usize = |this| this.member;
        /// The mutations from the regular complex of `source`.
        pub recipe() -> &[ArtifactMutation] = |this| &this.recipe;
        /// The derived equivalence from `source` to the recovered target.
        pub path() -> &DerivedEquivalencePath = |this| &this.path;
        /// The isomorphism from the recovered target to `member`.
        pub isomorphism() -> &AlgebraIsomorphism = |this| &this.isomorphism;
        /// Whether this merge joins two duplicate presentations.
        pub is_duplicate() -> bool = |this| this.path.steps().is_empty();
    }
}

/// One class of derived equivalent members.
#[derive(Clone, Debug)]
pub struct DerivedClass {
    members: Vec<usize>,
    merges: Vec<DerivedMerge>,
}

impl DerivedClass {
    accessor_methods! {
        /// The members, increasing.
        pub members() -> &[usize] = |this| &this.members;
        /// The least member.
        pub representative() -> usize = |this| this.members[0];
        /// The merges, a spanning tree of the members, in discovery order.
        pub merges() -> &[DerivedMerge] = |this| &this.merges;
    }
}

/// A separated pair of classes with the witness for one member of each.
#[derive(Clone, Debug)]
pub struct ClassSeparation {
    classes: (usize, usize),
    members: (usize, usize),
    witness: DerivedInequivalenceWitness,
}

impl ClassSeparation {
    accessor_methods! {
        /// The class indices, the first one smaller.
        pub classes() -> (usize, usize) = |this| this.classes;
        /// The witnessed member of each class.
        pub members() -> (usize, usize) = |this| this.members;
        /// The first differing invariant in table order, over every member
        /// pair of the two classes.
        pub witness() -> &DerivedInequivalenceWitness = |this| &this.witness;
    }
}

/// A pair of classes that neither a merge nor an invariant settles.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnresolvedPair {
    classes: (usize, usize),
    walks: Vec<usize>,
}

impl UnresolvedPair {
    accessor_methods! {
        /// The class indices, the first one smaller.
        pub classes() -> (usize, usize) = |this| this.classes;
        /// The indices into [`DerivedClassification::walks`] of every walk
        /// from a member of either class. Their stops say why the pair is
        /// open.
        pub walks() -> &[usize] = |this| &this.walks;
    }
}

/// The record of one mutation walk.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MutationWalk {
    member: usize,
    stop: DiscoveryStop,
    vertices: usize,
    blocked: usize,
    examined: usize,
    target_cuts: usize,
    unmatched: usize,
    merges: usize,
}

impl MutationWalk {
    accessor_methods! {
        /// The walked member.
        pub member() -> usize = |this| this.member;
        /// Why discovery stopped.
        pub stop() -> &DiscoveryStop = |this| &this.stop;
        /// The certified vertices found, silting ones included.
        pub vertices() -> usize = |this| this.vertices;
        /// The completed mutations that gave no vertex.
        pub blocked() -> usize = |this| this.blocked;
        /// The tilting vertices whose target was recovered or cut. Fewer than
        /// the tilting vertices only after cancellation.
        pub examined() -> usize = |this| this.examined;
        /// The vertices whose target recovery hit a limit.
        pub target_cuts() -> usize = |this| this.target_cuts;
        /// The recovered targets that matched no member.
        pub unmatched() -> usize = |this| this.unmatched;
        /// The merges this walk added.
        pub merges() -> usize = |this| this.merges;
    }
}

/// Whether every pair of classes is settled.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ClassificationStatus {
    /// Every pair of classes is separated.
    Complete,
    /// At least one pair of classes is unresolved.
    Incomplete,
}

impl ClassificationStatus {
    /// `complete` or `incomplete`, the name the atlas stores.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Complete => "complete",
            Self::Incomplete => "incomplete",
        }
    }
}

/// The result of [`classify_derived`].
#[derive(Clone, Debug)]
pub struct DerivedClassification {
    family: Vec<Arc<Algebra>>,
    limits: ClassificationLimits,
    invariants: Vec<DerivedInvariants>,
    groups: Vec<Vec<usize>>,
    classes: Vec<DerivedClass>,
    separations: Vec<ClassSeparation>,
    unresolved: Vec<UnresolvedPair>,
    walks: Vec<MutationWalk>,
}

impl DerivedClassification {
    accessor_methods! {
        /// The family, in input order.
        pub family() -> &[Arc<Algebra>] = |this| &this.family;
        /// The limits of the run.
        pub limits() -> &ClassificationLimits = |this| &this.limits;
        /// The invariants of each member.
        pub invariants() -> &[DerivedInvariants] = |this| &this.invariants;
        /// The stage 2 groups, each increasing, ordered by least member.
        pub groups() -> &[Vec<usize>] = |this| &this.groups;
        /// The classes, ordered by representative.
        pub classes() -> &[DerivedClass] = |this| &this.classes;
        /// One separation per separated pair of classes, in pair order.
        pub separations() -> &[ClassSeparation] = |this| &this.separations;
        /// Every unresolved pair of classes, in pair order.
        pub unresolved() -> &[UnresolvedPair] = |this| &this.unresolved;
        /// Every mutation walk, in the order it ran.
        pub walks() -> &[MutationWalk] = |this| &this.walks;
    }

    /// `Complete` exactly when no pair of classes is unresolved.
    pub fn status(&self) -> ClassificationStatus {
        if self.unresolved.is_empty() {
            ClassificationStatus::Complete
        } else {
            ClassificationStatus::Incomplete
        }
    }
}

/// Classifies `family` up to derived equivalence.
///
/// Each walk runs under `limits.discovery` and each target recovery under
/// `limits.target`. Cancellation stops the current walk and each later walk
/// before its first mutation. The result is then partial: every pair that
/// the stopped walks could have merged stays unresolved. Identical input
/// gives identical output, order included.
///
/// Errors when the members live over different fields, and on the internal
/// defects of [`ClassificationError`].
pub fn classify_derived(
    family: &[Arc<Algebra>],
    limits: &ClassificationLimits,
    control: &ComputationControl,
) -> Result<DerivedClassification, ClassificationError> {
    let index = FamilyIndex::new(family).map_err(ClassificationError::FieldMismatch)?;
    let invariants = family
        .iter()
        .enumerate()
        .map(|(member, algebra)| {
            DerivedInvariants::compute(algebra, limits.invariants, control)
                .map_err(|error| ClassificationError::Invariant { member, error })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let table = SeparationTable::new(&invariants);
    let groups = table.groups();
    let mut partition = Partition::new(family.len());
    for member in 0..family.len() {
        if let Some(original) = index.duplicate_of(member) {
            partition.merge_duplicate(&table, &index, original, member)?;
        }
    }
    let context = Context {
        index: &index,
        table: &table,
        limits,
    };
    let mut walks = Vec::new();
    for member in 0..family.len() {
        if index.duplicate_of(member).is_none() && partition.has_open_partner(&table, member) {
            walks.push(partition.walk(&context, member, control)?);
        }
    }
    let (classes, separations, unresolved) = assemble(partition, &table, &invariants, &walks);
    Ok(DerivedClassification {
        family: family.to_vec(),
        limits: limits.clone(),
        invariants,
        groups,
        classes,
        separations,
        unresolved,
        walks,
    })
}

#[cfg(test)]
mod family_tests;
#[cfg(test)]
mod tests;

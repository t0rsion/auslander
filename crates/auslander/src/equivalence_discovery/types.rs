use crate::tilting_complex::{
    ApproximationDirection, OrthogonalityGoal, TiltingComplexBlocker, TiltingComplexLimits,
};

/// Deterministic limits for one mutation walk.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DiscoveryLimits {
    /// The maximum number of stored tilting complexes.
    pub max_vertices: u64,
    /// The maximum number of attempted directed mutations.
    pub max_directed_mutations: u64,
    /// The greatest sum of stored bounded-complex term counts.
    pub max_total_terms: u64,
    /// The greatest sum of stored module and differential matrix entries.
    pub max_matrix_entries: u64,
    /// Limits for each tilting-complex classification.
    pub tilting: TiltingComplexLimits,
    /// Whether a mutation result that is silting but not tilting becomes a
    /// stored vertex. Off by default, which blocks it as
    /// [`BlockedMutationReason::SiltingOnly`].
    pub through_silting: bool,
}

impl Default for DiscoveryLimits {
    fn default() -> Self {
        DiscoveryLimits {
            max_vertices: 1_024,
            max_directed_mutations: 16_384,
            max_total_terms: 65_536,
            max_matrix_entries: 16_777_216,
            tilting: TiltingComplexLimits::default(),
            through_silting: false,
        }
    }
}

impl DiscoveryLimits {
    /// The classification each mutation result receives.
    pub(crate) fn goal(&self) -> OrthogonalityGoal {
        if self.through_silting {
            OrthogonalityGoal::Silting
        } else {
            OrthogonalityGoal::Tilting
        }
    }
}

/// The exact reason a mutation walk stopped.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DiscoveryStop {
    /// Every stored vertex and mutation direction was attempted.
    ///
    /// Each attempt ended at an edge to a stored vertex or at a blocked
    /// attempt, so the stored vertices are closed under left and right
    /// mutation up to isomorphism. Without an `Undetermined` blocker, they are
    /// every tilting complex reachable from the regular complex through a
    /// chain of mutations of tilting complexes. With
    /// [`DiscoveryLimits::through_silting`], they are every silting complex
    /// reachable through a chain of irreducible silting mutations. The rest of
    /// the silting graph stays outside the claim.
    ExhaustedFrontier,
    /// The caller requested cancellation. A mutation in progress is discarded.
    Cancelled { completed_mutations: u64 },
    /// The next directed mutation exceeded its count limit.
    MutationLimit { completed: u64, limit: u64 },
    /// A new vertex exceeded the stored-vertex limit.
    VertexLimit { stored: u64, limit: u64 },
    /// A new vertex exceeded the total term limit.
    TermLimit {
        stored: u64,
        requested: u64,
        limit: u64,
    },
    /// A new vertex exceeded the matrix-entry limit.
    MatrixLimit {
        stored: u64,
        requested: u64,
        limit: u64,
    },
}

/// A mutation that completed but did not produce a stored vertex.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BlockedMutationReason {
    /// A shifted Hom class made the result silting but not tilting. Only a
    /// walk without [`DiscoveryLimits::through_silting`] blocks it.
    SiltingOnly {
        source: usize,
        target: usize,
        degree: i32,
        dimension: usize,
    },
    /// A classification obligation remained open.
    Undetermined(TiltingComplexBlocker),
}

/// One stored non-edge from a complete mutation attempt.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockedTiltingMutation {
    pub(super) source: usize,
    pub(super) direction: ApproximationDirection,
    pub(super) summand: usize,
    pub(super) reason: BlockedMutationReason,
}

impl BlockedTiltingMutation {
    accessor_methods! {
        /// The source vertex index.
        pub source() -> usize = |this| this.source;
        /// The attempted mutation direction.
        pub direction() -> ApproximationDirection = |this| this.direction;
        /// The replaced summand index.
        pub summand() -> usize = |this| this.summand;
        /// Why no tilting edge was stored.
        pub reason() -> &BlockedMutationReason = |this| &this.reason;
    }
}

/// One certified directed mutation edge.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TiltingMutationEdge {
    pub(super) source: usize,
    pub(super) target: usize,
    pub(super) direction: ApproximationDirection,
    pub(super) summand: usize,
}

impl TiltingMutationEdge {
    accessor_methods! {
        /// The source vertex index.
        pub source() -> usize = |this| this.source;
        /// The target vertex index.
        pub target() -> usize = |this| this.target;
        /// The checked mutation direction.
        pub direction() -> ApproximationDirection = |this| this.direction;
        /// The replaced summand index.
        pub summand() -> usize = |this| this.summand;
    }
}

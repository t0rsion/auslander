use std::sync::Arc;

use crate::algebra::Algebra;
use crate::control::{ComputationControl, ProgressStage};
use crate::field::Fp;
use crate::hom::{HomError, Morphism};
use crate::iso::{is_isomorphic, IsoOutcome};
use crate::linalg::DenseMat;
use crate::module::{same_representation, Module, ModuleError};
use crate::quiver::ArrowId;

/// A coordinate in the deterministic arrow-major, row-major matrix layout.
///
/// The final coordinate is the least-significant mixed-radix digit of the raw
/// cursor. Cursor zero therefore contains only zero matrix entries.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CensusCoordinate {
    arrow: ArrowId,
    row: usize,
    column: usize,
}

impl CensusCoordinate {
    accessor_methods! {
        /// The arrow whose matrix contains this coordinate.
        pub arrow() -> ArrowId = |this| this.arrow;
        /// The row inside the arrow matrix.
        pub row() -> usize = |this| this.row;
        /// The column inside the arrow matrix.
        pub column() -> usize = |this| this.column;
    }
}

/// A finite raw census domain for one dimension vector.
#[derive(Clone, Debug)]
pub struct CensusDomain {
    algebra: Arc<Algebra>,
    dimensions: Vec<usize>,
    coordinates: Vec<CensusCoordinate>,
    raw_space_size: u128,
}

impl PartialEq for CensusDomain {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.algebra, &other.algebra)
            && self.dimensions == other.dimensions
            && self.coordinates == other.coordinates
            && self.raw_space_size == other.raw_space_size
    }
}

impl Eq for CensusDomain {}

impl CensusDomain {
    /// Builds a checked finite raw domain.
    ///
    /// The cardinality is represented by `u128`. A larger cardinality is a
    /// typed error, even when a caller would later impose a smaller limit.
    pub fn new(algebra: &Arc<Algebra>, dimensions: Vec<usize>) -> Result<Self, CensusError> {
        validate_dimensions(algebra, &dimensions)?;
        let coordinates = coordinate_layout(algebra, &dimensions)?;
        let raw_space_size = checked_power(algebra.field().modulus(), coordinates.len())?;
        Ok(Self {
            algebra: algebra.clone(),
            dimensions,
            coordinates,
            raw_space_size,
        })
    }

    accessor_methods! {
        /// The checked algebra of the domain.
        pub algebra() -> &Arc<Algebra> = |this| &this.algebra;
        /// The dimension vector, indexed by quiver vertex.
        pub dimensions() -> &[usize] = |this| &this.dimensions;
        /// The arrow-major, row-major coordinate order, with the final entry fastest.
        pub coordinates() -> &[CensusCoordinate] = |this| &this.coordinates;
        /// The number of matrix entries in one candidate.
        pub coordinate_count() -> usize = |this| this.coordinates.len();
        /// The checked number of raw matrix tuples.
        pub raw_space_size() -> u128 = |this| this.raw_space_size;
    }
}

/// Retention policy for duplicate census records.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CensusRetention {
    /// Retains every duplicate assignment and its witness.
    AllAssignments,
    /// Retains representatives and counters, then drops duplicate records.
    RepresentativesOnly,
}

impl CensusRetention {
    /// Returns the canonical JSON value for this retention mode.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::AllAssignments => "all_assignments",
            Self::RepresentativesOnly => "representatives_only",
        }
    }
}

/// Resource limits for one finite module census.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CensusLimits {
    /// Retention policy for duplicate classes.
    pub retention: CensusRetention,
    /// Maximum raw candidates fully processed.
    pub max_candidates: usize,
    /// Maximum retained representatives.
    pub max_representatives: usize,
    /// Maximum retained duplicate assignments and witnesses. Compact retention ignores this limit.
    pub max_assignments: usize,
    /// Maximum completed isomorphism comparisons.
    pub max_isomorphism_checks: usize,
    /// Maximum candidate and comparison work units.
    pub max_work_units: usize,
}

impl Default for CensusLimits {
    fn default() -> Self {
        Self {
            retention: CensusRetention::AllAssignments,
            max_candidates: 1_000_000,
            max_representatives: 100_000,
            max_assignments: 1_000_000,
            max_isomorphism_checks: 1_000_000,
            max_work_units: 10_000_000,
        }
    }
}

/// The stage of one deterministic census work reservation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CensusWorkStage {
    /// Constructing and checking one raw candidate.
    Candidate,
    /// Comparing one accepted candidate with one representative.
    Isomorphism,
}

/// Why a census stopped before its raw domain was exhausted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CensusCutReason {
    /// Cooperative cancellation was observed before the next candidate.
    Cancelled,
    /// The next candidate would exceed `max_candidates`.
    CandidateLimit { limit: usize },
    /// The next new class would exceed `max_representatives`.
    RepresentativeLimit { limit: usize },
    /// The next duplicate witness would exceed `max_assignments`.
    AssignmentLimit { limit: usize },
    /// The next comparison would exceed `max_isomorphism_checks`.
    IsomorphismLimit { limit: usize },
    /// The next reservation would exceed `max_work_units`.
    WorkLimit {
        stage: CensusWorkStage,
        limit: usize,
    },
    /// The existing isomorphism engine returned no certified decision.
    UnknownIsomorphism {
        representative: usize,
        reason: String,
    },
}

display_error! { CensusCutReason {
    Self::Cancelled => "census was cancelled";
    Self::CandidateLimit { limit } => "candidate limit {limit} reached";
    Self::RepresentativeLimit { limit } => "representative limit {limit} reached";
    Self::AssignmentLimit { limit } => "assignment limit {limit} reached";
    Self::IsomorphismLimit { limit } => "isomorphism limit {limit} reached";
    Self::WorkLimit { stage, limit } => "work limit {limit} reached at {stage:?}";
    Self::UnknownIsomorphism { representative, reason } => "isomorphism against representative {representative} is undetermined: {reason}";
} }

/// A rejected census domain or an arithmetic defect found before enumeration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CensusError {
    /// The dimension vector needs one entry per quiver vertex.
    DimensionVectorLength { expected: usize, got: usize },
    /// One arrow matrix entry count overflowed `usize`.
    MatrixEntryOverflow {
        arrow: ArrowId,
        rows: usize,
        columns: usize,
    },
    /// The total coordinate count overflowed `usize`.
    CoordinateCountOverflow,
    /// The coordinate layout could not reserve its checked capacity.
    CoordinateAllocationFailed { coordinates: usize },
    /// The exact raw cardinality overflowed `u128`.
    SearchSpaceOverflow { coordinates: usize, modulus: u64 },
}

display_error! { error CensusError {
    Self::DimensionVectorLength { expected, got } => "dimension vector has {got} entries, quiver has {expected} vertices";
    Self::MatrixEntryOverflow { arrow, rows, columns } => "matrix for arrow {} has {rows}x{columns} entries, which overflow usize", arrow.0;
    Self::CoordinateCountOverflow => "the total matrix-coordinate count overflows usize";
    Self::CoordinateAllocationFailed { coordinates } => "the census coordinate layout could not reserve {coordinates} entries";
    Self::SearchSpaceOverflow { coordinates, modulus } => "the raw search space {modulus}^{coordinates} overflows u128";
} }

/// A failure after a valid domain was constructed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CensusFailure {
    /// An isomorphism comparison rejected its checked input.
    Isomorphism {
        candidate_cursor: u128,
        representative: usize,
        error: HomError,
    },
    /// Candidate construction failed for a reason other than a rejected
    /// relation.
    CandidateConstruction {
        candidate_cursor: u128,
        error: ModuleError,
    },
    /// A deterministic counter overflowed before a result could be returned.
    WorkOverflow { candidate_cursor: u128 },
}

display_error! { CensusFailure {
    Self::Isomorphism { candidate_cursor, representative, error } => "isomorphism check at candidate {candidate_cursor} against representative {representative} failed: {error}";
    Self::CandidateConstruction { candidate_cursor, error } => "candidate {candidate_cursor} could not be constructed: {error}";
    Self::WorkOverflow { candidate_cursor } => "census work counter overflowed at candidate {candidate_cursor}";
} }

error_source! { CensusFailure {
    Self::Isomorphism { error, .. } => Some(error),
    Self::CandidateConstruction { error, .. } => Some(error),
    Self::WorkOverflow { .. } => None,
} }

use crate::algebra::BasisIdx;
/// Resource ceilings for one bar cohomology computation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BarLimits {
    /// Maximum number of tensor tuples at one degree.
    pub max_tensor_tuples: usize,
    /// Maximum number of cochain coordinates at one degree.
    pub max_cochain_dim: usize,
    /// Maximum retained matrix entries plus one live scratch reservation.
    pub max_matrix_entries: usize,
    /// Maximum deterministic work units across the request.
    pub max_work_units: u64,
}

/// A caller-controlled bar resource ceiling.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BarLimit {
    TensorTuples,
    CochainDimension,
    MatrixEntries,
    WorkUnits,
}

/// Why a bar computation stopped before the requested degree.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BarCutReason {
    Limit(BarLimit),
    SizeOverflow,
}

/// The reservation that stopped a bar computation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BarStage {
    DegreeRecord,
    Shape,
    Layout,
    Differential,
    Square,
    Cocycles,
    Coboundaries,
    Complement,
}

/// Typed diagnostics for a bar computation that ran out of resources.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BarBudgetDiagnostics {
    /// The limit or arithmetic overflow that stopped the computation.
    pub reason: BarCutReason,
    /// The operation whose reservation stopped the computation.
    pub stage: BarStage,
    /// The requested last cohomological degree.
    pub requested_degree: usize,
    /// The number of exact leading degrees retained in the cut result.
    pub completed_degree_count: usize,
    /// The first differential that did not finish.
    pub first_uncomputed_differential: usize,
    /// Work units reserved before the rejected reservation.
    pub work_units: u64,
    /// Matrix entries retained before the rejected reservation.
    pub matrix_entries: usize,
    /// The count already used by the rejected resource.
    pub used: u128,
    /// The rejected count after the proposed reservation.
    pub proposed: u128,
    /// The caller ceiling, or `None` for checked arithmetic overflow.
    pub ceiling: Option<u128>,
}

/// The final counters of a completed bar computation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BarRunDiagnostics {
    /// Work units reserved by the completed request.
    pub work_units: u64,
    /// Matrix entries retained by the completed request.
    pub matrix_entries: usize,
}

/// One cochain coordinate in a relative bar basis.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BarCoordinate {
    /// The lexicographic rank of the input tuple.
    pub tuple_rank: usize,
    /// The normal-word output basis index.
    pub output: BasisIdx,
}

/// A relative bar input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BarInput {
    /// The tagged empty tuple at this vertex, used only in degree zero.
    Vertex(u32),
    /// A positive-degree tuple of nontrivial normal-word basis indices.
    Tuple(Vec<BasisIdx>),
}

/// Rejected Hochschild cohomology input, or an internal differential defect.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HochschildError {
    /// The internally constructed differential square is nonzero.
    DifferentialSquare { degree: usize },
    /// A cochain coordinate vector has the wrong length.
    CoordinateCount { expected: usize, got: usize },
    /// The input has the wrong cohomological degree.
    WrongInputDegree { expected: usize, got: usize },
    /// A degree-zero input names a vertex outside the quiver.
    VertexOutOfRange { vertex: u32, num_vertices: u32 },
    /// A positive-degree input names a basis index outside the algebra basis.
    BasisOutOfRange { position: usize, index: usize },
    /// A positive-degree input contains a vertex idempotent.
    TrivialInput { position: usize },
    /// Adjacent input words do not compose.
    NonComposableInput { position: usize },
}

display_error! { error HochschildError {
    Self::DifferentialSquare { degree } => "the bar differential square is nonzero at degree {degree}";
    Self::CoordinateCount { expected, got } => "cochain has {got} coordinates, expected {expected}";
    Self::WrongInputDegree { expected, got } => "bar input has degree {got}, expected {expected}";
    Self::VertexOutOfRange { vertex, num_vertices } => "vertex {vertex} is outside 0..{num_vertices}";
    Self::BasisOutOfRange { position, index } => "bar input index {index} at position {position} is outside the basis";
    Self::TrivialInput { position } => "bar input at position {position} is a vertex idempotent";
    Self::NonComposableInput { position } => "bar input words at positions {position} and {} do not compose", position + 1;
}}

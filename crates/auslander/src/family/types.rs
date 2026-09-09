use std::sync::Arc;

use crate::algebra::Algebra;
use crate::field::Fp;
use crate::module::ModuleError;
use crate::quiver::ArrowId;

/// A coordinate in the arrow-major, row-major family layout.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FamilyCoordinate {
    pub(super) index: usize,
    pub(super) arrow: ArrowId,
    pub(super) row: usize,
    pub(super) column: usize,
}

impl FamilyCoordinate {
    accessor_methods! {
        /// The flat index in the family coordinate vector.
        pub index() -> usize = |this| this.index;
        /// The arrow whose matrix contains this coordinate.
        pub arrow() -> ArrowId = |this| this.arrow;
        /// The row inside the arrow matrix.
        pub row() -> usize = |this| this.row;
        /// The column inside the arrow matrix.
        pub column() -> usize = |this| this.column;
    }
}

/// A contiguous coordinate range for one arrow matrix.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FamilyCoordinateRange {
    pub(super) arrow: ArrowId,
    pub(super) start: usize,
    pub(super) length: usize,
}

impl FamilyCoordinateRange {
    accessor_methods! {
        /// The arrow whose matrix owns this range.
        pub arrow() -> ArrowId = |this| this.arrow;
        /// The first flat coordinate index in this range.
        pub start() -> usize = |this| this.start;
        /// The number of coordinates in this range.
        pub length() -> usize = |this| this.length;
    }

    /// The exclusive end index of this range.
    pub fn end(&self) -> usize {
        self.start + self.length
    }
}

/// The shape and coordinate range of one arrow matrix.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FamilyArrowLayout {
    pub(super) arrow: ArrowId,
    pub(super) source: u32,
    pub(super) target: u32,
    pub(super) rows: usize,
    pub(super) columns: usize,
    pub(super) range: FamilyCoordinateRange,
}

impl FamilyArrowLayout {
    accessor_methods! {
        /// The arrow identified by this layout.
        pub arrow() -> ArrowId = |this| this.arrow;
        /// The source vertex of the arrow.
        pub source() -> u32 = |this| this.source;
        /// The target vertex of the arrow.
        pub target() -> u32 = |this| this.target;
        /// The number of rows in the arrow matrix.
        pub rows() -> usize = |this| this.rows;
        /// The number of columns in the arrow matrix.
        pub columns() -> usize = |this| this.columns;
        /// The flat coordinate range of the arrow matrix.
        pub coordinate_range() -> FamilyCoordinateRange = |this| this.range;
    }
}

/// The fixed dimensions and deterministic map layout of a module family.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FamilyLayout {
    pub(super) dimensions: Vec<usize>,
    pub(super) arrows: Vec<FamilyArrowLayout>,
    pub(super) coordinates: Vec<FamilyCoordinate>,
    pub(super) hom_offsets: Vec<usize>,
    pub(super) hom_variable_count: usize,
}

impl FamilyLayout {
    accessor_methods! {
        /// The dimension vector, indexed by vertex.
        pub dimensions() -> &[usize] = |this| &this.dimensions;
        /// Arrow layouts in increasing arrow-id order.
        pub arrows() -> &[FamilyArrowLayout] = |this| &this.arrows;
        /// Coordinates in arrow-major, row-major order.
        pub coordinates() -> &[FamilyCoordinate] = |this| &this.coordinates;
        /// The number of arrow-matrix coordinates.
        pub coordinate_count() -> usize = |this| this.coordinates.len();
        /// The number of Hom variables for two fibers with this dimension vector.
        pub hom_variable_count() -> usize = |this| this.hom_variable_count;
    }
}

/// A fixed map entry in a family specification.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FamilyFixedEntry {
    pub(super) arrow: ArrowId,
    pub(super) row: usize,
    pub(super) column: usize,
    pub(super) value: Fp,
}

impl FamilyFixedEntry {
    /// Creates a fixed entry. The family checks the value against its field.
    pub fn new(arrow: ArrowId, row: usize, column: usize, value: Fp) -> Self {
        Self {
            arrow,
            row,
            column,
            value,
        }
    }

    accessor_methods! {
        /// The arrow whose matrix contains this entry.
        pub arrow() -> ArrowId = |this| this.arrow;
        /// The row inside the arrow matrix.
        pub row() -> usize = |this| this.row;
        /// The column inside the arrow matrix.
        pub column() -> usize = |this| this.column;
        /// The fixed field element.
        pub value() -> Fp = |this| this.value;
    }
}

/// A named parameter position in a family specification.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FamilyParameter {
    pub(super) name: String,
    pub(super) arrow: ArrowId,
    pub(super) row: usize,
    pub(super) column: usize,
}

impl FamilyParameter {
    /// Creates a named parameter position.
    pub fn new(name: impl Into<String>, arrow: ArrowId, row: usize, column: usize) -> Self {
        Self {
            name: name.into(),
            arrow,
            row,
            column,
        }
    }

    accessor_methods! {
        /// The parameter name.
        pub name() -> &str = |this| &this.name;
        /// The arrow whose matrix contains this parameter.
        pub arrow() -> ArrowId = |this| this.arrow;
        /// The row inside the arrow matrix.
        pub row() -> usize = |this| this.row;
        /// The column inside the arrow matrix.
        pub column() -> usize = |this| this.column;
    }
}

/// A compiled parameter name and its flat coordinate position.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FamilyParameterPosition {
    pub(super) name: String,
    pub(super) coordinate: FamilyCoordinate,
    pub(super) index: usize,
}

impl FamilyParameterPosition {
    accessor_methods! {
        /// The parameter name.
        pub name() -> &str = |this| &this.name;
        /// The arrow-matrix coordinate assigned to this parameter.
        pub coordinate() -> FamilyCoordinate = |this| this.coordinate;
        /// The parameter index used by [`CompiledModuleFamily::specialize`].
        pub index() -> usize = |this| this.index;
    }
}

/// One factor matrix read by a relation term.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationTermLayout {
    pub(super) coefficient: Fp,
    pub(super) path: Vec<ArrowId>,
    pub(super) factors: Vec<FamilyCoordinateRange>,
}

impl RelationTermLayout {
    accessor_methods! {
        /// The relation coefficient of this path term.
        pub coefficient() -> Fp = |this| this.coefficient;
        /// The path arrows in multiplication order.
        pub path() -> &[ArrowId] = |this| &this.path;
        /// Matrix ranges for the path factors in path order.
        pub factors() -> &[FamilyCoordinateRange] = |this| &this.factors;
    }
}

/// The structural evaluation layout of one reduced relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationEvaluationLayout {
    pub(super) relation: usize,
    pub(super) source: u32,
    pub(super) target: u32,
    pub(super) rows: usize,
    pub(super) columns: usize,
    pub(super) terms: Vec<RelationTermLayout>,
    pub(super) coordinate_support: Vec<FamilyCoordinateRange>,
}

impl RelationEvaluationLayout {
    accessor_methods! {
        /// The relation index in [`Algebra::relations`].
        pub relation() -> usize = |this| this.relation;
        /// The source vertex of the relation.
        pub source() -> u32 = |this| this.source;
        /// The target vertex of the relation.
        pub target() -> u32 = |this| this.target;
        /// The output row count of relation evaluation.
        pub rows() -> usize = |this| this.rows;
        /// The output column count of relation evaluation.
        pub columns() -> usize = |this| this.columns;
        /// Relation terms in the algebra's stored order.
        pub terms() -> &[RelationTermLayout] = |this| &this.terms;
        /// Distinct arrow-matrix ranges read by this relation.
        pub coordinate_support() -> &[FamilyCoordinateRange] = |this| &this.coordinate_support;
    }
}

/// A variable in a vertex matrix of a Hom equation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct HomVariable {
    pub(super) index: usize,
    pub(super) vertex: u32,
    pub(super) row: usize,
    pub(super) column: usize,
}

impl HomVariable {
    accessor_methods! {
        /// The flat Hom-variable index.
        pub index() -> usize = |this| this.index;
        /// The vertex of the Hom matrix.
        pub vertex() -> u32 = |this| this.vertex;
        /// The row inside the Hom matrix.
        pub row() -> usize = |this| this.row;
        /// The column inside the Hom matrix.
        pub column() -> usize = |this| this.column;
    }
}

/// The map side supplying a coefficient in a Hom equation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum HomCoefficientSide {
    /// The target fiber map in `f_source · N(a)`.
    Target,
    /// The source fiber map in `M(a) · f_target`.
    Source,
}

/// One variable and coefficient pair in a Hom equation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct HomEquationTerm {
    pub(super) variable: HomVariable,
    pub(super) coefficient: FamilyCoordinate,
    pub(super) side: HomCoefficientSide,
}

impl HomEquationTerm {
    accessor_methods! {
        /// The Hom variable in this term.
        pub variable() -> HomVariable = |this| this.variable;
        /// The family-map coefficient coordinate in this term.
        pub coefficient() -> FamilyCoordinate = |this| this.coefficient;
        /// The side of the commuting equation.
        pub side() -> HomCoefficientSide = |this| this.side;
    }

    /// The coefficient sign in `f_source · N(a) - M(a) · f_target`.
    pub fn sign(&self) -> i8 {
        match self.side {
            HomCoefficientSide::Target => 1,
            HomCoefficientSide::Source => -1,
        }
    }
}

/// The structural coordinate layout of one commuting-square equation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HomEquationLayout {
    pub(super) index: usize,
    pub(super) arrow: ArrowId,
    pub(super) source_row: usize,
    pub(super) target_column: usize,
    pub(super) terms: Vec<HomEquationTerm>,
}

impl HomEquationLayout {
    accessor_methods! {
        /// The flat equation index.
        pub index() -> usize = |this| this.index;
        /// The arrow whose square gives this equation.
        pub arrow() -> ArrowId = |this| this.arrow;
        /// The source-vertex row of the square entry.
        pub source_row() -> usize = |this| this.source_row;
        /// The target-vertex column of the square entry.
        pub target_column() -> usize = |this| this.target_column;
        /// Terms in the equation, target side first and source side second.
        pub terms() -> &[HomEquationTerm] = |this| &this.terms;
    }
}

/// A specification error or a rejected specialization.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FamilyError {
    /// The dimension vector needs one entry per quiver vertex.
    DimensionVectorLength { expected: usize, got: usize },
    /// An arrow id is outside the algebra's quiver.
    ArrowOutOfRange { arrow: ArrowId, num_arrows: usize },
    /// A coordinate is outside its arrow matrix.
    CoordinateOutOfRange {
        arrow: ArrowId,
        row: usize,
        column: usize,
        rows: usize,
        columns: usize,
    },
    /// One arrow matrix entry count overflowed `usize`.
    MatrixEntryOverflow {
        arrow: ArrowId,
        rows: usize,
        columns: usize,
    },
    /// The total coordinate count overflowed `usize`.
    CoordinateCountOverflow,
    /// The family coordinate layout could not reserve its checked capacity.
    CoordinateAllocationFailed { coordinates: usize },
    /// The Hom variable count overflowed `usize`.
    HomVariableCountOverflow { vertex: u32, dimension: usize },
    /// The commuting-equation count overflowed `usize`.
    HomEquationCountOverflow {
        arrow: ArrowId,
        rows: usize,
        columns: usize,
    },
    /// The Hom equation layout could not reserve its checked capacity.
    HomEquationAllocationFailed { equations: usize },
    /// One Hom equation could not reserve its term capacity.
    HomTermAllocationFailed {
        arrow: ArrowId,
        row: usize,
        column: usize,
    },
    /// A relation output shape overflowed `usize`.
    RelationOutputOverflow {
        relation: usize,
        rows: usize,
        columns: usize,
    },
    /// A relation term layout could not reserve its factor capacity.
    RelationTermAllocationFailed { relation: usize, term: usize },
    /// A relation support layout could not reserve its checked capacity.
    RelationSupportAllocationFailed { relation: usize },
    /// A parameter name is empty.
    EmptyParameterName,
    /// A parameter name occurs more than once.
    DuplicateParameterName { name: String },
    /// Two fixed entries use one coordinate.
    DuplicateFixedCoordinate {
        arrow: ArrowId,
        row: usize,
        column: usize,
    },
    /// Two parameters use one coordinate.
    DuplicateParameterCoordinate {
        arrow: ArrowId,
        row: usize,
        column: usize,
    },
    /// A fixed entry and a parameter use one coordinate.
    FixedParameterCollision {
        arrow: ArrowId,
        row: usize,
        column: usize,
    },
    /// A fixed value is not canonical for the family field.
    NonCanonicalFixedValue {
        arrow: ArrowId,
        row: usize,
        column: usize,
        value: u64,
    },
    /// The specialization has the wrong number of parameter values.
    ParameterCountMismatch { expected: usize, got: usize },
    /// A parameter value is not canonical for the family field.
    NonCanonicalParameterValue { index: usize, value: u64 },
    /// The filled coordinates do not define a module over the fixed algebra.
    Module(ModuleError),
}

display_error! { FamilyError {
    Self::DimensionVectorLength { expected, got } => "dimension vector has {got} entries, quiver has {expected} vertices";
    Self::ArrowOutOfRange { arrow, num_arrows } => "arrow {} outside 0..{num_arrows}", arrow.0;
    Self::CoordinateOutOfRange { arrow, row, column, rows, columns } => "coordinate ({row}, {column}) for arrow {} is outside {rows}x{columns}", arrow.0;
    Self::MatrixEntryOverflow { arrow, rows, columns } => "matrix for arrow {} has {rows}x{columns} entries, which overflow usize", arrow.0;
    Self::CoordinateCountOverflow => "the total family coordinate count overflows usize";
    Self::CoordinateAllocationFailed { coordinates } => "the family coordinate layout could not reserve {coordinates} entries";
    Self::HomVariableCountOverflow { vertex, dimension } => "Hom variables at vertex {vertex} with dimension {dimension} overflow usize";
    Self::HomEquationCountOverflow { arrow, rows, columns } => "Hom equations for arrow {} have {rows}x{columns} entries, which overflow usize", arrow.0;
    Self::HomEquationAllocationFailed { equations } => "the Hom equation layout could not reserve {equations} equations";
    Self::HomTermAllocationFailed { arrow, row, column } => "the Hom equation for arrow {} at ({row}, {column}) could not reserve its terms", arrow.0;
    Self::RelationOutputOverflow { relation, rows, columns } => "relation {relation} output has {rows}x{columns} entries, which overflow usize";
    Self::RelationTermAllocationFailed { relation, term } => "relation {relation} term {term} could not reserve its factors";
    Self::RelationSupportAllocationFailed { relation } => "relation {relation} could not reserve its coordinate support";
    Self::EmptyParameterName => "parameter name is empty";
    Self::DuplicateParameterName { name } => "parameter name {name:?} occurs more than once";
    Self::DuplicateFixedCoordinate { arrow, row, column } => "fixed coordinate ({row}, {column}) for arrow {} occurs more than once", arrow.0;
    Self::DuplicateParameterCoordinate { arrow, row, column } => "parameter coordinate ({row}, {column}) for arrow {} occurs more than once", arrow.0;
    Self::FixedParameterCollision { arrow, row, column } => "fixed coordinate ({row}, {column}) for arrow {} is also a parameter", arrow.0;
    Self::NonCanonicalFixedValue { arrow, row, column, value } => "fixed coordinate ({row}, {column}) for arrow {} has non-canonical value {value}", arrow.0;
    Self::ParameterCountMismatch { expected, got } => "specialization has {got} values, family has {expected} parameters";
    Self::NonCanonicalParameterValue { index, value } => "parameter {index} has non-canonical value {value}";
    Self::Module(error) => "specialization is not a module: {error}";
} }

error_source! { FamilyError {
    Self::Module(error) => Some(error),
    _ => None,
} }

impl From<ModuleError> for FamilyError {
    fn from(error: ModuleError) -> Self {
        Self::Module(error)
    }
}

/// A compiled fixed-pattern family of arrow-map specializations.
#[derive(Clone, Debug)]
pub struct CompiledModuleFamily {
    pub(super) algebra: Arc<Algebra>,
    pub(super) layout: FamilyLayout,
    pub(super) fixed: Vec<FamilyFixedEntry>,
    pub(super) parameters: Vec<FamilyParameterPosition>,
    pub(super) parameter_indices: std::collections::BTreeMap<String, usize>,
    pub(super) relation_evaluations: Vec<RelationEvaluationLayout>,
    pub(super) hom_equations: Vec<HomEquationLayout>,
}

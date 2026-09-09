use std::sync::Arc;

use crate::family::{
    CompiledModuleFamily, FamilyError, HomCoefficientSide, HomEquationLayout, HomEquationTerm,
};
use crate::field::{Fp, PrimeField};
use crate::hom::Morphism;
use crate::homspace::{HomSpace, row_times};
use crate::linalg::{DenseMat, SparseMat, SparseRow};
use crate::module::Module;
use crate::quiver::ArrowId;

use super::{InterfacePartition, InterfaceRegion};

/// A rejected fixed-interior Hom plan or fiber.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InterfaceFamilyHomError {
    /// The family and partition use distinct algebra objects.
    DifferentAlgebra,
    /// A parameter is on an arrow outside the interface.
    ParameterOutsideInterface {
        index: usize,
        name: String,
        arrow: ArrowId,
        source: u32,
        target: u32,
    },
    /// The anchor values do not define a valid family fiber.
    InvalidAnchor(FamilyError),
    /// The source values do not define a valid family fiber.
    InvalidSource(FamilyError),
    /// The target values do not define a valid family fiber.
    InvalidTarget(FamilyError),
    /// The source module uses another algebra object.
    SourceAlgebraMismatch,
    /// The target module uses another algebra object.
    TargetAlgebraMismatch,
    /// The source module has another dimension vector.
    SourceDimensionMismatch,
    /// The target module has another dimension vector.
    TargetDimensionMismatch,
    /// The source module does not match the family fixed coordinates.
    SourceOutsideFamily {
        arrow: ArrowId,
        row: usize,
        column: usize,
    },
    /// The target module does not match the family fixed coordinates.
    TargetOutsideFamily {
        arrow: ArrowId,
        row: usize,
        column: usize,
    },
}

display_error! { InterfaceFamilyHomError {
    Self::DifferentAlgebra => "the family and interface partition use different algebras";
    Self::ParameterOutsideInterface { index, name, arrow, source, target } => "parameter {index} {name:?} is on arrow {} from {source} to {target}, outside the interface", arrow.0;
    Self::InvalidAnchor(error) => "anchor fiber is invalid: {error}";
    Self::InvalidSource(error) => "source fiber is invalid: {error}";
    Self::InvalidTarget(error) => "target fiber is invalid: {error}";
    Self::SourceAlgebraMismatch => "the source module uses another algebra";
    Self::TargetAlgebraMismatch => "the target module uses another algebra";
    Self::SourceDimensionMismatch => "the source module has another dimension vector";
    Self::TargetDimensionMismatch => "the target module has another dimension vector";
    Self::SourceOutsideFamily { arrow, row, column } => "the source module differs from the family at arrow {} coordinate ({row}, {column})", arrow.0;
    Self::TargetOutsideFamily { arrow, row, column } => "the target module differs from the family at arrow {} coordinate ({row}, {column})", arrow.0;
} }

error_source! { InterfaceFamilyHomError {
    Self::InvalidAnchor(error) => Some(error),
    Self::InvalidSource(error) => Some(error),
    Self::InvalidTarget(error) => Some(error),
    _ => None,
} }

/// A compiled Hom plan with the outer-arrow equations eliminated once.
///
/// Every family parameter must lie on an arrow whose endpoints are in the
/// partition interface. The anchor supplies the fixed outer maps. For a pair
/// of fibers, the returned rows are `ker(D_J K_Jᵀ) K`. Here `K` is the fixed
/// kernel basis, `J` contains interface Hom variables, and `D_J` contains
/// only interface-arrow equations and columns.
#[derive(Clone)]
pub struct InterfaceFamilyHomPlan {
    family: CompiledModuleFamily,
    partition: InterfacePartition,
    anchor_values: Vec<Fp>,
    anchor: Module,
    internal_arrows: Vec<ArrowId>,
    internal_flags: Vec<bool>,
    interface_variables: Vec<usize>,
    interface_variable_slots: Vec<Option<usize>>,
    fixed_kernel: DenseMat,
    interface_kernel_columns: DenseMat,
    fixed_equations: usize,
    fixed_rank: usize,
}

impl InterfaceFamilyHomPlan {
    /// Compiles the fixed equations from one valid anchor fiber.
    pub fn compile(
        family: &CompiledModuleFamily,
        partition: &InterfacePartition,
        anchor_values: &[Fp],
    ) -> Result<Self, InterfaceFamilyHomError> {
        if !Arc::ptr_eq(family.algebra(), partition.algebra()) {
            return Err(InterfaceFamilyHomError::DifferentAlgebra);
        }
        let internal_flags = interface_flags(partition);
        check_parameters(family, partition, &internal_flags)?;
        let anchor = family
            .specialize(anchor_values)
            .map_err(InterfaceFamilyHomError::InvalidAnchor)?;
        let field = family.algebra().field();
        let fixed = equation_matrix(family, &internal_flags, &anchor, &anchor, false);
        let fixed_rank = fixed.rank(&field);
        let fixed_kernel = fixed.kernel_basis(&field);
        let interface_variables = interface_variables(family, &internal_flags);
        let interface_variable_slots =
            variable_slots(family.layout().hom_variable_count(), &interface_variables);
        let interface_kernel_columns = select_columns(&fixed_kernel, &interface_variables);
        let internal_arrows = internal_flags
            .iter()
            .enumerate()
            .filter_map(|(index, &internal)| internal.then_some(ArrowId(index as u32)))
            .collect();
        Ok(Self {
            family: family.clone(),
            partition: partition.clone(),
            anchor_values: anchor_values.to_vec(),
            anchor,
            internal_arrows,
            internal_flags,
            interface_variables,
            interface_variable_slots,
            fixed_kernel,
            interface_kernel_columns,
            fixed_equations: fixed.rows(),
            fixed_rank,
        })
    }

    accessor_methods! {
        /// The compiled module family.
        pub family() -> &CompiledModuleFamily = |this| &this.family;
        /// The checked left-interface-right partition.
        pub partition() -> &InterfacePartition = |this| &this.partition;
        /// Anchor values in the family parameter order.
        pub anchor_values() -> &[Fp] = |this| &this.anchor_values;
        /// The valid anchor fiber used for fixed equations.
        pub anchor() -> &Module = |this| &this.anchor;
        /// Arrows with both endpoints in the interface.
        pub internal_arrows() -> &[ArrowId] = |this| &this.internal_arrows;
        /// Global Hom-variable indices used by interface-arrow equations.
        pub interface_variables() -> &[usize] = |this| &this.interface_variables;
        /// The canonical kernel basis `K` of the fixed equations.
        pub fixed_kernel_basis() -> &DenseMat = |this| &this.fixed_kernel;
        /// Columns of `K` used by interface-arrow equations.
        pub interface_kernel_columns() -> &DenseMat = |this| &this.interface_kernel_columns;
        /// Number of nonzero fixed outer-arrow equations.
        pub fixed_equations() -> usize = |this| this.fixed_equations;
        /// Rank of the fixed outer-arrow equations.
        pub fixed_rank() -> usize = |this| this.fixed_rank;
        /// Dimension of the fixed equation kernel.
        pub fixed_kernel_dimension() -> usize = |this| this.fixed_kernel.rows();
    }

    /// Computes a Hom space from two family fibers.
    pub fn compute(
        &self,
        source_values: &[Fp],
        target_values: &[Fp],
    ) -> Result<InterfaceFamilyHom, InterfaceFamilyHomError> {
        let source = self
            .family
            .specialize(source_values)
            .map_err(InterfaceFamilyHomError::InvalidSource)?;
        let target = self
            .family
            .specialize(target_values)
            .map_err(InterfaceFamilyHomError::InvalidTarget)?;
        self.compute_modules(&source, &target)
    }

    /// Computes a Hom space from already validated modules with this shape.
    ///
    /// The modules must match the family's fixed and zero coordinates. Their
    /// parameter coordinates may differ from the anchor.
    pub fn compute_modules(
        &self,
        source: &Module,
        target: &Module,
    ) -> Result<InterfaceFamilyHom, InterfaceFamilyHomError> {
        check_module(self, source, true)?;
        check_module(self, target, false)?;
        let field = source.field();
        let interface = interface_equation_matrix(self, source, target);
        let reduced = interface.mul(&self.interface_kernel_columns.transpose(), &field);
        let coefficients = reduced.kernel_basis(&field);
        let flat = lift_rows(&coefficients, &self.fixed_kernel, &field);
        let space = HomSpace::from_checked_flat(source, target, flat);
        let work = InterfaceFamilyHomWork {
            fixed_equations: self.fixed_equations,
            fixed_rank: self.fixed_rank,
            fixed_kernel_dimension: self.fixed_kernel.rows(),
            interface_variables: self.interface_variables.len(),
            interface_equations: interface.rows(),
            interface_rank: reduced.rank(&field),
            hom_dimension: space.dim(),
        };
        Ok(InterfaceFamilyHom {
            plan: self.clone(),
            space,
            work,
        })
    }

    /// Computes a Hom space from two family fibers.
    pub fn hom_space(
        &self,
        source_values: &[Fp],
        target_values: &[Fp],
    ) -> Result<InterfaceFamilyHom, InterfaceFamilyHomError> {
        self.compute(source_values, target_values)
    }

    /// Rebuilds the plan and compares its fixed layout and kernel basis.
    pub fn verify(&self) -> bool {
        let Ok(rebuilt) = Self::compile(&self.family, &self.partition, &self.anchor_values) else {
            return false;
        };
        self.internal_arrows == rebuilt.internal_arrows
            && self.fixed_equations == rebuilt.fixed_equations
            && self.fixed_rank == rebuilt.fixed_rank
            && self.fixed_kernel == rebuilt.fixed_kernel
            && self.interface_variables == rebuilt.interface_variables
            && self.interface_kernel_columns == rebuilt.interface_kernel_columns
    }
}

debug_fields! { InterfaceFamilyHomPlan |this| {
    "family" => this.family;
    "partition" => this.partition;
    "anchor_values" => this.anchor_values;
    "fixed_equations" => this.fixed_equations;
    "fixed_rank" => this.fixed_rank;
    "fixed_kernel_dimension" => this.fixed_kernel.rows();
    "internal_arrows" => this.internal_arrows;
    "interface_variables" => this.interface_variables;
} }

/// Exact work counts for one fixed-interior Hom specialization.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InterfaceFamilyHomWork {
    /// Nonzero commuting equations eliminated at plan compilation.
    pub fixed_equations: usize,
    /// Rank of the fixed equation matrix.
    pub fixed_rank: usize,
    /// Rows of the canonical fixed kernel basis `K`.
    pub fixed_kernel_dimension: usize,
    /// Hom variables used by internal-interface equations.
    pub interface_variables: usize,
    /// Nonzero internal-interface equations assembled for this pair.
    pub interface_equations: usize,
    /// Rank of `D_J K_Jᵀ` for this pair.
    pub interface_rank: usize,
    /// Dimension of the resulting Hom space.
    pub hom_dimension: usize,
}

/// A Hom space produced by a fixed-interior plan.
#[derive(Clone)]
pub struct InterfaceFamilyHom {
    plan: InterfaceFamilyHomPlan,
    space: HomSpace,
    work: InterfaceFamilyHomWork,
}

impl InterfaceFamilyHom {
    accessor_methods! {
        /// The fixed-interior plan.
        pub plan() -> &InterfaceFamilyHomPlan = |this| &this.plan;
        /// The canonical Hom space.
        pub space() -> &HomSpace = |this| &this.space;
        /// The source module.
        pub source() -> &Module = |this| this.space.source();
        /// The target module.
        pub target() -> &Module = |this| this.space.target();
        /// `dim_k Hom(source, target)`.
        pub dim() -> usize = |this| this.space.dim();
        /// Exact fixed and per-fiber equation counts.
        pub work() -> InterfaceFamilyHomWork = |this| this.work;
        /// Basis morphism `index` in canonical flat-row order.
        pub basis_morphism(index: usize) -> Morphism = |this| this.space.basis_morphism(index);
    }

    /// Iterates over basis morphisms in canonical flat-row order.
    pub fn basis_iter(&self) -> impl Iterator<Item = Morphism> + '_ {
        self.space.basis_iter()
    }

    /// Returns the canonical basis morphisms.
    pub fn basis(&self) -> &[Morphism] {
        self.space.basis()
    }

    /// Compares the lifted basis with a freshly built generic Hom space.
    pub fn verify(&self) -> bool {
        let Ok(generic) = HomSpace::new(self.source(), self.target()) else {
            return false;
        };
        same_basis(&self.space, &generic)
    }
}

debug_fields! { InterfaceFamilyHom |this| {
    "source_dimensions" => this.source().dim_vector();
    "target_dimensions" => this.target().dim_vector();
    "dimension" => this.dim();
    "work" => this.work;
} }

fn interface_flags(partition: &InterfacePartition) -> Vec<bool> {
    let quiver = partition.algebra().quiver();
    (0..quiver.num_arrows())
        .map(|index| {
            let arrow = ArrowId(index as u32);
            partition.region(quiver.source(arrow)) == InterfaceRegion::Interface
                && partition.region(quiver.target(arrow)) == InterfaceRegion::Interface
        })
        .collect()
}

fn interface_variables(family: &CompiledModuleFamily, internal_flags: &[bool]) -> Vec<usize> {
    let mut variables = family
        .hom_equations()
        .iter()
        .filter(|equation| internal_flags[equation.arrow().index()])
        .flat_map(|equation| equation.terms().iter())
        .map(|term| term.variable().index())
        .collect::<Vec<_>>();
    variables.sort_unstable();
    variables.dedup();
    variables
}

fn variable_slots(width: usize, variables: &[usize]) -> Vec<Option<usize>> {
    let mut slots = vec![None; width];
    for (slot, &variable) in variables.iter().enumerate() {
        slots[variable] = Some(slot);
    }
    slots
}

fn select_columns(matrix: &DenseMat, columns: &[usize]) -> DenseMat {
    let mut selected = DenseMat::zero(matrix.rows(), columns.len());
    for row in 0..matrix.rows() {
        for (output, &input) in columns.iter().enumerate() {
            selected.set(row, output, matrix.get(row, input));
        }
    }
    selected
}

fn check_parameters(
    family: &CompiledModuleFamily,
    partition: &InterfacePartition,
    internal_flags: &[bool],
) -> Result<(), InterfaceFamilyHomError> {
    let quiver = partition.algebra().quiver();
    for (index, parameter) in family.parameters().iter().enumerate() {
        let coordinate = parameter.coordinate();
        let arrow = coordinate.arrow();
        if !internal_flags[arrow.index()] {
            return Err(InterfaceFamilyHomError::ParameterOutsideInterface {
                index,
                name: parameter.name().to_owned(),
                arrow,
                source: quiver.source(arrow),
                target: quiver.target(arrow),
            });
        }
    }
    Ok(())
}

fn check_module(
    plan: &InterfaceFamilyHomPlan,
    module: &Module,
    source: bool,
) -> Result<(), InterfaceFamilyHomError> {
    if !Arc::ptr_eq(module.algebra(), plan.family.algebra()) {
        return Err(if source {
            InterfaceFamilyHomError::SourceAlgebraMismatch
        } else {
            InterfaceFamilyHomError::TargetAlgebraMismatch
        });
    }
    if module.dim_vector() != plan.family.layout().dimensions() {
        return Err(if source {
            InterfaceFamilyHomError::SourceDimensionMismatch
        } else {
            InterfaceFamilyHomError::TargetDimensionMismatch
        });
    }
    if let Some((arrow, row, column)) = first_pattern_mismatch(plan, module) {
        return Err(if source {
            InterfaceFamilyHomError::SourceOutsideFamily { arrow, row, column }
        } else {
            InterfaceFamilyHomError::TargetOutsideFamily { arrow, row, column }
        });
    }
    Ok(())
}

fn first_pattern_mismatch(
    plan: &InterfaceFamilyHomPlan,
    module: &Module,
) -> Option<(ArrowId, usize, usize)> {
    plan.family
        .layout()
        .coordinates()
        .iter()
        .find_map(|coordinate| {
            let parameter = plan
                .family
                .parameters()
                .iter()
                .any(|entry| entry.coordinate() == *coordinate);
            if parameter {
                return None;
            }
            let expected = plan
                .family
                .fixed_entries()
                .iter()
                .find(|entry| {
                    entry.arrow() == coordinate.arrow()
                        && entry.row() == coordinate.row()
                        && entry.column() == coordinate.column()
                })
                .map_or(Fp::ZERO, |entry| entry.value());
            (module
                .map(coordinate.arrow())
                .get(coordinate.row(), coordinate.column())
                != expected)
                .then_some((coordinate.arrow(), coordinate.row(), coordinate.column()))
        })
}

fn equation_matrix(
    family: &CompiledModuleFamily,
    internal_flags: &[bool],
    source: &Module,
    target: &Module,
    keep_internal: bool,
) -> DenseMat {
    let field = source.field();
    let rows: Vec<SparseRow> = family
        .hom_equations()
        .iter()
        .filter(|equation| internal_flags[equation.arrow().index()] == keep_internal)
        .map(|equation| equation_row(equation, source, target, &field))
        .filter(|row| !row.is_zero())
        .collect();
    SparseMat::from_rows(rows, family.layout().hom_variable_count()).to_dense()
}

fn interface_equation_matrix(
    plan: &InterfaceFamilyHomPlan,
    source: &Module,
    target: &Module,
) -> DenseMat {
    let field = source.field();
    let rows = plan
        .family
        .hom_equations()
        .iter()
        .filter(|equation| plan.internal_flags[equation.arrow().index()])
        .map(|equation| {
            compact_equation_row(
                equation,
                source,
                target,
                &field,
                &plan.interface_variable_slots,
            )
        })
        .filter(|row| !row.is_zero())
        .collect();
    SparseMat::from_rows(rows, plan.interface_variables.len()).to_dense()
}

fn equation_row(
    equation: &HomEquationLayout,
    source: &Module,
    target: &Module,
    field: &PrimeField,
) -> SparseRow {
    let entries = equation
        .terms()
        .iter()
        .map(|term| equation_entry(term, source, target, field));
    SparseRow::from_entries(entries.collect(), field)
}

fn compact_equation_row(
    equation: &HomEquationLayout,
    source: &Module,
    target: &Module,
    field: &PrimeField,
    slots: &[Option<usize>],
) -> SparseRow {
    let entries = equation.terms().iter().map(|term| {
        let (variable, value) = equation_entry(term, source, target, field);
        let variable =
            slots[variable].expect("an interface equation uses an indexed interface variable");
        (variable, value)
    });
    SparseRow::from_entries(entries.collect(), field)
}

fn equation_entry(
    term: &HomEquationTerm,
    source: &Module,
    target: &Module,
    field: &PrimeField,
) -> (usize, Fp) {
    let coordinate = term.coefficient();
    let map = match term.side() {
        HomCoefficientSide::Target => target.map(coordinate.arrow()),
        HomCoefficientSide::Source => source.map(coordinate.arrow()),
    };
    let value = map.get(coordinate.row(), coordinate.column());
    let value = match term.side() {
        HomCoefficientSide::Target => value,
        HomCoefficientSide::Source => field.neg(value),
    };
    (term.variable().index(), value)
}

fn lift_rows(coefficients: &DenseMat, kernel: &DenseMat, field: &PrimeField) -> DenseMat {
    let mut flat = DenseMat::zero(coefficients.rows(), kernel.cols());
    for row in 0..coefficients.rows() {
        let lifted = row_times(coefficients.row(row), kernel, field);
        for (column, &value) in lifted.iter().enumerate() {
            flat.set(row, column, value);
        }
    }
    flat
}

fn same_basis(left: &HomSpace, right: &HomSpace) -> bool {
    left.dim() == right.dim()
        && (0..left.dim())
            .all(|index| same_morphism(&left.basis_morphism(index), &right.basis_morphism(index)))
}

fn same_morphism(left: &Morphism, right: &Morphism) -> bool {
    left.source().ptr_eq(right.source())
        && left.target().ptr_eq(right.target())
        && (0..left.source().algebra().quiver().num_vertices())
            .all(|vertex| left.map_at(vertex) == right.map_at(vertex))
}

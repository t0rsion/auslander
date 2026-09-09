use std::sync::Arc;

use super::{InterfaceHomError, InterfacePartition, InterfaceRegion};
use crate::field::Fp;
use crate::hom::Morphism;
use crate::homspace::{HomSpace, row_times};
use crate::linalg::DenseMat;
use crate::module::Module;
use crate::quiver::ArrowId;

#[derive(Clone, Debug)]
struct PieceLayout {
    offsets: Vec<Option<usize>>,
    width: usize,
}

impl PieceLayout {
    fn new(
        regions: &[InterfaceRegion],
        excluded: InterfaceRegion,
        source: &[usize],
        target: &[usize],
    ) -> Result<Self, InterfaceHomError> {
        let mut offsets = vec![None; regions.len()];
        let mut width = 0usize;
        for vertex in 0..regions.len() {
            if regions[vertex] == excluded {
                continue;
            }
            offsets[vertex] = Some(width);
            width = width
                .checked_add(
                    source[vertex]
                        .checked_mul(target[vertex])
                        .ok_or(InterfaceHomError::VariableCountOverflow)?,
                )
                .ok_or(InterfaceHomError::VariableCountOverflow)?;
        }
        Ok(Self { offsets, width })
    }

    fn contains(&self, vertex: usize) -> bool {
        self.offsets[vertex].is_some()
    }
}

/// Fixed layouts for an interface equalizer calculation.
#[derive(Clone)]
pub struct InterfaceHomPlan {
    partition: InterfacePartition,
    source_dimensions: Vec<usize>,
    target_dimensions: Vec<usize>,
    left: PieceLayout,
    right: PieceLayout,
    interface_width: usize,
}

impl InterfaceHomPlan {
    /// Compiles variable layouts for fixed source and target dimensions.
    pub fn compile(
        partition: &InterfacePartition,
        source_dimensions: &[usize],
        target_dimensions: &[usize],
    ) -> Result<Self, InterfaceHomError> {
        check_dimension_length(partition, "source", source_dimensions)?;
        check_dimension_length(partition, "target", target_dimensions)?;
        let left = PieceLayout::new(
            &partition.regions,
            InterfaceRegion::Right,
            source_dimensions,
            target_dimensions,
        )?;
        let right = PieceLayout::new(
            &partition.regions,
            InterfaceRegion::Left,
            source_dimensions,
            target_dimensions,
        )?;
        let interface_width =
            checked_vertex_width(partition.interface(), source_dimensions, target_dimensions)?;
        Ok(Self {
            partition: partition.clone(),
            source_dimensions: source_dimensions.to_vec(),
            target_dimensions: target_dimensions.to_vec(),
            left,
            right,
            interface_width,
        })
    }

    accessor_methods! {
        /// The checked partition.
        pub partition() -> &InterfacePartition = |this| &this.partition;
        /// Fixed source dimensions.
        pub source_dimensions() -> &[usize] = |this| &this.source_dimensions;
        /// Fixed target dimensions.
        pub target_dimensions() -> &[usize] = |this| &this.target_dimensions;
        /// Number of duplicated interface map coordinates.
        pub interface_width() -> usize = |this| this.interface_width;
    }

    /// Computes a basis as the equalizer of the two piece Hom spaces.
    pub fn compute(
        &self,
        source: &Module,
        target: &Module,
    ) -> Result<InterfaceHom, InterfaceHomError> {
        self.check_specialization(source, target)?;
        let field = source.field();
        let left_constraints = piece_constraints(&self.left, source, target);
        let right_constraints = piece_constraints(&self.right, source, target);
        let left_basis = left_constraints.kernel_basis(&field);
        let right_basis = right_constraints.kernel_basis(&field);
        let left_restriction = restriction_matrix(
            &self.left,
            &left_basis,
            self.partition.interface(),
            source,
            target,
        );
        let right_restriction = restriction_matrix(
            &self.right,
            &right_basis,
            self.partition.interface(),
            source,
            target,
        );
        let equalizer = equalizer_constraints(&left_restriction, &right_restriction, &field);
        let coefficients = equalizer.kernel_basis(&field);
        let basis = lift_basis(
            self,
            source,
            target,
            &left_basis,
            &right_basis,
            &coefficients,
        )?;
        let work = InterfaceHomWork {
            left_variables: self.left.width,
            right_variables: self.right.width,
            left_equations: left_constraints.rows(),
            right_equations: right_constraints.rows(),
            left_hom_dimension: left_basis.rows(),
            right_hom_dimension: right_basis.rows(),
            interface_coordinates: self.interface_width,
            equalizer_rank: equalizer.rank(&field),
        };
        Ok(InterfaceHom {
            plan: self.clone(),
            source: source.clone(),
            target: target.clone(),
            basis,
            work,
        })
    }

    fn check_specialization(
        &self,
        source: &Module,
        target: &Module,
    ) -> Result<(), InterfaceHomError> {
        for (endpoint, module, dimensions) in [
            ("source", source, self.source_dimensions.as_slice()),
            ("target", target, self.target_dimensions.as_slice()),
        ] {
            if !Arc::ptr_eq(module.algebra(), self.partition.algebra()) {
                return Err(InterfaceHomError::DifferentAlgebra { endpoint });
            }
            if module.dim_vector() != dimensions {
                return Err(InterfaceHomError::DimensionVectorMismatch { endpoint });
            }
        }
        Ok(())
    }
}

debug_fields! { InterfaceHomPlan |this| {
    "partition" => this.partition;
    "source_dimensions" => this.source_dimensions;
    "target_dimensions" => this.target_dimensions;
    "left_variables" => this.left.width;
    "right_variables" => this.right.width;
    "interface_width" => this.interface_width;
} }

fn check_dimension_length(
    partition: &InterfacePartition,
    endpoint: &'static str,
    dimensions: &[usize],
) -> Result<(), InterfaceHomError> {
    let expected = partition.regions.len();
    if dimensions.len() != expected {
        return Err(InterfaceHomError::DimensionVectorLength {
            endpoint,
            expected,
            got: dimensions.len(),
        });
    }
    Ok(())
}

fn checked_vertex_width(
    vertices: &[u32],
    source: &[usize],
    target: &[usize],
) -> Result<usize, InterfaceHomError> {
    vertices.iter().try_fold(0usize, |total, &vertex| {
        let vertex = vertex as usize;
        let width = source[vertex]
            .checked_mul(target[vertex])
            .ok_or(InterfaceHomError::VariableCountOverflow)?;
        total
            .checked_add(width)
            .ok_or(InterfaceHomError::VariableCountOverflow)
    })
}

fn piece_constraints(layout: &PieceLayout, source: &Module, target: &Module) -> DenseMat {
    let quiver = source.algebra().quiver();
    let mut equations = Vec::new();
    for index in 0..quiver.num_arrows() {
        let arrow = ArrowId(index as u32);
        let (u, v) = (quiver.source(arrow) as usize, quiver.target(arrow) as usize);
        if !(layout.contains(u) && layout.contains(v)) {
            continue;
        }
        append_arrow_equations(layout, source, target, arrow, &mut equations);
    }
    let equations: Vec<Vec<Fp>> = equations
        .into_iter()
        .filter(|row| row.iter().any(|entry| !entry.is_zero()))
        .collect();
    DenseMat::from_rows_with_cols(&equations, layout.width)
}

fn append_arrow_equations(
    layout: &PieceLayout,
    source: &Module,
    target: &Module,
    arrow: ArrowId,
    equations: &mut Vec<Vec<Fp>>,
) {
    let field = source.field();
    let quiver = source.algebra().quiver();
    let (u, v) = (quiver.source(arrow) as usize, quiver.target(arrow) as usize);
    let source_map = source.map(arrow);
    let target_map = target.map(arrow);
    for row_index in 0..source.dim_vector()[u] {
        for column_index in 0..target.dim_vector()[v] {
            let mut row = vec![Fp::ZERO; layout.width];
            add_source_block(
                &mut row,
                layout.offsets[u].expect("the piece contains the arrow source"),
                row_index,
                target.dim_vector()[u],
                target_map,
                column_index,
                &field,
            );
            add_target_block(
                &mut row,
                layout.offsets[v].expect("the piece contains the arrow target"),
                column_index,
                target.dim_vector()[v],
                source_map,
                row_index,
                &field,
            );
            equations.push(row);
        }
    }
}

fn add_source_block(
    equation: &mut [Fp],
    offset: usize,
    row: usize,
    width: usize,
    target_map: &DenseMat,
    column: usize,
    field: &crate::field::PrimeField,
) {
    for inner in 0..target_map.rows() {
        let index = offset + row * width + inner;
        equation[index] = field.add(equation[index], target_map.get(inner, column));
    }
}

fn add_target_block(
    equation: &mut [Fp],
    offset: usize,
    column: usize,
    width: usize,
    source_map: &DenseMat,
    row: usize,
    field: &crate::field::PrimeField,
) {
    for inner in 0..source_map.cols() {
        let index = offset + inner * width + column;
        equation[index] = field.add(equation[index], field.neg(source_map.get(row, inner)));
    }
}

fn restriction_matrix(
    layout: &PieceLayout,
    basis: &DenseMat,
    interface: &[u32],
    source: &Module,
    target: &Module,
) -> DenseMat {
    let width = interface.iter().fold(0usize, |total, &vertex| {
        let block = source
            .dim_at(vertex)
            .checked_mul(target.dim_at(vertex))
            .expect("the plan checked each interface block");
        total
            .checked_add(block)
            .expect("the plan checked the interface width")
    });
    let mut restriction = DenseMat::zero(basis.rows(), width);
    let mut output = 0;
    for &vertex in interface {
        let block = source.dim_at(vertex) * target.dim_at(vertex);
        let input = layout.offsets[vertex as usize].expect("both pieces contain the interface");
        for row in 0..basis.rows() {
            for column in 0..block {
                restriction.set(row, output + column, basis.get(row, input + column));
            }
        }
        output += block;
    }
    restriction
}

fn equalizer_constraints(
    left: &DenseMat,
    right: &DenseMat,
    field: &crate::field::PrimeField,
) -> DenseMat {
    debug_assert_eq!(left.cols(), right.cols());
    let mut equations = DenseMat::zero(left.cols(), left.rows() + right.rows());
    for coordinate in 0..left.cols() {
        for basis in 0..left.rows() {
            equations.set(coordinate, basis, left.get(basis, coordinate));
        }
        for basis in 0..right.rows() {
            equations.set(
                coordinate,
                left.rows() + basis,
                field.neg(right.get(basis, coordinate)),
            );
        }
    }
    equations
}

fn lift_basis(
    plan: &InterfaceHomPlan,
    source: &Module,
    target: &Module,
    left_basis: &DenseMat,
    right_basis: &DenseMat,
    coefficients: &DenseMat,
) -> Result<Vec<Morphism>, InterfaceHomError> {
    let field = source.field();
    (0..coefficients.rows())
        .map(|basis| {
            let row = coefficients.row(basis);
            let left = row_times(&row[..left_basis.rows()], left_basis, &field);
            let right = row_times(&row[left_basis.rows()..], right_basis, &field);
            let maps = merge_piece_rows(plan, source, target, &left, &right);
            Morphism::new(source, target, maps)
                .map_err(|error| InterfaceHomError::Lift { basis, error })
        })
        .collect()
}

fn merge_piece_rows(
    plan: &InterfaceHomPlan,
    source: &Module,
    target: &Module,
    left: &[Fp],
    right: &[Fp],
) -> Vec<DenseMat> {
    (0..source.algebra().quiver().num_vertices())
        .map(|vertex| {
            let width = source.dim_at(vertex) * target.dim_at(vertex);
            let (row, offset) = match plan.partition.region(vertex) {
                InterfaceRegion::Left | InterfaceRegion::Interface => (
                    left,
                    plan.left.offsets[vertex as usize]
                        .expect("the left piece contains this vertex"),
                ),
                InterfaceRegion::Right => (
                    right,
                    plan.right.offsets[vertex as usize]
                        .expect("the right piece contains this vertex"),
                ),
            };
            DenseMat::from_flat(
                source.dim_at(vertex),
                target.dim_at(vertex),
                &row[offset..offset + width],
            )
        })
        .collect()
}

/// Exact dimensions of the two piece systems and their equalizer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InterfaceHomWork {
    /// Variables in the left piece, including the interface.
    pub left_variables: usize,
    /// Variables in the right piece, including the interface.
    pub right_variables: usize,
    /// Nonzero commuting-square equations in the left piece.
    pub left_equations: usize,
    /// Nonzero commuting-square equations in the right piece.
    pub right_equations: usize,
    /// Dimension of the left piece Hom space.
    pub left_hom_dimension: usize,
    /// Dimension of the right piece Hom space.
    pub right_hom_dimension: usize,
    /// Vertex-map coordinates compared on the interface.
    pub interface_coordinates: usize,
    /// Rank of the interface compatibility system.
    pub equalizer_rank: usize,
}

/// A Hom basis lifted from a checked piece equalizer.
#[derive(Clone)]
pub struct InterfaceHom {
    plan: InterfaceHomPlan,
    source: Module,
    target: Module,
    basis: Vec<Morphism>,
    work: InterfaceHomWork,
}

impl InterfaceHom {
    accessor_methods! {
        /// The compiled separator plan.
        pub plan() -> &InterfaceHomPlan = |this| &this.plan;
        /// The source module.
        pub source() -> &Module = |this| &this.source;
        /// The target module.
        pub target() -> &Module = |this| &this.target;
        /// The equalizer basis.
        pub basis() -> &[Morphism] = |this| &this.basis;
        /// `dim_k Hom(source, target)`.
        pub dim() -> usize = |this| this.basis.len();
        /// Exact equation and rank counts.
        pub work() -> InterfaceHomWork = |this| this.work;
    }

    /// Checks that the lifted basis spans the generic global Hom space.
    pub fn verify(&self) -> bool {
        let Ok(space) = HomSpace::new(&self.source, &self.target) else {
            return false;
        };
        let Ok(lifted) = space.subspace(&self.basis) else {
            return false;
        };
        lifted == space.full_subspace()
    }
}

debug_fields! { InterfaceHom |this| {
    "source_dimensions" => this.source.dim_vector();
    "target_dimensions" => this.target.dim_vector();
    "dimension" => this.basis.len();
    "work" => this.work;
} }

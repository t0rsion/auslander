use std::sync::Arc;

use crate::algebra::Algebra;
use crate::hom::HomError;
use crate::quiver::{ArrowId, PathWord};

/// One part of a checked interface partition.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InterfaceRegion {
    /// The left interior.
    Left,
    /// The shared interface.
    Interface,
    /// The right interior.
    Right,
}

display_error! { InterfaceRegion {
    Self::Left => "left";
    Self::Interface => "interface";
    Self::Right => "right";
} }

/// A rejected separator, plan, or specialization.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InterfaceHomError {
    /// A listed vertex is outside the quiver.
    VertexOutOfRange { vertex: u32, vertices: u32 },
    /// A vertex occurs in two partition parts.
    DuplicateVertex {
        vertex: u32,
        first: InterfaceRegion,
        second: InterfaceRegion,
    },
    /// A quiver vertex occurs in no partition part.
    MissingVertex { vertex: u32 },
    /// An arrow directly joins the left and right interiors.
    CrossingArrow { arrow: ArrowId },
    /// A defining relation uses both interiors.
    CrossingRelation { relation: usize },
    /// One dimension vector has the wrong length.
    DimensionVectorLength {
        endpoint: &'static str,
        expected: usize,
        got: usize,
    },
    /// A fixed Hom variable count overflowed `usize`.
    VariableCountOverflow,
    /// A specialization does not use the plan's algebra object.
    DifferentAlgebra { endpoint: &'static str },
    /// A specialization has a different dimension vector.
    DimensionVectorMismatch { endpoint: &'static str },
    /// Building one lifted global morphism failed.
    Lift { basis: usize, error: HomError },
}

display_error! { error InterfaceHomError {
    Self::VertexOutOfRange { vertex, vertices } => "vertex {vertex} is outside 0..{vertices}";
    Self::DuplicateVertex { vertex, first, second } => "vertex {vertex} occurs in both the {first} and {second} parts";
    Self::MissingVertex { vertex } => "vertex {vertex} occurs in no partition part";
    Self::CrossingArrow { arrow } => "arrow {} directly joins the left and right interiors", arrow.0;
    Self::CrossingRelation { relation } => "relation {relation} uses both the left and right interiors";
    Self::DimensionVectorLength { endpoint, expected, got } => "{endpoint} dimensions have {got} entries, expected {expected}";
    Self::VariableCountOverflow => "the fixed Hom variable count overflows usize";
    Self::DifferentAlgebra { endpoint } => "the {endpoint} module does not use the interface plan algebra";
    Self::DimensionVectorMismatch { endpoint } => "the {endpoint} module does not use the interface plan dimensions";
    Self::Lift { basis, error } => "interface basis row {basis} does not lift to a global morphism: {error}";
} }

/// A vertex partition that satisfies the separator hypotheses.
#[derive(Clone)]
pub struct InterfacePartition {
    pub(super) algebra: Arc<Algebra>,
    pub(super) regions: Vec<InterfaceRegion>,
    left: Vec<u32>,
    interface: Vec<u32>,
    right: Vec<u32>,
}

impl InterfacePartition {
    /// Checks and stores a left-interface-right partition.
    pub fn new(
        algebra: &Arc<Algebra>,
        left: &[u32],
        interface: &[u32],
        right: &[u32],
    ) -> Result<Self, InterfaceHomError> {
        let vertices = algebra.quiver().num_vertices();
        let regions = assign_regions(vertices, left, interface, right)?;
        check_arrows(algebra, &regions)?;
        check_relations(algebra, &regions)?;
        let mut left = left.to_vec();
        let mut interface = interface.to_vec();
        let mut right = right.to_vec();
        left.sort_unstable();
        interface.sort_unstable();
        right.sort_unstable();
        Ok(Self {
            algebra: algebra.clone(),
            regions,
            left,
            interface,
            right,
        })
    }

    accessor_methods! {
        /// The checked algebra.
        pub algebra() -> &Arc<Algebra> = |this| &this.algebra;
        /// Left interior vertices in increasing order.
        pub left() -> &[u32] = |this| &this.left;
        /// Interface vertices in increasing order.
        pub interface() -> &[u32] = |this| &this.interface;
        /// Right interior vertices in increasing order.
        pub right() -> &[u32] = |this| &this.right;
        /// The part containing `vertex`.
        pub region(vertex: u32) -> InterfaceRegion = |this| this.regions[vertex as usize];
    }
}

debug_fields! { InterfacePartition |this| {
    "left" => this.left;
    "interface" => this.interface;
    "right" => this.right;
} }

fn assign_regions(
    vertices: u32,
    left: &[u32],
    interface: &[u32],
    right: &[u32],
) -> Result<Vec<InterfaceRegion>, InterfaceHomError> {
    let mut assigned = vec![None; vertices as usize];
    for (region, listed) in [
        (InterfaceRegion::Left, left),
        (InterfaceRegion::Interface, interface),
        (InterfaceRegion::Right, right),
    ] {
        for &vertex in listed {
            if vertex >= vertices {
                return Err(InterfaceHomError::VertexOutOfRange { vertex, vertices });
            }
            if let Some(first) = assigned[vertex as usize] {
                return Err(InterfaceHomError::DuplicateVertex {
                    vertex,
                    first,
                    second: region,
                });
            }
            assigned[vertex as usize] = Some(region);
        }
    }
    assigned
        .into_iter()
        .enumerate()
        .map(|(vertex, region)| {
            region.ok_or(InterfaceHomError::MissingVertex {
                vertex: vertex as u32,
            })
        })
        .collect()
}

fn check_arrows(algebra: &Algebra, regions: &[InterfaceRegion]) -> Result<(), InterfaceHomError> {
    let quiver = algebra.quiver();
    for index in 0..quiver.num_arrows() {
        let arrow = ArrowId(index as u32);
        let source = regions[quiver.source(arrow) as usize];
        let target = regions[quiver.target(arrow) as usize];
        if matches!(
            (source, target),
            (InterfaceRegion::Left, InterfaceRegion::Right)
                | (InterfaceRegion::Right, InterfaceRegion::Left)
        ) {
            return Err(InterfaceHomError::CrossingArrow { arrow });
        }
    }
    Ok(())
}

fn word_interiors(algebra: &Algebra, regions: &[InterfaceRegion], word: &PathWord) -> (bool, bool) {
    let mut left = regions[word.source() as usize] == InterfaceRegion::Left;
    let mut right = regions[word.source() as usize] == InterfaceRegion::Right;
    for &arrow in word.arrows() {
        let region = regions[algebra.quiver().target(arrow) as usize];
        left |= region == InterfaceRegion::Left;
        right |= region == InterfaceRegion::Right;
    }
    (left, right)
}

fn check_relations(
    algebra: &Algebra,
    regions: &[InterfaceRegion],
) -> Result<(), InterfaceHomError> {
    for (index, relation) in algebra.relations().iter().enumerate() {
        let (mut left, mut right) = (false, false);
        for (_, word) in relation.terms() {
            let interiors = word_interiors(algebra, regions, word);
            left |= interiors.0;
            right |= interiors.1;
        }
        if left && right {
            return Err(InterfaceHomError::CrossingRelation { relation: index });
        }
    }
    Ok(())
}

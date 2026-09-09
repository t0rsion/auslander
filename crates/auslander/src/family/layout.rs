use std::sync::Arc;

use crate::algebra::Algebra;
use crate::quiver::ArrowId;

use super::types::{
    FamilyArrowLayout, FamilyCoordinate, FamilyCoordinateRange, FamilyError, FamilyLayout,
    HomVariable,
};

impl FamilyLayout {
    /// Builds a checked layout for one algebra and dimension vector.
    pub fn new(algebra: &Arc<Algebra>, dimensions: Vec<usize>) -> Result<Self, FamilyError> {
        let expected = algebra.quiver().num_vertices() as usize;
        if dimensions.len() != expected {
            return Err(FamilyError::DimensionVectorLength {
                expected,
                got: dimensions.len(),
            });
        }
        let arrows = arrow_layouts(algebra, &dimensions)?;
        let coordinates = coordinate_layout(&arrows)?;
        let (hom_offsets, hom_variable_count) = hom_variables(&dimensions)?;
        Ok(Self {
            dimensions,
            arrows,
            coordinates,
            hom_offsets,
            hom_variable_count,
        })
    }

    /// Returns the layout for `arrow`, or `None` for an unknown arrow id.
    pub fn arrow(&self, arrow: ArrowId) -> Option<&FamilyArrowLayout> {
        self.arrows.get(arrow.index())
    }

    /// Returns the coordinate for `(arrow, row, column)`, or `None` if invalid.
    pub fn coordinate(
        &self,
        arrow: ArrowId,
        row: usize,
        column: usize,
    ) -> Option<FamilyCoordinate> {
        let layout = self.arrow(arrow)?;
        if row >= layout.rows || column >= layout.columns {
            return None;
        }
        let inside = row * layout.columns + column;
        Some(FamilyCoordinate {
            index: layout.range.start + inside,
            arrow,
            row,
            column,
        })
    }

    /// Returns the flat Hom-variable position for one vertex matrix entry.
    pub fn hom_variable(&self, vertex: u32, row: usize, column: usize) -> Option<HomVariable> {
        let vertex_index = vertex as usize;
        let dimension = *self.dimensions.get(vertex_index)?;
        if row >= dimension || column >= dimension {
            return None;
        }
        let offset = self.hom_offsets[vertex_index];
        Some(HomVariable {
            index: offset + row * dimension + column,
            vertex,
            row,
            column,
        })
    }
}

pub(super) fn checked_coordinate(
    layout: &FamilyLayout,
    arrow: ArrowId,
    row: usize,
    column: usize,
) -> Result<FamilyCoordinate, FamilyError> {
    let Some(arrow_layout) = layout.arrow(arrow) else {
        return Err(FamilyError::ArrowOutOfRange {
            arrow,
            num_arrows: layout.arrows.len(),
        });
    };
    layout
        .coordinate(arrow, row, column)
        .ok_or(FamilyError::CoordinateOutOfRange {
            arrow,
            row,
            column,
            rows: arrow_layout.rows,
            columns: arrow_layout.columns,
        })
}

fn arrow_layouts(
    algebra: &Algebra,
    dimensions: &[usize],
) -> Result<Vec<FamilyArrowLayout>, FamilyError> {
    let quiver = algebra.quiver();
    let mut layouts = Vec::new();
    layouts.try_reserve(quiver.num_arrows()).map_err(|_| {
        FamilyError::CoordinateAllocationFailed {
            coordinates: quiver.num_arrows(),
        }
    })?;
    let mut offset = 0usize;
    for index in 0..quiver.num_arrows() {
        let arrow = ArrowId(index as u32);
        let rows = dimensions[quiver.source(arrow) as usize];
        let columns = dimensions[quiver.target(arrow) as usize];
        let length = rows
            .checked_mul(columns)
            .ok_or(FamilyError::MatrixEntryOverflow {
                arrow,
                rows,
                columns,
            })?;
        let range = FamilyCoordinateRange {
            arrow,
            start: offset,
            length,
        };
        offset = offset
            .checked_add(length)
            .ok_or(FamilyError::CoordinateCountOverflow)?;
        layouts.push(FamilyArrowLayout {
            arrow,
            source: quiver.source(arrow),
            target: quiver.target(arrow),
            rows,
            columns,
            range,
        });
    }
    Ok(layouts)
}

fn coordinate_layout(arrows: &[FamilyArrowLayout]) -> Result<Vec<FamilyCoordinate>, FamilyError> {
    let total = arrows.last().map_or(0, |layout| layout.range.end());
    let mut coordinates = Vec::new();
    coordinates
        .try_reserve(total)
        .map_err(|_| FamilyError::CoordinateAllocationFailed { coordinates: total })?;
    for layout in arrows {
        for row in 0..layout.rows {
            for column in 0..layout.columns {
                coordinates.push(FamilyCoordinate {
                    index: layout.range.start + row * layout.columns + column,
                    arrow: layout.arrow,
                    row,
                    column,
                });
            }
        }
    }
    Ok(coordinates)
}

fn hom_variables(dimensions: &[usize]) -> Result<(Vec<usize>, usize), FamilyError> {
    let mut offsets = Vec::new();
    offsets
        .try_reserve(dimensions.len())
        .map_err(|_| FamilyError::CoordinateAllocationFailed {
            coordinates: dimensions.len(),
        })?;
    let mut total = 0usize;
    for (vertex, &dimension) in dimensions.iter().enumerate() {
        offsets.push(total);
        let square =
            dimension
                .checked_mul(dimension)
                .ok_or(FamilyError::HomVariableCountOverflow {
                    vertex: vertex as u32,
                    dimension,
                })?;
        total = total
            .checked_add(square)
            .ok_or(FamilyError::HomVariableCountOverflow {
                vertex: vertex as u32,
                dimension,
            })?;
    }
    Ok((offsets, total))
}

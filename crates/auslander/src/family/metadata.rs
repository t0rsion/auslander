use crate::algebra::Algebra;

use super::types::{
    FamilyCoordinateRange, FamilyError, FamilyLayout, HomCoefficientSide, HomEquationLayout,
    HomEquationTerm, RelationEvaluationLayout, RelationTermLayout,
};

pub(super) fn relation_layouts(
    algebra: &Algebra,
    layout: &FamilyLayout,
) -> Result<Vec<RelationEvaluationLayout>, FamilyError> {
    let mut out = Vec::new();
    out.try_reserve(algebra.relations().len())
        .map_err(|_| FamilyError::RelationSupportAllocationFailed { relation: 0 })?;
    for (relation_index, relation) in algebra.relations().iter().enumerate() {
        let rows = layout.dimensions[relation.source() as usize];
        let columns = layout.dimensions[relation.target() as usize];
        rows.checked_mul(columns)
            .ok_or(FamilyError::RelationOutputOverflow {
                relation: relation_index,
                rows,
                columns,
            })?;
        let mut terms = Vec::new();
        terms.try_reserve(relation.terms().len()).map_err(|_| {
            FamilyError::RelationTermAllocationFailed {
                relation: relation_index,
                term: 0,
            }
        })?;
        let mut support = Vec::new();
        support.try_reserve(relation.terms().len()).map_err(|_| {
            FamilyError::RelationSupportAllocationFailed {
                relation: relation_index,
            }
        })?;
        for (term_index, (coefficient, word)) in relation.terms().iter().enumerate() {
            let mut path = Vec::new();
            path.try_reserve(word.arrows().len()).map_err(|_| {
                FamilyError::RelationTermAllocationFailed {
                    relation: relation_index,
                    term: term_index,
                }
            })?;
            let mut factors = Vec::new();
            factors.try_reserve(word.arrows().len()).map_err(|_| {
                FamilyError::RelationTermAllocationFailed {
                    relation: relation_index,
                    term: term_index,
                }
            })?;
            append_relation_factors(layout, word.arrows(), &mut path, &mut factors, &mut support);
            terms.push(RelationTermLayout {
                coefficient: *coefficient,
                path,
                factors,
            });
        }
        support.sort_by_key(|range| range.arrow().index());
        out.push(RelationEvaluationLayout {
            relation: relation_index,
            source: relation.source(),
            target: relation.target(),
            rows,
            columns,
            terms,
            coordinate_support: support,
        });
    }
    Ok(out)
}

fn append_relation_factors(
    layout: &FamilyLayout,
    arrows: &[crate::quiver::ArrowId],
    path: &mut Vec<crate::quiver::ArrowId>,
    factors: &mut Vec<FamilyCoordinateRange>,
    support: &mut Vec<FamilyCoordinateRange>,
) {
    for &arrow in arrows {
        path.push(arrow);
        let arrow_layout = layout
            .arrow(arrow)
            .expect("algebra relation arrow belongs to its quiver");
        factors.push(arrow_layout.coordinate_range());
        if !support
            .iter()
            .any(|range: &FamilyCoordinateRange| range.arrow() == arrow)
        {
            support.push(arrow_layout.coordinate_range());
        }
    }
}

pub(super) fn hom_layout(layout: &FamilyLayout) -> Result<Vec<HomEquationLayout>, FamilyError> {
    let total = hom_equation_count(layout)?;
    let mut equations = Vec::new();
    equations
        .try_reserve(total)
        .map_err(|_| FamilyError::HomEquationAllocationFailed { equations: total })?;
    let mut index = 0usize;
    for arrow in &layout.arrows {
        index = append_hom_equations(layout, arrow, index, &mut equations)?;
    }
    Ok(equations)
}

fn hom_equation_count(layout: &FamilyLayout) -> Result<usize, FamilyError> {
    let mut total = 0usize;
    for arrow in &layout.arrows {
        let count =
            arrow
                .rows
                .checked_mul(arrow.columns)
                .ok_or(FamilyError::HomEquationCountOverflow {
                    arrow: arrow.arrow,
                    rows: arrow.rows,
                    columns: arrow.columns,
                })?;
        total = total
            .checked_add(count)
            .ok_or(FamilyError::HomEquationCountOverflow {
                arrow: arrow.arrow,
                rows: arrow.rows,
                columns: arrow.columns,
            })?;
    }
    Ok(total)
}

fn append_hom_equations(
    layout: &FamilyLayout,
    arrow: &super::types::FamilyArrowLayout,
    mut index: usize,
    equations: &mut Vec<HomEquationLayout>,
) -> Result<usize, FamilyError> {
    for row in 0..arrow.rows {
        for column in 0..arrow.columns {
            equations.push(hom_equation(layout, arrow, row, column, index)?);
            index += 1;
        }
    }
    Ok(index)
}

fn hom_equation(
    layout: &FamilyLayout,
    arrow: &super::types::FamilyArrowLayout,
    row: usize,
    column: usize,
    index: usize,
) -> Result<HomEquationLayout, FamilyError> {
    let term_capacity =
        arrow
            .rows
            .checked_add(arrow.columns)
            .ok_or(FamilyError::HomTermAllocationFailed {
                arrow: arrow.arrow,
                row,
                column,
            })?;
    let mut terms = Vec::new();
    terms
        .try_reserve(term_capacity)
        .map_err(|_| FamilyError::HomTermAllocationFailed {
            arrow: arrow.arrow,
            row,
            column,
        })?;
    append_target_terms(layout, arrow, row, column, &mut terms);
    append_source_terms(layout, arrow, row, column, &mut terms);
    Ok(HomEquationLayout {
        index,
        arrow: arrow.arrow,
        source_row: row,
        target_column: column,
        terms,
    })
}

fn append_target_terms(
    layout: &FamilyLayout,
    arrow: &super::types::FamilyArrowLayout,
    row: usize,
    column: usize,
    terms: &mut Vec<HomEquationTerm>,
) {
    for variable_column in 0..arrow.rows {
        let variable = layout
            .hom_variable(arrow.source, row, variable_column)
            .expect("source Hom variable is in the layout");
        let coefficient = layout
            .coordinate(arrow.arrow, variable_column, column)
            .expect("target map coordinate is in the layout");
        terms.push(HomEquationTerm {
            variable,
            coefficient,
            side: HomCoefficientSide::Target,
        });
    }
}

fn append_source_terms(
    layout: &FamilyLayout,
    arrow: &super::types::FamilyArrowLayout,
    row: usize,
    column: usize,
    terms: &mut Vec<HomEquationTerm>,
) {
    for variable_row in 0..arrow.columns {
        let variable = layout
            .hom_variable(arrow.target, variable_row, column)
            .expect("target Hom variable is in the layout");
        let coefficient = layout
            .coordinate(arrow.arrow, row, variable_row)
            .expect("source map coordinate is in the layout");
        terms.push(HomEquationTerm {
            variable,
            coefficient,
            side: HomCoefficientSide::Source,
        });
    }
}

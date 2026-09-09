use crate::hom::{Morphism, zero_morphism};
use crate::homotopy::{BoundedComplex, ChainHomSpace, ChainMap, DegreeRange};
use crate::linalg::DenseMat;
use crate::module::{Module, same_representation};

use super::DerivedTransportError;
use super::model::ProjectiveAddTModel;

pub(super) fn common_range(
    complexes: &[&BoundedComplex],
) -> Result<DegreeRange, DerivedTransportError> {
    let lower = complexes
        .iter()
        .map(|complex| complex.lower())
        .min()
        .ok_or(DerivedTransportError::DegreeOverflow)?;
    let upper = complexes
        .iter()
        .map(|complex| complex.upper())
        .max()
        .ok_or(DerivedTransportError::DegreeOverflow)?;
    DegreeRange::new(lower, upper).map_err(|_| DerivedTransportError::DegreeOverflow)
}

pub(super) fn agrees_after_padding(left: &BoundedComplex, right: &BoundedComplex) -> bool {
    common_range(&[left, right]).is_ok_and(|range| {
        left.padded_to(range).is_ok_and(|left| {
            right
                .padded_to(range)
                .is_ok_and(|right| left.agrees_with(&right))
        })
    })
}

fn padded_chain_map(map: &ChainMap, range: DegreeRange) -> Result<ChainMap, DerivedTransportError> {
    let source = map.source().padded_to(range)?;
    let target = map.target().padded_to(range)?;
    let components = (range.lower()..=range.upper())
        .map(|degree| {
            if map.range().contains(degree) {
                map.component(degree).cloned().map_err(Into::into)
            } else {
                let index = (degree - range.lower()) as usize;
                zero_morphism(&source.terms()[index], &target.terms()[index]).map_err(Into::into)
            }
        })
        .collect::<Result<Vec<_>, DerivedTransportError>>()?;
    ChainMap::new(&source, &target, components).map_err(Into::into)
}

pub(super) fn structural_chain_isomorphism(
    source: &BoundedComplex,
    target: &BoundedComplex,
) -> Result<ChainMap, DerivedTransportError> {
    let range = common_range(&[source, target])?;
    let source = source.padded_to(range)?;
    let target = target.padded_to(range)?;
    if !source.agrees_with(&target) {
        return Err(DerivedTransportError::Comparison);
    }
    let components = source
        .terms()
        .iter()
        .zip(target.terms())
        .map(|(source, target)| {
            let maps = source
                .dim_vector()
                .iter()
                .map(|&dimension| DenseMat::identity(dimension))
                .collect();
            Morphism::new(source, target, maps).map_err(Into::into)
        })
        .collect::<Result<Vec<_>, DerivedTransportError>>()?;
    ChainMap::new(&source, &target, components).map_err(Into::into)
}

fn comparison_image_rows(
    source_space: &ChainHomSpace,
    target_space: &ChainHomSpace,
    source_map: &ChainMap,
) -> Result<Vec<Vec<crate::field::Fp>>, DerivedTransportError> {
    let mut image_rows = Vec::with_capacity(source_space.dim());
    for basis in source_space.basis_iter() {
        image_rows.push(target_space.coords(&source_map.then(&basis)?)?);
    }
    Ok(image_rows)
}

pub(super) fn strict_comparison(
    source: &ProjectiveAddTModel,
    target: &ProjectiveAddTModel,
    original_map: &ChainMap,
) -> Result<ChainMap, DerivedTransportError> {
    let right = original_map.then(target.quasi_isomorphism().map())?;
    let source_space = ChainHomSpace::new(source.model().complex(), target.model().complex())?;
    let target_space = ChainHomSpace::new(
        source.quasi_isomorphism().map().source(),
        target.model().complex(),
    )?;
    let image_rows = comparison_image_rows(
        &source_space,
        &target_space,
        source.quasi_isomorphism().map(),
    )?;
    let images = DenseMat::from_rows_with_cols(&image_rows, target_space.dim());
    let desired = target_space.coords(&right)?;
    let coordinates = images
        .transpose()
        .solve(&desired, &source.model().complex().terms()[0].field())
        .ok_or(DerivedTransportError::Comparison)?;
    let comparison = source_space.morphism(&coordinates);
    if !source
        .quasi_isomorphism()
        .map()
        .then(&comparison)?
        .agrees_with(&right)
    {
        return Err(DerivedTransportError::Comparison);
    }
    Ok(comparison)
}

fn check_cone_square(
    source_map: &ChainMap,
    target_map: &ChainMap,
    source_vertical: &ChainMap,
    target_vertical: &ChainMap,
) -> Result<(), DerivedTransportError> {
    let left = source_vertical.then(target_map)?;
    let right = source_map.then(target_vertical)?;
    if !left.agrees_with(&right) {
        return Err(DerivedTransportError::Comparison);
    }
    Ok(())
}

fn cone_target_dimension(map: &ChainMap, range: DegreeRange, degree: i32, vertex: u32) -> usize {
    if range.contains(degree) {
        map.target()
            .term(degree)
            .expect("range contains degree")
            .dim_at(vertex)
    } else {
        0
    }
}

fn copy_cone_block(
    matrix: &mut DenseMat,
    block: &DenseMat,
    row_offset: usize,
    column_offset: usize,
) {
    for row in 0..block.rows() {
        for column in 0..block.cols() {
            matrix.set(
                row_offset + row,
                column_offset + column,
                block.get(row, column),
            );
        }
    }
}

struct ConeMapContext<'a> {
    range: DegreeRange,
    source_map: &'a ChainMap,
    target_map: &'a ChainMap,
    source_vertical: &'a ChainMap,
    target_vertical: &'a ChainMap,
    source_cone: &'a BoundedComplex,
    target_cone: &'a BoundedComplex,
}

fn cone_vertex_matrix(
    context: &ConeMapContext<'_>,
    source_term: &Module,
    target_term: &Module,
    degree: i32,
    vertex: u32,
) -> Result<DenseMat, DerivedTransportError> {
    let y_source_dim = cone_target_dimension(context.source_map, context.range, degree, vertex);
    let y_target_dim = cone_target_dimension(context.target_map, context.range, degree, vertex);
    let mut matrix = DenseMat::zero(source_term.dim_at(vertex), target_term.dim_at(vertex));
    if context.range.contains(degree) {
        let block = context.target_vertical.component(degree)?.map_at(vertex);
        copy_cone_block(&mut matrix, block, 0, 0);
    }
    let x_degree = degree - 1;
    if context.range.contains(x_degree) {
        let block = context.source_vertical.component(x_degree)?.map_at(vertex);
        copy_cone_block(&mut matrix, block, y_source_dim, y_target_dim);
    }
    Ok(matrix)
}

fn cone_component(
    context: &ConeMapContext<'_>,
    degree: i32,
) -> Result<Morphism, DerivedTransportError> {
    let index = (degree - context.range.lower()) as usize;
    let source_term = &context.source_cone.terms()[index];
    let target_term = &context.target_cone.terms()[index];
    let matrices = (0..source_term.algebra().quiver().num_vertices())
        .map(|vertex| cone_vertex_matrix(context, source_term, target_term, degree, vertex))
        .collect::<Result<Vec<_>, DerivedTransportError>>()?;
    Morphism::new(source_term, target_term, matrices).map_err(Into::into)
}

fn cone_components(context: &ConeMapContext<'_>) -> Result<Vec<Morphism>, DerivedTransportError> {
    let cone_upper = context
        .range
        .upper()
        .checked_add(1)
        .ok_or(DerivedTransportError::DegreeOverflow)?;
    (context.range.lower()..=cone_upper)
        .map(|degree| cone_component(context, degree))
        .collect()
}

pub(super) fn cone_chain_map(
    source_map: &ChainMap,
    target_map: &ChainMap,
    source_vertical: &ChainMap,
    target_vertical: &ChainMap,
) -> Result<ChainMap, DerivedTransportError> {
    let range = common_range(&[
        source_map.source(),
        source_map.target(),
        target_map.source(),
        target_map.target(),
        source_vertical.source(),
        source_vertical.target(),
        target_vertical.source(),
        target_vertical.target(),
    ])?;
    let source_map = padded_chain_map(source_map, range)?;
    let target_map = padded_chain_map(target_map, range)?;
    let source_vertical = padded_chain_map(source_vertical, range)?;
    let target_vertical = padded_chain_map(target_vertical, range)?;
    check_cone_square(&source_map, &target_map, &source_vertical, &target_vertical)?;
    let source_cone = source_map.mapping_cone()?;
    let target_cone = target_map.mapping_cone()?;
    let context = ConeMapContext {
        range,
        source_map: &source_map,
        target_map: &target_map,
        source_vertical: &source_vertical,
        target_vertical: &target_vertical,
        source_cone: &source_cone,
        target_cone: &target_cone,
    };
    let components = cone_components(&context)?;
    ChainMap::new(&source_cone, &target_cone, components).map_err(Into::into)
}

pub(super) fn attachment_map(
    source: &BoundedComplex,
    target: &BoundedComplex,
    differential: &Morphism,
    degree: i32,
) -> Result<ChainMap, DerivedTransportError> {
    let range = common_range(&[source, target])?;
    let source = source.padded_to(range)?;
    let target = target.padded_to(range)?;
    let components = (range.lower()..=range.upper())
        .map(|component_degree| {
            let index = (component_degree - range.lower()) as usize;
            if component_degree == degree {
                if !same_representation(differential.source(), &source.terms()[index])
                    || !same_representation(differential.target(), &target.terms()[index])
                {
                    return Err(DerivedTransportError::Comparison);
                }
                let maps = (0..differential.source().algebra().quiver().num_vertices())
                    .map(|vertex| differential.map_at(vertex).clone())
                    .collect();
                Morphism::new(&source.terms()[index], &target.terms()[index], maps)
                    .map_err(Into::into)
            } else {
                zero_morphism(&source.terms()[index], &target.terms()[index]).map_err(Into::into)
            }
        })
        .collect::<Result<Vec<_>, DerivedTransportError>>()?;
    ChainMap::new(&source, &target, components).map_err(Into::into)
}

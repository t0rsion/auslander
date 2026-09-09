//! Mapping cone construction for checked chain maps.

use crate::hom::Morphism;
use crate::module::{Module, direct_sum};

use super::chain::ChainMap;
use super::complex::{
    BoundedComplex, BoundedComplexError, DegreeRange, block_matrices, negate_morphism, padded_term,
    zero_between,
};

impl ChainMap {
    /// Builds the mapping cone `Cone(self)`.
    pub fn mapping_cone(&self) -> Result<BoundedComplex, BoundedComplexError> {
        mapping_cone_impl(self)
    }
}

fn mapping_cone_term(map: &ChainMap, degree: i32) -> Module {
    let y = padded_term(&map.target, degree);
    let x = padded_term(&map.source, degree - 1);
    let refs = [&y, &x];
    direct_sum(&refs).0
}

fn differential_or_zero(
    complex: &BoundedComplex,
    degree: i32,
    source: &Module,
    target: &Module,
    negate: bool,
) -> Morphism {
    complex
        .differential(degree)
        .map(|d| {
            if negate {
                negate_morphism(d)
            } else {
                d.clone()
            }
        })
        .unwrap_or_else(|| zero_between(source, target))
}

fn mapping_cone_differential(
    map: &ChainMap,
    degree: i32,
    source_sum: &Module,
    target_sum: &Module,
) -> Morphism {
    let y_source = padded_term(&map.target, degree);
    let x_source = padded_term(&map.source, degree - 1);
    let y_target = padded_term(&map.target, degree - 1);
    let x_target = padded_term(&map.source, degree - 2);
    let d_y = differential_or_zero(&map.target, degree, &y_source, &y_target, false);
    let f = if map.source.range.contains(degree - 1) {
        map.components[(degree - 1 - map.source.lower()) as usize].clone()
    } else {
        zero_between(&x_source, &y_target)
    };
    let d_x = differential_or_zero(&map.source, degree - 1, &x_source, &x_target, true);
    let source_parts = [y_source, x_source];
    let target_parts = [y_target, x_target];
    let blocks = [d_y, f, d_x];
    let placements = [(0, 0), (1, 0), (1, 1)];
    let matrices = block_matrices(
        &source_parts,
        &target_parts,
        &blocks,
        &placements,
        source_sum,
        target_sum,
    );
    Morphism::new(source_sum, target_sum, matrices)
        .expect("mapping cone block differential is A-linear")
}

fn mapping_cone_impl(map: &ChainMap) -> Result<BoundedComplex, BoundedComplexError> {
    let upper = map
        .source
        .upper()
        .checked_add(1)
        .ok_or(BoundedComplexError::DegreeOverflow {
            degree: map.source.upper(),
            shift: 1,
        })?;
    let lower = map.source.lower();
    let range = DegreeRange { lower, upper };
    let terms: Vec<Module> = (0..range.len())
        .map(|offset| mapping_cone_term(map, lower + offset as i32))
        .collect();
    let differentials: Vec<Morphism> = (0..range.len().saturating_sub(1))
        .map(|offset| {
            mapping_cone_differential(
                map,
                lower + offset as i32 + 1,
                &terms[offset + 1],
                &terms[offset],
            )
        })
        .collect();
    BoundedComplex::new(lower, terms, differentials)
}

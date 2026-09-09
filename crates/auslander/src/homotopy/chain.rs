//! Chain maps and chain homotopies over bounded complexes.

use std::sync::Arc;

use crate::decompose::add_morphisms;
use crate::field::Fp;
use crate::hom::{Morphism, identity};
use crate::homspace::scale_morphism;
use crate::module::{Module, same_morphism_data, same_representation, same_slice};

use super::complex::{
    BoundedComplex, BoundedComplexError, DegreeRange, checked_degree, padded_complex, zero_between,
};

pub(super) fn shifted_complex(
    complex: &BoundedComplex,
    amount: i32,
) -> Result<BoundedComplex, ChainMapError> {
    complex.shift(amount).map_err(|error| match error {
        BoundedComplexError::DegreeOverflow { degree, shift } => {
            ChainMapError::DegreeOverflow { degree, shift }
        }
        _ => ChainMapError::Padding(error),
    })
}

pub(super) fn padded_pair(
    source: &BoundedComplex,
    target: &BoundedComplex,
    range: DegreeRange,
) -> Result<(BoundedComplex, BoundedComplex), ChainMapError> {
    Ok((
        source.padded_to(range).map_err(ChainMapError::Padding)?,
        target.padded_to(range).map_err(ChainMapError::Padding)?,
    ))
}

/// Rejected chain map input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChainMapError {
    /// The source and target complexes use different algebras.
    DifferentAlgebras,
    /// The component count differs from the common interval length.
    ComponentCount { expected: usize, got: usize },
    /// The component at `degree` has wrong module endpoints.
    ComponentEndpointMismatch { degree: i32 },
    /// The chain equation fails at `degree`.
    ChainCondition { degree: i32 },
    /// A composition needs nominally identical middle complexes.
    CompositionMismatch,
    /// A chain map component was requested outside its interval.
    DegreeOutOfRange { degree: i32, range: DegreeRange },
    /// A degree shift does not fit in the degree type.
    DegreeOverflow { degree: i32, shift: i32 },
    /// Source or target padding failed.
    Padding(BoundedComplexError),
    /// A homotopy has the wrong component count.
    HomotopyComponentCount { expected: usize, got: usize },
    /// A homotopy component has wrong endpoints.
    HomotopyEndpointMismatch { degree: i32 },
    /// The map and homotopy do not share both endpoints.
    HomotopyEndpoint,
    /// The map does not lie in the ambient chain Hom space.
    OutsideHomSpace,
}

display_error! { ChainMapError {
    Self::DifferentAlgebras => "chain map complexes live over different algebras";
    Self::ComponentCount { expected, got } => "chain map has {got} components, expected {expected}";
    Self::ComponentEndpointMismatch { degree } => "chain map component at degree {degree} has wrong endpoints";
    Self::ChainCondition { degree } => "chain condition fails at degree {degree}";
    Self::CompositionMismatch => "chain map composition has a different middle complex";
    Self::DegreeOutOfRange { degree, range } => "degree {degree} is outside {}..{}", range.lower, range.upper;
    Self::DegreeOverflow { degree, shift } => "degree {degree} cannot be shifted by {shift}";
    Self::Padding(error) => "chain map padding failed: {error}";
    Self::HomotopyComponentCount { expected, got } => "chain homotopy has {got} components, expected {expected}";
    Self::HomotopyEndpointMismatch { degree } => "chain homotopy component at degree {degree} has wrong endpoints";
    Self::HomotopyEndpoint => "chain map and homotopy endpoints differ";
    Self::OutsideHomSpace => "chain map lies outside its ambient chain Hom space";
} }

error_source! { ChainMapError {
    Self::Padding(error) => Some(error),
    _ => None,
} }

/// A checked degree-preserving chain map.
#[derive(Clone, Debug)]
pub struct ChainMap {
    pub(super) source: BoundedComplex,
    pub(super) target: BoundedComplex,
    pub(super) components: Vec<Morphism>,
}

fn same_complex_identity(a: &BoundedComplex, b: &BoundedComplex) -> bool {
    a.range == b.range
        && a.terms.iter().zip(&b.terms).all(|(x, y)| x.ptr_eq(y))
        && a.differentials == b.differentials
}

pub(super) fn same_complex_data(a: &BoundedComplex, b: &BoundedComplex) -> bool {
    a.range == b.range
        && same_slice(&a.terms, &b.terms, same_representation)
        && same_slice(&a.differentials, &b.differentials, same_morphism_data)
}

fn same_complex_for_padding(a: &BoundedComplex, b: &BoundedComplex) -> bool {
    same_complex_identity(a, b) || same_complex_data(a, b)
}

pub(super) fn agrees_after_padding(a: &BoundedComplex, b: &BoundedComplex) -> bool {
    a.padded_to(b.range)
        .is_ok_and(|padded| padded.agrees_with(b))
}

pub(super) fn union_range(left: DegreeRange, right: DegreeRange) -> DegreeRange {
    DegreeRange {
        lower: left.lower.min(right.lower),
        upper: left.upper.max(right.upper),
    }
}

pub(super) fn checked_union_range(
    source: &BoundedComplex,
    target: &BoundedComplex,
) -> Result<DegreeRange, ChainMapError> {
    if !Arc::ptr_eq(source.terms[0].algebra(), target.terms[0].algebra()) {
        return Err(ChainMapError::DifferentAlgebras);
    }
    Ok(union_range(source.range, target.range))
}

fn padded_with_component_endpoints(
    complex: &BoundedComplex,
    range: DegreeRange,
    mut missing: impl FnMut(usize) -> Module,
) -> Result<BoundedComplex, ChainMapError> {
    let terms = (0..range.len())
        .map(|offset| {
            let degree = range.lower + offset as i32;
            if complex.range.contains(degree) {
                return Ok(complex.terms[(degree - complex.range.lower) as usize].clone());
            }
            let endpoint = missing(offset);
            let zero = Module::zero(complex.terms[0].algebra());
            if !endpoint.is_zero() || !same_representation(&endpoint, &zero) {
                return Err(ChainMapError::ComponentEndpointMismatch { degree });
            }
            Ok(endpoint)
        })
        .collect::<Result<Vec<_>, _>>()?;
    padded_complex(complex, range, terms).map_err(ChainMapError::Padding)
}

pub(super) fn rebase_morphism(f: &Morphism, source: &Module, target: &Module) -> Morphism {
    let maps = (0..source.algebra().quiver().num_vertices() as usize)
        .map(|vertex| f.map_at(vertex as u32).clone())
        .collect();
    Morphism::new(source, target, maps)
        .expect("structurally equal padded modules preserve A-linearity")
}

fn same_chain_data(a: &ChainMap, b: &ChainMap) -> bool {
    same_complex_data(&a.source, &b.source)
        && same_complex_data(&a.target, &b.target)
        && same_slice(&a.components, &b.components, same_morphism_data)
}

fn chain_map_range(map: &ChainMap) -> DegreeRange {
    union_range(map.source.range, map.target.range)
}

fn chain_difference(left: &ChainMap, right: &ChainMap) -> Result<ChainMap, ChainMapError> {
    let field = left.source.terms[0].field();
    right.scale(field.neg(field.one())).add(left)
}

fn padded_chain_maps(
    left: &ChainMap,
    right: &ChainMap,
    range: DegreeRange,
) -> Result<(ChainMap, ChainMap), ChainMapError> {
    Ok((left.padded_to(range)?, right.padded_to(range)?))
}

fn boundary_difference(
    left: &ChainMap,
    right: &ChainMap,
    homotopy: &ChainHomotopy,
) -> Result<(ChainMap, ChainMap), ChainMapError> {
    Ok((chain_difference(left, right)?, homotopy.boundary()?))
}

fn checked_homotopy_difference(
    left: &ChainMap,
    right: &ChainMap,
    components: Vec<Morphism>,
) -> Result<(ChainHomotopy, ChainMap, ChainMap), ChainMapError> {
    let homotopy = ChainHomotopy::new(&left.source, &left.target, components)?;
    let (difference, boundary) = boundary_difference(left, right, &homotopy)?;
    Ok((homotopy, difference, boundary))
}

fn same_map_endpoints(left: &ChainMap, right: &ChainMap) -> bool {
    same_complex_for_padding(&left.source, &right.source)
        && same_complex_for_padding(&left.target, &right.target)
}

fn same_homotopy_endpoints(left: &ChainMap, right: &ChainMap, homotopy: &ChainHomotopy) -> bool {
    same_map_endpoints(left, right)
        && same_complex_for_padding(&left.source, &homotopy.source)
        && same_complex_for_padding(&left.target, &homotopy.target)
}

fn padded_homotopy(
    left: &ChainMap,
    right: &ChainMap,
    homotopy: &ChainHomotopy,
    range: DegreeRange,
) -> Result<(ChainMap, ChainMap, ChainHomotopy), ChainMapError> {
    let (left, right) = padded_chain_maps(left, right, range)?;
    let homotopy = homotopy.padded_to(range)?;
    if !same_homotopy_endpoints(&left, &right, &homotopy) {
        return Err(ChainMapError::HomotopyEndpoint);
    }
    Ok((left, right, homotopy))
}

impl ChainMap {
    /// Builds a chain map after checking endpoints and every chain equation.
    pub fn new(
        source: &BoundedComplex,
        target: &BoundedComplex,
        components: Vec<Morphism>,
    ) -> Result<ChainMap, ChainMapError> {
        let range = checked_union_range(source, target)?;
        if components.len() != range.len() {
            return Err(ChainMapError::ComponentCount {
                expected: range.len(),
                got: components.len(),
            });
        }
        let source = padded_with_component_endpoints(source, range, |offset| {
            components[offset].source().clone()
        })?;
        let target = padded_with_component_endpoints(target, range, |offset| {
            components[offset].target().clone()
        })?;
        ChainMap::new_checked(&source, &target, components)
    }

    fn new_checked(
        source: &BoundedComplex,
        target: &BoundedComplex,
        components: Vec<Morphism>,
    ) -> Result<ChainMap, ChainMapError> {
        if components.len() != source.len() {
            return Err(ChainMapError::ComponentCount {
                expected: source.len(),
                got: components.len(),
            });
        }
        for (index, component) in components.iter().enumerate() {
            if !component.source().ptr_eq(&source.terms[index])
                || !component.target().ptr_eq(&target.terms[index])
            {
                return Err(ChainMapError::ComponentEndpointMismatch {
                    degree: source.range.lower + index as i32,
                });
            }
        }
        for index in 1..source.len() {
            let degree = source.range.lower + index as i32;
            let left = source.differentials[index - 1]
                .then(&components[index - 1])
                .expect("chain map source endpoint invariant");
            let right = components[index]
                .then(&target.differentials[index - 1])
                .expect("chain map target endpoint invariant");
            if left != right {
                return Err(ChainMapError::ChainCondition { degree });
            }
        }
        Ok(ChainMap {
            source: source.clone(),
            target: target.clone(),
            components,
        })
    }

    accessor_methods! {
        /// The source complex.
        pub source() -> &BoundedComplex = |this| &this.source;
        /// The target complex.
        pub target() -> &BoundedComplex = |this| &this.target;
        /// The components in increasing degree order.
        pub components() -> &[Morphism] = |this| &this.components;
        /// The common degree interval.
        pub range() -> DegreeRange = |this| this.source.range;
    }

    /// The component at `degree`.
    pub fn component(&self, degree: i32) -> Result<&Morphism, ChainMapError> {
        Ok(
            &self.components[checked_degree(self.source.range, degree).map_err(
                |error| match error {
                    BoundedComplexError::DegreeOutOfRange { degree, range } => {
                        ChainMapError::DegreeOutOfRange { degree, range }
                    }
                    _ => unreachable!(),
                },
            )?],
        )
    }

    /// The identity chain map on `complex`.
    pub fn identity(complex: &BoundedComplex) -> ChainMap {
        let components = complex.terms.iter().map(identity).collect();
        ChainMap::new(complex, complex, components).expect("module identities form a chain map")
    }

    /// The zero chain map, padded to the union of both degree ranges.
    pub fn zero(
        source: &BoundedComplex,
        target: &BoundedComplex,
    ) -> Result<ChainMap, ChainMapError> {
        let range = union_range(source.range, target.range);
        let (source, target) = padded_pair(source, target, range)?;
        let components = source
            .terms
            .iter()
            .zip(&target.terms)
            .map(|(source, target)| zero_between(source, target))
            .collect();
        ChainMap::new_checked(&source, &target, components)
    }

    /// Whether another chain map has the same nominal complexes and matrices.
    pub fn agrees_with(&self, other: &ChainMap) -> bool {
        same_chain_data(self, other)
    }

    /// Recomputes the chain equations and compares the stored map data.
    pub fn verify(&self) -> bool {
        let Ok(rebuilt) = ChainMap::new(&self.source, &self.target, self.components.clone()) else {
            return false;
        };
        same_chain_data(self, &rebuilt)
    }

    fn padded_to(&self, range: DegreeRange) -> Result<ChainMap, ChainMapError> {
        let (source, target) = padded_pair(&self.source, &self.target, range)?;
        let mut components = Vec::with_capacity(range.len());
        for offset in 0..range.len() {
            let degree = range.lower + offset as i32;
            if self.source.range.contains(degree) {
                components
                    .push(self.components[(degree - self.source.range.lower) as usize].clone());
            } else {
                components.push(zero_between(&source.terms[offset], &target.terms[offset]));
            }
        }
        ChainMap::new_checked(&source, &target, components)
    }

    /// Composes `self` first, then `other`.
    pub fn then(&self, other: &ChainMap) -> Result<ChainMap, ChainMapError> {
        let range = union_range(chain_map_range(self), chain_map_range(other));
        let (left, right) = padded_chain_maps(self, other, range)?;
        if !same_complex_for_padding(&left.target, &right.source) {
            return Err(ChainMapError::CompositionMismatch);
        }
        let components = left
            .components
            .iter()
            .zip(&right.components)
            .map(|(left, right)| {
                let right = rebase_morphism(right, left.target(), right.target());
                left.then(&right)
                    .expect("chain map composition endpoints were checked")
            })
            .collect();
        ChainMap::new_checked(&left.source, &right.target, components)
    }

    /// Adds two maps with the same source and target complexes.
    pub fn add(&self, other: &ChainMap) -> Result<ChainMap, ChainMapError> {
        let range = union_range(chain_map_range(self), chain_map_range(other));
        let left = self.padded_to(range)?;
        let right = other.padded_to(range)?;
        if !same_map_endpoints(&left, &right) {
            return Err(ChainMapError::CompositionMismatch);
        }
        let components = left
            .components
            .iter()
            .zip(&right.components)
            .map(|(left, right)| {
                let right = rebase_morphism(right, left.source(), left.target());
                add_morphisms(left, &right)
            })
            .collect();
        ChainMap::new_checked(&left.source, &left.target, components)
    }

    /// Multiplies every component by a field scalar.
    pub fn scale(&self, scalar: Fp) -> ChainMap {
        let components = self
            .components
            .iter()
            .map(|component| scale_morphism(component, scalar))
            .collect();
        ChainMap {
            source: self.source.clone(),
            target: self.target.clone(),
            components,
        }
    }

    /// Returns the shifted chain map between shifted complexes.
    pub fn shift(&self, amount: i32) -> Result<ChainMap, ChainMapError> {
        let source = shifted_complex(&self.source, amount)?;
        let target = shifted_complex(&self.target, amount)?;
        ChainMap::new(&source, &target, self.components.clone())
    }

    /// Returns the homotopy boundary of `homotopy`, namely `d h + h d`.
    pub fn homotopic_to(
        &self,
        other: &ChainMap,
        homotopy: &ChainHomotopy,
    ) -> Result<bool, ChainMapError> {
        let range = union_range(
            union_range(chain_map_range(self), chain_map_range(other)),
            union_range(homotopy.source.range, homotopy.target.range),
        );
        let (left, right, homotopy) = padded_homotopy(self, other, homotopy, range)?;
        let (difference, boundary) = boundary_difference(&left, &right, &homotopy)?;
        Ok(same_chain_data(&difference, &boundary))
    }
}

impl BoundedComplex {
    /// Whether two complexes have equal ranges and entrywise equal module data.
    pub fn agrees_with(&self, other: &BoundedComplex) -> bool {
        self.verify() && other.verify() && same_complex_data(self, other)
    }
}

/// A degree `+1` chain homotopy component family `h_n: X_n -> Y_(n + 1)`.
#[derive(Clone, Debug)]
pub struct ChainHomotopy {
    pub(super) source: BoundedComplex,
    pub(super) target: BoundedComplex,
    pub(super) components: Vec<Morphism>,
}

impl ChainHomotopy {
    /// Builds a homotopy component family after checking its endpoints.
    pub fn new(
        source: &BoundedComplex,
        target: &BoundedComplex,
        components: Vec<Morphism>,
    ) -> Result<ChainHomotopy, ChainMapError> {
        let range = checked_union_range(source, target)?;
        let expected = range.len().saturating_sub(1);
        if components.len() != expected {
            return Err(ChainMapError::HomotopyComponentCount {
                expected,
                got: components.len(),
            });
        }
        let source_algebra = source.terms[0].algebra().clone();
        let source = padded_with_component_endpoints(source, range, |offset| {
            components.get(offset).map_or_else(
                || Module::zero(&source_algebra),
                |component| component.source().clone(),
            )
        })?;
        let target_algebra = target.terms[0].algebra().clone();
        let target = padded_with_component_endpoints(target, range, |offset| {
            offset.checked_sub(1).map_or_else(
                || Module::zero(&target_algebra),
                |index| components[index].target().clone(),
            )
        })?;
        ChainHomotopy::new_checked(&source, &target, components)
    }

    fn new_checked(
        source: &BoundedComplex,
        target: &BoundedComplex,
        components: Vec<Morphism>,
    ) -> Result<ChainHomotopy, ChainMapError> {
        let expected = source.len().saturating_sub(1);
        if components.len() != expected {
            return Err(ChainMapError::HomotopyComponentCount {
                expected,
                got: components.len(),
            });
        }
        for (index, component) in components.iter().enumerate() {
            if !component.source().ptr_eq(&source.terms[index])
                || !component.target().ptr_eq(&target.terms[index + 1])
            {
                return Err(ChainMapError::HomotopyEndpointMismatch {
                    degree: source.range.lower + index as i32,
                });
            }
        }
        Ok(ChainHomotopy {
            source: source.clone(),
            target: target.clone(),
            components,
        })
    }

    fn padded_to(&self, range: DegreeRange) -> Result<ChainHomotopy, ChainMapError> {
        let (source, target) = padded_pair(&self.source, &self.target, range)?;
        let mut components = Vec::with_capacity(range.len().saturating_sub(1));
        for offset in 0..range.len().saturating_sub(1) {
            let degree = range.lower + offset as i32;
            if self.source.range.contains(degree) && degree < self.source.range.upper {
                components
                    .push(self.components[(degree - self.source.range.lower) as usize].clone());
            } else {
                components.push(zero_between(
                    &source.terms[offset],
                    &target.terms[offset + 1],
                ));
            }
        }
        ChainHomotopy::new_checked(&source, &target, components)
    }

    accessor_methods! {
        /// The source complex.
        pub source() -> &BoundedComplex = |this| &this.source;
        /// The target complex.
        pub target() -> &BoundedComplex = |this| &this.target;
        /// The components `h_n: X_n -> Y_(n + 1)`.
        pub components() -> &[Morphism] = |this| &this.components;
    }

    /// Computes the chain map `d h + h d`.
    pub fn boundary(&self) -> Result<ChainMap, ChainMapError> {
        let mut boundary = Vec::with_capacity(self.source.len());
        for index in 0..self.source.len() {
            let source_term = &self.source.terms[index];
            let target_term = &self.target.terms[index];
            let left = if index == 0 {
                zero_between(source_term, target_term)
            } else {
                self.source.differentials[index - 1]
                    .then(&self.components[index - 1])
                    .expect("homotopy source endpoints were checked")
            };
            let right = if index + 1 == self.source.len() {
                zero_between(source_term, target_term)
            } else {
                self.components[index]
                    .then(&self.target.differentials[index])
                    .expect("homotopy target endpoints were checked")
            };
            boundary.push(add_morphisms(&left, &right));
        }
        ChainMap::new(&self.source, &self.target, boundary)
    }

    /// Builds a homotopy from `left` to `right` and checks `left - right = d h + h d`.
    pub fn between(
        left: &ChainMap,
        right: &ChainMap,
        components: Vec<Morphism>,
    ) -> Result<ChainHomotopy, ChainMapError> {
        let range = union_range(chain_map_range(left), chain_map_range(right));
        let (left, right) = padded_chain_maps(left, right, range)?;
        if !same_map_endpoints(&left, &right) {
            return Err(ChainMapError::HomotopyEndpoint);
        }
        let (homotopy, difference, boundary) =
            checked_homotopy_difference(&left, &right, components)?;
        if !same_chain_data(&difference, &boundary) {
            return Err(ChainMapError::ChainCondition {
                degree: left.source.range.lower,
            });
        }
        Ok(homotopy)
    }

    /// Whether this homotopy rechecks against its boundary.
    pub fn verify(&self) -> bool {
        self.boundary().is_ok()
    }
}

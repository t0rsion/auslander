//! Bounded homological complexes and their homotopy category.
//!
//! A [`BoundedComplex`] stores terms in increasing homological degree. Its
//! differential at degree `n` has type `C_n -> C_(n - 1)`. A [`ChainMap`]
//! stores one module morphism in every degree and preserves this differential.
//! The shift is `(C[s])_n = C_(n - s)`, with differential multiplied by
//! `(-1)^s`. The mapping cone uses `Cone(f)_n = Y_n (+) X_(n - 1)` and
//! differential `[d_Y, f; 0, -d_X]`.

use std::sync::Arc;

use crate::complex::CheckedComplex;
use crate::decompose::add_morphisms;
use crate::field::Fp;
use crate::hom::{Morphism, identity, zero_morphism};
use crate::homspace::{HomSpace, deterministic_complement, row_times, scale_morphism, stack_rows};
use crate::linalg::DenseMat;
use crate::module::{Module, direct_sum, same_morphism_data, same_representation};

/// A finite homological degree interval.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DegreeRange {
    lower: i32,
    upper: i32,
}

impl DegreeRange {
    /// Builds a nonempty degree interval.
    pub fn new(lower: i32, upper: i32) -> Result<DegreeRange, DegreeRangeError> {
        if lower > upper {
            return Err(DegreeRangeError::Reversed { lower, upper });
        }
        Ok(DegreeRange { lower, upper })
    }

    accessor_methods! {
        /// The least stored degree.
        pub lower() -> i32 = |this| this.lower;
        /// The greatest stored degree.
        pub upper() -> i32 = |this| this.upper;
        /// The number of stored degrees.
        pub len() -> usize = |this| (this.upper as i64 - this.lower as i64 + 1) as usize;
        /// Whether this nonempty range has no degrees.
        pub is_empty() -> bool = |_this| false;
        /// Whether `degree` lies in this interval.
        pub contains(degree: i32) -> bool = |this| this.lower <= degree && degree <= this.upper;
    }

    /// The interval shifted by `amount`.
    pub fn shift(self, amount: i32) -> Result<DegreeRange, DegreeRangeError> {
        let lower = self
            .lower
            .checked_add(amount)
            .ok_or(DegreeRangeError::Overflow {
                degree: self.lower,
                shift: amount,
            })?;
        let upper = self
            .upper
            .checked_add(amount)
            .ok_or(DegreeRangeError::Overflow {
                degree: self.upper,
                shift: amount,
            })?;
        Ok(DegreeRange { lower, upper })
    }
}

/// Rejected degree interval input.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DegreeRangeError {
    /// The lower endpoint exceeds the upper endpoint.
    Reversed { lower: i32, upper: i32 },
    /// A shifted endpoint does not fit in `i32`.
    Overflow { degree: i32, shift: i32 },
}

display_error! { error DegreeRangeError {
    Self::Reversed { lower, upper } => "degree range {lower}..{upper} is reversed";
    Self::Overflow { degree, shift } => "degree {degree} cannot be shifted by {shift}";
} }

/// Rejected bounded complex input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BoundedComplexError {
    /// A bounded complex needs one stored term.
    Empty,
    /// The differential count is one less than the term count.
    DifferentialCount { expected: usize, got: usize },
    /// The named term uses another algebra value.
    DifferentAlgebras { term: usize },
    /// The differential at `degree` does not have its nominal endpoints.
    DifferentialEndpointMismatch { degree: i32 },
    /// Consecutive differentials have a nonzero composite.
    NonzeroComposite { degree: i32 },
    /// The requested degree is outside the stored interval.
    DegreeOutOfRange { degree: i32, range: DegreeRange },
    /// The degree range cannot hold one endpoint after an operation.
    DegreeOverflow { degree: i32, shift: i32 },
    /// A requested padding range does not contain the stored range.
    PaddingRange {
        requested: DegreeRange,
        stored: DegreeRange,
    },
    /// A direct sum needs at least one complex.
    NoComplexes,
    /// Direct-summed complexes use different algebra values.
    DirectSumAlgebras { complex: usize },
}

display_error! { error BoundedComplexError {
    Self::Empty => "a bounded complex needs at least one term";
    Self::DifferentialCount { expected, got } => "bounded complex has {got} differentials, expected {expected}";
    Self::DifferentAlgebras { term } => "bounded complex term {term} lives over another algebra";
    Self::DifferentialEndpointMismatch { degree } => "differential at degree {degree} has wrong endpoints";
    Self::NonzeroComposite { degree } => "differentials at degrees {degree} and {} have a nonzero composite", degree - 1;
    Self::DegreeOutOfRange { degree, range } => "degree {degree} is outside {}..{}", range.lower, range.upper;
    Self::DegreeOverflow { degree, shift } => "degree {degree} cannot be shifted by {shift}";
    Self::PaddingRange { requested, stored } => "padding range {}..{} does not contain {}..{}", requested.lower, requested.upper, stored.lower, stored.upper;
    Self::NoComplexes => "a direct sum needs one complex";
    Self::DirectSumAlgebras { complex } => "complex {complex} lives over another algebra";
} }

/// A nonempty finite homological complex with checked zero composites.
///
/// `terms[i]` has degree `range.lower() + i`. `differentials[i]` has source
/// degree `range.lower() + i + 1` and target degree `range.lower() + i`.
#[derive(Clone, Debug)]
pub struct BoundedComplex {
    range: DegreeRange,
    terms: Vec<Module>,
    differentials: Vec<Morphism>,
}

fn checked_degree(range: DegreeRange, degree: i32) -> Result<usize, BoundedComplexError> {
    if !range.contains(degree) {
        return Err(BoundedComplexError::DegreeOutOfRange { degree, range });
    }
    Ok((degree - range.lower) as usize)
}

fn negate_morphism(f: &Morphism) -> Morphism {
    let field = f.source().field();
    scale_morphism(f, field.neg(field.one()))
}

fn zero_between(source: &Module, target: &Module) -> Morphism {
    zero_morphism(source, target).expect("modules in one complex share an algebra")
}

fn shifted_complex(complex: &BoundedComplex, amount: i32) -> Result<BoundedComplex, ChainMapError> {
    complex.shift(amount).map_err(|error| match error {
        BoundedComplexError::DegreeOverflow { degree, shift } => {
            ChainMapError::DegreeOverflow { degree, shift }
        }
        _ => ChainMapError::Padding(error),
    })
}

impl BoundedComplex {
    /// Builds a bounded complex after checking algebra values, endpoints, and
    /// every composite `d_n.then(d_(n - 1))`.
    pub fn new(
        lower: i32,
        terms: Vec<Module>,
        differentials: Vec<Morphism>,
    ) -> Result<BoundedComplex, BoundedComplexError> {
        let width = terms
            .len()
            .checked_sub(1)
            .ok_or(BoundedComplexError::Empty)?;
        let shift = i32::try_from(width).map_err(|_| BoundedComplexError::DegreeOverflow {
            degree: lower,
            shift: i32::MAX,
        })?;
        let upper = lower
            .checked_add(shift)
            .ok_or(BoundedComplexError::DegreeOverflow {
                degree: lower,
                shift,
            })?;
        let range = DegreeRange { lower, upper };
        let first = terms.first().ok_or(BoundedComplexError::Empty)?;
        let expected = terms.len() - 1;
        if differentials.len() != expected {
            return Err(BoundedComplexError::DifferentialCount {
                expected,
                got: differentials.len(),
            });
        }
        if let Some(term) = terms
            .iter()
            .position(|module| !Arc::ptr_eq(first.algebra(), module.algebra()))
        {
            return Err(BoundedComplexError::DifferentAlgebras { term });
        }
        for (index, differential) in differentials.iter().enumerate() {
            let degree = lower + index as i32 + 1;
            if !differential.source().ptr_eq(&terms[index + 1])
                || !differential.target().ptr_eq(&terms[index])
            {
                return Err(BoundedComplexError::DifferentialEndpointMismatch { degree });
            }
        }
        for (index, pair) in differentials.windows(2).enumerate() {
            if !pair[1]
                .then(&pair[0])
                .expect("adjacent differentials share their middle endpoint")
                .is_zero()
            {
                return Err(BoundedComplexError::NonzeroComposite {
                    degree: lower + index as i32 + 2,
                });
            }
        }
        Ok(BoundedComplex {
            range,
            terms,
            differentials,
        })
    }

    /// Builds the homological version of a display-order checked complex.
    ///
    /// The first display term receives degree `lower`. Terms and maps are
    /// reversed so `d_n` lowers degree.
    pub fn from_checked(
        complex: &CheckedComplex,
        lower: i32,
    ) -> Result<BoundedComplex, BoundedComplexError> {
        let terms = complex.terms().iter().rev().cloned().collect();
        let differentials = complex.maps().iter().rev().cloned().collect();
        BoundedComplex::new(lower, terms, differentials)
    }

    accessor_methods! {
        /// The stored degree interval.
        pub range() -> DegreeRange = |this| this.range;
        /// The terms in increasing degree order.
        pub terms() -> &[Module] = |this| &this.terms;
        /// The differentials in increasing source-degree order.
        pub differentials() -> &[Morphism] = |this| &this.differentials;
        /// The number of stored terms.
        pub len() -> usize = |this| this.terms.len();
        /// Whether the complex has no stored terms.
        pub is_empty() -> bool = |_this| false;
        /// The least stored degree.
        pub lower() -> i32 = |this| this.range.lower;
        /// The greatest stored degree.
        pub upper() -> i32 = |this| this.range.upper;
    }

    /// The term at `degree`, or a typed range error.
    pub fn term(&self, degree: i32) -> Result<&Module, BoundedComplexError> {
        Ok(&self.terms[checked_degree(self.range, degree)?])
    }

    /// The differential `d_degree: C_degree -> C_(degree - 1)`.
    pub fn differential(&self, degree: i32) -> Option<&Morphism> {
        if degree <= self.range.lower || degree > self.range.upper {
            None
        } else {
            Some(&self.differentials[(degree - self.range.lower - 1) as usize])
        }
    }

    /// Pads the complex by explicit zero terms to `range`.
    pub fn padded_to(&self, range: DegreeRange) -> Result<BoundedComplex, BoundedComplexError> {
        if range.lower > self.range.lower || range.upper < self.range.upper {
            return Err(BoundedComplexError::PaddingRange {
                requested: range,
                stored: self.range,
            });
        }
        if range == self.range {
            return Ok(self.clone());
        }
        let mut terms = Vec::with_capacity(range.len());
        for offset in 0..range.len() {
            terms.push(padded_term(self, range.lower + offset as i32));
        }
        let mut differentials = Vec::with_capacity(range.len().saturating_sub(1));
        for offset in 0..range.len().saturating_sub(1) {
            let degree = range.lower + offset as i32 + 1;
            let source = &terms[offset + 1];
            let target = &terms[offset];
            differentials.push(
                self.differential(degree)
                    .cloned()
                    .unwrap_or_else(|| zero_between(source, target)),
            );
        }
        BoundedComplex::new(range.lower, terms, differentials)
    }

    /// Rechecks algebras, endpoints, and zero composites.
    pub fn verify(&self) -> bool {
        BoundedComplex::new(
            self.range.lower,
            self.terms.clone(),
            self.differentials.clone(),
        )
        .is_ok()
    }

    /// Whether every stored term is the zero module.
    pub fn is_zero(&self) -> bool {
        self.terms.iter().all(Module::is_zero)
    }

    /// Whether two complexes have equal ranges and entrywise equal module data.
    pub fn agrees_with(&self, other: &BoundedComplex) -> bool {
        self.range == other.range
            && self.verify()
            && other.verify()
            && self
                .terms
                .iter()
                .zip(&other.terms)
                .all(|(a, b)| same_representation(a, b))
            && self
                .differentials
                .iter()
                .zip(&other.differentials)
                .all(|(a, b)| same_morphism_data(a, b))
    }

    /// Returns the shifted complex `(C[s])_n = C_(n - s)`.
    pub fn shift(&self, amount: i32) -> Result<BoundedComplex, BoundedComplexError> {
        let range = self.range.shift(amount).map_err(|error| match error {
            DegreeRangeError::Overflow { degree, shift } => {
                BoundedComplexError::DegreeOverflow { degree, shift }
            }
            DegreeRangeError::Reversed { .. } => unreachable!(),
        })?;
        let differentials = if amount.rem_euclid(2) == 0 {
            self.differentials.clone()
        } else {
            self.differentials.iter().map(negate_morphism).collect()
        };
        BoundedComplex::new(range.lower, self.terms.clone(), differentials)
    }

    /// The direct sum of complexes, padded by zero terms to their common range.
    pub fn direct_sum(
        complexes: &[&BoundedComplex],
    ) -> Result<BoundedComplex, BoundedComplexError> {
        if complexes.is_empty() {
            return Err(BoundedComplexError::NoComplexes);
        }
        let first = complexes[0];
        for (index, complex) in complexes.iter().enumerate().skip(1) {
            if !Arc::ptr_eq(first.terms[0].algebra(), complex.terms[0].algebra()) {
                return Err(BoundedComplexError::DirectSumAlgebras { complex: index });
            }
        }
        let lower = complexes.iter().map(|c| c.lower()).min().unwrap();
        let upper = complexes.iter().map(|c| c.upper()).max().unwrap();
        let range = DegreeRange { lower, upper };
        let mut terms = Vec::with_capacity(range.len());
        for offset in 0..range.len() {
            let degree = lower + offset as i32;
            let parts: Vec<Module> = complexes
                .iter()
                .map(|complex| padded_term(complex, degree))
                .collect();
            let refs: Vec<&Module> = parts.iter().collect();
            terms.push(direct_sum(&refs).0);
        }
        let mut differentials = Vec::with_capacity(range.len().saturating_sub(1));
        for offset in 0..range.len().saturating_sub(1) {
            let degree = lower + offset as i32 + 1;
            let source_parts: Vec<Module> = complexes
                .iter()
                .map(|complex| padded_term(complex, degree))
                .collect();
            let target_parts: Vec<Module> = complexes
                .iter()
                .map(|complex| padded_term(complex, degree - 1))
                .collect();
            let blocks: Vec<Morphism> = complexes
                .iter()
                .zip(source_parts.iter().zip(&target_parts))
                .map(|(complex, (source, target))| {
                    complex
                        .differential(degree)
                        .cloned()
                        .unwrap_or_else(|| zero_between(source, target))
                })
                .collect();
            differentials.push(block_diagonal_map(
                &source_parts,
                &target_parts,
                &blocks,
                &terms[offset + 1],
                &terms[offset],
            ));
        }
        BoundedComplex::new(lower, terms, differentials)
    }
}

/// Builds the direct sum of bounded complexes, padding by zero terms.
pub fn direct_sum_complexes(
    complexes: &[&BoundedComplex],
) -> Result<BoundedComplex, BoundedComplexError> {
    BoundedComplex::direct_sum(complexes)
}

fn padded_term(complex: &BoundedComplex, degree: i32) -> Module {
    if complex.range.contains(degree) {
        complex.terms[(degree - complex.range.lower) as usize].clone()
    } else {
        Module::zero(complex.terms[0].algebra())
    }
}

fn block_diagonal_map(
    source_parts: &[Module],
    target_parts: &[Module],
    blocks: &[Morphism],
    source_sum: &Module,
    target_sum: &Module,
) -> Morphism {
    assert_eq!(source_parts.len(), target_parts.len());
    assert_eq!(source_parts.len(), blocks.len());
    let vertices = source_sum.algebra().quiver().num_vertices() as usize;
    let mut source_offsets = vec![0usize; source_parts.len() * vertices];
    let mut target_offsets = vec![0usize; target_parts.len() * vertices];
    for k in 0..source_parts.len() {
        for v in 0..vertices {
            source_offsets[k * vertices + v] =
                source_parts[..k].iter().map(|m| m.dim_at(v as u32)).sum();
            target_offsets[k * vertices + v] =
                target_parts[..k].iter().map(|m| m.dim_at(v as u32)).sum();
        }
    }
    let maps = (0..vertices)
        .map(|v| {
            let mut matrix =
                DenseMat::zero(source_sum.dim_at(v as u32), target_sum.dim_at(v as u32));
            for (k, block) in blocks.iter().enumerate() {
                for row in 0..block.map_at(v as u32).rows() {
                    for col in 0..block.map_at(v as u32).cols() {
                        matrix.set(
                            source_offsets[k * vertices + v] + row,
                            target_offsets[k * vertices + v] + col,
                            block.map_at(v as u32).get(row, col),
                        );
                    }
                }
            }
            matrix
        })
        .collect();
    Morphism::new(source_sum, target_sum, maps).expect("block diagonal maps are A-linear")
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
    source: BoundedComplex,
    target: BoundedComplex,
    components: Vec<Morphism>,
}

fn same_complex_identity(a: &BoundedComplex, b: &BoundedComplex) -> bool {
    a.range == b.range
        && a.terms.iter().zip(&b.terms).all(|(x, y)| x.ptr_eq(y))
        && a.differentials == b.differentials
}

fn same_differential_data(a: &BoundedComplex, b: &BoundedComplex) -> bool {
    a.differentials.len() == b.differentials.len()
        && a.differentials
            .iter()
            .zip(&b.differentials)
            .all(|(left, right)| same_morphism_data(left, right))
}

fn same_complex_for_padding(a: &BoundedComplex, b: &BoundedComplex) -> bool {
    same_complex_identity(a, b) || same_complex_data(a, b)
}

fn same_complex_data(a: &BoundedComplex, b: &BoundedComplex) -> bool {
    a.range == b.range
        && a.terms
            .iter()
            .zip(&b.terms)
            .all(|(left, right)| same_representation(left, right))
        && same_differential_data(a, b)
}

fn agrees_after_padding(a: &BoundedComplex, b: &BoundedComplex) -> bool {
    a.padded_to(b.range)
        .is_ok_and(|padded| padded.agrees_with(b))
}

fn union_range(left: DegreeRange, right: DegreeRange) -> DegreeRange {
    DegreeRange {
        lower: left.lower.min(right.lower),
        upper: left.upper.max(right.upper),
    }
}

fn padded_with_component_endpoints(
    complex: &BoundedComplex,
    range: DegreeRange,
    endpoints: &[Module],
) -> Result<BoundedComplex, ChainMapError> {
    let mut terms = Vec::with_capacity(range.len());
    for (offset, endpoint) in endpoints.iter().enumerate().take(range.len()) {
        let degree = range.lower + offset as i32;
        if complex.range.contains(degree) {
            terms.push(complex.terms[(degree - complex.range.lower) as usize].clone());
        } else {
            let endpoint = endpoint.clone();
            let zero = Module::zero(complex.terms[0].algebra());
            if !endpoint.is_zero() || !same_representation(&endpoint, &zero) {
                return Err(ChainMapError::ComponentEndpointMismatch { degree });
            }
            terms.push(endpoint);
        }
    }
    let mut differentials = Vec::with_capacity(range.len().saturating_sub(1));
    for offset in 0..range.len().saturating_sub(1) {
        let degree = range.lower + offset as i32 + 1;
        let source = &terms[offset + 1];
        let target = &terms[offset];
        differentials.push(
            complex
                .differential(degree)
                .cloned()
                .unwrap_or_else(|| zero_between(source, target)),
        );
    }
    BoundedComplex::new(range.lower, terms, differentials).map_err(ChainMapError::Padding)
}

fn rebase_morphism(f: &Morphism, source: &Module, target: &Module) -> Morphism {
    let maps = (0..source.algebra().quiver().num_vertices() as usize)
        .map(|vertex| f.map_at(vertex as u32).clone())
        .collect();
    Morphism::new(source, target, maps)
        .expect("structurally equal padded modules preserve A-linearity")
}

fn same_chain_data(a: &ChainMap, b: &ChainMap) -> bool {
    same_complex_data(&a.source, &b.source)
        && same_complex_data(&a.target, &b.target)
        && a.components.iter().zip(&b.components).all(|(left, right)| {
            same_representation(left.source(), right.source())
                && same_representation(left.target(), right.target())
                && (0..left.source().algebra().quiver().num_vertices())
                    .all(|vertex| left.map_at(vertex) == right.map_at(vertex))
        })
}

fn same_chain_map(a: &ChainMap, b: &ChainMap) -> bool {
    same_chain_data(a, b)
}

impl ChainMap {
    /// Builds a chain map after checking endpoints and every chain equation.
    pub fn new(
        source: &BoundedComplex,
        target: &BoundedComplex,
        components: Vec<Morphism>,
    ) -> Result<ChainMap, ChainMapError> {
        if !Arc::ptr_eq(source.terms[0].algebra(), target.terms[0].algebra()) {
            return Err(ChainMapError::DifferentAlgebras);
        }
        let range = union_range(source.range, target.range);
        if components.len() != range.len() {
            return Err(ChainMapError::ComponentCount {
                expected: range.len(),
                got: components.len(),
            });
        }
        let source_endpoints: Vec<Module> = components
            .iter()
            .map(|component| component.source().clone())
            .collect();
        let target_endpoints: Vec<Module> = components
            .iter()
            .map(|component| component.target().clone())
            .collect();
        let source = padded_with_component_endpoints(source, range, &source_endpoints)?;
        let target = padded_with_component_endpoints(target, range, &target_endpoints)?;
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
        let source = source.padded_to(range).map_err(ChainMapError::Padding)?;
        let target = target.padded_to(range).map_err(ChainMapError::Padding)?;
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
        same_chain_map(self, other)
    }

    /// Recomputes the chain equations and compares the stored map data.
    pub fn verify(&self) -> bool {
        let Ok(rebuilt) = ChainMap::new(&self.source, &self.target, self.components.clone()) else {
            return false;
        };
        same_chain_data(self, &rebuilt)
    }

    fn padded_to(&self, range: DegreeRange) -> Result<ChainMap, ChainMapError> {
        let source = self
            .source
            .padded_to(range)
            .map_err(ChainMapError::Padding)?;
        let target = self
            .target
            .padded_to(range)
            .map_err(ChainMapError::Padding)?;
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
        let range = union_range(
            union_range(self.source.range, self.target.range),
            union_range(other.source.range, other.target.range),
        );
        let left = self.padded_to(range)?;
        let right = other.padded_to(range)?;
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
        let range = union_range(
            union_range(self.source.range, self.target.range),
            union_range(other.source.range, other.target.range),
        );
        let left = self.padded_to(range)?;
        let right = other.padded_to(range)?;
        if !same_complex_for_padding(&left.source, &right.source)
            || !same_complex_for_padding(&left.target, &right.target)
        {
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
        let source = self.source.shift(amount).map_err(|error| match error {
            BoundedComplexError::DegreeOverflow { degree, shift } => {
                ChainMapError::DegreeOverflow { degree, shift }
            }
            _ => unreachable!(),
        })?;
        let target = self.target.shift(amount).map_err(|error| match error {
            BoundedComplexError::DegreeOverflow { degree, shift } => {
                ChainMapError::DegreeOverflow { degree, shift }
            }
            _ => unreachable!(),
        })?;
        ChainMap::new(&source, &target, self.components.clone())
    }

    /// Returns the homotopy boundary of `homotopy`, namely `d h + h d`.
    pub fn homotopic_to(
        &self,
        other: &ChainMap,
        homotopy: &ChainHomotopy,
    ) -> Result<bool, ChainMapError> {
        let range = union_range(
            union_range(
                union_range(self.source.range, self.target.range),
                union_range(other.source.range, other.target.range),
            ),
            union_range(homotopy.source.range, homotopy.target.range),
        );
        let left = self.padded_to(range)?;
        let right = other.padded_to(range)?;
        let homotopy = homotopy.padded_to(range)?;
        if !same_complex_for_padding(&left.source, &right.source)
            || !same_complex_for_padding(&left.target, &right.target)
            || !same_complex_for_padding(&left.source, &homotopy.source)
            || !same_complex_for_padding(&left.target, &homotopy.target)
        {
            return Err(ChainMapError::HomotopyEndpoint);
        }
        let boundary = homotopy.boundary()?;
        let difference = right
            .scale(
                left.source.terms[0]
                    .field()
                    .neg(left.source.terms[0].field().one()),
            )
            .add(&left)?;
        Ok(same_chain_data(&difference, &boundary))
    }

    /// Whether this map represents zero modulo chain homotopy.
    pub fn is_null_homotopic(&self) -> Result<bool, ChainMapError> {
        let quotient = ChainHomSpace::new(&self.source, &self.target)
            .map_err(|_| ChainMapError::OutsideHomSpace)?
            .quotient()?;
        Ok(quotient.reduce(self)?.0.iter().all(|x| x.is_zero()))
    }

    /// Builds the mapping cone `Cone(self)`.
    pub fn mapping_cone(&self) -> Result<BoundedComplex, BoundedComplexError> {
        mapping_cone_impl(self)
    }
}

/// A degree `+1` chain homotopy component family `h_n: X_n -> Y_(n + 1)`.
#[derive(Clone, Debug)]
pub struct ChainHomotopy {
    source: BoundedComplex,
    target: BoundedComplex,
    components: Vec<Morphism>,
}

impl ChainHomotopy {
    /// Builds a homotopy component family after checking its endpoints.
    pub fn new(
        source: &BoundedComplex,
        target: &BoundedComplex,
        components: Vec<Morphism>,
    ) -> Result<ChainHomotopy, ChainMapError> {
        if !Arc::ptr_eq(source.terms[0].algebra(), target.terms[0].algebra()) {
            return Err(ChainMapError::DifferentAlgebras);
        }
        let range = union_range(source.range, target.range);
        let expected = range.len().saturating_sub(1);
        if components.len() != expected {
            return Err(ChainMapError::HomotopyComponentCount {
                expected,
                got: components.len(),
            });
        }
        let source_endpoints: Vec<Module> = (0..range.len())
            .map(|offset| {
                let degree = range.lower + offset as i32;
                if source.range.contains(degree) {
                    source.terms[(degree - source.range.lower) as usize].clone()
                } else if offset < expected {
                    components[offset].source().clone()
                } else {
                    Module::zero(source.terms[0].algebra())
                }
            })
            .collect();
        let target_endpoints: Vec<Module> = (0..range.len())
            .map(|offset| {
                let degree = range.lower + offset as i32;
                if target.range.contains(degree) {
                    target.terms[(degree - target.range.lower) as usize].clone()
                } else if offset > 0 {
                    components[offset - 1].target().clone()
                } else {
                    Module::zero(target.terms[0].algebra())
                }
            })
            .collect();
        let source = padded_with_component_endpoints(source, range, &source_endpoints)?;
        let target = padded_with_component_endpoints(target, range, &target_endpoints)?;
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
        let source = self
            .source
            .padded_to(range)
            .map_err(ChainMapError::Padding)?;
        let target = self
            .target
            .padded_to(range)
            .map_err(ChainMapError::Padding)?;
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
        let range = union_range(
            union_range(left.source.range, left.target.range),
            union_range(right.source.range, right.target.range),
        );
        let left = left.padded_to(range)?;
        let right = right.padded_to(range)?;
        if !same_complex_for_padding(&left.source, &right.source)
            || !same_complex_for_padding(&left.target, &right.target)
        {
            return Err(ChainMapError::HomotopyEndpoint);
        }
        let homotopy = ChainHomotopy::new(&left.source, &left.target, components)?;
        let boundary = homotopy.boundary()?;
        let difference = right
            .scale(
                left.source.terms[0]
                    .field()
                    .neg(left.source.terms[0].field().one()),
            )
            .add(&left)?;
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
    let mut terms = Vec::with_capacity(range.len());
    for offset in 0..range.len() {
        let degree = lower + offset as i32;
        let y = padded_term(&map.target, degree);
        let x = padded_term(&map.source, degree - 1);
        let refs = [&y, &x];
        terms.push(direct_sum(&refs).0);
    }
    let mut differentials = Vec::with_capacity(range.len().saturating_sub(1));
    for offset in 0..range.len().saturating_sub(1) {
        let degree = lower + offset as i32 + 1;
        let y_source = padded_term(&map.target, degree);
        let x_source = padded_term(&map.source, degree - 1);
        let y_target = padded_term(&map.target, degree - 1);
        let x_target = padded_term(&map.source, degree - 2);
        let d_y = map
            .target
            .differential(degree)
            .cloned()
            .unwrap_or_else(|| zero_between(&y_source, &y_target));
        let f = if map.source.range.contains(degree - 1) {
            map.components[(degree - 1 - map.source.lower()) as usize].clone()
        } else {
            zero_between(&x_source, &y_target)
        };
        let d_x = map
            .source
            .differential(degree - 1)
            .cloned()
            .map(|d| negate_morphism(&d))
            .unwrap_or_else(|| zero_between(&x_source, &x_target));
        let source_parts = [y_source, x_source];
        let target_parts = [y_target, x_target];
        let blocks = [d_y, f, d_x];
        let source_sum = &terms[offset + 1];
        let target_sum = &terms[offset];
        let field = source_sum.field();
        let vertices = source_sum.algebra().quiver().num_vertices() as usize;
        let mut source_offsets = [vec![0usize; vertices], vec![0usize; vertices]];
        let mut target_offsets = [vec![0usize; vertices], vec![0usize; vertices]];
        for v in 0..vertices {
            source_offsets[1][v] = source_parts[0].dim_at(v as u32);
            target_offsets[1][v] = target_parts[0].dim_at(v as u32);
        }
        let matrices: Vec<DenseMat> = (0..vertices)
            .map(|v| {
                let mut matrix =
                    DenseMat::zero(source_sum.dim_at(v as u32), target_sum.dim_at(v as u32));
                for (block_index, block) in blocks.iter().enumerate() {
                    let (source_offset, target_offset) = match block_index {
                        0 => (0, 0),
                        1 => (source_offsets[1][v], 0),
                        2 => (source_offsets[1][v], target_offsets[1][v]),
                        _ => unreachable!(),
                    };
                    for row in 0..block.map_at(v as u32).rows() {
                        for col in 0..block.map_at(v as u32).cols() {
                            matrix.set(
                                source_offset + row,
                                target_offset + col,
                                field.add(
                                    matrix.get(source_offset + row, target_offset + col),
                                    block.map_at(v as u32).get(row, col),
                                ),
                            );
                        }
                    }
                }
                matrix
            })
            .collect();
        differentials.push(
            Morphism::new(source_sum, target_sum, matrices)
                .expect("mapping cone block differential is A-linear"),
        );
    }
    BoundedComplex::new(lower, terms, differentials)
}

/// A deterministic basis of chain maps between two bounded complexes.
#[derive(Clone, Debug)]
pub struct ChainHomSpace {
    source: BoundedComplex,
    target: BoundedComplex,
    components: Vec<HomSpace>,
    flat: DenseMat,
}

fn chain_flat(map: &ChainMap, spaces: &[HomSpace]) -> Vec<Fp> {
    let mut row = Vec::new();
    for (component, space) in map.components.iter().zip(spaces) {
        let component = if component.source().ptr_eq(space.source())
            && component.target().ptr_eq(space.target())
        {
            component.clone()
        } else {
            rebase_morphism(component, space.source(), space.target())
        };
        row.extend(
            space
                .coords(&component)
                .expect("chain map component has matching endpoints"),
        );
    }
    row
}

fn chain_map_from_flat(
    source: &BoundedComplex,
    target: &BoundedComplex,
    spaces: &[HomSpace],
    row: &[Fp],
) -> ChainMap {
    let mut components = Vec::with_capacity(spaces.len());
    let mut offset = 0;
    for space in spaces {
        let end = offset + space.dim();
        components.push(space.morphism(&row[offset..end]));
        offset = end;
    }
    ChainMap::new(source, target, components)
        .expect("chain Hom kernel rows satisfy the chain equations")
}

fn chain_constraints(
    source: &BoundedComplex,
    target: &BoundedComplex,
    spaces: &[HomSpace],
) -> DenseMat {
    let width: usize = spaces.iter().map(HomSpace::dim).sum();
    let mut offsets = Vec::with_capacity(spaces.len());
    let mut cursor = 0;
    for space in spaces {
        offsets.push(cursor);
        cursor += space.dim();
    }
    let mut rows: Vec<Vec<Fp>> = Vec::new();
    for index in 1..source.len() {
        let equation = HomSpace::new(&source.terms[index], &target.terms[index - 1])
            .expect("chain equation endpoints share the algebra");
        let equation_dim = equation.dim();
        let mut contributions: Vec<Vec<Fp>> =
            vec![vec![source.terms[0].field().zero(); width]; equation_dim];
        for (variable_index, space) in spaces.iter().enumerate() {
            for basis_index in 0..space.dim() {
                let basis = space.basis_morphism(basis_index);
                let contribution = if variable_index == index - 1 {
                    source.differentials[index - 1]
                        .then(&basis)
                        .expect("source differential and component endpoints match")
                } else if variable_index == index {
                    scale_morphism(
                        &basis
                            .then(&target.differentials[index - 1])
                            .expect("component and target differential endpoints match"),
                        source.terms[0].field().neg(source.terms[0].field().one()),
                    )
                } else {
                    continue;
                };
                let coordinates = equation
                    .coords(&contribution)
                    .expect("a composite of module morphisms lies in the equation Hom space");
                for (row, value) in coordinates.into_iter().enumerate() {
                    contributions[row][offsets[variable_index] + basis_index] = value;
                }
            }
        }
        rows.extend(contributions);
    }
    DenseMat::from_rows_with_cols(&rows, width)
}

fn homotopy_rows(
    source: &BoundedComplex,
    target: &BoundedComplex,
    spaces: &[HomSpace],
    ambient: &DenseMat,
) -> DenseMat {
    let field = source.terms[0].field();
    let mut rows = Vec::new();
    for index in 0..source.len().saturating_sub(1) {
        let space = HomSpace::new(&source.terms[index], &target.terms[index + 1])
            .expect("homotopy endpoints share the algebra");
        for basis_index in 0..space.dim() {
            let mut components = Vec::with_capacity(source.len().saturating_sub(1));
            for j in 0..source.len().saturating_sub(1) {
                let source_term = &source.terms[j];
                let target_term = &target.terms[j + 1];
                components.push(if j == index {
                    space.basis_morphism(basis_index)
                } else {
                    zero_between(source_term, target_term)
                });
            }
            let homotopy = ChainHomotopy::new(source, target, components)
                .expect("homotopy basis components have matching endpoints");
            let boundary = homotopy
                .boundary()
                .expect("homotopy boundary is a chain map");
            rows.push(chain_flat(&boundary, spaces));
        }
    }
    let inner = DenseMat::from_rows_with_cols(&rows, ambient.cols());
    inner.row_space_basis(&field)
}

impl ChainHomSpace {
    /// Builds the chain-map Hom space by solving the chain equations.
    pub fn new(
        source: &BoundedComplex,
        target: &BoundedComplex,
    ) -> Result<ChainHomSpace, ChainMapError> {
        if !Arc::ptr_eq(source.terms[0].algebra(), target.terms[0].algebra()) {
            return Err(ChainMapError::DifferentAlgebras);
        }
        let range = union_range(source.range, target.range);
        let source = source.padded_to(range).map_err(ChainMapError::Padding)?;
        let target = target.padded_to(range).map_err(ChainMapError::Padding)?;
        let components: Vec<HomSpace> = source
            .terms
            .iter()
            .zip(&target.terms)
            .map(|(source, target)| HomSpace::new(source, target).expect("algebras were checked"))
            .collect();
        let constraints = chain_constraints(&source, &target, &components);
        let flat = constraints.kernel_basis(&source.terms[0].field());
        Ok(ChainHomSpace {
            source: source.clone(),
            target: target.clone(),
            components,
            flat,
        })
    }

    accessor_methods! {
        /// The source complex.
        pub source() -> &BoundedComplex = |this| &this.source;
        /// The target complex.
        pub target() -> &BoundedComplex = |this| &this.target;
        /// The dimension of the chain-map space.
        pub dim() -> usize = |this| this.flat.rows();
        /// The chain-map basis in deterministic kernel order.
        pub basis_rows() -> &DenseMat = |this| &this.flat;
    }

    /// The basis chain map at `index`.
    pub fn basis_morphism(&self, index: usize) -> ChainMap {
        chain_map_from_flat(
            &self.source,
            &self.target,
            &self.components,
            self.flat.row(index),
        )
    }

    /// All basis chain maps in deterministic order.
    pub fn basis_iter(&self) -> impl Iterator<Item = ChainMap> + '_ {
        (0..self.dim()).map(|index| self.basis_morphism(index))
    }

    /// Rebuilds a chain map from coordinates in the chain-map basis.
    pub fn morphism(&self, coordinates: &[Fp]) -> ChainMap {
        assert_eq!(coordinates.len(), self.dim());
        let row = row_times(coordinates, &self.flat, &self.source.terms[0].field());
        chain_map_from_flat(&self.source, &self.target, &self.components, &row)
    }

    /// Coordinates of a chain map in the deterministic basis.
    pub fn coords(&self, map: &ChainMap) -> Result<Vec<Fp>, ChainMapError> {
        if !same_complex_data(&self.source, &map.source)
            || !same_complex_data(&self.target, &map.target)
        {
            return Err(ChainMapError::OutsideHomSpace);
        }
        let row = chain_flat(map, &self.components);
        self.flat
            .transpose()
            .solve(&row, &self.source.terms[0].field())
            .ok_or(ChainMapError::OutsideHomSpace)
    }

    /// Recomputes the chain-map equations and compares their deterministic basis.
    pub fn verify(&self) -> bool {
        let Ok(rebuilt) = ChainHomSpace::new(&self.source, &self.target) else {
            return false;
        };
        rebuilt.flat == self.flat
    }

    /// The quotient by null-homotopic chain maps.
    pub fn quotient(&self) -> Result<ChainHomQuotient, ChainMapError> {
        let null = homotopy_rows(&self.source, &self.target, &self.components, &self.flat);
        for row in 0..null.rows() {
            if self
                .flat
                .transpose()
                .solve(null.row(row), &self.source.terms[0].field())
                .is_none()
            {
                return Err(ChainMapError::OutsideHomSpace);
            }
        }
        let complement = deterministic_complement(&self.flat, &null, &self.source.terms[0].field());
        Ok(ChainHomQuotient {
            space: self.clone(),
            null,
            complement,
        })
    }
}

impl CheckedComplex {
    /// Converts a display-order checked complex to homological degree order.
    pub fn bounded(&self, lower: i32) -> Result<BoundedComplex, BoundedComplexError> {
        BoundedComplex::from_checked(self, lower)
    }
}

/// Hom chain maps modulo null-homotopic maps.
#[derive(Clone, Debug)]
pub struct ChainHomQuotient {
    space: ChainHomSpace,
    null: DenseMat,
    complement: DenseMat,
}

impl ChainHomQuotient {
    accessor_methods! {
        /// The source complex.
        pub source() -> &BoundedComplex = |this| this.space.source();
        /// The target complex.
        pub target() -> &BoundedComplex = |this| this.space.target();
        /// The quotient dimension.
        pub dim() -> usize = |this| this.complement.rows();
        /// The null-homotopic subspace in component coordinates.
        pub null_homotopic_basis() -> &DenseMat = |this| &this.null;
        /// The deterministic quotient complement in component coordinates.
        pub complement_basis() -> &DenseMat = |this| &this.complement;
    }

    /// Recomputes the ambient space, null-homotopic subspace, and complement.
    pub fn verify(&self) -> bool {
        self.space.verify()
            && self.space.quotient().is_ok_and(|rebuilt| {
                rebuilt.null == self.null && rebuilt.complement == self.complement
            })
    }

    /// Rebuilds a quotient representative from complement coordinates.
    pub fn representative(&self, coordinates: &[Fp]) -> ChainMap {
        assert_eq!(coordinates.len(), self.dim());
        let row = row_times(
            coordinates,
            &self.complement,
            &self.space.source.terms[0].field(),
        );
        chain_map_from_flat(
            &self.space.source,
            &self.space.target,
            &self.space.components,
            &row,
        )
    }

    /// Reduces a chain map to quotient coordinates and a null-homotopic remainder.
    pub fn reduce(&self, map: &ChainMap) -> Result<(Vec<Fp>, ChainMap), ChainMapError> {
        if !same_complex_data(&self.space.source, &map.source)
            || !same_complex_data(&self.space.target, &map.target)
        {
            return Err(ChainMapError::OutsideHomSpace);
        }
        let field = self.space.source.terms[0].field();
        let row = chain_flat(map, &self.space.components);
        let stacked = stack_rows(&[&self.complement, &self.null], self.complement.cols());
        let Some(coordinates) = stacked.transpose().solve(&row, &field) else {
            return Err(ChainMapError::OutsideHomSpace);
        };
        let quotient_coordinates = coordinates[..self.complement.rows()].to_vec();
        let null_row = row_times(&coordinates[self.complement.rows()..], &self.null, &field);
        Ok((
            quotient_coordinates,
            chain_map_from_flat(
                &self.space.source,
                &self.space.target,
                &self.space.components,
                &null_row,
            ),
        ))
    }
}

/// The degree-`q` chain Hom space obtained from `target.shift(q)`.
#[derive(Clone, Debug)]
pub struct HomotopyHom {
    degree: i32,
    source: BoundedComplex,
    target: BoundedComplex,
    shifted_target: BoundedComplex,
    space: ChainHomSpace,
}

impl HomotopyHom {
    /// Builds degree-`q` chain maps and retains the unshifted target.
    pub fn new(
        source: &BoundedComplex,
        target: &BoundedComplex,
        degree: i32,
    ) -> Result<HomotopyHom, ChainMapError> {
        let shifted_target = shifted_complex(target, degree)?;
        let space = ChainHomSpace::new(source, &shifted_target)?;
        Ok(HomotopyHom {
            degree,
            source: source.clone(),
            target: target.clone(),
            shifted_target,
            space,
        })
    }

    accessor_methods! {
        /// The retained degree `q`.
        pub degree() -> i32 = |this| this.degree;
        /// The unshifted source complex.
        pub source() -> &BoundedComplex = |this| &this.source;
        /// The unshifted target complex.
        pub target() -> &BoundedComplex = |this| &this.target;
        /// The target complex used by the degree-zero chain-map solver.
        pub shifted_target() -> &BoundedComplex = |this| &this.shifted_target;
        /// The normalized degree-zero chain Hom space.
        pub chain_space() -> &ChainHomSpace = |this| &this.space;
        /// The dimension of the degree-`q` chain-map space.
        pub dim() -> usize = |this| this.space.dim();
        /// The deterministic cycle basis in component coordinates.
        pub basis_rows() -> &DenseMat = |this| this.space.basis_rows();
    }

    /// The basis degree-`q` chain map at `index`.
    pub fn basis_morphism(&self, index: usize) -> ChainMap {
        self.space.basis_morphism(index)
    }

    /// All basis degree-`q` chain maps in deterministic order.
    pub fn basis_iter(&self) -> impl Iterator<Item = ChainMap> + '_ {
        self.space.basis_iter()
    }

    /// Rebuilds a degree-`q` chain map from deterministic coordinates.
    pub fn morphism(&self, coordinates: &[Fp]) -> ChainMap {
        self.space.morphism(coordinates)
    }

    /// Coordinates of a degree-`q` chain map in the deterministic basis.
    pub fn coords(&self, map: &ChainMap) -> Result<Vec<Fp>, ChainMapError> {
        self.space.coords(map)
    }

    /// Recomputes the shift and cycle basis stored by this value.
    pub fn verify(&self) -> bool {
        let Ok(shifted_target) = shifted_complex(&self.target, self.degree) else {
            return false;
        };
        agrees_after_padding(&self.source, self.space.source())
            && self.shifted_target.agrees_with(&shifted_target)
            && agrees_after_padding(&self.shifted_target, self.space.target())
            && self.space.verify()
    }

    /// Returns the quotient by null-homotopic degree-`q` maps.
    pub fn quotient(&self) -> Result<HomotopyHomQuotient, ChainMapError> {
        Ok(HomotopyHomQuotient {
            hom: self.clone(),
            quotient: self.space.quotient()?,
        })
    }
}

/// Degree-`q` chain Hom modulo null-homotopic maps.
#[derive(Clone, Debug)]
pub struct HomotopyHomQuotient {
    hom: HomotopyHom,
    quotient: ChainHomQuotient,
}

impl HomotopyHomQuotient {
    accessor_methods! {
        /// The degree-`q` Hom value behind this quotient.
        pub hom() -> &HomotopyHom = |this| &this.hom;
        /// The retained degree `q`.
        pub degree() -> i32 = |this| this.hom.degree();
        /// The unshifted source complex.
        pub source() -> &BoundedComplex = |this| this.hom.source();
        /// The unshifted target complex.
        pub target() -> &BoundedComplex = |this| this.hom.target();
        /// The shifted target used by the chain-map solver.
        pub shifted_target() -> &BoundedComplex = |this| this.hom.shifted_target();
        /// The quotient dimension.
        pub dim() -> usize = |this| this.quotient.dim();
        /// The null-homotopic basis in component coordinates.
        pub null_homotopic_basis() -> &DenseMat = |this| this.quotient.null_homotopic_basis();
        /// The deterministic quotient complement in component coordinates.
        pub complement_basis() -> &DenseMat = |this| this.quotient.complement_basis();
    }

    /// Recomputes the shift, cycle basis, boundary basis, and complement.
    pub fn verify(&self) -> bool {
        self.hom.verify()
            && self.quotient.verify()
            && agrees_after_padding(self.hom.source(), self.quotient.source())
            && agrees_after_padding(self.hom.shifted_target(), self.quotient.target())
    }

    /// Rebuilds a quotient representative from complement coordinates.
    pub fn representative(&self, coordinates: &[Fp]) -> ChainMap {
        self.quotient.representative(coordinates)
    }

    /// Reduces a degree-`q` chain map to class coordinates and a null map.
    pub fn reduce(&self, map: &ChainMap) -> Result<(Vec<Fp>, ChainMap), ChainMapError> {
        self.quotient.reduce(map)
    }
}

/// A short name for the bounded homological complex type.
pub type DegreeComplex = BoundedComplex;

/// A short name for a chain homotopy.
pub type Homotopy = ChainHomotopy;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::linear_an;
    use crate::field::PrimeField;
    use crate::module::Module;

    fn f5() -> PrimeField {
        PrimeField::new(5).unwrap()
    }

    fn one_term() -> (Arc<crate::algebra::Algebra>, Module) {
        let algebra = linear_an(1, f5());
        let module = Module::simple(&algebra, 0);
        (algebra, module)
    }

    fn zero_differential(m: &Module) -> Morphism {
        zero_between(m, m)
    }

    #[test]
    fn constructor_uses_homological_degree_order() {
        let (_algebra, simple) = one_term();
        let complex = BoundedComplex::new(
            -1,
            vec![simple.clone(), simple.clone()],
            vec![zero_differential(&simple)],
        )
        .unwrap();
        assert_eq!(complex.range(), DegreeRange::new(-1, 0).unwrap());
        assert!(complex.differential(0).unwrap().source().ptr_eq(&simple));
        assert!(complex.verify());
    }

    #[test]
    fn odd_shift_negates_differentials_and_moves_degrees() {
        let (_algebra, simple) = one_term();
        let differential = zero_differential(&simple);
        let complex =
            BoundedComplex::new(0, vec![simple.clone(), simple], vec![differential]).unwrap();
        let shifted = complex.shift(1).unwrap();
        assert_eq!(shifted.range(), DegreeRange::new(1, 2).unwrap());
        assert!(shifted.verify());
        assert!(shifted.differential(2).unwrap().is_zero());
    }

    #[test]
    fn identity_and_zero_chain_maps_check_composition() {
        let (_algebra, simple) = one_term();
        let complex = BoundedComplex::new(
            0,
            vec![simple.clone(), simple.clone()],
            vec![zero_differential(&simple)],
        )
        .unwrap();
        let identity = ChainMap::identity(&complex);
        let zero = ChainMap::zero(&complex, &complex).unwrap();
        assert!(identity.then(&identity).unwrap().agrees_with(&identity));
        assert!(zero.then(&identity).unwrap().agrees_with(&zero));
        assert_eq!(
            ChainMap::new(&complex, &complex, vec![identity.components()[0].clone()]).unwrap_err(),
            ChainMapError::ComponentCount {
                expected: 2,
                got: 1
            }
        );
        assert!(identity.verify());
    }

    #[test]
    fn composition_rejects_same_terms_with_different_differentials() {
        let (_algebra, simple) = one_term();
        let zero = BoundedComplex::new(
            0,
            vec![simple.clone(), simple.clone()],
            vec![zero_differential(&simple)],
        )
        .unwrap();
        let nonzero = BoundedComplex::new(
            0,
            vec![simple.clone(), simple.clone()],
            vec![identity(&simple)],
        )
        .unwrap();
        let left = ChainMap::identity(&nonzero);
        let right = ChainMap::identity(&zero);
        assert_eq!(
            left.then(&right).unwrap_err(),
            ChainMapError::CompositionMismatch
        );
    }

    #[test]
    fn zero_homotopy_has_zero_boundary() {
        let (_algebra, simple) = one_term();
        let complex = BoundedComplex::new(
            0,
            vec![simple.clone(), simple.clone()],
            vec![zero_differential(&simple)],
        )
        .unwrap();
        let h = ChainHomotopy::new(
            &complex,
            &complex,
            vec![zero_differential(&complex.terms()[0])],
        )
        .unwrap();
        assert!(
            h.boundary()
                .unwrap()
                .components()
                .iter()
                .all(Morphism::is_zero)
        );
    }

    #[test]
    fn cone_of_zero_map_has_signed_square_zero() {
        let (_algebra, simple) = one_term();
        let complex = BoundedComplex::new(
            0,
            vec![simple.clone(), simple.clone()],
            vec![zero_differential(&simple)],
        )
        .unwrap();
        let zero = ChainMap::zero(&complex, &complex).unwrap();
        let cone = zero.mapping_cone().unwrap();
        assert_eq!(cone.range(), DegreeRange::new(0, 2).unwrap());
        assert!(cone.verify());
    }

    #[test]
    fn chain_hom_quotient_reduces_a_null_homotopic_map() {
        let (_algebra, simple) = one_term();
        let complex = BoundedComplex::new(
            0,
            vec![simple.clone(), simple.clone()],
            vec![zero_differential(&simple)],
        )
        .unwrap();
        let space = ChainHomSpace::new(&complex, &complex).unwrap();
        let quotient = space.quotient().unwrap();
        assert_eq!(quotient.dim(), space.dim());
        let map = space.basis_morphism(0);
        let (coordinates, remainder) = quotient.reduce(&map).unwrap();
        assert_eq!(coordinates.len(), quotient.dim());
        let rebuilt = quotient
            .representative(&coordinates)
            .add(&remainder)
            .unwrap();
        assert!(map.agrees_with(&rebuilt));
    }

    #[test]
    fn identity_differential_complex_is_zero_in_the_homotopy_category() {
        let (_algebra, simple) = one_term();
        let identity = identity(&simple);
        let complex = BoundedComplex::new(0, vec![simple.clone(), simple], vec![identity]).unwrap();
        let space = ChainHomSpace::new(&complex, &complex).unwrap();
        let quotient = space.quotient().unwrap();
        assert_eq!(space.dim(), 1);
        assert_eq!(quotient.null_homotopic_basis().rows(), 1);
        assert_eq!(quotient.dim(), 0);
        for map in space.basis_iter() {
            assert!(map.is_null_homotopic().unwrap());
        }
    }

    #[test]
    fn chain_maps_pad_different_supports_to_the_union() {
        let algebra = linear_an(1, f5());
        let simple = Module::simple(&algebra, 0);
        let zero = Module::zero(&algebra);
        let short = BoundedComplex::new(0, vec![simple.clone()], Vec::new()).unwrap();
        let target_differential = zero_between(&simple, &zero);
        let long =
            BoundedComplex::new(-1, vec![zero, simple.clone()], vec![target_differential]).unwrap();
        let source = short.padded_to(DegreeRange::new(-1, 0).unwrap()).unwrap();
        let components = vec![
            zero_between(&source.terms()[0], &long.terms()[0]),
            identity(&simple),
        ];
        let map = ChainMap::new(&short, &long, components).unwrap();
        assert_eq!(map.range(), DegreeRange::new(-1, 0).unwrap());
        assert!(map.source().verify());
        assert!(map.target().verify());
        assert!(map.verify());
    }

    #[test]
    fn fresh_padding_rebases_hom_coordinates_and_reduction() {
        let algebra = linear_an(1, f5());
        let simple = Module::simple(&algebra, 0);
        let zero = Module::zero(&algebra);
        let short = BoundedComplex::new(0, vec![simple.clone()], Vec::new()).unwrap();
        let long = BoundedComplex::new(
            -1,
            vec![zero.clone(), simple.clone()],
            vec![zero_between(&simple, &zero)],
        )
        .unwrap();
        let fresh_zero = Module::zero(&algebra);
        let fresh_source = BoundedComplex::new(
            -1,
            vec![fresh_zero.clone(), simple.clone()],
            vec![zero_between(&simple, &fresh_zero)],
        )
        .unwrap();
        let fresh_map = ChainMap::new(
            &short,
            &long,
            vec![
                zero_between(&fresh_zero, &long.terms()[0]),
                identity(&simple),
            ],
        )
        .unwrap();
        assert!(fresh_source.agrees_with(&fresh_map.source().clone()));
        let space = ChainHomSpace::new(&short, &long).unwrap();
        assert!(space.coords(&fresh_map).is_ok());
        let quotient = space.quotient().unwrap();
        let (coordinates, remainder) = quotient.reduce(&fresh_map).unwrap();
        let rebuilt = quotient
            .representative(&coordinates)
            .add(&remainder)
            .unwrap();
        assert!(fresh_map.agrees_with(&rebuilt));
    }

    #[test]
    fn nonzero_cones_and_shift_signs_hold_in_characteristics_two_and_five() {
        for modulus in [2, 5] {
            let field = PrimeField::new(modulus).unwrap();
            let algebra = linear_an(1, field);
            let simple = Module::simple(&algebra, 0);
            let complex = BoundedComplex::new(
                0,
                vec![simple.clone(), simple.clone()],
                vec![identity(&simple)],
            )
            .unwrap();
            let cone = ChainMap::identity(&complex).mapping_cone().unwrap();
            assert!(cone.verify());
            assert!(!cone.differential(1).unwrap().is_zero());
            let shifted = complex.shift(1).unwrap();
            assert_eq!(
                shifted.differential(2).unwrap().map_at(0).get(0, 0),
                field.neg(field.one())
            );
        }
    }

    #[test]
    fn direct_sum_pads_support_and_rechecks_each_block() {
        let algebra = linear_an(1, f5());
        let simple = Module::simple(&algebra, 0);
        let zero = Module::zero(&algebra);
        let left = BoundedComplex::new(0, vec![simple.clone()], Vec::new()).unwrap();
        let right = BoundedComplex::new(
            -1,
            vec![zero.clone(), simple.clone()],
            vec![zero_between(&simple, &zero)],
        )
        .unwrap();
        let sum = BoundedComplex::direct_sum(&[&left, &right]).unwrap();
        assert_eq!(sum.range(), DegreeRange::new(-1, 0).unwrap());
        assert_eq!(sum.term(-1).unwrap().dim_at(0), 0);
        assert_eq!(sum.term(0).unwrap().dim_at(0), 2);
        assert!(sum.verify());
    }
}

//! Bounded complex construction, validation, padding, and direct sums.

use std::sync::Arc;

use crate::complex::{CheckedComplex, ComplexError};
use crate::hom::{Morphism, zero_morphism};
use crate::homspace::scale_morphism;
use crate::linalg::DenseMat;
use crate::module::{Module, direct_sum};

/// A finite homological degree interval.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DegreeRange {
    pub(super) lower: i32,
    pub(super) upper: i32,
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
    pub(super) range: DegreeRange,
    pub(super) terms: Vec<Module>,
    pub(super) differentials: Vec<Morphism>,
}

pub(super) fn checked_degree(
    range: DegreeRange,
    degree: i32,
) -> Result<usize, BoundedComplexError> {
    if !range.contains(degree) {
        return Err(BoundedComplexError::DegreeOutOfRange { degree, range });
    }
    Ok((degree - range.lower) as usize)
}

pub(super) fn negate_morphism(f: &Morphism) -> Morphism {
    let field = f.source().field();
    scale_morphism(f, field.neg(field.one()))
}

pub(super) fn zero_between(source: &Module, target: &Module) -> Morphism {
    zero_morphism(source, target).expect("modules in one complex share an algebra")
}

fn complex_range(lower: i32, terms: &[Module]) -> Result<DegreeRange, BoundedComplexError> {
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
    Ok(DegreeRange { lower, upper })
}

fn check_terms(terms: &[Module], differentials: &[Morphism]) -> Result<(), BoundedComplexError> {
    let expected = terms.len() - 1;
    if differentials.len() != expected {
        return Err(BoundedComplexError::DifferentialCount {
            expected,
            got: differentials.len(),
        });
    }
    let first = terms.first().ok_or(BoundedComplexError::Empty)?;
    match terms
        .iter()
        .position(|module| !Arc::ptr_eq(first.algebra(), module.algebra()))
    {
        Some(term) => Err(BoundedComplexError::DifferentAlgebras { term }),
        None => Ok(()),
    }
}

fn check_differential_endpoints(
    lower: i32,
    terms: &[Module],
    differentials: &[Morphism],
) -> Result<(), BoundedComplexError> {
    for (index, differential) in differentials.iter().enumerate() {
        if !differential.source().ptr_eq(&terms[index + 1])
            || !differential.target().ptr_eq(&terms[index])
        {
            return Err(BoundedComplexError::DifferentialEndpointMismatch {
                degree: lower + index as i32 + 1,
            });
        }
    }
    Ok(())
}

fn check_zero_composites(
    lower: i32,
    differentials: &[Morphism],
) -> Result<(), BoundedComplexError> {
    for (index, pair) in differentials.windows(2).enumerate() {
        let composite = pair[1]
            .then(&pair[0])
            .expect("adjacent differentials share their middle endpoint");
        if !composite.is_zero() {
            return Err(BoundedComplexError::NonzeroComposite {
                degree: lower + index as i32 + 2,
            });
        }
    }
    Ok(())
}

impl BoundedComplex {
    /// Builds a bounded complex after checking algebra values, endpoints, and
    /// every composite `d_n.then(d_(n - 1))`.
    pub fn new(
        lower: i32,
        terms: Vec<Module>,
        differentials: Vec<Morphism>,
    ) -> Result<BoundedComplex, BoundedComplexError> {
        let range = complex_range(lower, &terms)?;
        check_terms(&terms, &differentials)?;
        check_differential_endpoints(lower, &terms, &differentials)?;
        check_zero_composites(lower, &differentials)?;
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

    /// Returns the same complex in display order.
    ///
    /// The greatest homological degree comes first. Reversing this value with
    /// [`BoundedComplex::from_checked`] at `self.lower()` recovers `self`.
    pub fn to_checked(&self) -> Result<CheckedComplex, ComplexError> {
        let terms = self.terms.iter().rev().cloned().collect();
        let maps = self.differentials.iter().rev().cloned().collect();
        CheckedComplex::new(terms, maps)
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
        let terms: Vec<Module> = (0..range.len())
            .map(|offset| padded_term(self, range.lower + offset as i32))
            .collect();
        padded_complex(self, range, terms)
    }

    /// Rechecks algebras, endpoints, and zero composites.
    pub fn verify(&self) -> bool {
        self.to_checked().is_ok()
    }

    /// Whether every stored term is the zero module.
    pub fn is_zero(&self) -> bool {
        self.terms.iter().all(Module::is_zero)
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
                    padded_differential(complex, degree, source, target)
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

pub(super) fn padded_term(complex: &BoundedComplex, degree: i32) -> Module {
    if complex.range.contains(degree) {
        complex.terms[(degree - complex.range.lower) as usize].clone()
    } else {
        Module::zero(complex.terms[0].algebra())
    }
}

fn padded_differentials(
    complex: &BoundedComplex,
    range: DegreeRange,
    terms: &[Module],
) -> Vec<Morphism> {
    (0..range.len().saturating_sub(1))
        .map(|offset| {
            let degree = range.lower + offset as i32 + 1;
            let source = &terms[offset + 1];
            let target = &terms[offset];
            padded_differential(complex, degree, source, target)
        })
        .collect()
}

fn padded_differential(
    complex: &BoundedComplex,
    degree: i32,
    source: &Module,
    target: &Module,
) -> Morphism {
    complex
        .differential(degree)
        .cloned()
        .unwrap_or_else(|| zero_between(source, target))
}

pub(super) fn padded_complex(
    complex: &BoundedComplex,
    range: DegreeRange,
    terms: Vec<Module>,
) -> Result<BoundedComplex, BoundedComplexError> {
    let differentials = padded_differentials(complex, range, &terms);
    BoundedComplex::new(range.lower, terms, differentials)
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
    let placements: Vec<(usize, usize)> = (0..blocks.len()).map(|index| (index, index)).collect();
    let maps = block_matrices(
        source_parts,
        target_parts,
        blocks,
        &placements,
        source_sum,
        target_sum,
    );
    Morphism::new(source_sum, target_sum, maps).expect("block diagonal maps are A-linear")
}

fn part_offset(parts: &[Module], part: usize, vertex: u32) -> usize {
    parts[..part]
        .iter()
        .map(|module| module.dim_at(vertex))
        .sum()
}

fn insert_block(
    matrix: &mut DenseMat,
    block: &Morphism,
    vertex: u32,
    source_offset: usize,
    target_offset: usize,
) {
    for row in 0..block.map_at(vertex).rows() {
        for col in 0..block.map_at(vertex).cols() {
            matrix.set(
                source_offset + row,
                target_offset + col,
                block.map_at(vertex).get(row, col),
            );
        }
    }
}

pub(super) fn block_matrices(
    source_parts: &[Module],
    target_parts: &[Module],
    blocks: &[Morphism],
    placements: &[(usize, usize)],
    source_sum: &Module,
    target_sum: &Module,
) -> Vec<DenseMat> {
    assert_eq!(blocks.len(), placements.len());
    let vertices = source_sum.algebra().quiver().num_vertices() as usize;
    (0..vertices)
        .map(|v| {
            let mut matrix =
                DenseMat::zero(source_sum.dim_at(v as u32), target_sum.dim_at(v as u32));
            for (block, &(source_part, target_part)) in blocks.iter().zip(placements) {
                insert_block(
                    &mut matrix,
                    block,
                    v as u32,
                    part_offset(source_parts, source_part, v as u32),
                    part_offset(target_parts, target_part, v as u32),
                );
            }
            matrix
        })
        .collect()
}

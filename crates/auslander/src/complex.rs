//! Finite module complexes, with checked zero composites and exactness.
//!
//! Terms and maps use display order: `maps[i]: terms[i] -> terms[i + 1]`.
//! This makes a short exact sequence read `N -> E -> M` and a tilting
//! generation complex read `A -> T^0 -> ... -> T^n`.

use std::sync::Arc;

use crate::hom::Morphism;
use crate::module::{Module, same_morphism_data, same_representation, same_slice};
use crate::resolution::{ProjectiveResolution, ResolutionEnd};

/// Rejected complex input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ComplexError {
    /// A complex needs at least one term.
    Empty,
    /// A complex with `terms.len()` terms needs one fewer map.
    MapCount { expected: usize, got: usize },
    /// The named term does not share the first term's algebra value.
    DifferentAlgebras { term: usize },
    /// The named map does not have the adjacent terms as nominal endpoints.
    EndpointMismatch { map: usize },
    /// Two consecutive maps have a nonzero composite.
    NonzeroComposite { first_map: usize },
    /// A term index is outside the complex.
    TermOutOfRange { index: usize, len: usize },
}

display_error! { error ComplexError {
    Self::Empty => "a complex needs at least one term";
    Self::MapCount { expected, got } => "complex has {got} maps, expected {expected}";
    Self::DifferentAlgebras { term } => "complex term {term} lives over another algebra";
    Self::EndpointMismatch { map } => "complex map {map} does not join its adjacent terms";
    Self::NonzeroComposite { first_map } => "complex maps {first_map} and {} have a nonzero composite", first_map + 1;
    Self::TermOutOfRange { index, len } => "complex term {index} is outside 0..{len}";
} }

/// Why a projective resolution did not produce an exact complex.
#[derive(Clone, Debug)]
pub enum ResolutionComplexError {
    /// The resolution prefix ends before the next nonzero syzygy.
    Cut { at: usize },
    /// The public resolution fields do not form a complex.
    Invalid(ComplexError),
    /// The fields form a complex, but it is not exact.
    NotExact(NonExactWitness),
}

display_error! { ResolutionComplexError {
    Self::Cut { at } => "resolution was cut after {at} differentials";
    Self::Invalid(error) => "resolution fields are invalid: {error}";
    Self::NotExact(witness) => "resolution has nonzero homology at term {}", witness.homology().index();
} }

error_source! { ResolutionComplexError {
    Self::Invalid(error) => Some(error),
    Self::Cut { .. } | Self::NotExact(_) => None,
} }

/// A nonempty finite module complex whose consecutive maps compose to zero.
#[derive(Clone, Debug)]
pub struct CheckedComplex {
    terms: Vec<Module>,
    maps: Vec<Morphism>,
}

fn validate(terms: &[Module], maps: &[Morphism]) -> Result<(), ComplexError> {
    let first = terms.first().ok_or(ComplexError::Empty)?;
    let expected = terms.len() - 1;
    if maps.len() != expected {
        return Err(ComplexError::MapCount {
            expected,
            got: maps.len(),
        });
    }
    if let Some(term) = terms
        .iter()
        .position(|module| !Arc::ptr_eq(first.algebra(), module.algebra()))
    {
        return Err(ComplexError::DifferentAlgebras { term });
    }
    if let Some(map) = maps
        .iter()
        .enumerate()
        .position(|(i, map)| !map.source().ptr_eq(&terms[i]) || !map.target().ptr_eq(&terms[i + 1]))
    {
        return Err(ComplexError::EndpointMismatch { map });
    }
    if let Some(first_map) = maps.windows(2).position(|pair| {
        !pair[0]
            .then(&pair[1])
            .expect("adjacent complex maps share their middle endpoint")
            .is_zero()
    }) {
        return Err(ComplexError::NonzeroComposite { first_map });
    }
    Ok(())
}

fn dimensions(complex: &CheckedComplex, index: usize) -> Result<Vec<usize>, ComplexError> {
    let term = complex
        .terms
        .get(index)
        .ok_or(ComplexError::TermOutOfRange {
            index,
            len: complex.terms.len(),
        })?;
    let field = term.field();
    Ok((0..term.algebra().quiver().num_vertices())
        .map(|v| {
            let incoming = index
                .checked_sub(1)
                .map_or(0, |i| complex.maps[i].map_at(v).rank(&field));
            let outgoing = complex
                .maps
                .get(index)
                .map_or(0, |map| map.map_at(v).rank(&field));
            term.dim_at(v)
                .checked_sub(
                    incoming
                        .checked_add(outgoing)
                        .expect("two ranks of subspaces fit in the term dimension"),
                )
                .expect("a zero composite puts the incoming image in the outgoing kernel")
        })
        .collect())
}

fn is_exact(complex: &CheckedComplex) -> bool {
    (0..complex.len()).all(|i| dimensions(complex, i).is_ok_and(|d| d.iter().all(|&x| x == 0)))
}

impl CheckedComplex {
    /// Builds a complex after checking its term algebras, map endpoints, and zero composites.
    pub fn new(terms: Vec<Module>, maps: Vec<Morphism>) -> Result<CheckedComplex, ComplexError> {
        validate(&terms, &maps).map(|()| CheckedComplex { terms, maps })
    }

    accessor_methods! {
        /// The terms in display order.
        pub terms() -> &[Module] = |this| &this.terms;
        /// The maps in display order, with `maps[i]: terms[i] -> terms[i + 1]`.
        pub maps() -> &[Morphism] = |this| &this.maps;
        /// The number of terms.
        pub len() -> usize = |this| this.terms.len();
        /// Whether the complex has no terms.
        ///
        /// A checked complex is never empty, so this method always returns false.
        pub is_empty() -> bool = |_this| false;
        /// Rechecks the term algebras, map endpoints, and zero composites.
        pub verify() -> bool = |this| validate(&this.terms, &this.maps).is_ok();
    }

    /// Whether another checked complex has the same term and map matrices.
    ///
    /// Terms may be fresh module values, but both complexes must use one
    /// algebra value. This is structural comparison for certificate rechecks,
    /// not module identity.
    pub fn agrees_with(&self, other: &CheckedComplex) -> bool {
        self.verify()
            && other.verify()
            && same_slice(&self.terms, &other.terms, same_representation)
            && same_slice(&self.maps, &other.maps, same_morphism_data)
    }

    /// The exact homology dimension vector at one term.
    pub fn homology_dimensions(&self, index: usize) -> Result<HomologyDimensions, ComplexError> {
        Ok(HomologyDimensions {
            complex: self.clone(),
            index,
            dimension_vector: dimensions(self, index)?,
        })
    }

    /// Whether every term is exact, with proof data either way.
    pub fn exactness(&self) -> ExactnessOutcome {
        for index in 0..self.len() {
            let dimension_vector =
                dimensions(self, index).expect("the loop index names a complex term");
            if dimension_vector.iter().any(|&d| d != 0) {
                return ExactnessOutcome::NotExact(NonExactWitness {
                    homology: HomologyDimensions {
                        complex: self.clone(),
                        index,
                        dimension_vector,
                    },
                });
            }
        }
        ExactnessOutcome::Exact(ExactComplex {
            complex: self.clone(),
        })
    }
}

/// Exact homology dimensions at one term of a checked complex.
#[derive(Clone, Debug)]
pub struct HomologyDimensions {
    complex: CheckedComplex,
    index: usize,
    dimension_vector: Vec<usize>,
}

impl HomologyDimensions {
    accessor_methods! {
        /// The term index in display order.
        pub index() -> usize = |this| this.index;
        /// The homology dimension at each quiver vertex.
        pub dimension_vector() -> &[usize] = |this| &this.dimension_vector;
        /// Whether the homology module is zero.
        pub is_zero() -> bool = |this| this.dimension_vector.iter().all(|&d| d == 0);
        /// Rechecks the complex and the stored dimension vector.
        pub verify() -> bool = |this| this.complex.verify()
            && dimensions(&this.complex, this.index).as_deref()
                == Ok(this.dimension_vector.as_slice());
    }
}

/// The first nonexact term of a checked complex.
#[derive(Clone, Debug)]
pub struct NonExactWitness {
    homology: HomologyDimensions,
}

impl NonExactWitness {
    accessor_methods! {
        /// The first nonzero homology dimensions.
        pub homology() -> &HomologyDimensions = |this| &this.homology;
        /// Rechecks that this is the first nonexact term.
        pub verify() -> bool = |this| this.homology.verify()
            && !this.homology.is_zero()
            && (0..this.homology.index).all(|i| {
                dimensions(&this.homology.complex, i).is_ok_and(|d| d.iter().all(|&x| x == 0))
            });
    }
}

/// A finite module complex proved exact at every term.
#[derive(Clone, Debug)]
pub struct ExactComplex {
    complex: CheckedComplex,
}

impl ExactComplex {
    accessor_methods! {
        /// The checked complex.
        pub complex() -> &CheckedComplex = |this| &this.complex;
        /// Rechecks every zero composite and homology dimension.
        pub verify() -> bool = |this| this.complex.verify() && is_exact(&this.complex);
    }

    /// Rechecks a fresh construction and compares every term and map matrix.
    pub fn verify_reconstruction(&self, rebuilt: &CheckedComplex) -> bool {
        self.verify() && self.complex.agrees_with(rebuilt) && is_exact(rebuilt)
    }
}

/// Exactness proof or the first nonzero homology dimensions.
#[derive(Clone, Debug)]
pub enum ExactnessOutcome {
    /// Every term is exact.
    Exact(ExactComplex),
    /// The stored term is the first nonexact one.
    NotExact(NonExactWitness),
}

impl ProjectiveResolution {
    /// The complete resolution as an exact complex `P_l -> ... -> P_0 -> M`.
    ///
    /// A cut and malformed public resolution fields remain typed.
    pub fn checked_complex(&self) -> Result<ExactComplex, ResolutionComplexError> {
        if let ResolutionEnd::Cut { at } = self.end {
            return Err(ResolutionComplexError::Cut { at });
        }
        let mut terms: Vec<Module> = self.terms.iter().rev().cloned().collect();
        terms.push(self.augmentation.target().clone());
        let mut maps: Vec<Morphism> = self.maps.iter().rev().cloned().collect();
        maps.push(self.augmentation.clone());
        let complex = CheckedComplex::new(terms, maps).map_err(ResolutionComplexError::Invalid)?;
        match complex.exactness() {
            ExactnessOutcome::Exact(exact) => Ok(exact),
            ExactnessOutcome::NotExact(witness) => Err(ResolutionComplexError::NotExact(witness)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{commutative_square, linear_an};
    use crate::field::PrimeField;
    use crate::hom::{identity, zero_morphism};
    use crate::resolution::resolve;

    fn f5() -> PrimeField {
        PrimeField::new(5).unwrap()
    }

    #[test]
    fn finite_resolution_becomes_an_exact_display_order_complex() {
        let algebra = linear_an(2, f5());
        let simple = Module::simple(&algebra, 0);
        let resolution = resolve(&simple, 1);
        let exact = resolution.checked_complex().unwrap();
        assert_eq!(exact.complex().len(), 3);
        assert!(exact.complex().terms()[2].ptr_eq(&simple));
        assert!(exact.verify());
    }

    #[test]
    fn a_cut_resolution_keeps_its_cut() {
        let algebra = crate::algebra::dual_numbers(f5());
        let resolution = resolve(&Module::simple(&algebra, 0), 2);
        assert!(matches!(
            resolution.checked_complex(),
            Err(ResolutionComplexError::Cut { at: 2 })
        ));
    }

    #[test]
    fn resolution_adapter_covers_f2_and_a_nonmonomial_algebra() {
        for algebra in [
            linear_an(2, PrimeField::new(2).unwrap()),
            commutative_square(f5()),
        ] {
            let simple = Module::simple(&algebra, 0);
            let resolution = resolve(&simple, 4);
            assert!(resolution.checked_complex().unwrap().verify());
        }
    }

    #[test]
    fn forged_finite_resolution_returns_a_nonexact_witness() {
        let algebra = linear_an(2, f5());
        let simple = Module::simple(&algebra, 0);
        let forged = ProjectiveResolution {
            terms: vec![simple.clone()],
            maps: Vec::new(),
            augmentation: zero_morphism(&simple, &simple).unwrap(),
            end: ResolutionEnd::Finite,
        };
        let Err(ResolutionComplexError::NotExact(witness)) = forged.checked_complex() else {
            panic!("a zero augmentation of a nonzero term is not exact")
        };
        assert!(witness.verify());
    }

    #[test]
    fn constructor_rejects_an_endpoint_mismatch_and_a_nonzero_square() {
        let algebra = linear_an(2, f5());
        let simple = Module::simple(&algebra, 0);
        let other = Module::simple(&algebra, 0);
        assert_eq!(
            CheckedComplex::new(vec![simple.clone(), other], vec![identity(&simple)]).unwrap_err(),
            ComplexError::EndpointMismatch { map: 0 }
        );
        assert_eq!(
            CheckedComplex::new(
                vec![simple.clone(), simple.clone(), simple.clone()],
                vec![identity(&simple), identity(&simple)]
            )
            .unwrap_err(),
            ComplexError::NonzeroComposite { first_map: 0 }
        );
    }

    #[test]
    fn constructor_and_accessors_keep_structural_errors_typed() {
        let algebra = linear_an(2, f5());
        let other_algebra = linear_an(2, f5());
        let simple = Module::simple(&algebra, 0);
        let other = Module::simple(&other_algebra, 0);
        assert_eq!(
            CheckedComplex::new(Vec::new(), Vec::new()).unwrap_err(),
            ComplexError::Empty
        );
        assert_eq!(
            CheckedComplex::new(vec![simple.clone(), simple.clone()], Vec::new()).unwrap_err(),
            ComplexError::MapCount {
                expected: 1,
                got: 0
            }
        );
        assert_eq!(
            CheckedComplex::new(
                vec![simple.clone(), other],
                vec![zero_morphism(&simple, &simple).unwrap()],
            )
            .unwrap_err(),
            ComplexError::DifferentAlgebras { term: 1 }
        );
        let complex = CheckedComplex::new(vec![simple], Vec::new()).unwrap();
        assert_eq!(
            complex.homology_dimensions(1).unwrap_err(),
            ComplexError::TermOutOfRange { index: 1, len: 1 }
        );
    }

    #[test]
    fn forged_resolution_with_a_bad_map_count_is_invalid() {
        let algebra = linear_an(2, f5());
        let simple = Module::simple(&algebra, 0);
        let forged = ProjectiveResolution {
            terms: Vec::new(),
            maps: Vec::new(),
            augmentation: identity(&simple),
            end: ResolutionEnd::Finite,
        };
        assert!(matches!(
            forged.checked_complex(),
            Err(ResolutionComplexError::Invalid(ComplexError::MapCount {
                expected: 0,
                got: 1
            }))
        ));
    }

    #[test]
    fn nonexact_witness_is_the_first_nonzero_homology() {
        let algebra = linear_an(2, f5());
        let simple = Module::simple(&algebra, 0);
        let zero = zero_morphism(&simple, &simple).unwrap();
        let complex = CheckedComplex::new(vec![simple.clone(), simple], vec![zero]).unwrap();
        let ExactnessOutcome::NotExact(witness) = complex.exactness() else {
            panic!("the zero map between nonzero terms is not exact")
        };
        assert_eq!(witness.homology().index(), 0);
        assert_eq!(witness.homology().dimension_vector(), &[1, 0]);
        assert!(witness.verify());
    }

    #[test]
    fn nonexact_witness_can_start_after_an_exact_zero_term() {
        let algebra = linear_an(2, f5());
        let zero = Module::zero(&algebra);
        let simple = Module::simple(&algebra, 0);
        let map = zero_morphism(&zero, &simple).unwrap();
        let complex = CheckedComplex::new(vec![zero, simple], vec![map]).unwrap();
        let ExactnessOutcome::NotExact(witness) = complex.exactness() else {
            panic!("the final simple has nonzero homology")
        };
        assert_eq!(witness.homology().index(), 1);
        assert!(witness.verify());
    }

    #[test]
    fn exact_complex_accepts_fresh_entrywise_reconstruction() {
        let algebra = linear_an(2, f5());
        let simple = Module::simple(&algebra, 0);
        let first = resolve(&simple, 1).checked_complex().unwrap();
        let second = resolve(&simple, 1).checked_complex().unwrap();
        assert!(!first.complex().terms()[0].ptr_eq(&second.complex().terms()[0]));
        assert!(first.verify_reconstruction(second.complex()));

        let wrong = CheckedComplex::new(vec![Module::simple(&algebra, 1)], Vec::new()).unwrap();
        assert!(!first.verify_reconstruction(&wrong));

        let terms = second.complex().terms().to_vec();
        let mut maps = second.complex().maps().to_vec();
        maps[0] = zero_morphism(&terms[0], &terms[1]).unwrap();
        let changed_map = CheckedComplex::new(terms, maps).unwrap();
        assert!(!first.verify_reconstruction(&changed_map));
    }

    #[test]
    fn one_zero_term_is_exact_and_one_nonzero_term_is_not() {
        let algebra = linear_an(2, f5());
        let zero = CheckedComplex::new(vec![Module::zero(&algebra)], Vec::new()).unwrap();
        assert!(matches!(zero.exactness(), ExactnessOutcome::Exact(_)));
        let simple = CheckedComplex::new(vec![Module::simple(&algebra, 0)], Vec::new()).unwrap();
        assert!(matches!(simple.exactness(), ExactnessOutcome::NotExact(_)));
    }

    #[test]
    fn tampered_homology_dimensions_fail_verification() {
        let algebra = linear_an(2, f5());
        let simple = Module::simple(&algebra, 0);
        let complex = CheckedComplex::new(vec![simple], Vec::new()).unwrap();
        let mut homology = complex.homology_dimensions(0).unwrap();
        homology.dimension_vector[0] = 0;
        assert!(!homology.verify());
    }
}

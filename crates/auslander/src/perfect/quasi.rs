use crate::complex::{ComplexError, ExactComplex, ExactnessOutcome, NonExactWitness};
use crate::homotopy::{BoundedComplex, BoundedComplexError, ChainMap};

/// Why a chain map did not yield a checked quasi-isomorphism.
#[derive(Clone, Debug)]
pub enum QuasiIsomorphismError {
    /// The mapping cone could not be built.
    Cone(BoundedComplexError),
    /// The mapping cone could not enter the display-order exactness checker.
    Complex(ComplexError),
    /// The mapping cone has nonzero homology.
    NotExact(NonExactWitness),
}

display_error! { QuasiIsomorphismError {
    Self::Cone(error) => "mapping cone construction failed: {error}";
    Self::Complex(error) => "mapping cone is invalid: {error}";
    Self::NotExact(witness) => "mapping cone has nonzero homology at term {}", witness.homology().index();
} }

error_source! { QuasiIsomorphismError {
    Self::Cone(error) => Some(error),
    Self::Complex(error) => Some(error),
    Self::NotExact(_) => None,
} }

/// A chain map whose mapping cone is checked exact.
#[derive(Clone, Debug)]
pub struct QuasiIsomorphism {
    map: ChainMap,
    exact_cone: ExactComplex,
}

impl QuasiIsomorphism {
    /// Checks the mapping cone of `map` for exactness.
    pub fn new(map: ChainMap) -> Result<QuasiIsomorphism, QuasiIsomorphismError> {
        let checked = map
            .mapping_cone()
            .map_err(QuasiIsomorphismError::Cone)?
            .to_checked()
            .map_err(QuasiIsomorphismError::Complex)?;
        match checked.exactness() {
            ExactnessOutcome::Exact(exact_cone) => Ok(QuasiIsomorphism { map, exact_cone }),
            ExactnessOutcome::NotExact(witness) => Err(QuasiIsomorphismError::NotExact(witness)),
        }
    }

    accessor_methods! {
        /// The checked chain map.
        pub map() -> &ChainMap = |this| &this.map;
        /// The exact mapping-cone certificate.
        pub exact_cone() -> &ExactComplex = |this| &this.exact_cone;
    }

    /// Rebuilds the mapping cone and checks its exactness certificate.
    pub fn verify(&self) -> bool {
        self.map.mapping_cone().is_ok_and(|cone| {
            cone.to_checked().is_ok_and(|checked| {
                self.map.verify() && self.exact_cone.verify_reconstruction(&checked)
            })
        })
    }
}

pub(super) fn same_nominal_complex(left: &BoundedComplex, right: &BoundedComplex) -> bool {
    left.range() == right.range()
        && left
            .terms()
            .iter()
            .zip(right.terms())
            .all(|(a, b)| a.ptr_eq(b))
        && left.differentials() == right.differentials()
}

pub(super) fn agrees_with_zero_padding(input: &BoundedComplex, padded: &BoundedComplex) -> bool {
    input
        .padded_to(padded.range())
        .is_ok_and(|rebuilt| rebuilt.agrees_with(padded))
}

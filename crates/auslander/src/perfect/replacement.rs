use crate::hom::HomError;
use crate::homotopy::{BoundedComplex, BoundedComplexError, ChainMap, ChainMapError};

use super::cover::ComplexProjectiveCoverError;
use super::quasi::{
    QuasiIsomorphism, QuasiIsomorphismError, agrees_with_zero_padding, same_nominal_complex,
};
use super::term::{ProjectiveComplex, ProjectiveComplexError};

/// Why automatic replacement could not construct its next checked value.
#[derive(Clone, Debug)]
pub enum ReplacementError {
    /// A projective-object cover failed.
    Cover(ComplexProjectiveCoverError),
    /// A checked count overflowed `usize`.
    Arithmetic,
    /// A total degree does not fit in `i32`.
    DegreeOverflow,
    /// The total complex failed construction.
    Complex(BoundedComplexError),
    /// The total augmentation failed construction.
    Chain(ChainMapError),
    /// A total differential component failed construction.
    Hom(HomError),
    /// The total complex failed its projective witness.
    Projective(ProjectiveComplexError),
    /// The total augmentation failed its cone exactness check.
    QuasiIsomorphism(QuasiIsomorphismError),
    /// The final replacement endpoints failed.
    Replacement(PerfectReplacementError),
}

display_error! { ReplacementError {
    Self::Cover(error) => "complex-resolution cover failed: {error}";
    Self::Arithmetic => "replacement resource count overflowed";
    Self::DegreeOverflow => "replacement total degree overflowed";
    Self::Complex(error) => "replacement total complex is invalid: {error}";
    Self::Chain(error) => "replacement augmentation is invalid: {error}";
    Self::Hom(error) => "replacement total component is invalid: {error}";
    Self::Projective(error) => "replacement total term is not projective: {error}";
    Self::QuasiIsomorphism(error) => "replacement augmentation is not a quasi-isomorphism: {error}";
    Self::Replacement(error) => "replacement endpoints are invalid: {error}";
} }

error_source! { ReplacementError {
    Self::Cover(error) => Some(error),
    Self::Complex(error) => Some(error),
    Self::Chain(error) => Some(error),
    Self::Hom(error) => Some(error),
    Self::Projective(error) => Some(error),
    Self::QuasiIsomorphism(error) => Some(error),
    Self::Replacement(error) => Some(error),
    Self::Arithmetic | Self::DegreeOverflow => None,
} }

from_variants! { ReplacementError {
    ComplexProjectiveCoverError => Cover,
    BoundedComplexError => Complex,
    ChainMapError => Chain,
    HomError => Hom,
    ProjectiveComplexError => Projective,
    QuasiIsomorphismError => QuasiIsomorphism,
    PerfectReplacementError => Replacement,
} }

/// Why projective replacement data failed its endpoint checks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PerfectReplacementError {
    /// The quasi-isomorphism does not start at the stored projective model.
    SourceMismatch,
    /// The quasi-isomorphism does not end at the stored original complex after
    /// explicit zero padding.
    TargetMismatch,
}

display_error! { error PerfectReplacementError {
    Self::SourceMismatch => "replacement map does not start at the projective model";
    Self::TargetMismatch => "replacement map does not end at the original complex";
} }

/// A bounded projective model with a checked map to its original complex.
#[derive(Clone, Debug)]
pub struct PerfectReplacement {
    original: BoundedComplex,
    projective: ProjectiveComplex,
    quasi_isomorphism: QuasiIsomorphism,
}

impl PerfectReplacement {
    /// Builds replacement data after checking both nominal endpoints.
    pub fn new(
        original: BoundedComplex,
        projective: ProjectiveComplex,
        quasi_isomorphism: QuasiIsomorphism,
    ) -> Result<PerfectReplacement, PerfectReplacementError> {
        if !same_nominal_complex(projective.complex(), quasi_isomorphism.map().source()) {
            return Err(PerfectReplacementError::SourceMismatch);
        }
        if !agrees_with_zero_padding(&original, quasi_isomorphism.map().target()) {
            return Err(PerfectReplacementError::TargetMismatch);
        }
        Ok(PerfectReplacement {
            original,
            projective,
            quasi_isomorphism,
        })
    }

    /// Uses an already projective complex as its own model.
    pub fn identity(projective: ProjectiveComplex) -> PerfectReplacement {
        let original = projective.complex().clone();
        let quasi_isomorphism = QuasiIsomorphism::new(ChainMap::identity(&original))
            .expect("the cone of an identity chain map is exact");
        PerfectReplacement::new(original, projective, quasi_isomorphism)
            .expect("the identity map has the stored complex as both endpoints")
    }

    accessor_methods! {
        /// The ordinary input complex.
        pub original() -> &BoundedComplex = |this| &this.original;
        /// The bounded projective model.
        pub projective() -> &ProjectiveComplex = |this| &this.projective;
        /// The checked quasi-isomorphism from the model to the input.
        pub quasi_isomorphism() -> &QuasiIsomorphism = |this| &this.quasi_isomorphism;
    }

    /// Rechecks the projective model, map, cone, and nominal endpoints.
    pub fn verify(&self) -> bool {
        self.original.verify()
            && self.projective.verify()
            && self.quasi_isomorphism.verify()
            && PerfectReplacement::new(
                self.original.clone(),
                self.projective.clone(),
                self.quasi_isomorphism.clone(),
            )
            .is_ok()
    }
}

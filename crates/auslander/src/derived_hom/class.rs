use crate::field::{Fp, PrimeField};
use crate::homotopy::{
    BoundedComplex, ChainMap, ChainMapError, DegreeRange, HomotopyHom, HomotopyHomQuotient,
};
use crate::linalg::DenseMat;
use crate::perfect::PerfectReplacement;

use super::{DerivedHom, replacement_matches};

/// Why derived Hom class coordinates were rejected.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DerivedHomClassError {
    /// The requested degree lies outside the exact finite support.
    DegreeOutsideSupport { degree: i32, support: DegreeRange },
    /// The coordinate count differs from the quotient dimension.
    CoordinateCount { expected: usize, got: usize },
}

display_error! { error DerivedHomClassError {
    Self::DegreeOutsideSupport { degree, support } => "degree {degree} is outside derived Hom support {}..{}", support.lower(), support.upper();
    Self::CoordinateCount { expected, got } => "derived Hom class has {got} coordinates, expected {expected}";
} }

/// One checked class in a derived Hom quotient.
#[derive(Clone, Debug)]
pub struct DerivedHomClass {
    source: BoundedComplex,
    target: BoundedComplex,
    replacement: PerfectReplacement,
    space: HomotopyHomQuotient,
    coordinates: Vec<Fp>,
    representative: ChainMap,
}

impl DerivedHom {
    /// Builds a checked class in one support degree.
    pub fn class(
        &self,
        degree: i32,
        coordinates: &[Fp],
    ) -> Result<DerivedHomClass, DerivedHomClassError> {
        let space = self
            .space(degree)
            .ok_or(DerivedHomClassError::DegreeOutsideSupport {
                degree,
                support: self.support,
            })?;
        if coordinates.len() != space.dim() {
            return Err(DerivedHomClassError::CoordinateCount {
                expected: space.dim(),
                got: coordinates.len(),
            });
        }
        Ok(DerivedHomClass {
            source: self.source.clone(),
            target: self.target.clone(),
            replacement: self.replacement.clone(),
            space: space.clone(),
            coordinates: coordinates.to_vec(),
            representative: space.representative(coordinates),
        })
    }
}

fn comparison_image_rows(
    comparison_space: &HomotopyHomQuotient,
    shifted_quasi: &ChainMap,
    source_space: &HomotopyHomQuotient,
    field: PrimeField,
) -> Result<Vec<Vec<Fp>>, ChainMapError> {
    let mut image_rows = Vec::with_capacity(comparison_space.dim());
    for index in 0..comparison_space.dim() {
        let mut coordinates = vec![field.zero(); comparison_space.dim()];
        coordinates[index] = field.one();
        let image = comparison_space
            .representative(&coordinates)
            .then(shifted_quasi)?;
        image_rows.push(source_space.reduce(&image)?.0);
    }
    Ok(image_rows)
}

fn comparison_lift_coordinates(
    comparison_space: &HomotopyHomQuotient,
    source_space: &HomotopyHomQuotient,
    image_rows: &[Vec<Fp>],
    coordinates: &[Fp],
    field: &PrimeField,
) -> Result<Vec<Fp>, DerivedHomCompositionError> {
    let images = DenseMat::from_rows_with_cols(image_rows, source_space.dim());
    if images.rank(field) != source_space.dim() || comparison_space.dim() != source_space.dim() {
        return Err(DerivedHomCompositionError::ComparisonNotInvertible);
    }
    images
        .transpose()
        .solve(coordinates, field)
        .ok_or(DerivedHomCompositionError::ComparisonNotInvertible)
}

fn composition_setup(
    source: &DerivedHomClass,
    other: &DerivedHomClass,
) -> Result<(i32, HomotopyHomQuotient, ChainMap), DerivedHomCompositionError> {
    let degree = source
        .degree()
        .checked_add(other.degree())
        .ok_or(DerivedHomCompositionError::DegreeOverflow)?;
    let comparison_space = HomotopyHom::new(
        source.replacement.projective().complex(),
        other.replacement.projective().complex(),
        source.degree(),
    )?
    .quotient()?;
    let shifted_quasi = other
        .replacement
        .quasi_isomorphism()
        .map()
        .shift(source.degree())?;
    Ok((degree, comparison_space, shifted_quasi))
}

fn comparison_representative(
    comparison_space: &HomotopyHomQuotient,
    shifted_quasi: &ChainMap,
    source_space: &HomotopyHomQuotient,
    coordinates: &[Fp],
    field: &PrimeField,
    other: &DerivedHomClass,
    degree: i32,
) -> Result<ChainMap, DerivedHomCompositionError> {
    let image_rows = comparison_image_rows(comparison_space, shifted_quasi, source_space, *field)?;
    let lift_coordinates = comparison_lift_coordinates(
        comparison_space,
        source_space,
        &image_rows,
        coordinates,
        field,
    )?;
    let lifted = comparison_space.representative(&lift_coordinates);
    let shifted_other = other.representative.shift(degree)?;
    Ok(lifted.then(&shifted_other)?)
}

fn output_class_data(
    source: &DerivedHomClass,
    other: &DerivedHomClass,
    degree: i32,
    representative: &ChainMap,
) -> Result<(HomotopyHomQuotient, Vec<Fp>), DerivedHomCompositionError> {
    let output_space = HomotopyHom::new(
        source.replacement.projective().complex(),
        &other.target,
        degree,
    )?
    .quotient()?;
    let coordinates = output_space.reduce(representative)?.0;
    Ok((output_space, coordinates))
}

impl DerivedHomClass {
    accessor_methods! {
        /// The ordinary source complex.
        pub source() -> &BoundedComplex = |this| &this.source;
        /// The ordinary target complex.
        pub target() -> &BoundedComplex = |this| &this.target;
        /// The checked projective replacement of the source.
        pub replacement() -> &PerfectReplacement = |this| &this.replacement;
        /// The shift degree.
        pub degree() -> i32 = |this| this.space.degree();
        /// The deterministic quotient coordinates.
        pub coordinates() -> &[Fp] = |this| &this.coordinates;
        /// The stored representative chain map.
        pub representative() -> &ChainMap = |this| &this.representative;
        /// The derived Hom quotient containing this class.
        pub space() -> &HomotopyHomQuotient = |this| &this.space;
    }

    /// Reduces the representative and checks its stored coordinates.
    pub fn verify(&self) -> bool {
        replacement_matches(&self.source, &self.replacement)
            && self.target.verify()
            && self.space_matches()
    }

    fn space_matches(&self) -> bool {
        self.space
            .source()
            .agrees_with(self.replacement.projective().complex())
            && self.space.target().agrees_with(&self.target)
            && self.space.verify()
            && self.coordinates.len() == self.space.dim()
            && self
                .space
                .reduce(&self.representative)
                .is_ok_and(|(coordinates, _)| coordinates == self.coordinates)
    }

    /// Composes this class first, then `other`.
    pub fn then(
        &self,
        other: &DerivedHomClass,
    ) -> Result<DerivedHomClass, DerivedHomCompositionError> {
        if !self.target.agrees_with(&other.source) {
            return Err(DerivedHomCompositionError::MiddleMismatch);
        }
        let (degree, comparison_space, shifted_quasi) = composition_setup(self, other)?;
        let field = self.source.terms()[0].field();
        let representative = comparison_representative(
            &comparison_space,
            &shifted_quasi,
            &self.space,
            &self.coordinates,
            &field,
            other,
            self.degree(),
        )?;
        let (output_space, coordinates) = output_class_data(self, other, degree, &representative)?;
        let result = DerivedHomClass {
            source: self.source.clone(),
            target: other.target.clone(),
            replacement: self.replacement.clone(),
            space: output_space,
            coordinates,
            representative,
        };
        debug_assert!(result.verify());
        Ok(result)
    }
}

/// Why two checked derived Hom classes did not compose.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DerivedHomCompositionError {
    /// The first target differs from the second source.
    MiddleMismatch,
    /// The sum of the two shift degrees does not fit in `i32`.
    DegreeOverflow,
    /// A chain map or quotient construction failed.
    Chain(ChainMapError),
    /// The stored quasi-isomorphism did not induce an invertible Hom map.
    ComparisonNotInvertible,
}

display_error! { DerivedHomCompositionError {
    Self::MiddleMismatch => "derived Hom composition has a different middle complex";
    Self::DegreeOverflow => "derived Hom composition degree overflowed";
    Self::Chain(error) => "derived Hom composition failed: {error}";
    Self::ComparisonNotInvertible => "source replacement comparison is not invertible on homotopy Hom";
} }

error_source! { DerivedHomCompositionError {
    Self::Chain(error) => Some(error),
    _ => None,
} }

impl From<ChainMapError> for DerivedHomCompositionError {
    fn from(error: ChainMapError) -> Self {
        DerivedHomCompositionError::Chain(error)
    }
}

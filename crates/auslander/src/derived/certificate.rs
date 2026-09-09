use std::sync::Arc;

use crate::hom::HomError;
use crate::homotopy::{
    BoundedComplex, BoundedComplexError, ChainHomQuotient, ChainHomSpace, ChainMap, ChainMapError,
    DegreeRange,
};
use crate::homspace::{HomSpace, row_times};
use crate::linalg::DenseMat;
use crate::resolution::{ProjectiveResolution, ResolutionEnd, resolve};
use crate::target::VerifiedTargetPresentation;
use crate::tilting::ClassicalTiltingModule;

use super::transport::{StrictTransport, TransportError};

/// Rejected derived-equivalence certificate input or verification data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DerivedCertificateError {
    /// The tilting certificate does not verify.
    InvalidTilting,
    /// The target presentation does not verify.
    InvalidTarget,
    /// The target and tilting certificates use different source modules.
    DifferentSource,
    /// The projective resolution was not finite.
    ResolutionCut { at: usize },
    /// The named resolution term is not projective.
    ResolutionTermNotProjective { term: usize },
    /// The resolution does not form a bounded homological complex.
    ResolutionComplex(BoundedComplexError),
    /// A homotopy endomorphism space could not be constructed.
    Homotopy(ChainMapError),
    /// A nonzero self-Hom survives in the named degree.
    NonzeroSelfHom { degree: i32, dimension: usize },
    /// The degree-zero homotopy endomorphism space has the wrong dimension.
    DegreeZeroDimension {
        homotopy: usize,
        endomorphism: usize,
    },
    /// The degree-zero map to `End_A(T)` is not an algebra isomorphism.
    DegreeZeroIdentification { reason: String },
    /// The generation complex or one of its `add(T)` witnesses does not verify.
    Generation,
    /// Strict transport did not build from the target presentation.
    Transport(TransportError),
    /// A resolution width cannot be represented as a homological degree.
    DegreeOverflow { width: usize },
}

display_error! { DerivedCertificateError {
    Self::InvalidTilting => "tilting certificate does not verify";
    Self::InvalidTarget => "target presentation does not verify";
    Self::DifferentSource => "tilting and target certificates use different source modules";
    Self::ResolutionCut { at } => "tilting resolution was cut after {at} differentials";
    Self::ResolutionTermNotProjective { term } => "resolution term {term} is not projective";
    Self::ResolutionComplex(error) => "resolution complex rejected: {error}";
    Self::Homotopy(error) => "homotopy endomorphism space rejected: {error}";
    Self::NonzeroSelfHom { degree, dimension } => "homotopy self-Hom in degree {degree} has dimension {dimension}";
    Self::DegreeZeroDimension { homotopy, endomorphism } => "degree-zero homotopy dimension {homotopy} differs from End(T) dimension {endomorphism}";
    Self::DegreeZeroIdentification { reason } => "degree-zero End(T) identification failed: {reason}";
    Self::Generation => "generation complex or add(T) witnesses do not verify";
    Self::Transport(error) => "strict transport rejected: {error}";
    Self::DegreeOverflow { width } => "resolution width {width} does not fit in i32";
} }

error_source! { DerivedCertificateError {
    Self::ResolutionComplex(error) => Some(error),
    Self::Homotopy(error) => Some(error),
    Self::Transport(error) => Some(error),
    _ => None,
} }

/// One graded homotopy endomorphism space of the tilting resolution.
#[derive(Clone, Debug)]
pub struct GradedHomotopyEndomorphisms {
    pub(super) degree: i32,
    pub(super) quotient: ChainHomQuotient,
}

impl GradedHomotopyEndomorphisms {
    accessor_methods! {
        /// The target shift degree.
        pub degree() -> i32 = |this| this.degree;
        /// The deterministic homotopy quotient in this degree.
        pub quotient() -> &ChainHomQuotient = |this| &this.quotient;
    }

    /// Rechecks the stored quotient basis and null-homotopic subspace.
    pub fn verify(&self) -> bool {
        self.quotient.verify()
    }
}

/// The checked degree-zero map from homotopy endomorphisms to `End_A(T)`.
#[derive(Clone, Debug)]
pub struct DegreeZeroEndIdentification {
    pub(super) quotient: ChainHomQuotient,
    pub(super) coordinates: DenseMat,
}

impl DegreeZeroEndIdentification {
    accessor_methods! {
        /// The degree-zero homotopy endomorphism quotient.
        pub quotient() -> &ChainHomQuotient = |this| &this.quotient;
        /// Rows map quotient-basis coordinates to `End_A(T)` coordinates.
        pub coordinates() -> &DenseMat = |this| &this.coordinates;
    }
}

fn induced_endomorphism_coordinates(
    resolution: &ProjectiveResolution,
    map: &ChainMap,
    target: &VerifiedTargetPresentation,
) -> Result<Vec<crate::field::Fp>, DerivedCertificateError> {
    let endo = target.endo();
    let hom = HomSpace::new(&resolution.terms[0], target.source()).map_err(|error| {
        DerivedCertificateError::DegreeZeroIdentification {
            reason: format!("augmentation Hom space failed: {error}"),
        }
    })?;
    let rows: Vec<Vec<crate::field::Fp>> = endo
        .basis()
        .iter()
        .map(|basis| {
            resolution
                .augmentation
                .then(basis)
                .and_then(|map| hom.coords(&map).map_err(|_| HomError::EndpointMismatch))
        })
        .collect::<Result<_, _>>()
        .map_err(|error| DerivedCertificateError::DegreeZeroIdentification {
            reason: format!("End(T) action on the augmentation failed: {error}"),
        })?;
    let lift = DenseMat::from_rows_with_cols(&rows, hom.dim());
    let component = map
        .component(0)
        .map_err(DerivedCertificateError::Homotopy)?;
    let desired = component
        .then(&resolution.augmentation)
        .and_then(|map| hom.coords(&map).map_err(|_| HomError::EndpointMismatch))
        .map_err(|error| DerivedCertificateError::DegreeZeroIdentification {
            reason: format!("chain map did not descend along the augmentation: {error}"),
        })?;
    lift.transpose()
        .solve(&desired, &endo.field())
        .ok_or_else(|| DerivedCertificateError::DegreeZeroIdentification {
            reason: "chain map has no induced endomorphism of T".to_string(),
        })
}

fn basis_vector(
    field: &crate::field::PrimeField,
    dimension: usize,
    index: usize,
) -> Vec<crate::field::Fp> {
    let mut coordinates = vec![field.zero(); dimension];
    coordinates[index] = field.one();
    coordinates
}

fn degree_zero_basis_coordinates(
    resolution: &ProjectiveResolution,
    target: &VerifiedTargetPresentation,
    quotient: &ChainHomQuotient,
) -> Result<DenseMat, DerivedCertificateError> {
    let field = target.endo().field();
    let rows = (0..quotient.dim())
        .map(|index| {
            induced_endomorphism_coordinates(
                resolution,
                &quotient.representative(&basis_vector(&field, quotient.dim(), index)),
                target,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let coordinates = DenseMat::from_rows_with_cols(&rows, target.endo().dim());
    if coordinates.rank(&field) != target.endo().dim() {
        return Err(DerivedCertificateError::DegreeZeroIdentification {
            reason: "induced endomorphisms do not span End(T)".to_string(),
        });
    }
    Ok(coordinates)
}

fn degree_zero_product(
    resolution: &ProjectiveResolution,
    target: &VerifiedTargetPresentation,
    quotient: &ChainHomQuotient,
    coordinates: &DenseMat,
    left: usize,
    left_map: &ChainMap,
    right: usize,
) -> Result<(), DerivedCertificateError> {
    let right_map =
        quotient.representative(&basis_vector(&target.endo().field(), quotient.dim(), right));
    let product = left_map
        .then(&right_map)
        .map_err(DerivedCertificateError::Homotopy)?;
    let quotient_product = quotient
        .reduce(&product)
        .map_err(DerivedCertificateError::Homotopy)?
        .0;
    let expected = row_times(&quotient_product, coordinates, &target.endo().field());
    let actual = induced_endomorphism_coordinates(resolution, &product, target)?;
    let direct = target
        .endo()
        .multiply(coordinates.row(left), coordinates.row(right));
    if actual != expected || actual != direct {
        return Err(DerivedCertificateError::DegreeZeroIdentification {
            reason: format!("product mismatch at quotient basis pair ({left}, {right})"),
        });
    }
    Ok(())
}

fn verify_degree_zero_products(
    resolution: &ProjectiveResolution,
    target: &VerifiedTargetPresentation,
    quotient: &ChainHomQuotient,
    coordinates: &DenseMat,
) -> Result<(), DerivedCertificateError> {
    let field = target.endo().field();
    for left in 0..quotient.dim() {
        let left_map = quotient.representative(&basis_vector(&field, quotient.dim(), left));
        for right in 0..quotient.dim() {
            degree_zero_product(
                resolution,
                target,
                quotient,
                coordinates,
                left,
                &left_map,
                right,
            )?;
        }
    }
    Ok(())
}

fn degree_zero_identification(
    resolution_complex: &BoundedComplex,
    resolution: &ProjectiveResolution,
    target: &VerifiedTargetPresentation,
    quotient: &ChainHomQuotient,
) -> Result<DegreeZeroEndIdentification, DerivedCertificateError> {
    let endo = target.endo();
    if quotient.dim() != endo.dim() {
        return Err(DerivedCertificateError::DegreeZeroDimension {
            homotopy: quotient.dim(),
            endomorphism: endo.dim(),
        });
    }
    let coordinates = degree_zero_basis_coordinates(resolution, target, quotient)?;
    verify_degree_zero_products(resolution, target, quotient, &coordinates)?;
    if !resolution_complex.verify() {
        return Err(DerivedCertificateError::ResolutionComplex(
            BoundedComplexError::Empty,
        ));
    }
    Ok(DegreeZeroEndIdentification {
        quotient: quotient.clone(),
        coordinates,
    })
}

/// A certificate for the bounded derived equivalence from a split tilting target.
#[derive(Clone)]
pub struct DerivedEquivalenceCertificate {
    pub(super) tilting: ClassicalTiltingModule,
    pub(super) target: VerifiedTargetPresentation,
    pub(super) resolution_complex: BoundedComplex,
    pub(super) graded_homotopy: Vec<GradedHomotopyEndomorphisms>,
    pub(super) degree_zero: DegreeZeroEndIdentification,
    pub(super) transport: StrictTransport,
}

debug_fields!(DerivedEquivalenceCertificate |this| {
    "source_dim_vector" => this.tilting.module().dim_vector();
    "resolution_width" => this.tilting.projective_dimension();
    "graded_homotopy_spaces" => this.graded_homotopy.len();
});

fn certificate_resolution(
    tilting: &ClassicalTiltingModule,
) -> Result<(BoundedComplex, i32), DerivedCertificateError> {
    let resolution = tilting.resolution();
    if let ResolutionEnd::Cut { at } = resolution.end {
        return Err(DerivedCertificateError::ResolutionCut { at });
    }
    for (term, module) in resolution.terms.iter().enumerate() {
        if !matches!(resolve(module, 0).end, ResolutionEnd::Finite) {
            return Err(DerivedCertificateError::ResolutionTermNotProjective { term });
        }
    }
    let resolution_complex =
        BoundedComplex::new(0, resolution.terms.clone(), resolution.maps.clone())
            .map_err(DerivedCertificateError::ResolutionComplex)?;
    let width = i32::try_from(tilting.projective_dimension()).map_err(|_| {
        DerivedCertificateError::DegreeOverflow {
            width: tilting.projective_dimension(),
        }
    })?;
    Ok((resolution_complex, width))
}

fn graded_homotopy_at_degree(
    resolution: &BoundedComplex,
    degree: i32,
) -> Result<GradedHomotopyEndomorphisms, DerivedCertificateError> {
    let shifted = resolution
        .shift(degree)
        .map_err(DerivedCertificateError::ResolutionComplex)?;
    let quotient = ChainHomSpace::new(resolution, &shifted)
        .map_err(DerivedCertificateError::Homotopy)?
        .quotient()
        .map_err(DerivedCertificateError::Homotopy)?;
    if degree != 0 && quotient.dim() != 0 {
        return Err(DerivedCertificateError::NonzeroSelfHom {
            degree,
            dimension: quotient.dim(),
        });
    }
    Ok(GradedHomotopyEndomorphisms { degree, quotient })
}

fn graded_homotopy_spaces(
    resolution: &BoundedComplex,
    width: i32,
) -> Result<(Vec<GradedHomotopyEndomorphisms>, ChainHomQuotient), DerivedCertificateError> {
    let graded_homotopy = (-width..=width)
        .map(|degree| graded_homotopy_at_degree(resolution, degree))
        .collect::<Result<Vec<_>, _>>()?;
    let zero = graded_homotopy
        .iter()
        .find(|space| space.degree == 0)
        .expect("the degree range includes zero")
        .quotient
        .clone();
    Ok((graded_homotopy, zero))
}

fn generation_is_valid(tilting: &ClassicalTiltingModule) -> bool {
    let generation = tilting.generation_complex();
    let witnesses = tilting.add_witnesses();
    generation.verify()
        && witnesses.len() + 1 == generation.complex().len()
        && witnesses
            .iter()
            .all(|witness| witness.verify() && witness.target().ptr_eq(tilting.module()))
}

fn verify_certificate_base(certificate: &DerivedEquivalenceCertificate) -> bool {
    let tilting = &certificate.tilting;
    let resolution = tilting.resolution();
    tilting.verify()
        && certificate.target.verify()
        && tilting.module().ptr_eq(certificate.target.source())
        && certificate.resolution_complex.verify()
        && resolution.end == ResolutionEnd::Finite
        && resolution
            .terms
            .iter()
            .all(|term| matches!(resolve(term, 0).end, ResolutionEnd::Finite))
}

fn verify_graded_space(
    resolution: &BoundedComplex,
    width: i32,
    offset: usize,
    space: &GradedHomotopyEndomorphisms,
) -> bool {
    let degree = -width + offset as i32;
    if space.degree != degree || !space.verify() {
        return false;
    }
    let Some(shifted) = resolution.shift(degree).ok() else {
        return false;
    };
    let Some(range) = DegreeRange::new(
        resolution.lower().min(shifted.lower()),
        resolution.upper().max(shifted.upper()),
    )
    .ok() else {
        return false;
    };
    let (Some(source), Some(target)) = (
        resolution.padded_to(range).ok(),
        shifted.padded_to(range).ok(),
    ) else {
        return false;
    };
    space.quotient.source().agrees_with(&source)
        && space.quotient.target().agrees_with(&target)
        && (degree == 0 || space.quotient.dim() == 0)
}

fn verified_zero_homotopy(
    certificate: &DerivedEquivalenceCertificate,
) -> Option<&GradedHomotopyEndomorphisms> {
    if !verify_certificate_base(certificate) {
        return None;
    }
    let width = i32::try_from(certificate.tilting.projective_dimension()).ok()?;
    let count = usize::try_from(width)
        .ok()?
        .checked_mul(2)?
        .checked_add(1)?;
    if certificate.graded_homotopy.len() != count
        || !certificate
            .graded_homotopy
            .iter()
            .enumerate()
            .all(|(offset, space)| {
                verify_graded_space(&certificate.resolution_complex, width, offset, space)
            })
    {
        return None;
    }
    certificate
        .graded_homotopy
        .iter()
        .find(|space| space.degree == 0)
}

fn verify_degree_zero(
    certificate: &DerivedEquivalenceCertificate,
    zero: &GradedHomotopyEndomorphisms,
) -> bool {
    let quotient = &certificate.degree_zero.quotient;
    let resolution = &certificate.resolution_complex;
    let Ok(rebuilt) = degree_zero_identification(
        resolution,
        certificate.tilting.resolution(),
        &certificate.target,
        quotient,
    ) else {
        return false;
    };
    let stored = &certificate.degree_zero;
    stored.quotient.verify()
        && stored.quotient.dim() == zero.quotient.dim()
        && rebuilt.coordinates == stored.coordinates
        && quotient.source().agrees_with(resolution)
        && quotient.target().agrees_with(resolution)
        && {
            let tilting = &certificate.tilting;
            let generation = tilting.generation_complex();
            generation.verify()
                && tilting.add_witnesses().len() + 1 == generation.complex().len()
                && tilting
                    .add_witnesses()
                    .iter()
                    .zip(&generation.complex().terms()[1..])
                    .all(|(witness, term)| {
                        witness.verify()
                            && witness.module().ptr_eq(term)
                            && witness.target().ptr_eq(tilting.module())
                    })
        }
}

impl DerivedEquivalenceCertificate {
    /// Builds the complete bounded derived-equivalence certificate.
    pub fn new(
        tilting: ClassicalTiltingModule,
        target: VerifiedTargetPresentation,
    ) -> Result<DerivedEquivalenceCertificate, DerivedCertificateError> {
        if !tilting.verify() {
            return Err(DerivedCertificateError::InvalidTilting);
        }
        if !target.verify() {
            return Err(DerivedCertificateError::InvalidTarget);
        }
        if !tilting.module().ptr_eq(target.source()) {
            return Err(DerivedCertificateError::DifferentSource);
        }
        let (resolution_complex, width) = certificate_resolution(&tilting)?;
        let (graded_homotopy, zero) = graded_homotopy_spaces(&resolution_complex, width)?;
        let degree_zero =
            degree_zero_identification(&resolution_complex, tilting.resolution(), &target, &zero)?;
        if !generation_is_valid(&tilting) {
            return Err(DerivedCertificateError::Generation);
        }
        let transport =
            StrictTransport::new(target.clone()).map_err(DerivedCertificateError::Transport)?;
        Ok(DerivedEquivalenceCertificate {
            tilting,
            target,
            resolution_complex,
            graded_homotopy,
            degree_zero,
            transport,
        })
    }

    accessor_methods! {
        /// The verified classical tilting data.
        pub tilting() -> &ClassicalTiltingModule = |this| &this.tilting;
        /// The verified split target presentation.
        pub target() -> &VerifiedTargetPresentation = |this| &this.target;
        /// The bounded projective resolution as a homological complex.
        pub resolution_complex() -> &BoundedComplex = |this| &this.resolution_complex;
        /// The homotopy endomorphism quotients through the resolution width.
        pub graded_homotopy() -> &[GradedHomotopyEndomorphisms] = |this| &this.graded_homotopy;
        /// The checked degree-zero algebra identification.
        pub degree_zero_identification() -> &DegreeZeroEndIdentification = |this| &this.degree_zero;
        /// The strict `add(T)` and projective transport data.
        pub transport() -> &StrictTransport = |this| &this.transport;
    }

    /// Rechecks tilting, generation, target recovery, homotopy spaces, and transport.
    pub fn verify(&self) -> bool {
        let Some(zero) = verified_zero_homotopy(self) else {
            return false;
        };
        if !verify_degree_zero(self, zero) {
            return false;
        }
        let transport = &self.transport;
        transport.verify()
            && transport.target().source().ptr_eq(self.target.source())
            && Arc::ptr_eq(transport.target().target(), self.target.target())
    }
}

use crate::decompose::{add_morphisms, direct_sum_or_zero};
use crate::hom::{
    HomError, Morphism, cokernel, factor_through_monomorphism, kernel, zero_morphism,
};
use crate::homotopy::{BoundedComplex, BoundedComplexError, ChainMap, ChainMapError};
use crate::module::{Module, same_representation, same_slice};
use crate::resolution::projective_cover;

use super::quasi::same_nominal_complex;
use super::term::{ProjectiveComplex, ProjectiveComplexError};

/// Why a projective-object cover of a bounded complex failed.
#[derive(Clone, Debug)]
pub enum ComplexProjectiveCoverError {
    /// A bounded complex construction failed.
    Complex(BoundedComplexError),
    /// A chain map construction failed.
    Chain(ChainMapError),
    /// A component morphism construction failed.
    Hom(HomError),
    /// A projective-term witness failed after construction.
    Projective(ProjectiveComplexError),
}

display_error! { ComplexProjectiveCoverError {
    Self::Complex(error) => "complex projective cover is invalid: {error}";
    Self::Chain(error) => "complex projective cover map is invalid: {error}";
    Self::Hom(error) => "complex projective cover component failed: {error}";
    Self::Projective(error) => "complex projective cover term failed: {error}";
} }

error_source! { ComplexProjectiveCoverError {
    Self::Complex(error) => Some(error),
    Self::Chain(error) => Some(error),
    Self::Hom(error) => Some(error),
    Self::Projective(error) => Some(error),
} }

from_variants! { ComplexProjectiveCoverError {
    BoundedComplexError => Complex,
    ChainMapError => Chain,
    HomError => Hom,
    ProjectiveComplexError => Projective,
} }

/// A degreewise-surjective map from a projective object in bounded complexes.
#[derive(Clone, Debug)]
pub struct ComplexProjectiveCover {
    projective: ProjectiveComplex,
    augmentation: ChainMap,
    kernel: BoundedComplex,
    kernel_inclusion: ChainMap,
}

fn kernel_component_matches(component: &Morphism, stored_inclusion: &Morphism) -> bool {
    let (rebuilt_kernel, rebuilt_inclusion) = kernel(component);
    cokernel(component).0.is_zero()
        && same_representation(&rebuilt_kernel, stored_inclusion.source())
        && (0..component.source().algebra().quiver().num_vertices())
            .all(|vertex| rebuilt_inclusion.map_at(vertex) == stored_inclusion.map_at(vertex))
}

fn cover_maps_verify(cover: &ComplexProjectiveCover) -> bool {
    cover.augmentation.verify() && cover.kernel.verify() && cover.kernel_inclusion.verify()
}

fn cover_endpoints_match(cover: &ComplexProjectiveCover) -> bool {
    same_nominal_complex(cover.projective.complex(), cover.augmentation.source())
        && same_nominal_complex(&cover.kernel, cover.kernel_inclusion.source())
        && same_nominal_complex(cover.projective.complex(), cover.kernel_inclusion.target())
        && same_slice(
            cover.augmentation.components(),
            cover.kernel_inclusion.components(),
            kernel_component_matches,
        )
}

impl ComplexProjectiveCover {
    accessor_methods! {
        /// The projective object in the category of bounded complexes.
        pub projective() -> &ProjectiveComplex = |this| &this.projective;
        /// The degreewise-surjective chain map to the input complex.
        pub augmentation() -> &ChainMap = |this| &this.augmentation;
        /// The degreewise kernel complex.
        pub kernel() -> &BoundedComplex = |this| &this.kernel;
        /// The kernel inclusion into the projective object.
        pub kernel_inclusion() -> &ChainMap = |this| &this.kernel_inclusion;
    }

    /// Rechecks the projective source, both chain maps, and every kernel.
    pub fn verify(&self) -> bool {
        self.projective.verify() && cover_maps_verify(self) && cover_endpoints_match(self)
    }
}

#[derive(Clone, Copy)]
enum DiskPart {
    Top(usize),
    Bottom(usize),
}

fn disk_index(part: DiskPart) -> usize {
    match part {
        DiskPart::Top(index) | DiskPart::Bottom(index) => index,
    }
}

struct SumTerm {
    module: Module,
    parts: Vec<DiskPart>,
    inclusions: Vec<Morphism>,
    projections: Vec<Morphism>,
}

fn sum_morphisms(
    source: &Module,
    target: &Module,
    terms: impl IntoIterator<Item = Morphism>,
) -> Result<Morphism, HomError> {
    Ok(terms
        .into_iter()
        .fold(zero_morphism(source, target)?, |sum, term| {
            add_morphisms(&sum, &term)
        }))
}

fn projective_object(
    input: &BoundedComplex,
) -> Result<(BoundedComplex, ChainMap), ComplexProjectiveCoverError> {
    let range = input.range();
    let covers: Vec<(Module, Morphism)> = input.terms().iter().map(projective_cover).collect();
    let sum_terms = (0..range.len())
        .map(|offset| {
            let degree = range.lower() + offset as i32;
            let top = (degree - input.lower()) as usize;
            let parts = [
                Some(DiskPart::Top(top)),
                degree
                    .checked_add(1)
                    .filter(|&next| range.contains(next))
                    .map(|next| DiskPart::Bottom((next - input.lower()) as usize)),
            ]
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
            let (module, inclusions, projections) = direct_sum_or_zero(
                input.terms()[0].algebra(),
                parts.iter().map(|part| &covers[disk_index(*part)].0),
            );
            SumTerm {
                module,
                parts,
                inclusions,
                projections,
            }
        })
        .collect::<Vec<_>>();

    let differentials = sum_terms
        .windows(2)
        .map(|pair| {
            let target = &pair[0];
            let source = &pair[1];
            let components = source
                .parts
                .iter()
                .enumerate()
                .filter_map(|(source_slot, part)| {
                    let DiskPart::Top(index) = part else {
                        return None;
                    };
                    target
                        .parts
                        .iter()
                        .position(|candidate| {
                            matches!(candidate, DiskPart::Bottom(other) if other == index)
                        })
                        .map(|target_slot| {
                            source.projections[source_slot]
                                .then(&target.inclusions[target_slot])
                                .expect("disk copies use one projective module")
                        })
                });
            sum_morphisms(&source.module, &target.module, components)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let projective = BoundedComplex::new(
        range.lower(),
        sum_terms.iter().map(|term| term.module.clone()).collect(),
        differentials,
    )?;
    let components = sum_terms
        .iter()
        .enumerate()
        .map(|(offset, source)| {
            let target_term = &input.terms()[offset];
            let pieces = source.parts.iter().enumerate().map(|(slot, part)| {
                let part_map = match *part {
                    DiskPart::Top(index) => covers[index].1.clone(),
                    DiskPart::Bottom(index) => input
                        .differential(input.lower() + index as i32)
                        .map(|differential| {
                            covers[index]
                                .1
                                .then(differential)
                                .expect("a cover targets the differential source")
                        })
                        .unwrap_or_else(|| {
                            zero_morphism(&covers[index].0, target_term)
                                .expect("complex terms share an algebra")
                        }),
                };
                source.projections[slot]
                    .then(&part_map)
                    .expect("a disk projection targets its projective part")
            });
            sum_morphisms(&source.module, target_term, pieces)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let augmentation = ChainMap::new(&projective, input, components)?;
    Ok((projective, augmentation))
}

fn kernel_complex(
    map: &ChainMap,
) -> Result<(BoundedComplex, ChainMap), ComplexProjectiveCoverError> {
    let kernels: Vec<(Module, Morphism)> = map.components().iter().map(kernel).collect();
    let differentials = (1..kernels.len())
        .map(|index| {
            let into_source = kernels[index]
                .1
                .then(
                    map.source()
                        .differential(map.range().lower() + index as i32)
                        .expect("every nonlowest source term has a differential"),
                )
                .expect("the kernel inclusion targets the source differential");
            factor_through_monomorphism(&kernels[index - 1].1, &into_source)
        })
        .collect();
    let complex = BoundedComplex::new(
        map.range().lower(),
        kernels.iter().map(|(module, _)| module.clone()).collect(),
        differentials,
    )?;
    let inclusion = ChainMap::new(
        &complex,
        map.source(),
        kernels
            .iter()
            .map(|(_, inclusion)| inclusion.clone())
            .collect(),
    )?;
    Ok((complex, inclusion))
}

/// Builds the canonical projective-object cover of a bounded complex.
pub fn projective_complex_cover(
    input: &BoundedComplex,
) -> Result<ComplexProjectiveCover, ComplexProjectiveCoverError> {
    let (projective, augmentation) = projective_object(input)?;
    let projective = ProjectiveComplex::new(projective)?;
    let (kernel, kernel_inclusion) = kernel_complex(&augmentation)?;
    let cover = ComplexProjectiveCover {
        projective,
        augmentation,
        kernel,
        kernel_inclusion,
    };
    debug_assert!(cover.verify());
    Ok(cover)
}

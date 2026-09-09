use crate::decompose::{Split, SplitError, direct_sum_or_zero, inverse_morphism};
use crate::hom::{HomError, Morphism, kernel};
use crate::homotopy::{BoundedComplex, BoundedComplexError};
use crate::module::{Module, same_representation};
use crate::radical::top;
use crate::resolution::projective_cover;

/// Why a module has no checked canonical-projective split.
#[derive(Clone, Debug)]
pub enum ProjectiveTermError {
    /// The projective cover has a nonzero kernel.
    NotProjective,
    /// The reconstructed canonical sum does not match the projective cover.
    CoverMismatch,
    /// The projective cover did not yield an invertible map.
    CoverNotInvertible,
    /// The canonical summands did not form a checked split.
    Split(SplitError),
    /// A split component could not be composed.
    Hom(HomError),
}

display_error! { ProjectiveTermError {
    Self::NotProjective => "the module is not projective";
    Self::CoverMismatch => "the canonical projective sum differs from the projective cover";
    Self::CoverNotInvertible => "the projective cover of a projective module is not invertible";
    Self::Split(error) => "canonical projective split failed: {error}";
    Self::Hom(error) => "canonical projective split map failed: {error}";
} }

error_source! { ProjectiveTermError {
    Self::Split(error) => Some(error),
    Self::Hom(error) => Some(error),
    _ => None,
} }

from_variants! { ProjectiveTermError {
    SplitError => Split,
    HomError => Hom,
} }

/// A verified split of one module into canonical projectives.
#[derive(Clone, Debug)]
pub struct ProjectiveTermWitness {
    module: Module,
    vertices: Vec<u32>,
    split: Split,
}

fn projective_term_maps(
    canonical_sum: &Module,
    module: &Module,
    cover: &Morphism,
    inclusions: &[Morphism],
    projections: &[Morphism],
) -> Result<(Morphism, Morphism, Vec<Morphism>, Vec<Morphism>), ProjectiveTermError> {
    let maps = (0..module.algebra().quiver().num_vertices())
        .map(|vertex| cover.map_at(vertex).clone())
        .collect();
    let to_module = Morphism::new(canonical_sum, module, maps)?;
    let from_module =
        inverse_morphism(&to_module).ok_or(ProjectiveTermError::CoverNotInvertible)?;
    let split_inclusions = inclusions
        .iter()
        .map(|inclusion| inclusion.then(&to_module))
        .collect::<Result<_, _>>()?;
    let split_projections = projections
        .iter()
        .map(|projection| from_module.then(projection))
        .collect::<Result<_, _>>()?;
    Ok((to_module, from_module, split_inclusions, split_projections))
}

fn canonical_projective_split(
    module: &Module,
    cover_source: &Module,
    cover: &Morphism,
) -> Result<(Vec<u32>, Split), ProjectiveTermError> {
    let (module_top, _) = top(module);
    let (vertices, summands): (Vec<u32>, Vec<Module>) =
        (0..module.algebra().quiver().num_vertices())
            .flat_map(|vertex| std::iter::repeat_n(vertex, module_top.dim_at(vertex)))
            .map(|vertex| (vertex, Module::projective(module.algebra(), vertex)))
            .unzip();
    let (canonical_sum, inclusions, projections) =
        direct_sum_or_zero(module.algebra(), summands.iter());
    if !same_representation(cover_source, &canonical_sum) {
        return Err(ProjectiveTermError::CoverMismatch);
    }
    let (_, _, split_inclusions, split_projections) =
        projective_term_maps(&canonical_sum, module, cover, &inclusions, &projections)?;
    let split = Split::new(module, summands, split_inclusions, split_projections)?;
    Ok((vertices, split))
}

impl ProjectiveTermWitness {
    /// Builds the canonical-projective split of `module`.
    pub fn new(module: &Module) -> Result<ProjectiveTermWitness, ProjectiveTermError> {
        let (cover_source, cover) = projective_cover(module);
        if !kernel(&cover).0.is_zero() {
            return Err(ProjectiveTermError::NotProjective);
        }

        let (vertices, split) = canonical_projective_split(module, &cover_source, &cover)?;
        Ok(ProjectiveTermWitness {
            module: module.clone(),
            vertices,
            split,
        })
    }

    accessor_methods! {
        /// The projective module.
        pub module() -> &Module = |this| &this.module;
        /// The canonical-projective vertices, with multiplicity.
        pub vertices() -> &[u32] = |this| &this.vertices;
        /// The checked split into canonical projectives.
        pub split() -> &Split = |this| &this.split;
    }

    /// Rechecks projectivity and every split identity.
    pub fn verify(&self) -> bool {
        let Ok(rebuilt) = ProjectiveTermWitness::new(&self.module) else {
            return false;
        };
        self.split.verify()
            && self.split.total().ptr_eq(&self.module)
            && self.vertices == rebuilt.vertices
            && self
                .split
                .summands()
                .iter()
                .zip(rebuilt.split.summands())
                .all(|(left, right)| same_representation(left, right))
    }
}

/// Why a bounded complex has no checked projective-term witness.
#[derive(Clone, Debug)]
pub struct ProjectiveComplexError {
    degree: i32,
    source: ProjectiveTermError,
}

impl ProjectiveComplexError {
    accessor_methods! {
        /// The first nonprojective term degree.
        pub degree() -> i32 = |this| this.degree;
        /// Why that term failed.
        pub source_error() -> &ProjectiveTermError = |this| &this.source;
    }
}

display_error! { ProjectiveComplexError {
    Self { degree, source } => "complex term at degree {degree} is not projective: {source}";
} }

impl std::error::Error for ProjectiveComplexError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.source)
    }
}

/// A bounded complex with a canonical-projective split at every term.
#[derive(Clone, Debug)]
pub struct ProjectiveComplex {
    complex: BoundedComplex,
    terms: Vec<ProjectiveTermWitness>,
}

impl ProjectiveComplex {
    /// Checks every term of a bounded complex for projectivity.
    pub fn new(complex: BoundedComplex) -> Result<ProjectiveComplex, ProjectiveComplexError> {
        let terms = complex
            .terms()
            .iter()
            .enumerate()
            .map(|(offset, term)| {
                ProjectiveTermWitness::new(term).map_err(|source| ProjectiveComplexError {
                    degree: complex.lower() + offset as i32,
                    source,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(ProjectiveComplex { complex, terms })
    }

    accessor_methods! {
        /// The bounded complex.
        pub complex() -> &BoundedComplex = |this| &this.complex;
        /// One canonical-projective split per term.
        pub terms() -> &[ProjectiveTermWitness] = |this| &this.terms;
    }

    /// Rechecks the complex and every projective-term split.
    pub fn verify(&self) -> bool {
        self.complex.verify()
            && self.terms.len() == self.complex.len()
            && self
                .complex
                .terms()
                .iter()
                .zip(&self.terms)
                .all(|(module, witness)| module.ptr_eq(witness.module()) && witness.verify())
    }

    /// Returns the checked shift of this projective complex.
    pub fn shift(&self, amount: i32) -> Result<ProjectiveComplex, BoundedComplexError> {
        Ok(ProjectiveComplex {
            complex: self.complex.shift(amount)?,
            terms: self.terms.clone(),
        })
    }
}

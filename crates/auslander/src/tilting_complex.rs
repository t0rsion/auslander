//! Certified tilting complexes and checked left mutation.

mod approximation;
mod cache;
mod classification;

use std::sync::Arc;

use crate::algebra::Algebra;
use crate::hom::{HomError, Morphism};
use crate::homotopy::{
    BoundedComplex, BoundedComplexError, ChainMap, ChainMapError, DegreeRange, HomotopyHom,
    HomotopyHomQuotient,
};
use crate::linalg::DenseMat;
use crate::module::{Module, same_representation};
use crate::perfect::{ProjectiveComplex, ProjectiveComplexError};

use approximation::{approximation_map, approximation_map_with_blocks};
pub use cache::TiltingComplexWork;
use cache::{HomotopyBlockBuilder, HomotopyBlockCache};
use classification::{ClassificationFailure, classify_tilting_complex_inner};

/// Why a tilting-complex candidate was rejected at construction.
#[derive(Clone, Debug)]
pub enum TiltingComplexCandidateError {
    /// A candidate needs at least one summand.
    Empty,
    /// A summand is the zero complex.
    ZeroSummand { summand: usize },
    /// A summand uses another algebra value.
    DifferentAlgebra { summand: usize },
}

display_error! { error TiltingComplexCandidateError {
    Self::Empty => "a tilting-complex candidate needs one summand";
    Self::ZeroSummand { summand } => "tilting-complex summand {summand} is zero";
    Self::DifferentAlgebra { summand } => "tilting-complex summand {summand} uses another algebra";
} }

/// An ordered list of nonzero bounded projective complexes.
#[derive(Clone, Debug)]
pub struct TiltingComplexCandidate {
    summands: Vec<ProjectiveComplex>,
}

impl TiltingComplexCandidate {
    /// Checks a nonempty ordered summand list over one algebra.
    pub fn new(
        summands: Vec<ProjectiveComplex>,
    ) -> Result<TiltingComplexCandidate, TiltingComplexCandidateError> {
        let first = summands
            .first()
            .ok_or(TiltingComplexCandidateError::Empty)?;
        for (summand, complex) in summands.iter().enumerate() {
            if complex.complex().is_zero() {
                return Err(TiltingComplexCandidateError::ZeroSummand { summand });
            }
            if !Arc::ptr_eq(
                first.complex().terms()[0].algebra(),
                complex.complex().terms()[0].algebra(),
            ) {
                return Err(TiltingComplexCandidateError::DifferentAlgebra { summand });
            }
        }
        Ok(TiltingComplexCandidate { summands })
    }

    /// Builds the regular projective generator in vertex order.
    pub fn regular(algebra: &Arc<Algebra>) -> TiltingComplexCandidate {
        let summands = (0..algebra.quiver().num_vertices())
            .map(|vertex| {
                ProjectiveComplex::new(
                    BoundedComplex::new(0, vec![Module::projective(algebra, vertex)], Vec::new())
                        .expect("one projective module is a bounded complex"),
                )
                .expect("a canonical projective has a projective witness")
            })
            .collect();
        TiltingComplexCandidate { summands }
    }

    accessor_methods! {
        /// The ordered projective-complex summands.
        pub summands() -> &[ProjectiveComplex] = |this| &this.summands;
        /// The number of ordered summands.
        pub len() -> usize = |this| this.summands.len();
        /// Whether the candidate has no summands.
        pub is_empty() -> bool = |_this| false;
    }

    /// The shared source algebra.
    pub fn algebra(&self) -> &Arc<Algebra> {
        self.summands[0].complex().terms()[0].algebra()
    }

    /// Rechecks every projective summand and the candidate constraints.
    pub fn verify(&self) -> bool {
        self.summands.iter().all(ProjectiveComplex::verify)
            && TiltingComplexCandidate::new(self.summands.clone()).is_ok()
    }
}

fn complexes_agree(left: &ProjectiveComplex, right: &ProjectiveComplex) -> bool {
    left.verify() && right.verify() && left.complex().agrees_with(right.complex())
}

/// A checked proof that the candidate generates `K^b(proj A)`.
#[derive(Clone)]
pub enum ThickGenerationWitness {
    /// The candidate is the regular projective generator in vertex order.
    Regular,
    /// One cone mutation preserves the thick closure of a certified parent.
    Mutation {
        parent: Arc<CertifiedTiltingComplex>,
        approximation: ComplexApproximationWitness,
    },
}

impl std::fmt::Debug for ThickGenerationWitness {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ThickGenerationWitness::Regular => formatter.write_str("Regular"),
            ThickGenerationWitness::Mutation { approximation, .. } => formatter
                .debug_struct("Mutation")
                .field("direction", &approximation.direction)
                .field("replaced", &approximation.replaced)
                .field("indices", &approximation.indices)
                .finish(),
        }
    }
}

fn regular_generation(candidate: &TiltingComplexCandidate) -> bool {
    candidate.len() == candidate.algebra().quiver().num_vertices() as usize
        && candidate
            .summands()
            .iter()
            .enumerate()
            .all(|(vertex, summand)| {
                let complex = summand.complex();
                complex.lower() == 0
                    && complex.upper() == 0
                    && same_representation(
                        &complex.terms()[0],
                        &Module::projective(candidate.algebra(), vertex as u32),
                    )
            })
}

/// The side on which an approximation map starts.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ApproximationDirection {
    /// A map from the replaced summand to the other summands.
    Left,
    /// A map from the other summands to the replaced summand.
    Right,
}

impl ApproximationDirection {
    fn orient<T>(self, left: T, right: T) -> (T, T) {
        match self {
            Self::Left => (left, right),
            Self::Right => (right, left),
        }
    }
}

/// A universal approximation in the supported exceptional domain.
#[derive(Clone, Debug)]
pub struct ComplexApproximationWitness {
    direction: ApproximationDirection,
    replaced: usize,
    indices: Vec<usize>,
    map: ChainMap,
}

impl ComplexApproximationWitness {
    accessor_methods! {
        /// Whether the approximation is left or right.
        pub direction() -> ApproximationDirection = |this| this.direction;
        /// The parent summand replaced by mutation.
        pub replaced() -> usize = |this| this.replaced;
        /// One parent index per Hom-basis component, in deterministic order.
        pub indices() -> &[usize] = |this| &this.indices;
        /// The checked universal approximation map.
        pub map() -> &ChainMap = |this| &this.map;
    }

    /// Rebuilds every Hom basis and the resulting approximation map.
    pub fn verify(&self, parent: &CertifiedTiltingComplex) -> bool {
        let rebuilt = approximation_map(parent, self.replaced, self.direction);
        rebuilt.is_ok_and(|(map, indices)| {
            indices == self.indices && map.agrees_with(&self.map) && map.verify()
        })
    }

    /// Rebuilds the cone replacement in the parent grading convention.
    pub fn replacement(&self) -> Result<BoundedComplex, BoundedComplexError> {
        let cone = self.map.mapping_cone()?;
        match self.direction {
            ApproximationDirection::Left => Ok(cone),
            ApproximationDirection::Right => cone.shift(-1),
        }
    }
}

impl ThickGenerationWitness {
    /// Rechecks the regular generator or the inherited cone relation.
    pub fn verify(&self, candidate: &TiltingComplexCandidate) -> bool {
        match self {
            ThickGenerationWitness::Regular => regular_generation(candidate),
            ThickGenerationWitness::Mutation {
                parent,
                approximation,
            } => {
                let replaced = approximation.replaced;
                if !parent.verify()
                    || replaced >= parent.candidate().len()
                    || candidate.len() != parent.candidate().len()
                    || approximation
                        .indices
                        .iter()
                        .any(|&index| index >= parent.candidate().len() || index == replaced)
                {
                    return false;
                }
                let unchanged = candidate
                    .summands()
                    .iter()
                    .enumerate()
                    .all(|(index, summand)| {
                        index == replaced
                            || complexes_agree(summand, &parent.candidate().summands()[index])
                    });
                let Ok(replacement) = approximation.replacement() else {
                    return false;
                };
                unchanged
                    && approximation.verify(parent)
                    && replacement.agrees_with(candidate.summands()[replaced].complex())
            }
        }
    }

    fn verify_with_cached_blocks(&self, candidate: &TiltingComplexCandidate) -> bool {
        match self {
            ThickGenerationWitness::Regular => regular_generation(candidate),
            ThickGenerationWitness::Mutation {
                parent,
                approximation,
            } => {
                let replaced = approximation.replaced;
                if !parent.candidate().verify()
                    || replaced >= parent.candidate().len()
                    || candidate.len() != parent.candidate().len()
                    || approximation
                        .indices
                        .iter()
                        .any(|&index| index >= parent.candidate().len() || index == replaced)
                {
                    return false;
                }
                let unchanged = candidate
                    .summands()
                    .iter()
                    .enumerate()
                    .all(|(index, summand)| {
                        index == replaced
                            || complexes_agree(summand, &parent.candidate().summands()[index])
                    });
                let Ok(replacement) = approximation.replacement() else {
                    return false;
                };
                let mut blocks = HomotopyBlockBuilder::with_inherited(parent.block_cache());
                let rebuilt = approximation_map_with_blocks(
                    parent,
                    replaced,
                    approximation.direction,
                    &mut blocks,
                );
                unchanged
                    && approximation.map.verify()
                    && rebuilt.is_ok_and(|(map, indices)| {
                        indices == approximation.indices && map.agrees_with(&approximation.map)
                    })
                    && replacement.agrees_with(candidate.summands()[replaced].complex())
            }
        }
    }
}

/// Limits for exact tilting-complex checks.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TiltingComplexLimits {
    /// The greatest number of homotopy Hom quotients built.
    pub max_hom_spaces: usize,
}

impl Default for TiltingComplexLimits {
    fn default() -> Self {
        TiltingComplexLimits {
            max_hom_spaces: 4_096,
        }
    }
}

/// One checked shifted homotopy Hom quotient.
#[derive(Clone, Debug)]
pub struct TiltingHomCheck {
    source: usize,
    target: usize,
    degree: i32,
    quotient: HomotopyHomQuotient,
}

impl TiltingHomCheck {
    accessor_methods! {
        /// The source summand index.
        pub source() -> usize = |this| this.source;
        /// The target summand index.
        pub target() -> usize = |this| this.target;
        /// The target shift degree.
        pub degree() -> i32 = |this| this.degree;
        /// The checked homotopy Hom quotient.
        pub quotient() -> &HomotopyHomQuotient = |this| &this.quotient;
    }

    /// Rechecks the stored quotient.
    pub fn verify(&self) -> bool {
        self.degree == self.quotient.degree() && self.quotient.verify()
    }
}

/// A nonzero shifted Hom class that rejects tilting.
#[derive(Clone, Debug)]
pub struct TiltingSelfOrthogonalityRejection {
    source: usize,
    target: usize,
    degree: i32,
    quotient: HomotopyHomQuotient,
    representative: ChainMap,
}

impl TiltingSelfOrthogonalityRejection {
    accessor_methods! {
        /// The source summand index.
        pub source() -> usize = |this| this.source;
        /// The target summand index.
        pub target() -> usize = |this| this.target;
        /// The nonzero target shift degree.
        pub degree() -> i32 = |this| this.degree;
        /// The nonzero quotient dimension.
        pub dimension() -> usize = |this| this.quotient.dim();
        /// One nonzero representative chain map.
        pub representative() -> &ChainMap = |this| &this.representative;
    }

    /// Rechecks the quotient and representative class.
    pub fn verify(&self) -> bool {
        self.degree != 0
            && self.quotient.verify()
            && self.quotient.dim() > 0
            && self
                .quotient
                .reduce(&self.representative)
                .is_ok_and(|(coordinates, _)| coordinates.iter().any(|value| !value.is_zero()))
    }
}

/// Why exact tilting classification remains open.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TiltingComplexBlocker {
    /// A summand endomorphism quotient needs a general local-algebra test.
    EndomorphismLocality { summand: usize, dimension: usize },
    /// Two summands are isomorphic in the homotopy category.
    RepeatedSummand { first: usize, second: usize },
    /// No checked thick-generation witness was supplied.
    Generation,
    /// The Hom-space limit stopped the finite check.
    HomLimit { completed: usize, limit: usize },
}

/// A certified basic tilting complex.
#[derive(Clone)]
pub struct CertifiedTiltingComplex {
    candidate: TiltingComplexCandidate,
    generation: ThickGenerationWitness,
    degree_zero_endomorphisms: Vec<HomotopyHomQuotient>,
    zero_shifted_homs: Vec<TiltingHomCheck>,
    limits: TiltingComplexLimits,
    block_cache: HomotopyBlockCache,
    work: TiltingComplexWork,
}

impl std::fmt::Debug for CertifiedTiltingComplex {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("CertifiedTiltingComplex")
            .field("summands", &self.candidate.len())
            .field("zero_shifted_homs", &self.zero_shifted_homs.len())
            .field("hom_spaces_built", &self.work.hom_spaces_built())
            .field("hom_spaces_reused", &self.work.hom_spaces_reused())
            .finish()
    }
}

impl CertifiedTiltingComplex {
    accessor_methods! {
        /// The ordered projective-complex candidate.
        pub candidate() -> &TiltingComplexCandidate = |this| &this.candidate;
        /// The checked thick-generation witness.
        pub generation() -> &ThickGenerationWitness = |this| &this.generation;
        /// One degree-zero endomorphism quotient per summand.
        pub degree_zero_endomorphisms() -> &[HomotopyHomQuotient] = |this| &this.degree_zero_endomorphisms;
        /// Every checked zero quotient in a nonzero shift.
        pub zero_shifted_homs() -> &[TiltingHomCheck] = |this| &this.zero_shifted_homs;
        /// The effective classification limits.
        pub limits() -> TiltingComplexLimits = |this| this.limits;
        /// The exact Homotopy-block work for this classification.
        pub work() -> TiltingComplexWork = |this| this.work;
    }

    fn block_cache(&self) -> &HomotopyBlockCache {
        &self.block_cache
    }

    /// Recomputes the complete tilting classification.
    pub fn verify(&self) -> bool {
        matches!(
            classify_tilting_complex(
                self.candidate.clone(),
                Some(self.generation.clone()),
                self.limits,
            ),
            Ok(TiltingComplexResult::Tilting(ref rebuilt))
                if rebuilt.zero_shifted_homs.len() == self.zero_shifted_homs.len()
                    && rebuilt.degree_zero_endomorphisms.len()
                        == self.degree_zero_endomorphisms.len()
        )
    }
}

/// Exact tilting classification, rejection, or typed blocker.
#[derive(Clone, Debug)]
pub enum TiltingComplexResult {
    /// Every tilting obligation completed.
    Tilting(Box<CertifiedTiltingComplex>),
    /// A nonzero shifted Hom class rejects self-orthogonality.
    NotTilting(Box<TiltingSelfOrthogonalityRejection>),
    /// A local-algebra, generation, or resource check remains open.
    Undetermined(TiltingComplexBlocker),
}

/// Why a tilting-complex check failed structurally.
#[derive(Clone, Debug)]
pub enum TiltingComplexError {
    /// A homotopy Hom quotient failed construction.
    Chain(ChainMapError),
    /// A degree endpoint overflowed.
    DegreeOverflow,
    /// A cone ceased to have projective terms.
    Projective(ProjectiveComplexError),
    /// A cone failed bounded-complex construction.
    Complex(BoundedComplexError),
    /// An approximation component failed construction.
    Hom(HomError),
}

display_error! { TiltingComplexError {
    Self::Chain(error) => "tilting-complex Hom check failed: {error}";
    Self::DegreeOverflow => "tilting-complex shift degree overflowed";
    Self::Projective(error) => "tilting-complex cone is not projective: {error}";
    Self::Complex(error) => "tilting-complex cone failed: {error}";
    Self::Hom(error) => "tilting-complex approximation failed: {error}";
} }

error_source! { TiltingComplexError {
    Self::Chain(error) => Some(error),
    Self::Projective(error) => Some(error),
    Self::Complex(error) => Some(error),
    Self::Hom(error) => Some(error),
    Self::DegreeOverflow => None,
} }

from_variants! { TiltingComplexError {
    ChainMapError => Chain,
    ProjectiveComplexError => Projective,
    BoundedComplexError => Complex,
    HomError => Hom,
} }

/// Checks basicness, self-orthogonality, and thick generation.
pub fn classify_tilting_complex(
    candidate: TiltingComplexCandidate,
    generation: Option<ThickGenerationWitness>,
    limits: TiltingComplexLimits,
) -> Result<TiltingComplexResult, TiltingComplexError> {
    match classify_tilting_complex_inner(
        candidate,
        generation,
        limits,
        HomotopyBlockBuilder::cold(),
        true,
    ) {
        Ok(outcome) | Err(ClassificationFailure::Outcome(outcome)) => Ok(outcome),
        Err(ClassificationFailure::Error(error)) => Err(error),
    }
}

/// Certifies the regular projective generator.
pub fn regular_tilting_complex(
    algebra: &Arc<Algebra>,
    limits: TiltingComplexLimits,
) -> Result<TiltingComplexResult, TiltingComplexError> {
    let candidate = TiltingComplexCandidate::regular(algebra);
    classify_tilting_complex(candidate, Some(ThickGenerationWitness::Regular), limits)
}

/// The result of one checked left mutation.
#[derive(Clone, Debug)]
pub enum TiltingMutationOutcome {
    /// The cone remains a certified tilting complex.
    Tilting(Box<CertifiedTiltingComplex>),
    /// The cone generates but has a nonzero shifted Hom class.
    SiltingOnly(Box<TiltingSelfOrthogonalityRejection>),
    /// Basicness or a resource limit remains open.
    Undetermined(TiltingComplexBlocker),
}

fn mutated_candidate(
    parent: &CertifiedTiltingComplex,
    approximation: &ComplexApproximationWitness,
) -> Result<TiltingComplexCandidate, TiltingComplexError> {
    let cone = ProjectiveComplex::new(approximation.replacement()?)?;
    let mut summands = parent.candidate().summands().to_vec();
    summands[approximation.replaced] = cone;
    Ok(TiltingComplexCandidate::new(summands)
        .expect("mutation keeps a nonempty list over one algebra"))
}

fn tilting_mutation(
    parent: &CertifiedTiltingComplex,
    replaced: usize,
    limits: TiltingComplexLimits,
    direction: ApproximationDirection,
) -> Result<TiltingMutationOutcome, TiltingComplexError> {
    tilting_mutation_with_cache(parent, replaced, limits, direction, true)
}

fn tilting_mutation_with_cache(
    parent: &CertifiedTiltingComplex,
    replaced: usize,
    limits: TiltingComplexLimits,
    direction: ApproximationDirection,
    reuse: bool,
) -> Result<TiltingMutationOutcome, TiltingComplexError> {
    if replaced >= parent.candidate().len() {
        return Ok(TiltingMutationOutcome::Undetermined(
            TiltingComplexBlocker::Generation,
        ));
    }
    let mut blocks = mutation_blocks(parent, reuse);
    let (map, indices) = approximation_map_with_blocks(parent, replaced, direction, &mut blocks)?;
    let approximation = ComplexApproximationWitness {
        direction,
        replaced,
        indices,
        map,
    };
    let candidate = mutated_candidate(parent, &approximation)?;
    blocks.set_changed(replaced);
    let generation = ThickGenerationWitness::Mutation {
        parent: Arc::new(parent.clone()),
        approximation,
    };
    let classified = classify_mutated(candidate, generation, limits, blocks)?;
    Ok(mutation_outcome(classified))
}

fn mutation_blocks(parent: &CertifiedTiltingComplex, reuse: bool) -> HomotopyBlockBuilder<'_> {
    if reuse {
        HomotopyBlockBuilder::with_inherited(parent.block_cache())
    } else {
        HomotopyBlockBuilder::cold()
    }
}

fn classify_mutated(
    candidate: TiltingComplexCandidate,
    generation: ThickGenerationWitness,
    limits: TiltingComplexLimits,
    blocks: HomotopyBlockBuilder<'_>,
) -> Result<TiltingComplexResult, TiltingComplexError> {
    match classify_tilting_complex_inner(candidate, Some(generation), limits, blocks, false) {
        Ok(outcome) | Err(ClassificationFailure::Outcome(outcome)) => Ok(outcome),
        Err(ClassificationFailure::Error(error)) => Err(error),
    }
}

fn mutation_outcome(classified: TiltingComplexResult) -> TiltingMutationOutcome {
    match classified {
        TiltingComplexResult::Tilting(value) => TiltingMutationOutcome::Tilting(value),
        TiltingComplexResult::NotTilting(rejection) => {
            TiltingMutationOutcome::SiltingOnly(rejection)
        }
        TiltingComplexResult::Undetermined(blocker) => {
            TiltingMutationOutcome::Undetermined(blocker)
        }
    }
}

/// Computes the universal left mutation at one exceptional summand.
pub fn left_tilting_mutation(
    parent: &CertifiedTiltingComplex,
    replaced: usize,
    limits: TiltingComplexLimits,
) -> Result<TiltingMutationOutcome, TiltingComplexError> {
    tilting_mutation(parent, replaced, limits, ApproximationDirection::Left)
}

/// Computes the universal right mutation at one exceptional summand.
pub fn right_tilting_mutation(
    parent: &CertifiedTiltingComplex,
    replaced: usize,
    limits: TiltingComplexLimits,
) -> Result<TiltingMutationOutcome, TiltingComplexError> {
    tilting_mutation(parent, replaced, limits, ApproximationDirection::Right)
}

#[cfg(test)]
mod tests;

//! Certified tilting and silting complexes and checked mutation.

mod approximation;
mod cache;
mod certified;
mod classification;
mod locality;
mod mutation;
mod reduction;

use std::sync::Arc;

use crate::algebra::Algebra;
use crate::control::{Cancelled, WorkMeter};
use crate::field::Fp;
use crate::hom::{HomError, Morphism};
use crate::homotopy::{
    BoundedComplex, BoundedComplexError, ChainMap, ChainMapError, DegreeRange, HomotopyHom,
    HomotopyHomQuotient,
};
use crate::linalg::DenseMat;
use crate::module::{Module, same_representation};
use crate::perfect::{ProjectiveComplex, ProjectiveComplexError};

use approximation::{approximation_map, approximation_map_with_blocks};
use cache::HomotopyBlockBuilder;
pub use cache::TiltingComplexWork;
pub(crate) use certified::OrthogonalityGoal;
pub use certified::{CertifiedSiltingComplex, CertifiedTiltingComplex};
pub(crate) use classification::summands_isomorphic;
use classification::{ClassificationFailure, classify_tilting_complex_inner, classify_with_goal};
use mutation::cone_replacement;
pub use mutation::{
    TiltingMutationOutcome, left_tilting_mutation, right_tilting_mutation, silting_mutation,
};
pub(crate) use mutation::{metered_tilting_mutation, tilting_mutation};
pub use reduction::MinimalReduction;

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
    ///
    /// The cone relation needs only that the parent generates, so a silting
    /// parent suffices.
    Mutation {
        parent: Arc<CertifiedSiltingComplex>,
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

/// A minimal approximation of one summand by the other summands.
#[derive(Clone, Debug)]
pub struct ComplexApproximationWitness {
    direction: ApproximationDirection,
    replaced: usize,
    indices: Vec<usize>,
    map: ChainMap,
    reduction: Box<MinimalReduction>,
}

impl ComplexApproximationWitness {
    accessor_methods! {
        /// Whether the approximation is left or right.
        pub direction() -> ApproximationDirection = |this| this.direction;
        /// The parent summand replaced by mutation.
        pub replaced() -> usize = |this| this.replaced;
        /// One parent index per kept Hom-basis component, in deterministic order.
        pub indices() -> &[usize] = |this| &this.indices;
        /// The checked universal approximation map.
        pub map() -> &ChainMap = |this| &this.map;
        /// The homotopy equivalence from the replacement to the stored summand.
        pub reduction() -> &MinimalReduction = |this| &this.reduction;
    }

    /// Rebuilds every Hom basis, the minimal selection, and the approximation map.
    pub fn verify(&self, parent: &CertifiedSiltingComplex) -> bool {
        let rebuilt = approximation_map(parent, self.replaced, self.direction);
        rebuilt.is_ok_and(|(map, indices)| {
            indices == self.indices && map.agrees_with(&self.map) && map.verify()
        })
    }

    /// Rebuilds the cone replacement in the parent grading convention.
    ///
    /// The stored summand is the minimal complex of
    /// [`ComplexApproximationWitness::reduction`], not this cone.
    pub fn replacement(&self) -> Result<BoundedComplex, BoundedComplexError> {
        cone_replacement(&self.map, self.direction)
    }

    /// Whether `summand` is the checked minimal reduction of the rebuilt cone.
    fn replacement_matches(&self, summand: &ProjectiveComplex) -> bool {
        self.replacement()
            .is_ok_and(|replacement| self.reduction.verify(&replacement))
            && complexes_agree(self.reduction.minimal(), summand)
    }

    /// Whether the indices are in range and `candidate` keeps every parent
    /// summand except the replaced one.
    fn keeps_parent_summands(
        &self,
        parent: &CertifiedSiltingComplex,
        candidate: &TiltingComplexCandidate,
    ) -> bool {
        let kept = parent.candidate().summands();
        let in_range = |index: usize| index < kept.len() && index != self.replaced;
        self.replaced < kept.len()
            && candidate.len() == kept.len()
            && self.indices.iter().all(|&index| in_range(index))
            && candidate.summands().iter().zip(kept).enumerate().all(
                |(index, (summand, parent))| {
                    index == self.replaced || complexes_agree(summand, parent)
                },
            )
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
                parent.verify()
                    && approximation.keeps_parent_summands(parent, candidate)
                    && approximation.verify(parent)
                    && approximation
                        .replacement_matches(&candidate.summands()[approximation.replaced])
            }
        }
    }

    fn verify_with_cached_blocks(
        &self,
        candidate: &TiltingComplexCandidate,
        meter: &mut WorkMeter,
    ) -> Result<bool, Cancelled> {
        let ThickGenerationWitness::Mutation {
            parent,
            approximation,
        } = self
        else {
            return Ok(regular_generation(candidate));
        };
        if !parent.candidate().verify()
            || !approximation.keeps_parent_summands(parent, candidate)
            || !approximation.map.verify()
            || !approximation.replacement_matches(&candidate.summands()[approximation.replaced])
        {
            return Ok(false);
        }
        let mut blocks = HomotopyBlockBuilder::with_inherited(parent.block_cache(), meter);
        let (replaced, direction) = (approximation.replaced, approximation.direction);
        match approximation_map_with_blocks(parent, replaced, direction, &mut blocks) {
            Ok((map, indices)) => {
                Ok(indices == approximation.indices && map.agrees_with(&approximation.map))
            }
            Err(Interrupt::Cancelled) => Err(Cancelled),
            Err(Interrupt::Error(_)) => Ok(false),
        }
    }
}

/// Limits for exact tilting-complex checks.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TiltingComplexLimits {
    /// The maximum number of homotopy Hom quotients built.
    pub max_hom_spaces: u64,
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
    /// A summand endomorphism ring is not shown to be local with residue
    /// field `k`.
    EndomorphismLocality { summand: usize, dimension: usize },
    /// Two summands are isomorphic in the homotopy category.
    RepeatedSummand { first: usize, second: usize },
    /// No checked thick-generation witness was supplied.
    Generation,
    /// The Hom-space limit stopped the finite check.
    HomLimit { completed: usize, limit: u64 },
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

/// A structural error, or cancellation observed inside one metered check.
#[derive(Debug)]
pub(crate) enum Interrupt {
    Error(TiltingComplexError),
    Cancelled,
}

impl<E: Into<TiltingComplexError>> From<E> for Interrupt {
    fn from(error: E) -> Self {
        Interrupt::Error(error.into())
    }
}

impl From<Cancelled> for Interrupt {
    fn from(_: Cancelled) -> Self {
        Interrupt::Cancelled
    }
}

/// The structural error of a check run under a meter without a control.
fn unmetered<T>(result: Result<T, Interrupt>) -> Result<T, TiltingComplexError> {
    result.map_err(|interrupt| match interrupt {
        Interrupt::Error(error) => error,
        Interrupt::Cancelled => unreachable!("a meter without a control never cancels"),
    })
}

/// Checks basicness, self-orthogonality, and thick generation.
pub fn classify_tilting_complex(
    candidate: TiltingComplexCandidate,
    generation: Option<ThickGenerationWitness>,
    limits: TiltingComplexLimits,
) -> Result<TiltingComplexResult, TiltingComplexError> {
    let goal = OrthogonalityGoal::Tilting;
    unmetered(classified(classify_with_goal(
        candidate, generation, limits, goal,
    )))
}

/// The tilting result of a classification under [`OrthogonalityGoal::Tilting`],
/// which never keeps a negative class.
fn classified(
    result: Result<Box<CertifiedSiltingComplex>, ClassificationFailure>,
) -> Result<TiltingComplexResult, Interrupt> {
    match result {
        Ok(silting) => Ok(TiltingComplexResult::Tilting(Box::new(
            CertifiedTiltingComplex { silting: *silting },
        ))),
        Err(ClassificationFailure::Outcome(outcome)) => Ok(outcome),
        Err(ClassificationFailure::Interrupt(interrupt)) => Err(interrupt),
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

#[cfg(test)]
mod tests;

#[cfg(test)]
mod reduction_tests;

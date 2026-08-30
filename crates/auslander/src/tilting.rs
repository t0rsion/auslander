//! Classical tilting modules with finite projective and generation bounds.
//!
//! A successful value stores a complete minimal projective resolution, every
//! positive self-Ext space through its projective dimension, and an exact
//! complex `A -> T^0 -> ... -> T^n` with each displayed target in `add(T)`.
//! A bound cut stays undetermined. Only a positive self-extension rejects a
//! candidate.

use std::fmt;
use std::sync::Arc;

use crate::algebra::Algebra;
use crate::approx::{ApproxError, MinimalLeftApproximation, left_approximation};
use crate::basic::{AddClosureWitness, BasicDecomposition, BasicError};
use crate::complex::{CheckedComplex, ComplexError, ExactComplex, ExactnessOutcome};
use crate::ext::{ExtError, ExtSpace};
use crate::hom::{Morphism, cokernel, kernel};
use crate::module::{Module, same_morphism_data, same_representation, summand_sum};
use crate::resolution::{Bounded, ProjectiveResolution, ResolutionEnd, resolve};

/// Independent bounds for projective dimension and generation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TiltingLimits {
    /// Maximum number of projective-resolution differentials.
    pub max_projective_dimension: usize,
    /// Maximum number of minimal left approximation maps.
    pub max_generation_steps: usize,
}

/// Rejected input or a failed internal construction check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TiltingError {
    /// The basic layer rejected the candidate or an `add(T)` witness.
    Basic(BasicError),
    /// The approximation layer rejected the basic summands.
    Approx(ApproxError),
    /// The Ext layer rejected the self-Ext pair.
    Ext(ExtError),
    /// Generated terms or maps did not form a complex.
    Complex(ComplexError),
    /// A checked consequence of the construction failed.
    Defect { reason: String },
}

display_error! { TiltingError {
    Self::Basic(error) => "basic layer: {error}";
    Self::Approx(error) => "approximation layer: {error}";
    Self::Ext(error) => "ext layer: {error}";
    Self::Complex(error) => "complex layer: {error}";
    Self::Defect { reason } => "internal cross-check failed: {reason}";
} }

error_source! { TiltingError {
    Self::Basic(error) => Some(error),
    Self::Approx(error) => Some(error),
    Self::Ext(error) => Some(error),
    Self::Complex(error) => Some(error),
    Self::Defect { .. } => None,
} }

/// A positive self-extension after finite projective dimension was proved.
pub struct PositiveSelfExtension {
    module: Module,
    projective_dimension: usize,
    resolution: ProjectiveResolution,
    zero_before: Vec<ExtSpace>,
    space: ExtSpace,
}

debug_fields!(PositiveSelfExtension |this| {
    "dim_vector" => this.module.dim_vector();
    "projective_dimension" => this.projective_dimension;
    "degree" => this.space.degree();
    "dimension" => this.space.dim();
});

impl PositiveSelfExtension {
    accessor_methods! {
        /// The rejected module.
        pub module() -> &Module = |this| &this.module;
        /// The first positive degree with nonzero self-Ext.
        pub degree() -> usize = |this| this.space.degree();
        /// The positive Ext dimension.
        pub dimension() -> usize = |this| this.space.dim();
        /// The positive Ext space.
        pub space() -> &ExtSpace = |this| &this.space;
        /// The proved finite projective dimension.
        pub projective_dimension() -> usize = |this| this.projective_dimension;
        /// The complete resolution that proves finite projective dimension.
        pub resolution() -> &ProjectiveResolution = |this| &this.resolution;
    }

    /// Recomputes the finite resolution and every Ext space through the witness.
    pub fn verify(&self) -> bool {
        verify_guard!(
            finite_resolution_valid(&self.module, &self.resolution, self.projective_dimension)
                && self.space.degree() != 0
                && self.space.degree() <= self.projective_dimension
                && self.space.dim() != 0
                && self.zero_before.len() + 1 == self.space.degree()
        );
        let fresh_resolution = resolve(&self.module, self.projective_dimension);
        verify_guard!(self.resolution.agrees_with(&fresh_resolution));
        self.zero_before
            .iter()
            .enumerate()
            .all(|(i, space)| valid_self_ext(space, &self.module, i + 1, false))
            && valid_self_ext(&self.space, &self.module, self.space.degree(), true)
    }
}

/// A genuine lower bound from a cut minimal projective resolution.
pub struct ProjectiveDimensionBlocker {
    module: Module,
    bound: usize,
    lower_bound: usize,
    resolution: ProjectiveResolution,
}

debug_fields!(ProjectiveDimensionBlocker |this| {
    "dim_vector" => this.module.dim_vector();
    "bound" => this.bound;
    "lower_bound" => this.lower_bound;
});

impl ProjectiveDimensionBlocker {
    accessor_methods! {
        /// The module whose resolution was cut.
        pub module() -> &Module = |this| &this.module;
        /// The requested projective-dimension bound.
        pub bound() -> usize = |this| this.bound;
        /// The proved lower bound on projective dimension.
        pub lower_bound() -> usize = |this| this.lower_bound;
        /// The typed partial projective dimension.
        pub projective_dimension() -> Bounded<usize> = |this| Bounded::AtLeast(this.lower_bound);
        /// The cut resolution prefix.
        pub resolution() -> &ProjectiveResolution = |this| &this.resolution;
    }

    /// Recomputes the same cut resolution prefix.
    pub fn verify(&self) -> bool {
        let_or_false!(ResolutionEnd::Cut { at } = self.resolution.end);
        verify_guard!(
            at == self.bound
                && at.checked_add(1) == Some(self.lower_bound)
                && self.resolution.augmentation.target().ptr_eq(&self.module)
        );
        self.resolution
            .agrees_with(&resolve(&self.module, self.bound))
    }
}

/// A bounded generation construction stopped before an exact complex.
pub enum GenerationBlocker {
    /// The next minimal left approximation was not monic.
    NonMonic {
        module: Module,
        max_steps: usize,
        stage: usize,
        partial: CheckedComplex,
        approximation: Box<MinimalLeftApproximation>,
        kernel_dimension_vector: Vec<usize>,
    },
    /// The step bound was reached with a nonzero cokernel.
    StepLimit {
        module: Module,
        max_steps: usize,
        stage: usize,
        partial: CheckedComplex,
        cokernel: Module,
        cokernel_dimension_vector: Vec<usize>,
    },
}

impl fmt::Debug for GenerationBlocker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (name, dimension_name, dimensions) = match self {
            Self::NonMonic {
                kernel_dimension_vector,
                ..
            } => (
                "NonMonic",
                "kernel_dimension_vector",
                kernel_dimension_vector,
            ),
            Self::StepLimit {
                cokernel_dimension_vector,
                ..
            } => (
                "StepLimit",
                "cokernel_dimension_vector",
                cokernel_dimension_vector,
            ),
        };
        f.debug_struct(name)
            .field("stage", &self.stage())
            .field(dimension_name, dimensions)
            .finish()
    }
}

impl GenerationBlocker {
    accessor_methods! {
        /// The candidate module.
        pub module() -> &Module = |this| match this {
            Self::NonMonic { module, .. } | Self::StepLimit { module, .. } => module,
        };
        /// The generation-step bound.
        pub max_steps() -> usize = |this| match this {
            Self::NonMonic { max_steps, .. } | Self::StepLimit { max_steps, .. } => *max_steps,
        };
        /// The first blocked approximation stage.
        pub stage() -> usize = |this| match this {
            Self::NonMonic { stage, .. } | Self::StepLimit { stage, .. } => *stage,
        };
        /// The checked maps built before the blocked stage.
        pub partial_complex() -> &CheckedComplex = |this| match this {
            Self::NonMonic { partial, .. } | Self::StepLimit { partial, .. } => partial,
        };
    }

    optional_accessors! {
        /// The failed approximation, only for a non-monic blocker.
        pub approximation() -> &MinimalLeftApproximation = Self::NonMonic { approximation, .. } => approximation;
        /// The nonzero kernel dimensions, only for a non-monic blocker.
        pub kernel_dimension_vector() -> &[usize] = Self::NonMonic { kernel_dimension_vector, .. } => kernel_dimension_vector;
        /// The last nonzero cokernel, only for a step-limit blocker.
        pub cokernel() -> &Module = Self::StepLimit { cokernel, .. } => cokernel;
        /// The last nonzero cokernel dimensions, only for a step-limit blocker.
        pub cokernel_dimension_vector() -> &[usize] = Self::StepLimit { cokernel_dimension_vector, .. } => cokernel_dimension_vector;
    }

    /// Rebuilds the same minimal approximations through the blocked stage.
    pub fn verify(&self) -> bool {
        let_or_false!(Ok(basic) = BasicDecomposition::new(self.module()));
        matches!(
            build_generation(self.module(), &basic, self.max_steps()),
            Ok(GenerationBuild::Blocked(ref fresh)) if same_generation_blocker(self, fresh)
        )
    }
}

/// Why a classification remains undetermined.
#[derive(Debug)]
pub enum TiltingBlocker {
    /// The projective resolution reached its bound with a nonzero syzygy.
    ProjectiveDimension(ProjectiveDimensionBlocker),
    /// The bounded minimal-approximation construction did not finish.
    Generation(GenerationBlocker),
}

impl TiltingBlocker {
    optional_accessors! {
        /// The projective-dimension blocker, when that bound stopped classification.
        pub projective_dimension() -> &ProjectiveDimensionBlocker = Self::ProjectiveDimension(blocker) => blocker;
        /// The generation blocker, when bounded approximation stopped classification.
        pub generation() -> &GenerationBlocker = Self::Generation(blocker) => blocker;
    }
    accessor_methods! {
        /// Recomputes the stored cut or generation obstruction.
        pub verify() -> bool = |this| match this {
            Self::ProjectiveDimension(blocker) => blocker.verify(),
            Self::Generation(blocker) => blocker.verify(),
        };
    }
}

/// The three outcomes of classical tilting classification.
#[derive(Debug)]
pub enum ClassicalTiltingResult {
    /// Every classical tilting condition was certified.
    Tilting(ClassicalTiltingModule),
    /// A positive self-extension proves that the candidate is not tilting.
    NotTilting(PositiveSelfExtension),
    /// A caller bound or non-monic bounded construction leaves the question open.
    Undetermined(TiltingBlocker),
}

impl ClassicalTiltingResult {
    optional_accessors! {
        /// The accepted certificate, if classification finished positively.
        pub tilting() -> &ClassicalTiltingModule = Self::Tilting(value) => value;
        /// The positive self-extension, if classification rejected the candidate.
        pub rejection() -> &PositiveSelfExtension = Self::NotTilting(value) => value;
        /// The cut or generation blocker, if classification is undetermined.
        pub blocker() -> &TiltingBlocker = Self::Undetermined(value) => value;
    }
}

struct GenerationSuccess {
    exact: ExactComplex,
    add_witnesses: Vec<AddClosureWitness>,
}

enum GenerationBuild {
    Complete(GenerationSuccess),
    Blocked(GenerationBlocker),
}

/// A basic module certified against all three classical tilting conditions.
#[derive(Clone)]
pub struct ClassicalTiltingModule {
    module: Module,
    limits: TiltingLimits,
    projective_dimension: usize,
    resolution: ProjectiveResolution,
    ext_spaces: Vec<ExtSpace>,
    generation: ExactComplex,
    add_witnesses: Vec<AddClosureWitness>,
}

debug_fields!(ClassicalTiltingModule |this| {
    "dim_vector" => this.module.dim_vector();
    "projective_dimension" => this.projective_dimension;
    "generation_terms" => this.generation.complex().len();
});

impl ClassicalTiltingModule {
    /// Classifies a basic candidate under two independent bounds.
    pub fn classify(
        module: &Module,
        limits: TiltingLimits,
    ) -> Result<ClassicalTiltingResult, TiltingError> {
        classify(module, limits)
    }

    accessor_methods! {
        /// The certified module.
        pub module() -> &Module = |this| &this.module;
        /// The limits used by the successful classification.
        pub limits() -> TiltingLimits = |this| this.limits;
        /// The exact projective dimension.
        pub projective_dimension() -> usize = |this| this.projective_dimension;
        /// The complete minimal projective resolution.
        pub resolution() -> &ProjectiveResolution = |this| &this.resolution;
        /// The zero self-Ext spaces in degrees `1..=pd T`.
        pub ext_spaces() -> &[ExtSpace] = |this| &this.ext_spaces;
        /// The exact generation complex `A -> T^0 -> ... -> T^n`.
        pub generation_complex() -> &ExactComplex = |this| &this.generation;
        /// One `add(T)` witness for each generation term after `A`.
        pub add_witnesses() -> &[AddClosureWitness] = |this| &this.add_witnesses;
    }

    /// Recomputes the finite resolution, all Ext spaces, and generation route.
    pub fn verify(&self) -> bool {
        let_or_false!(Ok(basic) = BasicDecomposition::new(&self.module));
        verify_guard!(
            finite_resolution_valid(&self.module, &self.resolution, self.projective_dimension)
                && self.projective_dimension <= self.limits.max_projective_dimension
        );
        let fresh_resolution = resolve(&self.module, self.limits.max_projective_dimension);
        verify_guard!(
            self.resolution.agrees_with(&fresh_resolution)
                && self.ext_spaces.len() == self.projective_dimension
                && self
                    .ext_spaces
                    .iter()
                    .enumerate()
                    .all(|(i, space)| valid_self_ext(space, &self.module, i + 1, false))
                && self.generation.verify()
                && self.add_witnesses.len() + 1 == self.generation.complex().len()
                && self
                    .add_witnesses
                    .iter()
                    .zip(&self.generation.complex().terms()[1..])
                    .all(|(witness, term)| {
                        witness.verify()
                            && witness.module().ptr_eq(term)
                            && witness.target().ptr_eq(&self.module)
                    })
        );
        let_or_false!(
            Ok(GenerationBuild::Complete(fresh)) =
                build_generation(&self.module, &basic, self.limits.max_generation_steps)
        );
        self.generation.verify_reconstruction(fresh.exact.complex())
            && fresh.add_witnesses.iter().all(AddClosureWitness::verify)
    }
}

/// Classifies a basic module under finite projective and generation bounds.
pub fn classify(
    module: &Module,
    limits: TiltingLimits,
) -> Result<ClassicalTiltingResult, TiltingError> {
    let basic = BasicDecomposition::new(module).map_err(TiltingError::Basic)?;
    let resolution = resolve(module, limits.max_projective_dimension);
    if let ResolutionEnd::Cut { at } = resolution.end {
        let lower_bound = at.checked_add(1).ok_or_else(|| TiltingError::Defect {
            reason: "the projective-dimension lower bound overflowed usize".to_string(),
        })?;
        return Ok(ClassicalTiltingResult::Undetermined(
            TiltingBlocker::ProjectiveDimension(ProjectiveDimensionBlocker {
                module: module.clone(),
                bound: limits.max_projective_dimension,
                lower_bound,
                resolution,
            }),
        ));
    }
    let projective_dimension = resolution.terms.len() - 1;
    let mut ext_spaces = Vec::with_capacity(projective_dimension);
    for degree in 1..=projective_dimension {
        let space = ExtSpace::new(module, module, degree).map_err(TiltingError::Ext)?;
        if space.dim() != 0 {
            return Ok(ClassicalTiltingResult::NotTilting(PositiveSelfExtension {
                module: module.clone(),
                projective_dimension,
                resolution,
                zero_before: ext_spaces,
                space,
            }));
        }
        ext_spaces.push(space);
    }
    match build_generation(module, &basic, limits.max_generation_steps)? {
        GenerationBuild::Blocked(blocker) => Ok(ClassicalTiltingResult::Undetermined(
            TiltingBlocker::Generation(blocker),
        )),
        GenerationBuild::Complete(success) => {
            Ok(ClassicalTiltingResult::Tilting(ClassicalTiltingModule {
                module: module.clone(),
                limits,
                projective_dimension,
                resolution,
                ext_spaces,
                generation: success.exact,
                add_witnesses: success.add_witnesses,
            }))
        }
    }
}

fn regular_module(algebra: &Arc<Algebra>) -> Module {
    let vertices: Vec<u32> = (0..algebra.quiver().num_vertices()).collect();
    summand_sum(algebra, &vertices, Module::projective)
}

fn partial_complex(terms: &[Module], maps: &[Morphism]) -> Result<CheckedComplex, TiltingError> {
    CheckedComplex::new(terms.to_vec(), maps.to_vec()).map_err(TiltingError::Complex)
}

fn valid_self_ext(space: &ExtSpace, module: &Module, degree: usize, positive: bool) -> bool {
    space.degree() == degree
        && (space.dim() != 0) == positive
        && space.source().ptr_eq(module)
        && space.target().ptr_eq(module)
        && space.matches_recomputation()
}

fn finite_resolution_valid(
    module: &Module,
    resolution: &ProjectiveResolution,
    projective_dimension: usize,
) -> bool {
    resolution.end == ResolutionEnd::Finite
        && resolution.terms.len() == projective_dimension + 1
        && resolution.augmentation.target().ptr_eq(module)
}

fn build_generation(
    module: &Module,
    basic: &BasicDecomposition,
    max_steps: usize,
) -> Result<GenerationBuild, TiltingError> {
    let summands: Vec<Module> = basic
        .summands()
        .iter()
        .map(|summand| summand.module().clone())
        .collect();
    let mut current = regular_module(module.algebra());
    let mut terms = vec![current.clone()];
    let mut maps = Vec::new();
    let mut previous_projection: Option<Morphism> = None;
    let mut add_witnesses = Vec::new();
    let mut stage = 0usize;
    loop {
        if stage == max_steps {
            let partial = partial_complex(&terms, &maps)?;
            return Ok(GenerationBuild::Blocked(GenerationBlocker::StepLimit {
                module: module.clone(),
                max_steps,
                stage,
                partial,
                cokernel_dimension_vector: current.dim_vector().to_vec(),
                cokernel: current,
            }));
        }
        let approximation =
            left_approximation(&current, &summands).map_err(TiltingError::Approx)?;
        let (approximation_kernel, _) = kernel(approximation.map());
        if !approximation_kernel.is_zero() {
            let partial = partial_complex(&terms, &maps)?;
            return Ok(GenerationBuild::Blocked(GenerationBlocker::NonMonic {
                module: module.clone(),
                max_steps,
                stage,
                partial,
                kernel_dimension_vector: approximation_kernel.dim_vector().to_vec(),
                approximation: Box::new(approximation),
            }));
        }
        let target = approximation.map().target().clone();
        let Some(add_witness) =
            AddClosureWitness::from_module(&target, basic).map_err(TiltingError::Basic)?
        else {
            return Err(TiltingError::Defect {
                reason: "a minimal left add(T)-approximation target lay outside add(T)".to_string(),
            });
        };
        let displayed = match previous_projection.take() {
            Some(projection) => {
                projection
                    .then(approximation.map())
                    .map_err(|error| TiltingError::Defect {
                        reason: format!("successive generation maps did not compose: {error}"),
                    })?
            }
            None => approximation.map().clone(),
        };
        let (next, projection) = cokernel(approximation.map());
        terms.push(target);
        maps.push(displayed);
        add_witnesses.push(add_witness);
        if next.is_zero() {
            let checked = partial_complex(&terms, &maps)?;
            return match checked.exactness() {
                ExactnessOutcome::Exact(exact) => {
                    Ok(GenerationBuild::Complete(GenerationSuccess {
                        exact,
                        add_witnesses,
                    }))
                }
                ExactnessOutcome::NotExact(witness) => Err(TiltingError::Defect {
                    reason: format!(
                        "the monic cokernel construction has homology at term {}",
                        witness.homology().index()
                    ),
                }),
            };
        }
        current = next;
        previous_projection = Some(projection);
        stage = stage.checked_add(1).ok_or_else(|| TiltingError::Defect {
            reason: "the generation stage overflowed usize".to_string(),
        })?;
    }
}

fn same_generation_blocker(x: &GenerationBlocker, y: &GenerationBlocker) -> bool {
    verify_guard!(
        x.max_steps() == y.max_steps()
            && x.stage() == y.stage()
            && x.partial_complex().agrees_with(y.partial_complex())
    );
    match (
        x.approximation(),
        y.approximation(),
        x.cokernel(),
        y.cokernel(),
    ) {
        (Some(xa), Some(ya), None, None) => {
            x.kernel_dimension_vector() == y.kernel_dimension_vector()
                && xa.verify()
                && ya.verify()
                && xa.slots() == ya.slots()
                && same_morphism_data(xa.map(), ya.map())
        }
        (None, None, Some(xc), Some(yc)) => {
            x.cokernel_dimension_vector() == y.cokernel_dimension_vector()
                && same_representation(xc, yc)
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{an_with_relations, dual_numbers, kronecker, linear_an};
    use crate::field::PrimeField;
    use crate::linalg::DenseMat;
    use crate::module::direct_sum;

    fn fields() -> [PrimeField; 2] {
        [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()]
    }

    fn generous() -> TiltingLimits {
        TiltingLimits {
            max_projective_dimension: 4,
            max_generation_steps: 5,
        }
    }

    fn sum(parts: &[Module]) -> Module {
        direct_sum(&parts.iter().collect::<Vec<_>>()).0
    }

    #[test]
    fn regular_module_is_zero_tilting_over_f2_and_f5() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let regular = regular_module(&algebra);
            let ClassicalTiltingResult::Tilting(tilting) = classify(&regular, generous()).unwrap()
            else {
                panic!("the regular module is tilting")
            };
            assert_eq!(tilting.projective_dimension(), 0);
            assert!(tilting.ext_spaces().is_empty());
            assert_eq!(tilting.generation_complex().complex().len(), 2);
            assert!(
                tilting.generation_complex().complex().terms()[1].dim_vector()
                    == regular.dim_vector()
            );
            assert!(tilting.verify());
        }
    }

    #[test]
    fn dual_numbers_simple_keeps_an_honest_projective_cut() {
        for field in fields() {
            let algebra = dual_numbers(field);
            let simple = Module::simple(&algebra, 0);
            let limits = TiltingLimits {
                max_projective_dimension: 2,
                max_generation_steps: 3,
            };
            let ClassicalTiltingResult::Undetermined(TiltingBlocker::ProjectiveDimension(blocker)) =
                classify(&simple, limits).unwrap()
            else {
                panic!("the periodic resolution must cut")
            };
            assert_eq!(blocker.lower_bound(), 3);
            assert!(blocker.verify());
        }
    }

    #[test]
    fn self_extension_is_the_only_negative_outcome() {
        for field in fields() {
            let algebra = kronecker(2, field);
            let mut first = DenseMat::zero(1, 1);
            first.set(0, 0, field.one());
            let module =
                Module::new(algebra, vec![1, 1], vec![first, DenseMat::zero(1, 1)]).unwrap();
            let ClassicalTiltingResult::NotTilting(witness) =
                classify(&module, generous()).unwrap()
            else {
                panic!("the Kronecker module has a self-extension")
            };
            assert_eq!(witness.degree(), 1);
            assert_eq!(witness.dimension(), 1);
            assert!(witness.verify());
        }
    }

    #[test]
    fn generation_has_separate_step_and_non_monic_blockers() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let regular = regular_module(&algebra);
            let limits = TiltingLimits {
                max_projective_dimension: 0,
                max_generation_steps: 0,
            };
            let ClassicalTiltingResult::Undetermined(TiltingBlocker::Generation(
                step @ GenerationBlocker::StepLimit { .. },
            )) = classify(&regular, limits).unwrap()
            else {
                panic!("zero generation steps must cut")
            };
            assert_eq!(step.stage(), 0);
            assert!(step.verify());

            let simple = Module::simple(&algebra, 0);
            let ClassicalTiltingResult::Undetermined(TiltingBlocker::Generation(
                non_monic @ GenerationBlocker::NonMonic { .. },
            )) = classify(&simple, generous()).unwrap()
            else {
                panic!("the approximation of A by add(S_0) is not monic")
            };
            assert_eq!(non_monic.stage(), 0);
            assert!(non_monic.verify());
        }
    }

    #[test]
    fn dual_module_over_a3_mod_ab_is_pd2_tilting() {
        for field in fields() {
            let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
            let injectives: Vec<Module> = (0..3)
                .map(|vertex| Module::injective(&algebra, vertex))
                .collect();
            let dual = sum(&injectives);
            assert_eq!(dual.dim_vector(), [2, 2, 1]);
            let ClassicalTiltingResult::Tilting(tilting) = classify(&dual, generous()).unwrap()
            else {
                panic!("D(A) is the named projective-dimension-two tilting fixture")
            };
            assert_eq!(tilting.projective_dimension(), 2);
            let dimensions: Vec<&[usize]> = tilting
                .generation_complex()
                .complex()
                .terms()
                .iter()
                .map(Module::dim_vector)
                .collect();
            assert_eq!(
                dimensions,
                vec![&[1, 2, 2][..], &[1, 3, 2], &[1, 1, 0], &[1, 0, 0]]
            );
            assert!(tilting.verify());
        }
    }

    #[test]
    fn repeated_summand_is_a_basic_error() {
        let algebra = linear_an(2, PrimeField::new(5).unwrap());
        let projective = Module::projective(&algebra, 0);
        let doubled = sum(&[projective.clone(), projective]);
        assert_eq!(
            classify(&doubled, generous()).unwrap_err(),
            TiltingError::Basic(BasicError::NotBasic {
                first: 0,
                second: 1,
            })
        );
    }

    #[test]
    fn pd2_generation_step_bound_keeps_the_partial_complex() {
        let field = PrimeField::new(5).unwrap();
        let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
        let dual = sum(&(0..3)
            .map(|vertex| Module::injective(&algebra, vertex))
            .collect::<Vec<_>>());
        let limits = TiltingLimits {
            max_projective_dimension: 2,
            max_generation_steps: 2,
        };
        let ClassicalTiltingResult::Undetermined(TiltingBlocker::Generation(
            blocker @ GenerationBlocker::StepLimit { .. },
        )) = classify(&dual, limits).unwrap()
        else {
            panic!("two maps do not finish the three-map generation complex")
        };
        assert_eq!(blocker.stage(), 2);
        assert_eq!(blocker.partial_complex().len(), 3);
        assert!(blocker.verify());
    }
}

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

struct GenerationState {
    current: Module,
    terms: Vec<Module>,
    maps: Vec<Morphism>,
    previous_projection: Option<Morphism>,
    add_witnesses: Vec<AddClosureWitness>,
    stage: usize,
}

enum GenerationStep {
    Continue(GenerationState),
    Finished(GenerationBuild),
}

enum ApproximationStep {
    Ready(MinimalLeftApproximation),
    Blocked(GenerationBuild),
}

impl GenerationState {
    fn new(algebra: &Arc<Algebra>) -> GenerationState {
        let current = regular_module(algebra);
        GenerationState {
            terms: vec![current.clone()],
            current,
            maps: Vec::new(),
            previous_projection: None,
            add_witnesses: Vec::new(),
            stage: 0,
        }
    }

    fn step_limit(
        &self,
        module: &Module,
        max_steps: usize,
    ) -> Result<GenerationBuild, TiltingError> {
        let partial = partial_complex(&self.terms, &self.maps)?;
        Ok(GenerationBuild::Blocked(GenerationBlocker::StepLimit {
            module: module.clone(),
            max_steps,
            stage: self.stage,
            partial,
            cokernel_dimension_vector: self.current.dim_vector().to_vec(),
            cokernel: self.current.clone(),
        }))
    }

    fn monic_approximation(
        &self,
        module: &Module,
        summands: &[Module],
        max_steps: usize,
    ) -> Result<ApproximationStep, TiltingError> {
        let approximation =
            left_approximation(&self.current, summands).map_err(TiltingError::Approx)?;
        let (approximation_kernel, _) = kernel(approximation.map());
        if approximation_kernel.is_zero() {
            return Ok(ApproximationStep::Ready(approximation));
        }
        let partial = partial_complex(&self.terms, &self.maps)?;
        Ok(ApproximationStep::Blocked(GenerationBuild::Blocked(
            GenerationBlocker::NonMonic {
                module: module.clone(),
                max_steps,
                stage: self.stage,
                partial,
                kernel_dimension_vector: approximation_kernel.dim_vector().to_vec(),
                approximation: Box::new(approximation),
            },
        )))
    }

    fn closure_witness(
        target: &Module,
        basic: &BasicDecomposition,
    ) -> Result<AddClosureWitness, TiltingError> {
        match AddClosureWitness::from_module(target, basic).map_err(TiltingError::Basic)? {
            Some(witness) => Ok(witness),
            None => Err(TiltingError::Defect {
                reason: "a minimal left add(T)-approximation target lay outside add(T)".to_string(),
            }),
        }
    }

    fn finish(self) -> Result<GenerationBuild, TiltingError> {
        let checked = partial_complex(&self.terms, &self.maps)?;
        match checked.exactness() {
            ExactnessOutcome::Exact(exact) => Ok(GenerationBuild::Complete(GenerationSuccess {
                exact,
                add_witnesses: self.add_witnesses,
            })),
            ExactnessOutcome::NotExact(witness) => Err(TiltingError::Defect {
                reason: format!(
                    "the monic cokernel construction has homology at term {}",
                    witness.homology().index()
                ),
            }),
        }
    }

    fn continue_or_finish(
        mut self,
        next: Module,
        projection: Morphism,
    ) -> Result<GenerationStep, TiltingError> {
        if next.is_zero() {
            return Ok(GenerationStep::Finished(self.finish()?));
        }
        self.current = next;
        self.previous_projection = Some(projection);
        self.stage = self
            .stage
            .checked_add(1)
            .ok_or_else(|| TiltingError::Defect {
                reason: "the generation stage overflowed usize".to_string(),
            })?;
        Ok(GenerationStep::Continue(self))
    }

    fn advance_monic(
        mut self,
        approximation: MinimalLeftApproximation,
        basic: &BasicDecomposition,
    ) -> Result<GenerationStep, TiltingError> {
        let target = approximation.map().target().clone();
        let add_witness = Self::closure_witness(&target, basic)?;
        let displayed = match self.previous_projection.take() {
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
        self.terms.push(target);
        self.maps.push(displayed);
        self.add_witnesses.push(add_witness);
        self.continue_or_finish(next, projection)
    }

    fn advance(
        self,
        module: &Module,
        basic: &BasicDecomposition,
        summands: &[Module],
        max_steps: usize,
    ) -> Result<GenerationStep, TiltingError> {
        if self.stage == max_steps {
            return self
                .step_limit(module, max_steps)
                .map(GenerationStep::Finished);
        }
        match self.monic_approximation(module, summands, max_steps)? {
            ApproximationStep::Ready(approximation) => self.advance_monic(approximation, basic),
            ApproximationStep::Blocked(blocked) => Ok(GenerationStep::Finished(blocked)),
        }
    }
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
    let mut state = GenerationState::new(module.algebra());
    loop {
        match state.advance(module, basic, &summands, max_steps)? {
            GenerationStep::Continue(next) => state = next,
            GenerationStep::Finished(result) => return Ok(result),
        }
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
mod tests;

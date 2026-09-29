use super::*;

/// The result of one checked left or right mutation.
#[derive(Clone, Debug)]
pub enum TiltingMutationOutcome {
    /// The cone remains a certified tilting complex.
    Tilting(Box<CertifiedTiltingComplex>),
    /// The cone has a nonzero class in a negative shift. Only
    /// [`left_tilting_mutation`] and [`right_tilting_mutation`] return it.
    SiltingOnly(Box<TiltingSelfOrthogonalityRejection>),
    /// The cone is a certified silting complex with a nonzero class in a
    /// negative shift. Only [`silting_mutation`] returns it.
    Silting(Box<CertifiedSiltingComplex>),
    /// Basicness or a resource limit remains open.
    Undetermined(TiltingComplexBlocker),
}

pub(super) fn cone_replacement(
    map: &ChainMap,
    direction: ApproximationDirection,
) -> Result<BoundedComplex, BoundedComplexError> {
    let cone = map.mapping_cone()?;
    match direction {
        ApproximationDirection::Left => Ok(cone),
        ApproximationDirection::Right => cone.shift(-1),
    }
}

fn mutated_candidate(
    parent: &CertifiedSiltingComplex,
    approximation: &ComplexApproximationWitness,
) -> TiltingComplexCandidate {
    let mut summands = parent.candidate().summands().to_vec();
    summands[approximation.replaced] = approximation.reduction.minimal().clone();
    TiltingComplexCandidate::new(summands)
        .expect("mutation keeps nonzero summands over one algebra")
}

/// Computes one mutation and classifies the result under `goal`.
pub(crate) fn tilting_mutation(
    parent: &CertifiedSiltingComplex,
    replaced: usize,
    limits: TiltingComplexLimits,
    step: (ApproximationDirection, OrthogonalityGoal),
) -> Result<TiltingMutationOutcome, TiltingComplexError> {
    let mut meter = WorkMeter::default();
    unmetered(tilting_mutation_with_cache(
        parent, replaced, limits, step, true, &mut meter,
    ))
}

/// Computes one mutation and observes cancellation before each work unit.
///
/// A work unit is one homotopy Hom quotient build, one product of basis maps
/// reduced to quotient coordinates, or one elimination step of the cone
/// reduction. On [`Interrupt::Cancelled`] the caller discards the partial
/// mutation.
///
/// `goal` selects the classification of the result, as in
/// [`silting_mutation`].
pub(crate) fn metered_tilting_mutation(
    parent: &CertifiedSiltingComplex,
    replaced: usize,
    limits: TiltingComplexLimits,
    step: (ApproximationDirection, OrthogonalityGoal),
    meter: &mut WorkMeter,
) -> Result<TiltingMutationOutcome, Interrupt> {
    tilting_mutation_with_cache(parent, replaced, limits, step, true, meter)
}

pub(super) fn tilting_mutation_with_cache(
    parent: &CertifiedSiltingComplex,
    replaced: usize,
    limits: TiltingComplexLimits,
    (direction, goal): (ApproximationDirection, OrthogonalityGoal),
    reuse: bool,
    meter: &mut WorkMeter,
) -> Result<TiltingMutationOutcome, Interrupt> {
    if replaced >= parent.candidate().len() {
        return Ok(TiltingMutationOutcome::Undetermined(
            TiltingComplexBlocker::Generation,
        ));
    }
    let mut blocks = mutation_blocks(parent, reuse, meter);
    let (map, indices) = approximation_map_with_blocks(parent, replaced, direction, &mut blocks)?;
    let cone = ProjectiveComplex::new(cone_replacement(&map, direction)?)?;
    let Some(reduction) = MinimalReduction::new(&cone, blocks.meter)? else {
        return Ok(TiltingMutationOutcome::Undetermined(
            TiltingComplexBlocker::EndomorphismLocality {
                summand: replaced,
                dimension: 0,
            },
        ));
    };
    let approximation = ComplexApproximationWitness {
        direction,
        replaced,
        indices,
        map,
        reduction: Box::new(reduction),
    };
    let candidate = mutated_candidate(parent, &approximation);
    blocks.set_changed(replaced);
    let generation = ThickGenerationWitness::Mutation {
        parent: Arc::new(parent.clone()),
        approximation,
    };
    let classified =
        classify_tilting_complex_inner(candidate, Some(generation), limits, blocks, false, goal);
    mutation_outcome(classified)
}

fn mutation_blocks<'a>(
    parent: &'a CertifiedSiltingComplex,
    reuse: bool,
    meter: &'a mut WorkMeter,
) -> HomotopyBlockBuilder<'a> {
    if reuse {
        HomotopyBlockBuilder::with_inherited(parent.block_cache(), meter)
    } else {
        HomotopyBlockBuilder::cold(meter)
    }
}

/// The mutation outcome of one classification.
fn mutation_outcome(
    classified: Result<Box<CertifiedSiltingComplex>, ClassificationFailure>,
) -> Result<TiltingMutationOutcome, Interrupt> {
    match classified {
        Ok(certified) if certified.negative_class.is_some() => {
            Ok(TiltingMutationOutcome::Silting(certified))
        }
        Ok(certified) => Ok(TiltingMutationOutcome::Tilting(Box::new(
            CertifiedTiltingComplex {
                silting: *certified,
            },
        ))),
        Err(ClassificationFailure::Outcome(outcome)) => Ok(failed_outcome(outcome)),
        Err(ClassificationFailure::Interrupt(interrupt)) => Err(interrupt),
    }
}

/// The outcome of a classification that certified nothing.
///
/// A rejection lies in a negative shift. Irreducible mutation of a silting
/// complex is silting (Aihara and Iyama, Theorem 2.31), so a positive shift
/// is a library bug.
fn failed_outcome(outcome: TiltingComplexResult) -> TiltingMutationOutcome {
    match outcome {
        TiltingComplexResult::NotTilting(rejection) => {
            assert!(rejection.degree < 0, "a mutation lost silting; library bug");
            TiltingMutationOutcome::SiltingOnly(rejection)
        }
        TiltingComplexResult::Undetermined(blocker) => {
            TiltingMutationOutcome::Undetermined(blocker)
        }
        TiltingComplexResult::Tilting(_) => unreachable!("a failed classification is not tilting"),
    }
}

/// Computes the universal left mutation at one exceptional summand.
pub fn left_tilting_mutation(
    parent: &CertifiedTiltingComplex,
    replaced: usize,
    limits: TiltingComplexLimits,
) -> Result<TiltingMutationOutcome, TiltingComplexError> {
    let step = (ApproximationDirection::Left, OrthogonalityGoal::Tilting);
    tilting_mutation(parent, replaced, limits, step)
}

/// Computes the universal right mutation at one exceptional summand.
pub fn right_tilting_mutation(
    parent: &CertifiedTiltingComplex,
    replaced: usize,
    limits: TiltingComplexLimits,
) -> Result<TiltingMutationOutcome, TiltingComplexError> {
    let step = (ApproximationDirection::Right, OrthogonalityGoal::Tilting);
    tilting_mutation(parent, replaced, limits, step)
}

/// Computes the irreducible silting mutation at one summand of a silting
/// complex.
///
/// The approximation and cone are those of [`left_tilting_mutation`] and
/// [`right_tilting_mutation`]. The result is
/// [`TiltingMutationOutcome::Tilting`] when every nonzero shift vanishes and
/// [`TiltingMutationOutcome::Silting`] when a negative shift does not. It is
/// never `SiltingOnly`.
pub fn silting_mutation(
    parent: &CertifiedSiltingComplex,
    replaced: usize,
    direction: ApproximationDirection,
    limits: TiltingComplexLimits,
) -> Result<TiltingMutationOutcome, TiltingComplexError> {
    tilting_mutation(
        parent,
        replaced,
        limits,
        (direction, OrthogonalityGoal::Silting),
    )
}

use super::cache::HomotopyBlockBuilder;
use super::*;

fn hom_range(
    source: &BoundedComplex,
    target: &BoundedComplex,
) -> Result<DegreeRange, TiltingComplexError> {
    let lower = source
        .lower()
        .checked_sub(target.upper())
        .ok_or(TiltingComplexError::DegreeOverflow)?;
    let upper = source
        .upper()
        .checked_sub(target.lower())
        .ok_or(TiltingComplexError::DegreeOverflow)?;
    DegreeRange::new(lower, upper).map_err(|_| TiltingComplexError::DegreeOverflow)
}

pub(super) fn quotient(
    source: &ProjectiveComplex,
    target: &ProjectiveComplex,
    degree: i32,
) -> Result<HomotopyHomQuotient, TiltingComplexError> {
    HomotopyHom::new(source.complex(), target.complex(), degree)?
        .quotient()
        .map_err(Into::into)
}

pub(super) fn basis_representative(space: &HomotopyHomQuotient, index: usize) -> ChainMap {
    let field = space.source().terms()[0].field();
    let mut coordinates = vec![field.zero(); space.dim()];
    coordinates[index] = field.one();
    space.representative(&coordinates)
}

enum RepeatedSummandCheck {
    Distinct,
    Repeated { first: usize, second: usize },
    Cut,
}

fn pair_is_repeated(
    end: &HomotopyHomQuotient,
    forward: &HomotopyHomQuotient,
    backward: &HomotopyHomQuotient,
) -> Result<bool, TiltingComplexError> {
    for left in 0..forward.dim() {
        let found = (0..backward.dim()).try_fold(false, |found, right| {
            Ok::<_, TiltingComplexError>(
                found || basis_product_is_nonzero(end, forward, backward, left, right)?,
            )
        })?;
        if found {
            return Ok(true);
        }
    }
    Ok(false)
}

fn basis_product_is_nonzero(
    end: &HomotopyHomQuotient,
    forward: &HomotopyHomQuotient,
    backward: &HomotopyHomQuotient,
    left: usize,
    right: usize,
) -> Result<bool, TiltingComplexError> {
    let product =
        basis_representative(forward, left).then(&basis_representative(backward, right))?;
    Ok(end.reduce(&product)?.0.iter().any(|value| !value.is_zero()))
}

fn repeated_pair(
    candidate: &TiltingComplexCandidate,
    end: &HomotopyHomQuotient,
    first: usize,
    second: usize,
    blocks: &mut HomotopyBlockBuilder<'_>,
    limit: usize,
) -> Result<RepeatedSummandCheck, TiltingComplexError> {
    let keys = [(first, second, 0), (second, first, 0)];
    if blocks.blocks_needed(candidate, &keys) > limit.saturating_sub(blocks.budget_built) {
        return Ok(RepeatedSummandCheck::Cut);
    }
    let forward = blocks.get(candidate, first, second, 0)?;
    let backward = blocks.get(candidate, second, first, 0)?;
    if pair_is_repeated(end, &forward, &backward)? {
        return Ok(RepeatedSummandCheck::Repeated { first, second });
    }
    Ok(RepeatedSummandCheck::Distinct)
}

fn repeated_summand(
    candidate: &TiltingComplexCandidate,
    ends: &[HomotopyHomQuotient],
    blocks: &mut HomotopyBlockBuilder<'_>,
    limit: usize,
) -> Result<RepeatedSummandCheck, TiltingComplexError> {
    for (first, end) in ends.iter().enumerate().take(candidate.len()) {
        match repeated_for_first(candidate, end, first, blocks, limit)? {
            RepeatedSummandCheck::Distinct => {}
            outcome => return Ok(outcome),
        }
    }
    Ok(RepeatedSummandCheck::Distinct)
}

fn repeated_for_first(
    candidate: &TiltingComplexCandidate,
    end: &HomotopyHomQuotient,
    first: usize,
    blocks: &mut HomotopyBlockBuilder<'_>,
    limit: usize,
) -> Result<RepeatedSummandCheck, TiltingComplexError> {
    for second in first + 1..candidate.len() {
        match repeated_pair(candidate, end, first, second, blocks, limit)? {
            RepeatedSummandCheck::Distinct => {}
            outcome => return Ok(outcome),
        }
    }
    Ok(RepeatedSummandCheck::Distinct)
}

struct BasicnessData {
    ends: Vec<HomotopyHomQuotient>,
}

enum BasicnessCheck {
    Basic(BasicnessData),
    Blocked(TiltingComplexBlocker),
}

fn endomorphism_checks(
    candidate: &TiltingComplexCandidate,
    blocks: &mut HomotopyBlockBuilder<'_>,
    limit: usize,
) -> Result<BasicnessCheck, TiltingComplexError> {
    let mut ends = Vec::with_capacity(candidate.len());
    for (summand, _complex) in candidate.summands().iter().enumerate() {
        if !blocks.cached(candidate, summand, summand, 0) && blocks.budget_built == limit {
            return Ok(BasicnessCheck::Blocked(TiltingComplexBlocker::HomLimit {
                completed: blocks.budget_built,
                limit,
            }));
        }
        let end = blocks.get(candidate, summand, summand, 0)?;
        if end.dim() != 1 {
            return Ok(BasicnessCheck::Blocked(
                TiltingComplexBlocker::EndomorphismLocality {
                    summand,
                    dimension: end.dim(),
                },
            ));
        }
        ends.push(end);
    }
    Ok(BasicnessCheck::Basic(BasicnessData { ends }))
}

fn basicness_check(
    candidate: &TiltingComplexCandidate,
    blocks: &mut HomotopyBlockBuilder<'_>,
    limit: usize,
) -> Result<BasicnessCheck, TiltingComplexError> {
    use RepeatedSummandCheck::*;
    use TiltingComplexBlocker::*;
    match endomorphism_checks(candidate, blocks, limit)? {
        BasicnessCheck::Basic(data) => (|| -> Result<BasicnessCheck, TiltingComplexError> {
            let blocker = match repeated_summand(candidate, &data.ends, blocks, limit)? {
                Distinct => return Ok(BasicnessCheck::Basic(data)),
                Repeated { first, second } => RepeatedSummand { first, second },
                Cut => HomLimit {
                    completed: blocks.budget_built,
                    limit,
                },
            };
            Ok(BasicnessCheck::Blocked(blocker))
        })(),
        BasicnessCheck::Blocked(blocker) => Ok(BasicnessCheck::Blocked(blocker)),
    }
}

enum ShiftedHomCheck {
    Zero(Box<TiltingHomCheck>),
    Nonzero(Box<TiltingSelfOrthogonalityRejection>),
    Cut,
}

fn shifted_hom_check(
    candidate: &TiltingComplexCandidate,
    source: usize,
    target: usize,
    degree: i32,
    blocks: &mut HomotopyBlockBuilder<'_>,
    limit: usize,
) -> Result<ShiftedHomCheck, TiltingComplexError> {
    if !blocks.cached(candidate, source, target, degree) && blocks.budget_built == limit {
        return Ok(ShiftedHomCheck::Cut);
    }
    let space = blocks.get(candidate, source, target, degree)?;
    if space.dim() != 0 {
        return Ok(ShiftedHomCheck::Nonzero(Box::new(
            TiltingSelfOrthogonalityRejection {
                source,
                target,
                degree,
                representative: basis_representative(&space, 0),
                quotient: space,
            },
        )));
    }
    Ok(ShiftedHomCheck::Zero(Box::new(TiltingHomCheck {
        source,
        target,
        degree,
        quotient: space,
    })))
}

enum OrthogonalityCheck {
    Orthogonal(Vec<TiltingHomCheck>),
    Nonzero(Box<TiltingSelfOrthogonalityRejection>),
    Cut { completed: usize, limit: usize },
}

fn append_shifted_check(
    candidate: &TiltingComplexCandidate,
    source: usize,
    target: usize,
    degree: i32,
    blocks: &mut HomotopyBlockBuilder<'_>,
    limit: usize,
    checks: &mut Vec<TiltingHomCheck>,
) -> Result<Option<OrthogonalityCheck>, TiltingComplexError> {
    match shifted_hom_check(candidate, source, target, degree, blocks, limit)? {
        ShiftedHomCheck::Zero(check) => {
            checks.push(*check);
            Ok(None)
        }
        ShiftedHomCheck::Nonzero(rejection) => Ok(Some(OrthogonalityCheck::Nonzero(rejection))),
        ShiftedHomCheck::Cut => Ok(Some(OrthogonalityCheck::Cut {
            completed: blocks.budget_built,
            limit,
        })),
    }
}

fn shifted_range_check(
    candidate: &TiltingComplexCandidate,
    source: usize,
    target: usize,
    blocks: &mut HomotopyBlockBuilder<'_>,
    limit: usize,
    checks: &mut Vec<TiltingHomCheck>,
) -> Result<Option<OrthogonalityCheck>, TiltingComplexError> {
    let range = hom_range(
        candidate.summands()[source].complex(),
        candidate.summands()[target].complex(),
    )?;
    for degree in (range.lower()..=range.upper()).filter(|degree| *degree != 0) {
        if let Some(outcome) =
            append_shifted_check(candidate, source, target, degree, blocks, limit, checks)?
        {
            return Ok(Some(outcome));
        }
    }
    Ok(None)
}

fn orthogonality_check(
    candidate: &TiltingComplexCandidate,
    blocks: &mut HomotopyBlockBuilder<'_>,
    limit: usize,
) -> Result<OrthogonalityCheck, TiltingComplexError> {
    let mut checks = Vec::new();
    for source in 0..candidate.len() {
        for target in 0..candidate.len() {
            if let Some(outcome) =
                shifted_range_check(candidate, source, target, blocks, limit, &mut checks)?
            {
                return Ok(outcome);
            }
        }
    }
    Ok(OrthogonalityCheck::Orthogonal(checks))
}

pub(super) enum ClassificationFailure {
    Outcome(TiltingComplexResult),
    Error(TiltingComplexError),
}

impl From<TiltingComplexError> for ClassificationFailure {
    fn from(error: TiltingComplexError) -> Self {
        Self::Error(error)
    }
}

fn completed_orthogonality(
    candidate: &TiltingComplexCandidate,
    blocks: &mut HomotopyBlockBuilder<'_>,
    limit: usize,
) -> Result<Vec<TiltingHomCheck>, ClassificationFailure> {
    let outcome = match orthogonality_check(candidate, blocks, limit)? {
        OrthogonalityCheck::Orthogonal(checks) => return Ok(checks),
        OrthogonalityCheck::Nonzero(rejection) => TiltingComplexResult::NotTilting(rejection),
        OrthogonalityCheck::Cut { completed, limit } => {
            TiltingComplexResult::Undetermined(TiltingComplexBlocker::HomLimit { completed, limit })
        }
    };
    Err(ClassificationFailure::Outcome(outcome))
}

pub(super) fn classify_tilting_complex_inner(
    candidate: TiltingComplexCandidate,
    generation: Option<ThickGenerationWitness>,
    limits: TiltingComplexLimits,
    mut blocks: HomotopyBlockBuilder<'_>,
    cold_generation_check: bool,
) -> Result<TiltingComplexResult, ClassificationFailure> {
    blocks.begin_classification();
    let basicness = (|| -> Result<BasicnessData, ClassificationFailure> {
        match basicness_check(&candidate, &mut blocks, limits.max_hom_spaces)? {
            BasicnessCheck::Basic(data) => Ok(data),
            BasicnessCheck::Blocked(blocker) => Err(ClassificationFailure::Outcome(
                TiltingComplexResult::Undetermined(blocker),
            )),
        }
    })()?;
    let zero_shifted_homs =
        completed_orthogonality(&candidate, &mut blocks, limits.max_hom_spaces)?;
    let generation_valid = generation.as_ref().is_some_and(|witness| {
        if cold_generation_check {
            witness.verify(&candidate)
        } else {
            witness.verify_with_cached_blocks(&candidate)
        }
    });
    if !generation_valid {
        return Ok(TiltingComplexResult::Undetermined(
            TiltingComplexBlocker::Generation,
        ));
    }
    let (block_cache, work) = blocks.finish(&candidate);
    Ok(TiltingComplexResult::Tilting(Box::new(
        CertifiedTiltingComplex {
            candidate,
            generation: generation.expect("generation was checked"),
            degree_zero_endomorphisms: basicness.ends,
            zero_shifted_homs,
            limits,
            block_cache,
            work,
        },
    )))
}

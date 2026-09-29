use super::cache::HomotopyBlockBuilder;
use super::locality::{local_residue, residue_of};
use super::*;
use crate::homotopy::{HomSpaceMemo, same_complex_data};

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
    homs: &mut HomSpaceMemo,
) -> Result<HomotopyHomQuotient, TiltingComplexError> {
    HomotopyHom::new_in(source.complex(), target.complex(), degree, homs)?
        .into_quotient(homs)
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

/// Two summands with local endomorphism rings are isomorphic exactly when
/// some composite `T_i → T_j → T_i` is a unit, that is, lies outside the
/// radical. The radical is a subspace, so basis composites suffice.
pub(super) fn pair_is_repeated(
    end: &HomotopyHomQuotient,
    residue: &[Fp],
    forward: &HomotopyHomQuotient,
    backward: &HomotopyHomQuotient,
    meter: &mut WorkMeter,
) -> Result<bool, Interrupt> {
    for left in 0..forward.dim() {
        for right in 0..backward.dim() {
            meter.charge()?;
            if basis_product_is_unit(end, residue, forward, backward, left, right)? {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

/// Whether summand `left_index` of `left` and summand `right_index` of
/// `right` are isomorphic in `K^b(proj A)`.
///
/// Equal complex data proves it directly. Otherwise both summands are
/// indecomposable with local endomorphism rings, and the test is
/// [`pair_is_repeated`] against the left endomorphism ring.
pub(crate) fn summands_isomorphic(
    left: &CertifiedSiltingComplex,
    left_index: usize,
    right: &CertifiedSiltingComplex,
    right_index: usize,
    meter: &mut WorkMeter,
) -> Result<bool, Interrupt> {
    let source = &left.candidate.summands[left_index];
    let target = &right.candidate.summands[right_index];
    if same_complex_data(source.complex(), target.complex()) {
        return Ok(true);
    }
    let homs = &mut HomSpaceMemo::default();
    meter.charge()?;
    let forward = quotient(source, target, 0, homs)?;
    meter.charge()?;
    let backward = quotient(target, source, 0, homs)?;
    pair_is_repeated(
        &left.degree_zero_endomorphisms[left_index],
        &left.degree_zero_residues[left_index],
        &forward,
        &backward,
        meter,
    )
}

fn basis_product_is_unit(
    end: &HomotopyHomQuotient,
    residue: &[Fp],
    forward: &HomotopyHomQuotient,
    backward: &HomotopyHomQuotient,
    left: usize,
    right: usize,
) -> Result<bool, TiltingComplexError> {
    let product =
        basis_representative(forward, left).then(&basis_representative(backward, right))?;
    let field = end.source().terms()[0].field();
    Ok(!residue_of(field, residue, &end.reduce(&product)?.0).is_zero())
}

fn repeated_pair(
    candidate: &TiltingComplexCandidate,
    end: &HomotopyHomQuotient,
    residue: &[Fp],
    first: usize,
    second: usize,
    blocks: &mut HomotopyBlockBuilder<'_>,
    limit: u64,
) -> Result<RepeatedSummandCheck, Interrupt> {
    let keys = [(first, second, 0), (second, first, 0)];
    if blocks.blocks_needed(candidate, &keys) as u64
        > limit.saturating_sub(blocks.budget_built as u64)
    {
        return Ok(RepeatedSummandCheck::Cut);
    }
    let forward = blocks.get(candidate, first, second, 0)?;
    let backward = blocks.get(candidate, second, first, 0)?;
    if pair_is_repeated(end, residue, &forward, &backward, blocks.meter)? {
        return Ok(RepeatedSummandCheck::Repeated { first, second });
    }
    Ok(RepeatedSummandCheck::Distinct)
}

fn repeated_summand(
    candidate: &TiltingComplexCandidate,
    data: &BasicnessData,
    blocks: &mut HomotopyBlockBuilder<'_>,
    limit: u64,
) -> Result<RepeatedSummandCheck, Interrupt> {
    let summands = data.ends.iter().zip(&data.residues).enumerate();
    for (first, (end, residue)) in summands.take(candidate.len()) {
        match repeated_for_first(candidate, end, residue, first, blocks, limit)? {
            RepeatedSummandCheck::Distinct => {}
            outcome => return Ok(outcome),
        }
    }
    Ok(RepeatedSummandCheck::Distinct)
}

fn repeated_for_first(
    candidate: &TiltingComplexCandidate,
    end: &HomotopyHomQuotient,
    residue: &[Fp],
    first: usize,
    blocks: &mut HomotopyBlockBuilder<'_>,
    limit: u64,
) -> Result<RepeatedSummandCheck, Interrupt> {
    for second in first + 1..candidate.len() {
        match repeated_pair(candidate, end, residue, first, second, blocks, limit)? {
            RepeatedSummandCheck::Distinct => {}
            outcome => return Ok(outcome),
        }
    }
    Ok(RepeatedSummandCheck::Distinct)
}

struct BasicnessData {
    ends: Vec<HomotopyHomQuotient>,
    residues: Vec<Vec<Fp>>,
}

enum BasicnessCheck {
    Basic(BasicnessData),
    Blocked(TiltingComplexBlocker),
}

fn endomorphism_checks(
    candidate: &TiltingComplexCandidate,
    blocks: &mut HomotopyBlockBuilder<'_>,
    limit: u64,
) -> Result<BasicnessCheck, Interrupt> {
    let mut ends = Vec::with_capacity(candidate.len());
    let mut residues = Vec::with_capacity(candidate.len());
    for (summand, _complex) in candidate.summands().iter().enumerate() {
        if !blocks.cached(candidate, summand, summand, 0) && blocks.budget_built as u64 == limit {
            return Ok(BasicnessCheck::Blocked(TiltingComplexBlocker::HomLimit {
                completed: blocks.budget_built,
                limit,
            }));
        }
        let end = blocks.get(candidate, summand, summand, 0)?;
        let Some(residue) = local_residue(&end, blocks.meter)? else {
            return Ok(BasicnessCheck::Blocked(
                TiltingComplexBlocker::EndomorphismLocality {
                    summand,
                    dimension: end.dim(),
                },
            ));
        };
        ends.push(end);
        residues.push(residue);
    }
    Ok(BasicnessCheck::Basic(BasicnessData { ends, residues }))
}

fn basicness_check(
    candidate: &TiltingComplexCandidate,
    blocks: &mut HomotopyBlockBuilder<'_>,
    limit: u64,
) -> Result<BasicnessCheck, Interrupt> {
    use RepeatedSummandCheck::*;
    use TiltingComplexBlocker::*;
    match endomorphism_checks(candidate, blocks, limit)? {
        BasicnessCheck::Basic(data) => (|| -> Result<BasicnessCheck, Interrupt> {
            let blocker = match repeated_summand(candidate, &data, blocks, limit)? {
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
    limit: u64,
) -> Result<ShiftedHomCheck, Interrupt> {
    if !blocks.cached(candidate, source, target, degree) && blocks.budget_built as u64 == limit {
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

/// The zero checks and the kept negative class of one orthogonality scan.
struct Scan {
    goal: OrthogonalityGoal,
    checks: Vec<TiltingHomCheck>,
    negative: Option<Box<TiltingSelfOrthogonalityRejection>>,
}

impl Scan {
    /// Whether `degree` still needs a check. Under
    /// [`OrthogonalityGoal::Silting`], one negative class settles every
    /// negative shift.
    fn needs(&self, degree: i32) -> bool {
        degree != 0 && (degree > 0 || self.negative.is_none())
    }

    /// Keeps `rejection` when the goal allows it, else returns it.
    fn absorb(
        &mut self,
        rejection: Box<TiltingSelfOrthogonalityRejection>,
    ) -> Option<Box<TiltingSelfOrthogonalityRejection>> {
        if self.goal == OrthogonalityGoal::Silting && rejection.degree < 0 {
            self.negative = Some(rejection);
            return None;
        }
        Some(rejection)
    }
}

enum OrthogonalityCheck {
    Orthogonal(Scan),
    Nonzero(Box<TiltingSelfOrthogonalityRejection>),
    Cut { completed: usize, limit: u64 },
}

fn append_shifted_check(
    candidate: &TiltingComplexCandidate,
    (source, target, degree): (usize, usize, i32),
    blocks: &mut HomotopyBlockBuilder<'_>,
    limit: u64,
    scan: &mut Scan,
) -> Result<Option<OrthogonalityCheck>, Interrupt> {
    match shifted_hom_check(candidate, source, target, degree, blocks, limit)? {
        ShiftedHomCheck::Zero(check) => {
            scan.checks.push(*check);
            Ok(None)
        }
        ShiftedHomCheck::Nonzero(rejection) => {
            Ok(scan.absorb(rejection).map(OrthogonalityCheck::Nonzero))
        }
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
    limit: u64,
    scan: &mut Scan,
) -> Result<Option<OrthogonalityCheck>, Interrupt> {
    let range = hom_range(
        candidate.summands()[source].complex(),
        candidate.summands()[target].complex(),
    )?;
    for degree in range.lower()..=range.upper() {
        if !scan.needs(degree) {
            continue;
        }
        let key = (source, target, degree);
        if let Some(outcome) = append_shifted_check(candidate, key, blocks, limit, scan)? {
            return Ok(Some(outcome));
        }
    }
    Ok(None)
}

fn orthogonality_check(
    candidate: &TiltingComplexCandidate,
    blocks: &mut HomotopyBlockBuilder<'_>,
    limit: u64,
    goal: OrthogonalityGoal,
) -> Result<OrthogonalityCheck, Interrupt> {
    let mut scan = Scan {
        goal,
        checks: Vec::new(),
        negative: None,
    };
    for source in 0..candidate.len() {
        for target in 0..candidate.len() {
            if let Some(outcome) =
                shifted_range_check(candidate, source, target, blocks, limit, &mut scan)?
            {
                return Ok(outcome);
            }
        }
    }
    Ok(OrthogonalityCheck::Orthogonal(scan))
}

pub(super) enum ClassificationFailure {
    Outcome(TiltingComplexResult),
    Interrupt(Interrupt),
}

impl<E: Into<Interrupt>> From<E> for ClassificationFailure {
    fn from(interrupt: E) -> Self {
        Self::Interrupt(interrupt.into())
    }
}

fn completed_orthogonality(
    candidate: &TiltingComplexCandidate,
    blocks: &mut HomotopyBlockBuilder<'_>,
    limit: u64,
    goal: OrthogonalityGoal,
) -> Result<Scan, ClassificationFailure> {
    let outcome = match orthogonality_check(candidate, blocks, limit, goal)? {
        OrthogonalityCheck::Orthogonal(scan) => return Ok(scan),
        OrthogonalityCheck::Nonzero(rejection) => TiltingComplexResult::NotTilting(rejection),
        OrthogonalityCheck::Cut { completed, limit } => {
            TiltingComplexResult::Undetermined(TiltingComplexBlocker::HomLimit { completed, limit })
        }
    };
    Err(ClassificationFailure::Outcome(outcome))
}

/// Classifies `candidate` from a cold block cache.
pub(super) fn classify_with_goal(
    candidate: TiltingComplexCandidate,
    generation: Option<ThickGenerationWitness>,
    limits: TiltingComplexLimits,
    goal: OrthogonalityGoal,
) -> Result<Box<CertifiedSiltingComplex>, ClassificationFailure> {
    let mut meter = WorkMeter::default();
    let blocks = HomotopyBlockBuilder::cold(&mut meter);
    classify_tilting_complex_inner(candidate, generation, limits, blocks, true, goal)
}

/// Checks basicness, the shifted Hom spaces that `goal` requires to vanish,
/// and thick generation.
pub(super) fn classify_tilting_complex_inner(
    candidate: TiltingComplexCandidate,
    generation: Option<ThickGenerationWitness>,
    limits: TiltingComplexLimits,
    mut blocks: HomotopyBlockBuilder<'_>,
    cold_generation_check: bool,
    goal: OrthogonalityGoal,
) -> Result<Box<CertifiedSiltingComplex>, ClassificationFailure> {
    blocks.begin_classification();
    let basicness = (|| -> Result<BasicnessData, ClassificationFailure> {
        match basicness_check(&candidate, &mut blocks, limits.max_hom_spaces)? {
            BasicnessCheck::Basic(data) => Ok(data),
            BasicnessCheck::Blocked(blocker) => Err(ClassificationFailure::Outcome(
                TiltingComplexResult::Undetermined(blocker),
            )),
        }
    })()?;
    let scan = completed_orthogonality(&candidate, &mut blocks, limits.max_hom_spaces, goal)?;
    let generation_valid = match &generation {
        None => false,
        Some(witness) if cold_generation_check => witness.verify(&candidate),
        Some(witness) => witness.verify_with_cached_blocks(&candidate, blocks.meter)?,
    };
    let Some(generation) = generation.filter(|_| generation_valid) else {
        return Err(ClassificationFailure::Outcome(
            TiltingComplexResult::Undetermined(TiltingComplexBlocker::Generation),
        ));
    };
    let (block_cache, work) = blocks.finish(&candidate);
    Ok(Box::new(CertifiedSiltingComplex {
        candidate,
        generation,
        degree_zero_endomorphisms: basicness.ends,
        degree_zero_residues: basicness.residues,
        zero_shifted_homs: scan.checks,
        negative_class: scan.negative,
        limits,
        block_cache,
        work,
    }))
}

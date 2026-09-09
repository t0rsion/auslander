use std::sync::Arc;

use crate::algebra::Algebra;
use crate::approx::left_approximation;
use crate::basic::{
    AddClosureWitness, BasicDecomposition, ProjectiveSupport, SupportPairIsoOutcome,
    SupportPairObstruction, pair_iso,
};
use crate::context::VerificationContext;
use crate::hom::{cokernel, hom};
use crate::module::Module;
use crate::profile::{Site, hit};
use crate::supporttau::{
    AlmostCompleteClassification, AlmostCompletePair, SupportTauTiltingClassification,
    SupportTauTiltingPair,
};
use crate::taurigid::TauCache;

use super::build::build_target;
use super::common::{support, trace_dims};
use super::error::{Endpoint, MutationDefect, MutationError, defect};
use super::fac::FacWitness;
use super::witness::{ExchangeShape, MutationWitness};

/// A left mutation at one slot, with the pair it lands on.
#[derive(Debug)]
pub struct Mutation {
    pub(super) slot: usize,
    pub(super) target: SupportTauTiltingPair,
    pub(super) witness: MutationWitness,
}

impl Mutation {
    accessor_methods! {
        /// The slot the mutation was taken at.
        pub slot() -> usize = |this| this.slot;
        /// The pair the mutation lands on.
        pub target() -> &SupportTauTiltingPair = |this| &this.target;
    }

    /// The pair the mutation lands on, by value.
    #[inline]
    pub fn into_target(self) -> SupportTauTiltingPair {
        self.target
    }

    accessor_methods! {
        /// The five checks and the exchange sequence.
        pub witness() -> &MutationWitness = |this| &this.witness;
        /// Which of the two shapes the mutation took.
        pub shape() -> &ExchangeShape = |this| this.witness.shape();
    }

    verify_methods!(pub(crate), { hit(Site::MutationVerify); },
        /// Recomputes the witness and the target pair, and binds the two.
        ///
        /// The binding is [`Module::ptr_eq`] between the module part of the
        /// target pair and the target module the witness proves things about,
        /// plus equality of the two projective supports. Without it a witness
        /// for one target would pass next to a target pair for another.
        ///
        /// The slot is bound as well. The witness proves a statement about one
        /// slot, so a mutation carrying its own slot label could otherwise
        /// present a witness for a different one and still verify.
        |self, context| {
        self.slot == self.witness.slot()
            && self
                .target
                .module()
                .module()
                .ptr_eq(self.witness.target_module())
            && self.target.projective().vertices() == self.witness.target_projective()
            && self.witness.verify_with_context(context)
            && self.target.verify_with_context(context)
    });
}

/// What slot `j` of a pair admits.
#[derive(Debug)]
pub enum SlotOutcome {
    /// `X_j` lies in `Fac(M/X_j)`, so the mutation at this slot is a right
    /// mutation and there is no left mutation.
    NoLeftMutation(FacWitness),
    /// The left mutation at this slot, with its target.
    ///
    /// The mutation is boxed because it carries the whole target pair and
    /// every witness, which is much larger than a [`FacWitness`].
    LeftMutation(Box<Mutation>),
}

impl SlotOutcome {
    binary_outcome_accessors!(
        LeftMutation,
        NoLeftMutation,
        mutation -> Mutation = |value| value.as_ref(),
        fac_witness -> FacWitness = |value| value,
        is_left_mutation,
        into_mutation -> Mutation = |value| *value;
        flag = "Whether the slot admits a left mutation.";
        positive = "The mutation, or `None` when the slot admits no left mutation.";
        negative = "The `Fac` witness, or `None` when the slot admits a left mutation.";
        into = "The mutation by value, or `None` when the slot admits no left mutation.";
    );
}

/// The left mutation of `pair` at slot `slot`, over a cache of its own.
///
/// Summands are indexed by position and the cokernel summand gets the next
/// index, which is stable within this one call. Use
/// [`mutate_at_with_cache`] to share AR translates across several mutations.
///
/// # Errors
/// [`MutationError::SlotOutOfRange`] when the slot is not a module summand,
/// the wrapped errors of the layers a check runs through, and
/// [`MutationError::Defect`] on a failed internal cross-check.
pub fn mutate_at(pair: &SupportTauTiltingPair, slot: usize) -> Result<SlotOutcome, MutationError> {
    let count = pair.module().len();
    let indices: Vec<usize> = (0..count).collect();
    mutate_at_with_cache(pair, slot, &indices, count, None)
}

struct MutationInput {
    algebra: Arc<Algebra>,
    x: Module,
    u_dec: BasicDecomposition,
    u: Module,
    u_indices: Vec<usize>,
    u_summands: Vec<Module>,
}

fn prepare_input(
    pair: &SupportTauTiltingPair,
    slot: usize,
    summand_indices: &[usize],
) -> Result<MutationInput, MutationError> {
    let m = pair.module();
    if slot >= m.len() {
        return Err(MutationError::SlotOutOfRange {
            slot,
            summands: m.len(),
        });
    }
    if summand_indices.len() != m.len() {
        return Err(MutationError::SummandIndexCount {
            indices: summand_indices.len(),
            summands: m.len(),
        });
    }
    let algebra = m.module().algebra().clone();
    let x = m.summands()[slot].module().clone();
    let u_dec = m.without(slot).expect("the slot is a summand position");
    let u = u_dec.module().clone();
    let u_indices = summand_indices
        .iter()
        .enumerate()
        .filter(|(index, _)| *index != slot)
        .map(|(_, &index)| index)
        .collect();
    let u_summands = u_dec
        .summands()
        .iter()
        .map(|summand| summand.module().clone())
        .collect();
    Ok(MutationInput {
        algebra,
        x,
        u_dec,
        u,
        u_indices,
        u_summands,
    })
}

fn classify_target(
    input: &MutationInput,
    decomposition: BasicDecomposition,
    vertices: &[u32],
    replacement: bool,
    fresh_index: usize,
    cache: &mut TauCache,
) -> Result<SupportTauTiltingPair, MutationError> {
    let mut target_indices = input.u_indices.clone();
    target_indices.extend(replacement.then_some(fresh_index));
    let target_proj = ProjectiveSupport::new(&input.algebra, vertices)?;
    match SupportTauTiltingPair::classify_with_cache(
        decomposition,
        target_proj,
        &target_indices,
        Some(&mut *cache),
    )? {
        SupportTauTiltingClassification::Pair(target) => Ok(target),
        SupportTauTiltingClassification::Rejected(rejection) => {
            Err(defect(MutationDefect::TargetRejected(rejection)))
        }
    }
}

fn endpoint_data(
    source: &SupportTauTiltingPair,
    almost_complete: &AlmostCompletePair,
    target: &SupportTauTiltingPair,
) -> Result<(AddClosureWitness, AddClosureWitness, SupportPairObstruction), MutationError> {
    let Some(source_extension) = AddClosureWitness::new(almost_complete.module(), source.module())?
    else {
        return Err(defect(MutationDefect::AddClosureMissing {
            endpoint: Endpoint::Source,
        }));
    };
    let Some(target_extension) = AddClosureWitness::new(almost_complete.module(), target.module())?
    else {
        return Err(defect(MutationDefect::AddClosureMissing {
            endpoint: Endpoint::Target,
        }));
    };
    if almost_complete.projective().vertices() != source.projective().vertices() {
        return Err(defect(MutationDefect::ProjectiveSupportNotExtended {
            endpoint: Endpoint::Source,
        }));
    }
    if !almost_complete
        .projective()
        .vertices()
        .iter()
        .all(|&vertex| target.projective().contains(vertex))
    {
        return Err(defect(MutationDefect::ProjectiveSupportNotExtended {
            endpoint: Endpoint::Target,
        }));
    }
    let distinct = match pair_iso(
        source.module(),
        &source.projective(),
        target.module(),
        &target.projective(),
    )? {
        SupportPairIsoOutcome::NotIsomorphic(obstruction) => obstruction,
        SupportPairIsoOutcome::Isomorphic(_) => {
            return Err(defect(MutationDefect::EndpointsIsomorphic));
        }
    };
    Ok((source_extension, target_extension, distinct))
}

fn prepare_mutation(
    pair: &SupportTauTiltingPair,
    slot: usize,
    input: MutationInput,
    fresh_index: usize,
    cache: &mut TauCache,
) -> Result<SlotOutcome, MutationError> {
    let projective = ProjectiveSupport::new(&input.algebra, pair.projective().vertices())?;
    let almost_complete = match AlmostCompletePair::classify_with_cache(
        input.u_dec.clone(),
        projective,
        &input.u_indices,
        Some(&mut *cache),
    )? {
        AlmostCompleteClassification::Pair(almost) => almost,
        AlmostCompleteClassification::Rejected(rejection) => {
            return Err(defect(MutationDefect::AlmostCompleteRejected(rejection)));
        }
    };
    let approximation =
        left_approximation(&input.x, &input.u_summands).map_err(MutationError::Approx)?;
    let (y, exchange) = cokernel(approximation.map());
    // AIR Theorem 2.30 picks the shape by whether U is sincere.
    let dropped: Vec<u32> = support(pair.module().module())
        .into_iter()
        .filter(|&vertex| input.u.dim_at(vertex) == 0)
        .collect();
    let built = build_target(pair, &input.u_dec, &y, &dropped)?;
    let super::build::BuiltTarget {
        decomposition,
        vertices,
        shape,
        replacement,
    } = built;
    let target = classify_target(
        &input,
        decomposition,
        &vertices,
        replacement.is_some(),
        fresh_index,
        cache,
    )?;
    let (source_extension, target_extension, distinct) =
        endpoint_data(pair, &almost_complete, &target)?;
    let witness = MutationWitness {
        slot,
        exchanged: input.x,
        almost_complete,
        source_module: pair.module().module().clone(),
        source_projective: pair.projective().vertices().to_vec(),
        source_extension,
        target_module: target.module().module().clone(),
        target_projective: target.projective().vertices().to_vec(),
        target_extension,
        distinct,
        approximation,
        exchange,
        shape,
        replacement,
    };
    Ok(SlotOutcome::LeftMutation(Box::new(Mutation {
        slot,
        target,
        witness,
    })))
}

/// The left mutation of `pair` at slot `slot`, taking AR translates from
/// `cache`.
///
/// `summand_indices[i]` is the caller's stable label for summand `i` of the
/// module part, and `fresh_index` labels the cokernel summand of a
/// [`ExchangeShape::ReplacedByModule`] mutation. The labels travel to the
/// witnesses of the target pair and to
/// [`crate::taurigid::NonTauRigidWitness`]. They are not cache keys, so a
/// repeated label costs nothing but a confusing report. [`TauCache`] keys on
/// the identity of the module value.
///
/// The plain [`mutate_at`] labels summands by position because it builds and
/// drops its own cache. A caller that shares one cache usually has its own
/// numbering, which is why this entry point takes it.
///
/// With `cache` as `None` the call builds a cache, uses it, and drops it.
///
/// # Errors
/// As [`mutate_at`], plus [`MutationError::SummandIndexCount`] when the index
/// list and the summand list have different lengths.
pub fn mutate_at_with_cache(
    pair: &SupportTauTiltingPair,
    slot: usize,
    summand_indices: &[usize],
    fresh_index: usize,
    cache: Option<&mut TauCache>,
) -> Result<SlotOutcome, MutationError> {
    let input = prepare_input(pair, slot, summand_indices)?;
    let maps = hom(&input.u, &input.x)?;
    if trace_dims(&maps, &input.x) == input.x.dim_vector() {
        return Ok(SlotOutcome::NoLeftMutation(FacWitness {
            module: input.u,
            summands: input
                .u_dec
                .summands()
                .iter()
                .map(|summand| summand.module().clone())
                .collect(),
            summand: input.x,
            maps,
        }));
    }
    let mut owned = TauCache::new();
    let cache = cache.unwrap_or(&mut owned);
    prepare_mutation(pair, slot, input, fresh_index, cache)
}

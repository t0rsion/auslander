use std::sync::Arc;

use crate::algebra::Algebra;
use crate::basic::{BasicDecomposition, ProjectiveSupport};
use crate::decompose::direct_sum_or_zero;
use crate::dynkin::{DynkinType, dynkin_quiver};
use crate::field::PrimeField;
use crate::module::Module;
use crate::mutation::{FacWitness, Mutation, SlotOutcome, mutate_at};
use crate::quiver::Quiver;
use crate::supporttau::{SupportTauTiltingClassification, SupportTauTiltingPair};

/// The direct sum of `parts`, and the zero module when `parts` is empty.
pub(super) fn assemble(algebra: &Arc<Algebra>, parts: &[&Module]) -> Module {
    direct_sum_or_zero(algebra, parts.iter().copied()).0
}

pub(super) fn f2() -> PrimeField {
    PrimeField::new(2).unwrap()
}

pub(super) fn f5() -> PrimeField {
    PrimeField::new(5).unwrap()
}

pub(super) fn fields() -> [PrimeField; 2] {
    [f2(), f5()]
}

pub(super) fn path_algebra(quiver: Quiver, field: PrimeField) -> Arc<Algebra> {
    crate::algebra::path_algebra(quiver, field)
        .expect("the zero ideal over an acyclic quiver completes")
}

pub(super) fn semisimple(n: u32, field: PrimeField) -> Arc<Algebra> {
    path_algebra(
        Quiver::new(n, &[]).expect("no arrow is out of range"),
        field,
    )
}

// D_4 as dynkin_quiver builds it: vertex 0 is the center, arrows 0 -> 1,
// 0 -> 2, 0 -> 3.
pub(super) fn d4(field: PrimeField) -> Arc<Algebra> {
    path_algebra(
        dynkin_quiver(DynkinType::D(4)).expect("D_4 has a quiver"),
        field,
    )
}

pub(super) fn pair_of(
    algebra: &Arc<Algebra>,
    parts: &[&Module],
    projective: &[u32],
) -> SupportTauTiltingPair {
    let module = assemble(algebra, parts);
    let decomposition = BasicDecomposition::new(&module).expect("the fixture module part is basic");
    let support =
        ProjectiveSupport::new(algebra, projective).expect("the fixture vertices are in range");
    match SupportTauTiltingPair::classify(decomposition, support)
        .expect("the fixture parts share one algebra")
    {
        SupportTauTiltingClassification::Pair(pair) => pair,
        SupportTauTiltingClassification::Rejected(rejection) => panic!(
            "the fixture is a pair, condition {} says otherwise: {rejection}",
            rejection.condition()
        ),
    }
}

/// The regular module `A = P_0 + ... + P_{n-1}`.
pub(super) fn regular_pair(algebra: &Arc<Algebra>) -> SupportTauTiltingPair {
    let parts: Vec<Module> = (0..algebra.quiver().num_vertices())
        .map(|v| Module::projective(algebra, v))
        .collect();
    let refs: Vec<&Module> = parts.iter().collect();
    pair_of(algebra, &refs, &[])
}

/// The slot addressing the summand with dimension vector `dim`.
///
/// Every fixture below has module summands of pairwise distinct dimension
/// vectors, so the lookup is unambiguous. Over the Dynkin fixtures the
/// dimension vector also determines the indecomposable, since the
/// indecomposables are the positive roots.
pub(super) fn slot_of(pair: &SupportTauTiltingPair, dim: &[usize]) -> usize {
    let hits: Vec<usize> = pair
        .module()
        .summands()
        .iter()
        .enumerate()
        .filter(|(_, s)| s.module().dim_vector() == dim)
        .map(|(i, _)| i)
        .collect();
    assert_eq!(hits.len(), 1, "one summand of dimension vector {dim:?}");
    hits[0]
}

pub(super) fn sorted_dims(pair: &SupportTauTiltingPair) -> Vec<Vec<usize>> {
    let mut dims = pair.module().dim_vectors();
    dims.sort();
    dims
}

/// The mutation at the slot addressing `dim`, with both verifications run.
pub(super) fn left(pair: &SupportTauTiltingPair, dim: &[usize]) -> Mutation {
    let slot = slot_of(pair, dim);
    let outcome = mutate_at(pair, slot).expect("the fixture slot mutates");
    let mutation = match outcome {
        SlotOutcome::LeftMutation(mutation) => *mutation,
        SlotOutcome::NoLeftMutation(_) => {
            panic!("slot {slot} of dimension vector {dim:?} has a left mutation")
        }
    };
    assert!(mutation.witness().verify(), "the witness recomputes");
    assert!(mutation.verify(), "the mutation recomputes");
    mutation
}

pub(super) fn no_left(pair: &SupportTauTiltingPair, dim: &[usize]) -> FacWitness {
    let slot = slot_of(pair, dim);
    match mutate_at(pair, slot).expect("the fixture slot classifies") {
        SlotOutcome::NoLeftMutation(witness) => {
            assert!(witness.verify(), "the Fac witness recomputes");
            witness
        }
        SlotOutcome::LeftMutation(_) => {
            panic!("slot {slot} of dimension vector {dim:?} has no left mutation")
        }
    }
}

pub(super) fn assert_target(mutation: &Mutation, dims: &[&[usize]], projective: &[u32]) {
    let mut expected: Vec<Vec<usize>> = dims.iter().map(|d| d.to_vec()).collect();
    expected.sort();
    assert_eq!(sorted_dims(mutation.target()), expected);
    assert_eq!(mutation.target().projective().vertices(), projective);
}

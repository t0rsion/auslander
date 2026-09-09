use super::super::*;
use std::sync::Arc;

use crate::algebra::Algebra;
use crate::basic::{PairFingerprint, SupportPairIsoOutcome, pair_iso};
use crate::context::VerificationContext;
use crate::mutation::FacWitness;
use crate::profile::{Site, hit};
use crate::supporttau::SupportTauTiltingPair;

use super::super::support::regular_parts;
use crate::algebra::{linear_an, linear_nakayama, radical_square_zero_cycle, truncated_poly};
use crate::arquiver::IndecomposableCatalog;
use crate::dynkin::{DynkinType, dynkin_quiver};
use crate::field::PrimeField;
use crate::quiver::Quiver;

impl ClosureWitness {
    pub(super) fn pairwise_distinct(&self) -> bool {
        pairwise_distinct(self)
    }

    pub(super) fn slots_resolved(&self) -> bool {
        slots_resolved(self)
    }

    pub(super) fn verify_without_context(&self) -> bool {
        hit(Site::ClosureWitnessVerify);
        self.vertices.iter().all(|vertex| {
            Arc::ptr_eq(vertex.pair.module().module().algebra(), &self.algebra)
                && vertex.pair.verify()
        }) && pairwise_distinct(self)
            && root_is_regular(self)
            && slots_resolved(self)
            && self.endpoints_bound()
            && self.connected()
            && self.n_regular()
    }

    pub(super) fn fingerprints_without_context(&self) -> Vec<PairFingerprint> {
        self.vertices
            .iter()
            .map(|vertex| {
                PairFingerprint::new(vertex.pair.module(), &vertex.pair.projective())
                    .expect("the graph stores compatible pairs")
            })
            .collect()
    }

    pub(super) fn fingerprints_with_context(
        &self,
        context: &VerificationContext,
    ) -> Vec<PairFingerprint> {
        self.vertices
            .iter()
            .map(|vertex| {
                PairFingerprint::new_with_context(
                    vertex.pair.module(),
                    &vertex.pair.projective(),
                    context,
                )
                .expect("the graph stores compatible pairs")
            })
            .collect()
    }
}

fn pairwise_distinct(witness: &ClosureWitness) -> bool {
    let mut fingerprints = Vec::with_capacity(witness.vertices.len());
    for vertex in &witness.vertices {
        match PairFingerprint::new(vertex.pair.module(), &vertex.pair.projective()) {
            Ok(fingerprint) => fingerprints.push(fingerprint),
            Err(_) => return false,
        }
    }
    for (i, left) in witness.vertices.iter().enumerate() {
        for (j, right) in witness.vertices.iter().enumerate().skip(i + 1) {
            if fingerprints[i] == fingerprints[j]
                && !matches!(
                    pair_iso(
                        left.pair.module(),
                        &left.pair.projective(),
                        right.pair.module(),
                        &right.pair.projective(),
                    ),
                    Ok(SupportPairIsoOutcome::NotIsomorphic(_))
                )
            {
                return false;
            }
        }
    }
    true
}

fn root_is_regular(witness: &ClosureWitness) -> bool {
    let_or_false!(Some(root) = witness.vertices.first());
    let_or_false!(Ok((module, support)) = regular_parts(&witness.algebra));
    matches!(
        pair_iso(
            &module,
            &support,
            root.pair.module(),
            &root.pair.projective(),
        ),
        Ok(SupportPairIsoOutcome::Isomorphic(_))
    )
}

fn edge_indices_match(
    edge: &VerifiedMutation,
    vertex_index: usize,
    slot: usize,
    vertex_count: usize,
) -> bool {
    edge.source == vertex_index
        && edge.slot == slot
        && edge.target < vertex_count
        && edge.mutation.slot() == slot
}

fn edge_source_matches(edge: &VerifiedMutation, vertex: &GraphVertex) -> bool {
    edge.mutation.verify()
        && edge
            .mutation
            .witness()
            .source_module()
            .ptr_eq(vertex.pair.module().module())
        && edge.mutation.witness().source_projective() == vertex.pair.projective().vertices()
}

fn resolve_left_slot(
    witness: &ClosureWitness,
    referenced: &mut [bool],
    vertex_index: usize,
    vertex: &GraphVertex,
    slot: usize,
    mutation: usize,
) -> bool {
    let Some(edge) = witness.mutations.get(mutation) else {
        return false;
    };
    if referenced[mutation]
        || !edge_indices_match(edge, vertex_index, slot, witness.vertices.len())
        || !edge_source_matches(edge, vertex)
    {
        return false;
    }
    referenced[mutation] = true;
    true
}

fn fac_summands_match(fac: &FacWitness, vertex: &GraphVertex, slot: usize) -> bool {
    let summands = vertex.pair.module().summands();
    let Some(summand) = summands.get(slot) else {
        return false;
    };
    let kept = summands
        .iter()
        .enumerate()
        .filter(|(index, _)| *index != slot)
        .map(|(_, summand)| summand.module());
    fac.verify()
        && fac.summand().ptr_eq(summand.module())
        && fac.summands().len() + 1 == summands.len()
        && kept.zip(fac.summands().iter()).all(|(a, b)| a.ptr_eq(b))
}

fn slot_resolved(
    witness: &ClosureWitness,
    referenced: &mut [bool],
    vertex_index: usize,
    vertex: &GraphVertex,
    slot: usize,
    record: &SlotRecord,
) -> bool {
    match record {
        SlotRecord::LeftMutation { mutation } => {
            resolve_left_slot(witness, referenced, vertex_index, vertex, slot, *mutation)
        }
        SlotRecord::NoLeftMutation(fac) => fac_summands_match(fac, vertex, slot),
    }
}

fn vertex_slots_resolved(
    witness: &ClosureWitness,
    referenced: &mut [bool],
    vertex_index: usize,
    vertex: &GraphVertex,
) -> bool {
    if vertex.slots.len() != vertex.pair.module().len() {
        return false;
    }
    vertex.slots.iter().enumerate().all(|(slot, record)| {
        slot_resolved(witness, referenced, vertex_index, vertex, slot, record)
    })
}

fn slots_resolved(witness: &ClosureWitness) -> bool {
    let mut referenced = vec![false; witness.mutations.len()];
    for (vertex_index, vertex) in witness.vertices.iter().enumerate() {
        if !vertex_slots_resolved(witness, &mut referenced, vertex_index, vertex) {
            return false;
        }
    }
    referenced.iter().all(|used| *used)
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

fn path_algebra(quiver: Quiver, field: PrimeField) -> Arc<Algebra> {
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

pub(super) fn walk(algebra: &Arc<Algebra>) -> ClosedSupportTauTiltingGraph {
    let outcome = support_tau_tilting_graph(algebra, &MutationGraphLimits::default())
        .expect("the fixture walks without a defect");
    match outcome {
        SupportTauTiltingGraphOutcome::Closed(graph) => graph,
        SupportTauTiltingGraphOutcome::Incomplete(graph) => {
            panic!("the walk stopped short: {}", graph.reason())
        }
    }
}

/// The catalog fixtures both routes run over, in one order.
///
/// Every entry has an exhaustive [`IndecomposableCatalog`], so the second
/// route can enumerate it from the definition. The list matches the one
/// `supporttau` uses, so the two routes cover the same domains.
pub(super) fn catalog_fixtures(
    field: PrimeField,
) -> Vec<(String, Arc<Algebra>, IndecomposableCatalog)> {
    let modulus = field.modulus();
    let mut out = Vec::new();
    for n in [2u32, 3, 4] {
        let algebra = semisimple(n, field);
        let catalog = IndecomposableCatalog::nakayama(&algebra).expect("no arrow means Nakayama");
        out.push((
            format!("semisimple({n}) over F_{modulus}"),
            algebra,
            catalog,
        ));
    }
    for n in [2usize, 3] {
        let algebra = linear_an(n, field);
        let catalog = IndecomposableCatalog::dynkin(&algebra).expect("A_n is Dynkin");
        out.push((format!("linear_an({n}) over F_{modulus}"), algebra, catalog));
    }
    let tp = truncated_poly(3, field).expect("k[x]/(x^3) is admissible");
    let catalog = IndecomposableCatalog::nakayama(&tp).expect("one loop is Nakayama");
    out.push((format!("truncated_poly(3) over F_{modulus}"), tp, catalog));
    let cycle = radical_square_zero_cycle(3, field);
    let catalog = IndecomposableCatalog::nakayama(&cycle).expect("a cycle is Nakayama");
    out.push((
        format!("radical_square_zero_cycle(3) over F_{modulus}"),
        cycle,
        catalog,
    ));
    let nakayama = linear_nakayama(&[2, 2, 1], field).expect("[2, 2, 1] is a Kupisch series");
    let catalog = IndecomposableCatalog::nakayama(&nakayama).expect("a linear quiver is Nakayama");
    out.push((
        format!("linear_nakayama([2, 2, 1]) over F_{modulus}"),
        nakayama,
        catalog,
    ));
    out
}

/// Whether every pair of `left` has a partner in `right` and back, matched
/// by [`pair_iso`].
///
/// Both lists are pairwise non-isomorphic, so a pair matches at most one
/// partner and the greedy scan decides set equality.
pub(super) fn same_pair_set(
    left: &[&SupportTauTiltingPair],
    right: &[&SupportTauTiltingPair],
) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut used = vec![false; right.len()];
    for a in left {
        let mut matched = false;
        for (j, b) in right.iter().enumerate() {
            if used[j] {
                continue;
            }
            match pair_iso(a.module(), &a.projective(), b.module(), &b.projective())
                .expect("both routes build pairs over one algebra")
            {
                SupportPairIsoOutcome::Isomorphic(witness) => {
                    assert!(witness.verify(), "the matching isomorphism rechecks");
                    used[j] = true;
                    matched = true;
                    break;
                }
                SupportPairIsoOutcome::NotIsomorphic(_) => {}
            }
        }
        if !matched {
            return false;
        }
    }
    used.iter().all(|hit| *hit)
}

/// A normalized rendering of a closed graph, byte comparable across runs.
pub(super) fn render(graph: &ClosedSupportTauTiltingGraph) -> String {
    let mut out = String::new();
    for (v, vertex) in graph.vertices().iter().enumerate() {
        out.push_str(&format!(
            "v{v} {:?} p{:?}\n",
            vertex.pair().module().dim_vectors(),
            vertex.pair().projective().vertices()
        ));
        for (slot, record) in vertex.slots().iter().enumerate() {
            match record {
                SlotRecord::LeftMutation { mutation } => {
                    out.push_str(&format!("  s{slot} -> e{mutation}\n"));
                }
                SlotRecord::NoLeftMutation(witness) => {
                    out.push_str(&format!(
                        "  s{slot} fac {:?} of {:?} maps {}\n",
                        witness.summand().dim_vector(),
                        witness.module().dim_vector(),
                        witness.maps().len()
                    ));
                }
            }
        }
    }
    for (e, edge) in graph.mutations().iter().enumerate() {
        out.push_str(&format!(
            "e{e} {}:{} -> {} shape {:?} exchanged {:?} target {:?} bijection {:?}\n",
            edge.source(),
            edge.slot(),
            edge.target(),
            edge.mutation().shape(),
            edge.mutation().witness().exchanged().dim_vector(),
            edge.mutation().witness().target_module().dim_vector(),
            edge.endpoint().bijection()
        ));
    }
    out
}

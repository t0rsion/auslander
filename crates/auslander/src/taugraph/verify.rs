//! Independent checks for mutation-graph certificates.

use std::sync::Arc;

use crate::algebra::Algebra;
use crate::basic::{PairFingerprint, SupportPairIsoOutcome, pairwise_distinct_by};
use crate::context::VerificationContext;
use crate::dynkin::reachable_count;
use crate::profile::{Site, hit};

use super::contracts::{
    ClosedSupportTauTiltingGraph, GraphError, GraphVertex, SlotRecord, VerifiedMutation, defect,
};
use super::support::regular_parts_with_context;
pub(super) fn reachable_from_root(
    vertex_count: usize,
    edges: impl IntoIterator<Item = (usize, usize)>,
) -> usize {
    let mut out: Vec<Vec<usize>> = vec![Vec::new(); vertex_count];
    for (source, target) in edges {
        if source < vertex_count && target < vertex_count {
            out[source].push(target);
        }
    }
    reachable_count(&out, 0)
}

/// The proof that a vertex set is closed under left mutation, rechecked from
/// the stored data.
///
/// [`ClosureWitness::verify`] recomputes every obligation. Nothing is
/// inferred from the walk that built it.
#[derive(Debug)]
pub struct ClosureWitness {
    // Fields stay crate-private so the verifier and the test module can replay the certificate.
    pub(super) algebra: Arc<Algebra>,
    pub(super) vertices: Vec<GraphVertex>,
    pub(super) mutations: Vec<VerifiedMutation>,
}

impl ClosureWitness {
    accessor_methods! {
        /// The algebra the pairs live over.
        pub algebra() -> &Arc<Algebra> = |this| &this.algebra;
        /// The vertices, in discovery order from `(A, 0)`.
        pub vertices() -> &[GraphVertex] = |this| &this.vertices;
        /// The left-mutation edges, in discovery order.
        pub mutations() -> &[VerifiedMutation] = |this| &this.mutations;
    }

    fn vertices_certified_with_context(&self, context: &VerificationContext) -> bool {
        self.vertices.iter().all(|v| {
            Arc::ptr_eq(v.pair.module().module().algebra(), &self.algebra)
                && v.pair.verify_with_context(context)
        })
    }

    fn pairwise_distinct_with_context(&self, context: &VerificationContext) -> bool {
        pairwise_distinct_by(
            &self.vertices,
            |vertex| {
                PairFingerprint::new_with_context(
                    vertex.pair.module(),
                    &vertex.pair.projective(),
                    context,
                )
                .ok()
            },
            |left, right| {
                matches!(
                    context.pair_iso_for(
                        left.pair.module(),
                        &left.pair.projective(),
                        right.pair.module(),
                        &right.pair.projective(),
                    ),
                    Ok(outcome)
                        if matches!(outcome.as_ref(), SupportPairIsoOutcome::NotIsomorphic(_))
                )
            },
        )
    }

    fn root_is_regular_with_context(&self, context: &VerificationContext) -> bool {
        let_or_false!(Some(root) = self.vertices.first());
        let_or_false!(Ok((module, support)) = regular_parts_with_context(&self.algebra, context));
        matches!(
            context.pair_iso_for(
                &module,
                &support,
                root.pair.module(),
                &root.pair.projective(),
            ),
            Ok(outcome) if matches!(outcome.as_ref(), SupportPairIsoOutcome::Isomorphic(_))
        )
    }

    fn slots_resolved_with_context(&self, context: &VerificationContext) -> bool {
        let mut referenced = vec![false; self.mutations.len()];
        for (v, vertex) in self.vertices.iter().enumerate() {
            verify_guard!(vertex.slots.len() == vertex.pair.module().len());
            for (slot, record) in vertex.slots.iter().enumerate() {
                match record {
                    SlotRecord::LeftMutation { mutation } => {
                        let_or_false!(Some(edge) = self.mutations.get(*mutation));
                        verify_guard!(
                            !referenced[*mutation]
                                && edge.source == v
                                && edge.slot == slot
                                && edge.target < self.vertices.len()
                                && edge.mutation.slot() == slot
                                && edge.mutation.verify_with_context(context)
                        );
                        verify_guard!(
                            edge.mutation
                                .witness()
                                .source_module()
                                .ptr_eq(vertex.pair.module().module())
                                && edge.mutation.witness().source_projective()
                                    == vertex.pair.projective().vertices()
                        );
                        referenced[*mutation] = true;
                    }
                    SlotRecord::NoLeftMutation(witness) => {
                        verify_guard!(witness.verify());
                        let summands = vertex.pair.module().summands();
                        let_or_false!(Some(x) = summands.get(slot));
                        verify_guard!(witness.summand().ptr_eq(x.module()));
                        let kept = summands
                            .iter()
                            .enumerate()
                            .filter(|(i, _)| *i != slot)
                            .map(|(_, other)| other.module());
                        let stored = witness.summands();
                        verify_guard!(
                            stored.len() + 1 == summands.len()
                                && kept.zip(stored).all(|(a, b)| a.ptr_eq(b))
                        );
                    }
                }
            }
        }
        referenced.iter().all(|used| *used)
    }

    /// Obligation 5: every edge endpoint carries a pair-isomorphism witness to
    /// its indexed vertex, and the stored maps run between those two pairs.
    pub(super) fn endpoints_bound(&self) -> bool {
        for edge in &self.mutations {
            let_or_false!(Some(vertex) = self.vertices.get(edge.target));
            let built = edge.mutation.target();
            verify_guard!(built.projective().vertices() == vertex.pair.projective().vertices());
            let from = built.module().summands();
            let to = vertex.pair.module().summands();
            let bijection = edge.endpoint.bijection();
            verify_guard!(bijection.len() == from.len() && from.len() == to.len());
            verify_guard!(edge.endpoint.verify());
            for (i, &j) in bijection.iter().enumerate() {
                let_or_false!((Some(source), Some(target)) = (from.get(i), to.get(j)));
                let forward = &edge.endpoint.forward()[i];
                let backward = &edge.endpoint.backward()[i];
                verify_guard!(
                    forward.source().ptr_eq(source.module())
                        && forward.target().ptr_eq(target.module())
                        && backward.source().ptr_eq(target.module())
                        && backward.target().ptr_eq(source.module())
                );
            }
        }
        true
    }

    /// Obligation 6: every vertex is reachable from vertex zero along the
    /// stored left-mutation edges.
    pub(super) fn connected(&self) -> bool {
        reachable_from_root(
            self.vertices.len(),
            self.mutations.iter().map(|edge| (edge.source, edge.target)),
        ) == self.vertices.len()
    }

    /// Obligation 7, a cross-check: `incoming = Fac slots + |P|` at every
    /// vertex, and `outgoing + incoming = n`. See [`ClosureWitness::verify`]
    /// for why this is a cross-check rather than a gate.
    pub(super) fn n_regular(&self) -> bool {
        let n = self.algebra.quiver().num_vertices() as usize;
        let mut incoming = vec![0usize; self.vertices.len()];
        for edge in &self.mutations {
            verify_guard!(edge.target < incoming.len());
            incoming[edge.target] += 1;
        }
        for (v, vertex) in self.vertices.iter().enumerate() {
            let outgoing = vertex
                .slots
                .iter()
                .filter(|record| record.mutation().is_some())
                .count();
            let fac = vertex.slots.len() - outgoing;
            verify_guard!(incoming[v] == fac + vertex.pair.projective().len());
            verify_guard!(outgoing + incoming[v] == n);
        }
        true
    }

    verify_methods!(pub(super), { hit(Site::ClosureWitnessVerify); },
    /// Rechecks all seven obligations of `docs/support-tau-tilting.md` section 8.
    ///
    /// 1. Every vertex is a verified basic support tau-tilting pair.
    /// 2. The vertices are pairwise non-isomorphic.
    /// 3. Vertex zero is certified isomorphic to `(A, 0)`.
    /// 4. Every module-summand slot of every vertex carries a verified left
    ///    mutation whose target is a vertex of the set, or a certified
    ///    [`crate::mutation::FacWitness`] proving that no left mutation exists there.
    /// 5. Every edge endpoint carries a pair-isomorphism witness to its
    ///    indexed vertex, and the stored maps run between those two pairs.
    /// 6. Every vertex is reachable from vertex zero along the stored edges.
    /// 7. As a cross-check, the graph is `n`-regular.
    ///
    /// Every check recomputes from the stored pairs and maps. The vertices are
    /// re-verified, the vertex comparisons rerun, the mutations re-verified,
    /// the endpoint witnesses rebound, and connectivity is recomputed from
    /// the edge list rather than inferred from the walk.
    ///
    /// Obligation 7 is a cross-check and not a gate on soundness. The
    /// underlying graph of the support tau-tilting quiver is `n`-regular with
    /// `n` the number of simple modules, which here is the number of vertices
    /// of the quiver (Demonet, Iyama, and Jasso, arXiv:1503.00285, stated
    /// right after their result that arrows of the Hasse quiver are mutations;
    /// it follows from AIR Theorem 2.18). Each of the `n` slots of a vertex
    /// gives one neighbour: a module slot with a left mutation gives an
    /// outgoing edge, and a module slot in the `Fac` branch or a projective
    /// summand gives a right mutation, hence an incoming edge. So for every
    /// vertex
    ///
    /// ```text
    /// incoming edges = Fac slots + |P|      and      outgoing + incoming = n.
    /// ```
    ///
    /// The content is the first equation: the incoming count is read off the
    /// stored edge list, which no single vertex built, while the right side is
    /// read off the vertex itself.
    ///
    /// Completeness rests on obligations 1 to 5, which are finite left
    /// closure with `(A, 0)` present. Obligation 6 follows from those: the
    /// descending chain of AIR Theorem 2.35(b) reaches every pair from
    /// `(A, 0)` along edges obligation 4 stores. Obligation 7 is outside the
    /// argument altogether. Both stay gates all the same, because a failure
    /// of either contradicts a theorem whose hypotheses hold, so it is a
    /// crate defect.
        |self, context| {
        self.vertices_certified_with_context(context)
            && self.pairwise_distinct_with_context(context)
            && self.root_is_regular_with_context(context)
            && self.slots_resolved_with_context(context)
            && self.endpoints_bound()
            && self.connected()
            && self.n_regular()
    });
}

pub(super) fn close(
    algebra: &Arc<Algebra>,
    vertices: Vec<GraphVertex>,
    mutations: Vec<VerifiedMutation>,
    work_units: u64,
) -> Result<ClosedSupportTauTiltingGraph, GraphError> {
    let witness = ClosureWitness {
        algebra: algebra.clone(),
        vertices,
        mutations,
    };
    if !witness.verify() {
        return Err(defect(
            "the walk drained its frontier and the closure recheck failed".to_string(),
        ));
    }
    Ok(ClosedSupportTauTiltingGraph {
        witness,
        work_units,
    })
}

use crate::basic::{
    BasicDecomposition, ProjectiveSupport, SupportPairIsoOutcome, SupportPairIsoWitness, pair_iso,
};
use crate::mutation::{FacWitness, Mutation, MutationError, SlotOutcome, mutate_at_with_cache};

use super::super::contracts::{
    GraphError, GraphLimit, SlotRecord, VerifiedMutation, defect, mutation_blocker,
};
use super::accounting::{hom_entries, iso_units, scale_of, slot_units};
use super::registry::{SlotPlan, Stop, Walk};

impl Walk<'_> {
    /// Whether the Hom system of the `Fac` test at this slot fits in
    /// `max_matrix_entries`, checked before the mutation layer allocates it.
    ///
    /// The system is `Hom(U, X_j)`, with `sum_v dim U_v dim X_v` unknowns, and
    /// it is the widest one the slot allocates among those the walk can size
    /// ahead of the call: every approximation system `Hom(X_j, U_i)` has at
    /// most as many unknowns, since `U_i` is a summand of `U`. The systems
    /// `Hom(X_i, tau X_j)` are not covered, because `tau X_j` is not known
    /// before it is computed.
    fn fac_system_fits(&self, vertex: usize, slot: usize) -> bool {
        let summands = self.vertices[vertex].pair.module().summands();
        let x = summands[slot].module().dim_vector();
        let mut kept = vec![0usize; x.len()];
        for (i, other) in summands.iter().enumerate() {
            if i == slot {
                continue;
            }
            for (entry, dim) in kept.iter_mut().zip(other.module().dim_vector().iter()) {
                *entry += dim;
            }
        }
        hom_entries(&kept, x) <= self.limits.max_matrix_entries
    }

    fn prepare_slot(&mut self, vertex: usize, slot: usize) -> Result<SlotPlan, Stop> {
        self.at_vertex = vertex;
        self.at_slot = Some(slot);
        let summands = self.vertices[vertex].pair.module().len();
        let scale = scale_of(self.vertices[vertex].pair.module().module().dim_vector());
        if !self.fac_system_fits(vertex, slot) {
            return Err(Stop::Budget(GraphLimit::MatrixEntries));
        }
        // The left-mutation charge includes the Fac branch, so this check
        // runs before the branch is known.
        if self.ledger.would_exceed(
            slot_units(summands, true, scale),
            self.limits.max_work_units,
        ) {
            return Err(Stop::Budget(GraphLimit::WorkUnits));
        }
        Ok(SlotPlan {
            summands,
            scale,
            fresh: self.registry.fresh(),
            indices: self.indices[vertex].clone(),
        })
    }

    fn mutation_failure(error: MutationError) -> Result<Result<SlotOutcome, Stop>, GraphError> {
        match mutation_blocker(&error) {
            Some(reason) => Ok(Err(Stop::Blocked(reason))),
            None => Err(error.into()),
        }
    }

    fn run_slot_mutation(
        &mut self,
        vertex: usize,
        slot: usize,
        plan: &SlotPlan,
    ) -> Result<Result<SlotOutcome, Stop>, GraphError> {
        let misses = self.cache.misses();
        let outcome = mutate_at_with_cache(
            &self.vertices[vertex].pair,
            slot,
            &plan.indices,
            plan.fresh,
            Some(&mut self.cache),
        );
        self.charge_tau(misses, plan.scale);
        match outcome {
            Ok(outcome) => Ok(Ok(outcome)),
            Err(error) => Self::mutation_failure(error),
        }
    }

    fn record_no_left_mutation(&mut self, vertex: usize, witness: FacWitness, plan: &SlotPlan) {
        self.ledger
            .charge(slot_units(plan.summands, false, plan.scale));
        self.vertices[vertex]
            .slots
            .push(SlotRecord::NoLeftMutation(witness));
        self.verified_slots += 1;
    }

    fn rebuild_target(
        &mut self,
        mutation: &Mutation,
        fresh: usize,
    ) -> Result<Result<usize, Stop>, GraphError> {
        if self.vertices.len() >= self.limits.max_vertices {
            return Ok(Err(Stop::Budget(GraphLimit::Vertices)));
        }
        // The rebuilt pair keeps the endpoint check independent of the
        // decomposition stored by the mutation.
        let module = BasicDecomposition::new(mutation.target().module().module())?;
        let support =
            ProjectiveSupport::new(&self.algebra, mutation.target().projective().vertices())?;
        // The mutation already assigned `fresh` to its cokernel summand.
        let preferred = mutation.witness().replacement().map(|_| fresh);
        self.push_vertex(module, support, preferred)
    }

    fn bind_rebuilt_target(
        &self,
        mutation: &Mutation,
        index: usize,
    ) -> Result<SupportPairIsoWitness, GraphError> {
        match pair_iso(
            mutation.target().module(),
            &mutation.target().projective(),
            self.vertices[index].pair.module(),
            &self.vertices[index].pair.projective(),
        )? {
            SupportPairIsoOutcome::Isomorphic(witness) => Ok(witness),
            SupportPairIsoOutcome::NotIsomorphic(obstruction) => Err(defect(format!(
                "the rebuilt vertex is not isomorphic to the mutation target: {obstruction:?}"
            ))),
        }
    }

    fn create_target(
        &mut self,
        mutation: &Mutation,
        plan: &SlotPlan,
    ) -> Result<Result<(usize, SupportPairIsoWitness), Stop>, GraphError> {
        let index = match self.rebuild_target(mutation, plan.fresh)? {
            Ok(index) => index,
            Err(stop) => return Ok(Err(stop)),
        };
        self.new_vertices += 1;
        self.ledger.charge(iso_units(
            mutation.target().module().len(),
            scale_of(mutation.target().module().module().dim_vector()),
        ));
        let witness = self.bind_rebuilt_target(mutation, index)?;
        Ok(Ok((index, witness)))
    }

    fn resolve_target(
        &mut self,
        mutation: &Mutation,
        plan: &SlotPlan,
    ) -> Result<Result<(usize, SupportPairIsoWitness), Stop>, GraphError> {
        match self.find_vertex(mutation.target())? {
            Some((index, witness)) => {
                self.repeated_endpoints += 1;
                Ok(Ok((index, witness)))
            }
            None => self.create_target(mutation, plan),
        }
    }

    fn record_left_mutation(
        &mut self,
        vertex: usize,
        slot: usize,
        mutation: Box<Mutation>,
        plan: &SlotPlan,
    ) -> Result<Option<Stop>, GraphError> {
        self.ledger
            .charge(slot_units(plan.summands, true, plan.scale));
        if self.mutations.len() >= self.limits.max_directed_mutations {
            return Ok(Some(Stop::Budget(GraphLimit::DirectedMutations)));
        }
        let (target, endpoint) = match self.resolve_target(&mutation, plan)? {
            Ok(target) => target,
            Err(stop) => return Ok(Some(stop)),
        };
        let edge = self.mutations.len();
        self.mutations.push(VerifiedMutation {
            source: vertex,
            slot,
            target,
            mutation: *mutation,
            endpoint,
        });
        self.vertices[vertex]
            .slots
            .push(SlotRecord::LeftMutation { mutation: edge });
        self.verified_slots += 1;
        Ok(None)
    }

    fn record_slot_outcome(
        &mut self,
        vertex: usize,
        slot: usize,
        outcome: SlotOutcome,
        plan: &SlotPlan,
    ) -> Result<Option<Stop>, GraphError> {
        match outcome {
            SlotOutcome::NoLeftMutation(witness) => {
                self.record_no_left_mutation(vertex, witness, plan);
                Ok(None)
            }
            SlotOutcome::LeftMutation(mutation) => {
                self.record_left_mutation(vertex, slot, mutation, plan)
            }
        }
    }

    fn visit_prepared_slot(
        &mut self,
        vertex: usize,
        slot: usize,
        plan: SlotPlan,
    ) -> Result<Option<Stop>, GraphError> {
        match self.run_slot_mutation(vertex, slot, &plan)? {
            Ok(outcome) => self.record_slot_outcome(vertex, slot, outcome, &plan),
            Err(stop) => Ok(Some(stop)),
        }
    }

    /// Visits one slot of one vertex.
    pub(super) fn visit_slot(
        &mut self,
        vertex: usize,
        slot: usize,
    ) -> Result<Option<Stop>, GraphError> {
        match self.prepare_slot(vertex, slot) {
            Ok(plan) => self.visit_prepared_slot(vertex, slot, plan),
            Err(stop) => Ok(Some(stop)),
        }
    }
}

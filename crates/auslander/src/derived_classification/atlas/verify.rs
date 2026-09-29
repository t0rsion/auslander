use std::sync::Arc;

use crate::algebra::Algebra;
use crate::algebra_isomorphism::AlgebraIsomorphism;
use crate::certificate::Certificate;
use crate::control::{ComputationControl, ProgressStage};
use crate::derived_artifact::{ArtifactVerificationCut, declared_limits, exceeded};
use crate::derived_invariant::{
    DerivedInequivalenceWitness, DerivedInvariantKind, DerivedInvariants,
};
use crate::equivalence_edge::DerivedEquivalencePath;
use crate::field::{Fp, PrimeField};
use crate::verify::verify_certificate;

use super::super::stages::groups_by_key;
use super::super::verify::{covers_pairs, partitions, replay_edge, spanning_tree};
use super::super::{
    ClassSeparation, ClassificationStatus, DerivedClass, DerivedClassification, DerivedMerge,
};
use super::errors::DerivedAtlasError;
use super::model::{
    AtlasMerge, AtlasReading, AtlasSeparation, DerivedAtlasArtifact, DerivedAtlasVerifyLimits,
    encode_value,
};

/// A verified atlas and the classification it rebuilds.
#[derive(Clone, Debug)]
pub struct VerifiedDerivedAtlas {
    artifact: DerivedAtlasArtifact,
    classification: DerivedClassification,
}

impl VerifiedDerivedAtlas {
    accessor_methods! {
        /// The canonical parsed atlas.
        pub artifact() -> &DerivedAtlasArtifact = |this| &this.artifact;
        /// The rebuilt classification: the verified family, the recomputed
        /// invariants, and every replayed merge and separation.
        pub classification() -> &DerivedClassification = |this| &this.classification;
    }
}

/// A verified atlas, or a typed stop before the verifier decided.
#[derive(Clone, Debug)]
pub enum DerivedAtlasVerification {
    /// Every stored claim replayed.
    Verified(Box<VerifiedDerivedAtlas>),
    /// Cancellation or a verifier ceiling stopped the run. `Cancelled` and
    /// `WorkLimit` count the mutations replayed over all merges.
    Stopped(ArtifactVerificationCut),
}

/// Why replay ended before a verdict or with a rejection.
enum Halt {
    Stopped(ArtifactVerificationCut),
    Rejected(DerivedAtlasError),
}

impl From<DerivedAtlasError> for Halt {
    fn from(error: DerivedAtlasError) -> Self {
        Halt::Rejected(error)
    }
}

/// The replayed mutation count against the verifier ceiling, with the
/// cancellation check before each charge.
struct Budget<'a> {
    control: &'a ComputationControl,
    completed: usize,
    limit: usize,
}

impl Budget<'_> {
    fn charge(&mut self, mutations: usize) -> Result<(), Halt> {
        let completed = self.completed;
        if self.control.is_cancelled() {
            let completed_mutations = completed;
            return Err(Halt::Stopped(ArtifactVerificationCut::Cancelled {
                completed_mutations,
            }));
        }
        let next = completed.saturating_add(mutations);
        if next > self.limit {
            let limit = self.limit;
            return Err(Halt::Stopped(ArtifactVerificationCut::WorkLimit {
                completed,
                limit,
            }));
        }
        self.control
            .update(ProgressStage::ArtifactVerify, completed, next);
        self.completed = next;
        Ok(())
    }
}

/// Parses and verifies one untrusted atlas.
///
/// Runs no discovery. It rebuilds every member through the certificate
/// verifier, recomputes every reading, rebuilds every separation witness,
/// replays every merge recipe, and checks every isomorphism. See
/// [`DerivedAtlasArtifact::verify`].
pub fn verify_derived_atlas_artifact(
    text: &str,
    limits: DerivedAtlasVerifyLimits,
    control: &ComputationControl,
) -> Result<DerivedAtlasVerification, DerivedAtlasError> {
    control.update(ProgressStage::ArtifactVerify, 0, 0);
    DerivedAtlasArtifact::from_json(text, limits.parse)?.verify(limits, control)
}

impl DerivedAtlasArtifact {
    /// Verifies the parsed atlas under `limits`.
    ///
    /// The checks run cheap first. The fingerprint must match, and every
    /// declared limit must lie within its ceiling. The classes must
    /// partition the family, the merges of each class must form a spanning
    /// tree, and each pair of classes must be separated or unresolved
    /// exactly once. No unresolved pair may be merged or separated, the
    /// walk records must match the merges, and the status must be
    /// `complete` exactly when no pair is unresolved. Then every member
    /// rebuilds, every reading recomputes to its stored form, every
    /// separation rebuilds a [`DerivedInequivalenceWitness`] with the
    /// stored values, and every merge replays to a target whose
    /// [`AlgebraIsomorphism`] onto the member verifies.
    ///
    /// Cancellation is checked before each member and each merge.
    pub fn verify(
        &self,
        limits: DerivedAtlasVerifyLimits,
        control: &ComputationControl,
    ) -> Result<DerivedAtlasVerification, DerivedAtlasError> {
        match self.replay(limits, control) {
            Ok(classification) => Ok(DerivedAtlasVerification::Verified(Box::new(
                VerifiedDerivedAtlas {
                    artifact: self.clone(),
                    classification,
                },
            ))),
            Err(Halt::Stopped(cut)) => Ok(DerivedAtlasVerification::Stopped(cut)),
            Err(Halt::Rejected(error)) => Err(error),
        }
    }

    fn replay(
        &self,
        limits: DerivedAtlasVerifyLimits,
        control: &ComputationControl,
    ) -> Result<DerivedClassification, Halt> {
        if !self.has_valid_fingerprint() {
            return Err(DerivedAtlasError::FingerprintMismatch.into());
        }
        if let Some(cut) = self.declared_cut(&limits) {
            return Err(Halt::Stopped(cut));
        }
        self.check_structure()?;
        let family = self.rebuild_family()?;
        let mut budget = Budget {
            control,
            completed: 0,
            limit: limits.replay.max_work_units,
        };
        let invariants = self.recompute(&family, &mut budget)?;
        let separations = self.rebuild_separations(&invariants)?;
        let classes = self.replay_classes(&family, &mut budget)?;
        control.update(ProgressStage::Complete, budget.completed, budget.completed);
        Ok(DerivedClassification {
            family,
            limits: self.limits.clone(),
            groups: groups_by_key(&invariants, &self.invariants),
            invariants,
            classes,
            separations,
            unresolved: self.unresolved.clone(),
            walks: self.walks.clone(),
        })
    }

    fn declared_cut(&self, limits: &DerivedAtlasVerifyLimits) -> Option<ArtifactVerificationCut> {
        let (invariants, bar) = (&self.limits.invariants, &self.limits.invariants.bar);
        let member = self.members.iter().map(Certificate::declared_dimension);
        let tilting = self.limits.discovery.tilting;
        let replay = declared_limits(tilting, &self.limits.target, &limits.replay);
        let own = [
            (
                "hochschild_degree",
                invariants.hochschild_degree as u64,
                limits.max_hochschild_degree,
            ),
            (
                "max_tensor_tuples",
                bar.max_tensor_tuples,
                limits.max_tensor_tuples,
            ),
            (
                "max_cochain_dim",
                bar.max_cochain_dim,
                limits.max_cochain_dim,
            ),
            (
                "bar.max_matrix_entries",
                bar.max_matrix_entries,
                limits.max_bar_matrix_entries,
            ),
            (
                "bar.max_work_units",
                bar.max_work_units,
                limits.max_bar_work_units,
            ),
            (
                "member_dimension",
                member.max().unwrap_or(0),
                limits.max_member_dimension,
            ),
        ];
        exceeded(own.into_iter().chain(replay))
    }

    /// The family is not empty, each member has a row, and the classes
    /// partition the family.
    fn check_family(&self) -> Result<(), DerivedAtlasError> {
        let size = self.members.len();
        if size == 0 {
            return Err(DerivedAtlasError::EmptyFamily);
        }
        if self.invariants.len() != size {
            let (rows, members) = (self.invariants.len(), size);
            return Err(DerivedAtlasError::RowCount { rows, members });
        }
        match partitions(size, self.classes.iter().map(|class| class.members())) {
            true => Ok(()),
            false => Err(DerivedAtlasError::Partition),
        }
    }

    /// The spanning trees keep every merge inside its class, and the pair
    /// coverage lists each pair once, so no unresolved pair is merged or
    /// separated.
    fn check_structure(&self) -> Result<(), DerivedAtlasError> {
        self.check_family()?;
        for (index, class) in self.classes.iter().enumerate() {
            let edges = class
                .merges
                .iter()
                .map(|merge| (merge.source, merge.member));
            if !spanning_tree(&class.members, edges) {
                return Err(DerivedAtlasError::SpanningTree { class: index });
            }
        }
        let separated = self.separations.iter().map(|separation| separation.classes);
        if !covers_pairs(self.classes.len(), separated, &self.unresolved) {
            return Err(DerivedAtlasError::PairCoverage);
        }
        self.check_walks()?;
        let complete = self.status == ClassificationStatus::Complete;
        match complete == self.unresolved.is_empty() {
            true => Ok(()),
            false => Err(DerivedAtlasError::Status),
        }
    }

    /// The class of each member. The classes partition the family.
    fn class_of(&self) -> Vec<usize> {
        let mut class_of = vec![0; self.members.len()];
        for (class, members) in self.classes.iter().enumerate() {
            for &member in members.members() {
                class_of[member] = class;
            }
        }
        class_of
    }

    /// The walks run in member order, each walk added exactly the merges
    /// with a recipe from its member, and each unresolved pair lists every
    /// walk from a member of either class.
    ///
    /// Runs after the spanning-tree and pair checks, so every merge source
    /// is a member and every unresolved class exists.
    fn check_walks(&self) -> Result<(), DerivedAtlasError> {
        let merges = self.classes.iter().flat_map(|class| class.merges());
        let mut from = vec![0usize; self.members.len()];
        for merge in merges.filter(|merge| !merge.recipe.is_empty()) {
            from[merge.source] += 1;
        }
        let walks = &self.walks;
        let increasing = walks.windows(2).all(|pair| pair[0].member < pair[1].member);
        let counted = walks.iter().all(|w| from.get(w.member) == Some(&w.merges));
        let covered = || walks.iter().map(|w| from[w.member]).sum::<usize>();
        if !(increasing && counted && covered() == from.iter().sum::<usize>()) {
            return Err(DerivedAtlasError::Walks);
        }
        let class_of = self.class_of();
        let mut per_class = vec![0usize; self.classes.len()];
        walks
            .iter()
            .for_each(|walk| per_class[class_of[walk.member]] += 1);
        for pair in &self.unresolved {
            let (left, right) = pair.classes;
            let in_pair = |&walk: &usize| {
                walks.get(walk).is_some_and(|walk| {
                    let class = class_of[walk.member];
                    class == left || class == right
                })
            };
            let listed = pair.walks.len() == per_class[left] + per_class[right]
                && pair.walks.windows(2).all(|w| w[0] < w[1])
                && pair.walks.iter().all(in_pair);
            if !listed {
                let classes = pair.classes;
                return Err(DerivedAtlasError::UnresolvedWalks { classes });
            }
        }
        Ok(())
    }

    fn rebuild_family(&self) -> Result<Vec<Arc<Algebra>>, DerivedAtlasError> {
        PrimeField::new(self.field).map_err(DerivedAtlasError::Field)?;
        let rebuild = |(member, certificate): (usize, &Certificate)| {
            if certificate.field != self.field {
                let found = certificate.field;
                return Err(DerivedAtlasError::FieldMismatch { member, found });
            }
            let verified = verify_certificate(certificate.clone())
                .map_err(|error| DerivedAtlasError::Verify { member, error })?;
            Algebra::from_verified(verified)
                .map_err(|error| DerivedAtlasError::Algebra { member, error })
        };
        self.members.iter().enumerate().map(rebuild).collect()
    }

    fn recompute(
        &self,
        family: &[Arc<Algebra>],
        budget: &mut Budget,
    ) -> Result<Vec<DerivedInvariants>, Halt> {
        let mut records = Vec::with_capacity(family.len());
        for (member, algebra) in family.iter().enumerate() {
            budget.charge(0)?;
            let record =
                DerivedInvariants::compute(algebra, self.limits.invariants, budget.control)
                    .map_err(|error| DerivedAtlasError::Invariant { member, error })?;
            budget.charge(0)?;
            let stored = &self.invariants[member];
            let differs = |&&kind: &&DerivedInvariantKind| {
                AtlasReading::from_reading(record.reading(kind)).as_ref()
                    != Some(&stored[kind as usize])
            };
            if let Some(&kind) = DerivedInvariantKind::ALL.iter().find(differs) {
                return Err(DerivedAtlasError::ReadingMismatch { member, kind }.into());
            }
            records.push(record);
        }
        Ok(records)
    }

    fn rebuild_separations(
        &self,
        invariants: &[DerivedInvariants],
    ) -> Result<Vec<ClassSeparation>, DerivedAtlasError> {
        let rebuild = |separation: &AtlasSeparation| {
            self.witness(separation, invariants)
                .map(|witness| ClassSeparation {
                    classes: separation.classes,
                    members: separation.members,
                    witness,
                })
                .ok_or(DerivedAtlasError::Separation {
                    classes: separation.classes,
                })
        };
        self.separations.iter().map(rebuild).collect()
    }

    /// The witness of `separation` from the recomputed records, when its
    /// members lie in its classes and its values are the recomputed ones.
    fn witness(
        &self,
        separation: &AtlasSeparation,
        invariants: &[DerivedInvariants],
    ) -> Option<DerivedInequivalenceWitness> {
        let (left, right) = separation.members;
        let (left_class, right_class) = separation.classes;
        let holds = |class: usize, member| self.classes[class].members.binary_search(&member);
        let inside = holds(left_class, left).is_ok() && holds(right_class, right).is_ok();
        let witness = inside.then(|| {
            DerivedInequivalenceWitness::new(&invariants[left], &invariants[right], separation.kind)
        })?;
        let witness = witness.ok()?;
        let stored = (&separation.left, &separation.right);
        let values = (
            &encode_value(witness.left_value()),
            &encode_value(witness.right_value()),
        );
        (stored == values).then_some(witness)
    }

    fn replay_classes(
        &self,
        family: &[Arc<Algebra>],
        budget: &mut Budget,
    ) -> Result<Vec<DerivedClass>, Halt> {
        let mut classes = Vec::with_capacity(self.classes.len());
        for class in &self.classes {
            let merges = class.merges().iter();
            let merges = merges.map(|merge| self.replay_merge(family, merge, budget));
            classes.push(DerivedClass {
                members: class.members.clone(),
                merges: merges.collect::<Result<_, _>>()?,
            });
        }
        Ok(classes)
    }

    /// Replays the recipe of `merge` and checks its isomorphism. An empty
    /// recipe is a duplicate: the target is the source member itself.
    fn replay_merge(
        &self,
        family: &[Arc<Algebra>],
        merge: &AtlasMerge,
        budget: &mut Budget,
    ) -> Result<DerivedMerge, Halt> {
        budget.charge(merge.recipe.len())?;
        let (source, member) = (merge.source, merge.member);
        let algebra = &family[source];
        let (path, target) = if merge.recipe.is_empty() {
            (DerivedEquivalencePath::identity(algebra), algebra.clone())
        } else {
            let edge = replay_edge(algebra, &merge.recipe, &self.limits)
                .ok_or(DerivedAtlasError::Replay { source, member })?;
            (edge.path(), edge.target().clone())
        };
        let rejected = DerivedAtlasError::Isomorphism { source, member };
        let isomorphism = AlgebraIsomorphism {
            source: target,
            target: family[member].clone(),
            vertex_map: merge.vertex_map.clone(),
            arrow_images: self.coordinates(merge).ok_or(rejected.clone())?,
        };
        if !isomorphism.verify() {
            return Err(rejected.into());
        }
        Ok(DerivedMerge {
            source,
            member,
            recipe: merge.recipe.clone(),
            path,
            isomorphism,
        })
    }

    /// The arrow images as field elements, or `None` when a residue lies
    /// outside `0..p`.
    fn coordinates(&self, merge: &AtlasMerge) -> Option<Vec<Vec<Fp>>> {
        let field = PrimeField::new(self.field).ok()?;
        let element = |&value: &u64| (value < self.field).then(|| field.elem(value as i64));
        let image = |values: &Vec<u64>| values.iter().map(element).collect::<Option<Vec<_>>>();
        merge.arrow_images.iter().map(image).collect()
    }
}

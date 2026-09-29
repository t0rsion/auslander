use crate::derived_artifact::replay_recipe;
use crate::equivalence_edge::{DerivedEquivalenceEdge, DerivedEquivalenceEdgeOutcome};

use super::*;

fn same(left: &Algebra, right: &Algebra) -> bool {
    left.certificate() == right.certificate()
}

/// Whether `classes`, each increasing and ordered by least member, partition
/// `0..size`.
pub(super) fn partitions<'a>(size: usize, classes: impl IntoIterator<Item = &'a [usize]>) -> bool {
    let mut seen = vec![false; size];
    let mut last = None;
    for members in classes {
        let increasing = members.windows(2).all(|pair| pair[0] < pair[1]);
        verify_guard!(increasing && members.first().copied() > last);
        last = members.first().copied();
        for &member in members {
            verify_guard!(member < size && !std::mem::replace(&mut seen[member], true));
        }
    }
    seen.iter().all(|&found| found)
}

/// Whether `edges`, read as undirected, form a spanning tree of the
/// increasing list `members`: every endpoint is a member, there is one edge
/// fewer than members, and no edge closes a cycle.
///
/// Union-find keeps the cost near linear, because the edges are untrusted.
pub(super) fn spanning_tree(
    members: &[usize],
    edges: impl ExactSizeIterator<Item = (usize, usize)>,
) -> bool {
    verify_guard!(edges.len() + 1 == members.len());
    let mut parent: Vec<usize> = (0..members.len()).collect();
    for (left, right) in edges {
        let (Ok(left), Ok(right)) = (members.binary_search(&left), members.binary_search(&right))
        else {
            return false;
        };
        let (left, right) = (root(&mut parent, left), root(&mut parent, right));
        verify_guard!(left != right);
        parent[left] = right;
    }
    true
}

/// The root of `node` in a union-find forest, with path halving.
fn root(parent: &mut [usize], mut node: usize) -> usize {
    while parent[node] != node {
        parent[node] = parent[parent[node]];
        node = parent[node];
    }
    node
}

/// Whether each pair of `count` classes is in `separated` or `unresolved`
/// exactly once, with both lists in pair order.
///
/// The pair count is compared before any table is built, so a large `count`
/// with short lists costs no allocation.
pub(super) fn covers_pairs(
    count: usize,
    separated: impl Iterator<Item = (usize, usize)>,
    unresolved: &[UnresolvedPair],
) -> bool {
    let mut pairs: Vec<_> = separated.collect();
    let open: Vec<_> = unresolved.iter().map(|pair| pair.classes).collect();
    let increasing = |pairs: &[(usize, usize)]| pairs.windows(2).all(|w| w[0] < w[1]);
    verify_guard!(increasing(&pairs) && increasing(&open));
    let all = count
        .checked_mul(count.saturating_sub(1))
        .map(|twice| twice / 2);
    verify_guard!(all == Some(pairs.len() + open.len()));
    pairs.extend(open);
    pairs.sort_unstable();
    let valid = |&(left, right): &(usize, usize)| left < right && right < count;
    increasing(&pairs) && pairs.iter().all(valid)
}

/// The certified edge from `source` to the target that `recipe` reaches,
/// replayed from the regular complex under `limits`. `None` when a mutation
/// fails, a walk without `through_silting` passes a silting complex, or
/// target recovery stops or fails.
pub(super) fn replay_edge(
    source: &Arc<Algebra>,
    recipe: &[ArtifactMutation],
    limits: &ClassificationLimits,
) -> Option<Box<DerivedEquivalenceEdge>> {
    let discovery = &limits.discovery;
    let tilting = replay_recipe(source, recipe, discovery.tilting, discovery.goal()).ok()?;
    match DerivedEquivalenceEdge::recover(tilting, &limits.target) {
        Ok(DerivedEquivalenceEdgeOutcome::Certified(edge)) => Some(edge),
        _ => None,
    }
}

impl DerivedClassification {
    /// Rechecks every class, merge, and separation without discovery.
    ///
    /// The classes must partition the family, ordered by representative,
    /// and the merges of each class must form a spanning tree of its
    /// members. Each merge replays its recipe from the regular complex of
    /// its source member, recovers the target, and checks the isomorphism
    /// onto its member. Each separation recomputes its witness. Every pair
    /// of classes must be separated or unresolved exactly once.
    pub fn verify(&self) -> bool {
        let members = self.classes.iter().map(|class| &class.members[..]);
        partitions(self.family.len(), members)
            && self.classes.iter().all(|class| self.class_holds(class))
            && covers_pairs(
                self.classes.len(),
                self.separations.iter().map(|separation| separation.classes),
                &self.unresolved,
            )
            && self
                .separations
                .iter()
                .all(|separation| self.separation_holds(separation))
    }

    /// Whether the merges form a spanning tree of `class` and each replays.
    fn class_holds(&self, class: &DerivedClass) -> bool {
        let edges = class
            .merges
            .iter()
            .map(|merge| (merge.source, merge.member));
        spanning_tree(&class.members, edges)
            && class.merges.iter().all(|merge| self.merge_holds(merge))
    }

    fn merge_holds(&self, merge: &DerivedMerge) -> bool {
        let_or_false!(Some(source) = self.family.get(merge.source));
        let_or_false!(Some(member) = self.family.get(merge.member));
        let reached = match merge.path.steps() {
            [] => merge.recipe.is_empty() && same(merge.path.source(), source),
            [_] => same(merge.path.source(), source) && self.replays(merge, source),
            _ => false,
        };
        reached
            && same(merge.isomorphism.source(), merge.path.target())
            && same(merge.isomorphism.target(), member)
            && merge.isomorphism.verify()
    }

    /// Whether the recipe reaches a tilting complex whose recovered target
    /// is the end of the stored path.
    fn replays(&self, merge: &DerivedMerge, source: &Arc<Algebra>) -> bool {
        let_or_false!(Some(edge) = replay_edge(source, &merge.recipe, &self.limits));
        same(edge.target(), merge.path.target())
    }

    fn separation_holds(&self, separation: &ClassSeparation) -> bool {
        let (left, right) = separation.members;
        let (left_class, right_class) = separation.classes;
        let witness = &separation.witness;
        self.classes[left_class].members.contains(&left)
            && self.classes[right_class].members.contains(&right)
            && same(witness.left(), &self.family[left])
            && same(witness.right(), &self.family[right])
            && witness.limits() == self.limits.invariants
            && witness.verify()
    }
}

use std::collections::BTreeMap;

use crate::equivalence_discovery::{IncompleteEquivalenceGraph, discover_equivalences};
use crate::equivalence_edge::{DerivedEquivalenceEdge, DerivedEquivalenceEdgeOutcome};
use crate::tilting_complex::CertifiedTiltingComplex;

use super::*;

/// [`first_difference`] of every pair of members, and the groups: the
/// connected components of the pairs it does not separate.
pub(super) struct SeparationTable {
    size: usize,
    kinds: Vec<Option<DerivedInvariantKind>>,
    group_of: Vec<usize>,
    groups: Vec<Vec<usize>>,
}

impl SeparationTable {
    pub(super) fn new(invariants: &[DerivedInvariants]) -> SeparationTable {
        let size = invariants.len();
        let mut kinds = vec![None; size * size];
        for left in 0..size {
            for right in 0..left {
                let kind = first_difference(&invariants[left], &invariants[right]);
                kinds[left * size + right] = kind;
                kinds[right * size + left] = kind;
            }
        }
        let (group_of, groups) =
            components(size, |left, right| kinds[left * size + right].is_none());
        SeparationTable {
            size,
            kinds,
            group_of,
            groups,
        }
    }

    pub(super) fn groups(&self) -> Vec<Vec<usize>> {
        self.groups.clone()
    }

    /// The least `(kind, left, right)` over `left` in `lefts` and `right` in
    /// `rights` whose invariants differ.
    fn separation(
        &self,
        lefts: &[usize],
        rights: &[usize],
    ) -> Option<(DerivedInvariantKind, usize, usize)> {
        let pairs = lefts
            .iter()
            .flat_map(|&left| rights.iter().map(move |&right| (left, right)));
        pairs
            .filter_map(|(left, right)| Some((self.kinds[left * self.size + right]?, left, right)))
            .min()
    }
}

/// The groups of [`SeparationTable::groups`] without a table of member pairs.
///
/// Members with equal `keys` must have equal readings. The pairs are then
/// compared once per pair of distinct keys, so memory stays linear in the
/// family and duplicates cost no comparisons.
pub(super) fn groups_by_key<K: std::hash::Hash + Eq>(
    invariants: &[DerivedInvariants],
    keys: &[K],
) -> Vec<Vec<usize>> {
    let mut index = rustc_hash::FxHashMap::default();
    let mut representatives = Vec::new();
    let key_of: Vec<usize> = keys
        .iter()
        .enumerate()
        .map(|(member, key)| {
            *index.entry(key).or_insert_with(|| {
                representatives.push(member);
                representatives.len() - 1
            })
        })
        .collect();
    let (group_of, groups) = components(representatives.len(), |left, right| {
        let pair = (representatives[left], representatives[right]);
        first_difference(&invariants[pair.0], &invariants[pair.1]).is_none()
    });
    let mut members = vec![Vec::new(); groups.len()];
    for (member, &key) in key_of.iter().enumerate() {
        members[group_of[key]].push(member);
    }
    members
}

/// The connected components of `joined` on `0..size`, each increasing and
/// ordered by least member, with the component index of each member.
fn components(size: usize, joined: impl Fn(usize, usize) -> bool) -> (Vec<usize>, Vec<Vec<usize>>) {
    let mut group_of = vec![usize::MAX; size];
    let mut groups = Vec::new();
    for start in 0..size {
        if group_of[start] != usize::MAX {
            continue;
        }
        let id = groups.len();
        group_of[start] = id;
        let mut group = vec![start];
        let mut position = 0;
        while let Some(&current) = group.get(position) {
            for (other, slot) in group_of.iter_mut().enumerate() {
                if *slot == usize::MAX && joined(current, other) {
                    *slot = id;
                    group.push(other);
                }
            }
            position += 1;
        }
        group.sort_unstable();
        groups.push(group);
    }
    (group_of, groups)
}

/// The fixed inputs of every walk.
pub(super) struct Context<'a> {
    pub(super) index: &'a FamilyIndex,
    pub(super) table: &'a SeparationTable,
    pub(super) limits: &'a ClassificationLimits,
}

/// What one walk vertex added.
enum Examined {
    TargetCut,
    Unmatched,
    Known,
    Merged,
}

/// The classes found so far, as a union-find forest whose roots are the
/// least members, with the merges that joined them.
pub(super) struct Partition {
    parent: Vec<usize>,
    merges: Vec<DerivedMerge>,
}

impl Partition {
    pub(super) fn new(size: usize) -> Partition {
        Partition {
            parent: (0..size).collect(),
            merges: Vec::new(),
        }
    }

    fn root(&self, mut member: usize) -> usize {
        while self.parent[member] != member {
            member = self.parent[member];
        }
        member
    }

    /// The members of every class in the group of `member`, by root. A class
    /// never leaves its group: [`Self::join`] refuses separated classes.
    fn group_classes(&self, table: &SeparationTable, member: usize) -> BTreeMap<usize, Vec<usize>> {
        let mut classes: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
        for &other in &table.groups[table.group_of[member]] {
            classes.entry(self.root(other)).or_default().push(other);
        }
        classes
    }

    /// Whether another class in the group of `member` is neither merged with
    /// nor separated from the class of `member`.
    pub(super) fn has_open_partner(&self, table: &SeparationTable, member: usize) -> bool {
        let classes = self.group_classes(table, member);
        let own = &classes[&self.root(member)];
        classes
            .values()
            .any(|other| other != own && table.separation(own, other).is_none())
    }

    /// Joins the classes of `merge.source` and `merge.member`, which must be
    /// distinct. Errors when an invariant separates them.
    fn join(
        &mut self,
        table: &SeparationTable,
        merge: DerivedMerge,
        vertex: Option<usize>,
    ) -> Result<(), ClassificationError> {
        let (left, right) = (self.root(merge.source), self.root(merge.member));
        let members = |root| -> Vec<usize> {
            (0..self.parent.len())
                .filter(|&m| self.root(m) == root)
                .collect()
        };
        if let Some((kind, one, other)) = table.separation(&members(left), &members(right)) {
            return Err(ClassificationError::Contradiction {
                source: merge.source,
                vertex,
                member: merge.member,
                separated: (one, other),
                kind,
            });
        }
        self.parent[left.max(right)] = left.min(right);
        self.merges.push(merge);
        Ok(())
    }

    /// Merges the duplicate `member` into `original` by the identity path.
    pub(super) fn merge_duplicate(
        &mut self,
        table: &SeparationTable,
        index: &FamilyIndex,
        original: usize,
        member: usize,
    ) -> Result<(), ClassificationError> {
        let merge = DerivedMerge {
            source: original,
            member,
            recipe: Vec::new(),
            path: DerivedEquivalencePath::identity(&index.family()[original]),
            isomorphism: index.duplicate_isomorphism(original, member),
        };
        self.join(table, merge, None)
    }

    /// Walks from `member`, then recovers and matches the target of every
    /// tilting vertex until cancellation. A silting vertex that is not
    /// tilting has no target and is skipped.
    pub(super) fn walk(
        &mut self,
        context: &Context,
        member: usize,
        control: &ComputationControl,
    ) -> Result<MutationWalk, ClassificationError> {
        let algebra = &context.index.family()[member];
        let graph = discover_equivalences(algebra, context.limits.discovery, control)
            .map_err(|error| ClassificationError::Discovery { member, error })?;
        let mut record = MutationWalk {
            member,
            stop: graph.stop().clone(),
            vertices: graph.vertices().len(),
            blocked: graph.blocked().len(),
            examined: 0,
            target_cuts: 0,
            unmatched: 0,
            merges: 0,
        };
        for vertex in 0..graph.vertices().len() {
            if control.is_cancelled() {
                break;
            }
            let Some(tilting) = graph.vertices()[vertex].to_tilting() else {
                continue;
            };
            record.examined += 1;
            match self.examine(context, &graph, (member, vertex), tilting)? {
                Examined::TargetCut => record.target_cuts += 1,
                Examined::Unmatched => record.unmatched += 1,
                Examined::Known => {}
                Examined::Merged => record.merges += 1,
            }
        }
        Ok(record)
    }

    fn examine(
        &mut self,
        context: &Context,
        graph: &IncompleteEquivalenceGraph,
        (member, vertex): (usize, usize),
        tilting: CertifiedTiltingComplex,
    ) -> Result<Examined, ClassificationError> {
        let limits = &context.limits.target;
        let outcome = DerivedEquivalenceEdge::recover(tilting, limits).map_err(|error| {
            ClassificationError::Target {
                member,
                vertex,
                error,
            }
        })?;
        let DerivedEquivalenceEdgeOutcome::Certified(edge) = outcome else {
            return Ok(Examined::TargetCut);
        };
        let Some((matched, isomorphism)) = context.index.match_member(edge.target()) else {
            return Ok(Examined::Unmatched);
        };
        if self.root(member) == self.root(matched) {
            return Ok(Examined::Known);
        }
        let merge = DerivedMerge {
            source: member,
            member: matched,
            recipe: recipe(graph, vertex),
            path: edge.path(),
            isomorphism,
        };
        self.join(context.table, merge, Some(vertex))?;
        Ok(Examined::Merged)
    }
}

/// The mutations from the regular complex to `vertex`, read backward along
/// the edge that first reached each vertex. That edge starts at an earlier
/// vertex, so the walk back ends at the root `0`. The steps can pass through
/// silting vertices.
fn recipe(graph: &IncompleteEquivalenceGraph, mut vertex: usize) -> Vec<ArtifactMutation> {
    let mut steps = Vec::new();
    while vertex != 0 {
        let edge = graph
            .edges()
            .iter()
            .find(|edge| edge.target() == vertex)
            .expect("every stored vertex but the root has a discovering edge");
        steps.push(ArtifactMutation::new(edge.direction(), edge.summand()));
        vertex = edge.source();
    }
    steps.reverse();
    steps
}

type Settled = (Vec<DerivedClass>, Vec<ClassSeparation>, Vec<UnresolvedPair>);

/// The final classes with their merges, and every pair of classes either
/// separated or unresolved.
pub(super) fn assemble(
    partition: Partition,
    table: &SeparationTable,
    invariants: &[DerivedInvariants],
    walks: &[MutationWalk],
) -> Settled {
    let mut class_of = vec![usize::MAX; partition.parent.len()];
    let mut classes: Vec<DerivedClass> = Vec::new();
    for member in 0..partition.parent.len() {
        let root = partition.root(member);
        if root == member {
            class_of[root] = classes.len();
            classes.push(DerivedClass {
                members: Vec::new(),
                merges: Vec::new(),
            });
        }
        classes[class_of[root]].members.push(member);
    }
    let roots: Vec<usize> = (0..partition.parent.len())
        .map(|m| partition.root(m))
        .collect();
    for merge in partition.merges {
        classes[class_of[roots[merge.source]]].merges.push(merge);
    }
    let (mut separations, mut unresolved) = (Vec::new(), Vec::new());
    for left in 0..classes.len() {
        for right in left + 1..classes.len() {
            let pair = (&classes[left].members, &classes[right].members);
            match table.separation(pair.0, pair.1) {
                Some(found) => separations.push(separation((left, right), found, invariants)),
                None => unresolved.push(open_pair((left, right), pair, walks)),
            }
        }
    }
    (classes, separations, unresolved)
}

fn separation(
    classes: (usize, usize),
    (kind, left, right): (DerivedInvariantKind, usize, usize),
    invariants: &[DerivedInvariants],
) -> ClassSeparation {
    let witness = DerivedInequivalenceWitness::new(&invariants[left], &invariants[right], kind)
        .expect("a separating kind of one family gives a witness; library bug");
    ClassSeparation {
        classes,
        members: (left, right),
        witness,
    }
}

/// The unresolved pair `classes` with every walk from a member of either
/// class, given as `(lefts, rights)`.
pub(super) fn open_pair(
    classes: (usize, usize),
    (lefts, rights): (&Vec<usize>, &Vec<usize>),
    walks: &[MutationWalk],
) -> UnresolvedPair {
    let walks = walks
        .iter()
        .enumerate()
        .filter(|(_, walk)| lefts.contains(&walk.member) || rights.contains(&walk.member))
        .map(|(position, _)| position)
        .collect();
    UnresolvedPair { classes, walks }
}

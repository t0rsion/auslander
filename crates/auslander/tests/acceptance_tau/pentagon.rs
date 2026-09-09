use std::collections::BTreeSet;

use auslander::mutation::ExchangeShape;
use auslander::taugraph::{ClosedSupportTauTiltingGraph, SlotRecord};

use super::checks::key;
use super::fixtures::cached;

/// What the A_2 walk must produce at slot `(pair, summand)`.
enum Slot {
    /// No left mutation: `X_j` lies in `Fac(M/X_j)`.
    Fac,
    /// A left mutation onto the pair with this key, of this shape.
    To((Vec<Vec<usize>>, Vec<u32>), ExchangeShape),
}

type PairKey = (Vec<Vec<usize>>, Vec<u32>);

struct PentagonKeys {
    regular: PairKey,
    other_tilting: PairKey,
    s1_pair: PairKey,
    s0_pair: PairKey,
    zero_pair: PairKey,
}

impl PentagonKeys {
    fn new() -> Self {
        Self {
            regular: (vec![vec![0, 1], vec![1, 1]], Vec::new()),
            other_tilting: (vec![vec![1, 0], vec![1, 1]], Vec::new()),
            s1_pair: (vec![vec![0, 1]], vec![0]),
            s0_pair: (vec![vec![1, 0]], vec![1]),
            zero_pair: (Vec::new(), vec![0, 1]),
        }
    }

    fn all(&self) -> BTreeSet<PairKey> {
        BTreeSet::from([
            self.regular.clone(),
            self.other_tilting.clone(),
            self.s1_pair.clone(),
            self.s0_pair.clone(),
            self.zero_pair.clone(),
        ])
    }

    fn slot(&self, here: &PairKey, summand: &[usize]) -> Slot {
        if *here == self.regular {
            return self.regular_slot(summand);
        }
        if *here == self.other_tilting {
            return self.other_tilting_slot(summand);
        }
        if *here == self.s1_pair {
            return self.s1_slot(summand);
        }
        if *here == self.s0_pair {
            return self.s0_slot(summand);
        }
        panic!("A_2 has no slot {summand:?} at {here:?}")
    }

    fn regular_slot(&self, summand: &[usize]) -> Slot {
        match summand {
            [0, 1] => Slot::To(
                self.other_tilting.clone(),
                ExchangeShape::ReplacedByModule { multiplicity: 1 },
            ),
            [1, 1] => Slot::To(
                self.s1_pair.clone(),
                ExchangeShape::MovesToProjective { vertex: 0 },
            ),
            _ => panic!("the regular A_2 pair has no slot {summand:?}"),
        }
    }

    fn other_tilting_slot(&self, summand: &[usize]) -> Slot {
        match summand {
            [1, 0] => Slot::Fac,
            [1, 1] => Slot::To(
                self.s0_pair.clone(),
                ExchangeShape::MovesToProjective { vertex: 1 },
            ),
            _ => panic!("the second A_2 tilting pair has no slot {summand:?}"),
        }
    }

    fn s1_slot(&self, summand: &[usize]) -> Slot {
        assert_eq!(summand, [0, 1]);
        Slot::To(
            self.zero_pair.clone(),
            ExchangeShape::MovesToProjective { vertex: 1 },
        )
    }

    fn s0_slot(&self, summand: &[usize]) -> Slot {
        assert_eq!(summand, [1, 0]);
        Slot::To(
            self.zero_pair.clone(),
            ExchangeShape::MovesToProjective { vertex: 0 },
        )
    }
}

fn assert_pentagon_slot(
    graph: &ClosedSupportTauTiltingGraph,
    here: &PairKey,
    slot: usize,
    expected: Slot,
) -> bool {
    let record = &graph
        .vertices()
        .iter()
        .find(|vertex| key(vertex.pair()) == *here)
        .expect("the pentagon key is present")
        .slots()[slot];
    match (record, expected) {
        (SlotRecord::NoLeftMutation(fac), Slot::Fac) => {
            assert!(fac.verify(), "the Fac witness failed its recheck");
            assert_eq!(fac.module().dim_vector(), [1, 1]);
            assert_eq!(fac.summand().dim_vector(), [1, 0]);
            assert_eq!(fac.image_dims(), [1, 0]);
            true
        }
        (SlotRecord::LeftMutation { mutation }, Slot::To(target, shape)) => {
            let edge = &graph.mutations()[*mutation];
            assert_eq!(edge.slot(), slot);
            assert_eq!(key(graph.vertices()[edge.target()].pair()), target);
            assert_eq!(*edge.mutation().shape(), shape);
            assert!(edge.mutation().verify());
            assert!(edge.endpoint().verify());
            false
        }
        _ => panic!("A_2 slot {slot} of {here:?} has the wrong outcome"),
    }
}

fn assert_pentagon(graph: &ClosedSupportTauTiltingGraph, keys: &PentagonKeys) {
    assert_eq!(graph.len(), 5);
    assert_eq!(graph.mutations().len(), 5);
    assert_eq!(graph.pairs().map(key).collect::<BTreeSet<_>>(), keys.all());
    assert_eq!(key(graph.vertices()[0].pair()), keys.regular);
    assert!(graph.mutations().iter().all(|edge| edge.target() != 0));

    let mut fac_slots = 0;
    for vertex in graph.vertices() {
        let here = key(vertex.pair());
        let summands = vertex.pair().module().summands();
        assert_eq!(vertex.slots().len(), summands.len());
        for (slot, summand) in summands.iter().enumerate() {
            fac_slots += usize::from(assert_pentagon_slot(
                graph,
                &here,
                slot,
                keys.slot(&here, summand.module().dim_vector()),
            ));
        }
    }
    assert_eq!(fac_slots, 1);
}

/// The A_2 pentagon, computed by hand and checked slot by slot.
///
/// `A = kQ` for `Q: 0 -> 1`, so `P_0 = [1, 1]`, `P_1 = S_1 = [0, 1]`, and
/// `S_0 = [1, 0]`. The five pairs:
///
/// - `(P_0 + P_1, 0)`, the regular module.
/// - `(P_0 + S_0, 0)`, the other tilting module.
/// - `(S_1, {0})`, since `Hom(P_0, S_1) = (S_1)_0 = 0`.
/// - `(S_0, {1})`, since `Hom(P_1, S_0) = (S_0)_1 = 0`.
/// - `(0, {0, 1})`.
///
/// The six module slots, each decided by the `Fac` test of design section 8:
///
/// - `(P_0 + P_1, 0)` at `P_1`: `Fac(P_0) = {P_0, S_0, 0}` misses `S_1`, so
///   the left mutation exists. The minimal left `add(P_0)`-approximation of
///   `S_1` is the socle inclusion `S_1 -> P_0` with cokernel `S_0`, giving
///   `(P_0 + S_0, 0)`.
/// - `(P_0 + P_1, 0)` at `P_0`: `Fac(P_1) = {S_1, 0}` misses `P_0`, and
///   `Hom(P_0, P_1) = (P_1)_0 = 0`, so the approximation is `P_0 -> 0`, the
///   support loses vertex 0, and the target is `(S_1, {0})`.
/// - `(P_0 + S_0, 0)` at `S_0`: `S_0 = P_0 / rad P_0` lies in `Fac(P_0)`, so
///   this is the one slot with a `FacWitness` and no outgoing edge.
/// - `(P_0 + S_0, 0)` at `P_0`: `Fac(S_0) = {S_0, 0}` misses `P_0`. The
///   minimal left `add(S_0)`-approximation of `P_0` is the top projection, so
///   the cokernel is zero, the support loses vertex 1, and the target is
///   `(S_0, {1})`.
/// - `(S_1, {0})` at `S_1` and `(S_0, {1})` at `S_0`: `M / X_j = 0` and
///   `Fac(0) = {0}`, so both approximations are `X_j -> 0` and both targets
///   are `(0, {0, 1})`.
/// - `(0, {0, 1})` has no module slot.
///
/// Five edges on five vertices, and the undirected graph is the pentagon.
#[test]
fn the_a2_pentagon_matches_the_hand_computation() {
    let keys = PentagonKeys::new();
    for entry in cached("linear_an(2)") {
        let graph = entry.graph.as_ref().expect("A_2 is in the always-on tier");
        assert_pentagon(graph, &keys);
    }
}

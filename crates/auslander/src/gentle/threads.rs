use crate::quiver::ArrowId;

use super::shape::{Kind, Shape, Sign};

/// A permitted or forbidden thread of a gentle presentation, with its signs.
///
/// A nontrivial permitted thread is a maximal path with no relation `b·c` in
/// it. A nontrivial forbidden thread is a maximal path of distinct arrows
/// whose consecutive pairs are all relations. The trivial threads are the
/// trivial paths `e_v` that section 2.2 of Avella-Alaminos and Geiss selects.
/// That section assumes an arrow exists. The quiver of `k` has none, and it
/// gets two trivial threads of each kind, so `A_1` has `φ = [(2, 0)]`.
///
/// `sigma` is `σ` of the first arrow and `epsilon` is `ε` of the last one.
/// For a trivial thread both follow the same section.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct GentleThread {
    start: u32,
    end: u32,
    arrows: Vec<ArrowId>,
    sigma: Sign,
    epsilon: Sign,
}

impl GentleThread {
    accessor_methods! {
        /// The first vertex.
        pub start() -> u32 = |this| this.start;
        /// The last vertex.
        pub end() -> u32 = |this| this.end;
        /// The arrows in path order, first arrow first. Empty for a trivial thread.
        pub arrows() -> &[ArrowId] = |this| &this.arrows;
        /// The number of arrows.
        pub length() -> usize = |this| this.arrows.len();
        /// Whether the thread is a trivial path.
        pub is_trivial() -> bool = |this| this.arrows.is_empty();
        /// The value `σ(H)`.
        pub sigma() -> Sign = |this| this.sigma;
        /// The value `ε(H)`.
        pub epsilon() -> Sign = |this| this.epsilon;
    }
}

/// The threads of one gentle shape.
#[derive(Clone, Debug)]
pub(crate) struct Threads {
    pub(crate) permitted: Vec<GentleThread>,
    pub(crate) forbidden: Vec<GentleThread>,
    pub(crate) cycles: Vec<Vec<ArrowId>>,
}

impl Threads {
    pub(crate) fn new(shape: &Shape) -> Threads {
        let forbidden = threads_of(shape, Kind::Forbidden);
        let cycles = full_relation_cycles(shape, &forbidden);
        Threads {
            permitted: threads_of(shape, Kind::Permitted),
            forbidden,
            cycles,
        }
    }
}

/// Every thread of kind `kind`, in order of its first slot.
///
/// A thread starts at vertex `v` with `σ = s` exactly when the incoming slot
/// `kind.partner(s)` at `v` is empty. A filled outgoing slot `s` starts a
/// nontrivial thread. An empty one is the trivial thread at `v`. Each empty
/// incoming slot therefore starts one thread of each kind.
fn threads_of(shape: &Shape, kind: Kind) -> Vec<GentleThread> {
    let mut threads = Vec::new();
    for vertex in 0..shape.vertices() {
        for sign in [Sign::Plus, Sign::Minus] {
            let partner = kind.partner(sign);
            if shape.incoming(vertex, partner).is_some() {
                continue;
            }
            threads.push(match shape.outgoing(vertex, sign) {
                Some(first) => follow(shape, kind, first),
                None => GentleThread {
                    start: vertex,
                    end: vertex,
                    arrows: Vec::new(),
                    sigma: sign,
                    epsilon: partner,
                },
            });
        }
    }
    threads
}

/// The thread of kind `kind` that starts with `first`.
///
/// A permitted cycle would make the algebra infinite dimensional, and a
/// forbidden chain that starts at an empty slot cannot enter a cycle. So the
/// walk ends within the arrow count.
fn follow(shape: &Shape, kind: Kind, first: ArrowId) -> GentleThread {
    let mut arrows = vec![first];
    let mut last = first;
    while let Some(next) = shape.successor(kind, last) {
        assert!(
            arrows.len() < shape.arrows().len(),
            "a {kind:?} thread repeats an arrow; library bug"
        );
        arrows.push(next);
        last = next;
    }
    GentleThread {
        start: shape.source(first),
        end: shape.target(last),
        arrows,
        sigma: shape.sigma(first),
        epsilon: shape.epsilon(last),
    }
}

/// The oriented cycles whose consecutive pairs, the closing pair included,
/// are all relations. Each starts at its least arrow.
fn full_relation_cycles(shape: &Shape, forbidden: &[GentleThread]) -> Vec<Vec<ArrowId>> {
    let mut used = vec![false; shape.arrows().len()];
    for arrow in forbidden.iter().flat_map(GentleThread::arrows) {
        used[arrow.index()] = true;
    }
    let mut cycles = Vec::new();
    for first in 0..used.len() {
        if used[first] {
            continue;
        }
        let mut cycle = Vec::new();
        let mut arrow = ArrowId(first as u32);
        while !used[arrow.index()] {
            used[arrow.index()] = true;
            cycle.push(arrow);
            arrow = shape
                .successor(Kind::Forbidden, arrow)
                .expect("an arrow outside every open forbidden thread lies on a cycle");
        }
        cycles.push(cycle);
    }
    cycles
}

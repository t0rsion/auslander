use super::shape::{Shape, Sign};
use super::threads::GentleThread;

/// One end of the arc of a vertex: the vertex and the sign of its position.
type End = (u32, Sign);

/// A traversal of the arc of a vertex: the vertex and the sign of the end it
/// starts from.
type Step = (u32, Sign);

/// The ribbon graph of a gentle presentation: one node per permitted thread
/// and one edge per vertex.
///
/// Each permitted thread is a marked point on the boundary of the surface
/// model, and each vertex is an arc. The arcs at one marked point, in
/// counterclockwise order, are the vertices of the thread in path order. See
/// `docs/gentle-derived-invariant.md`, section 2.
///
/// The end `(v, s)` is the thread position that leaves `v` through the
/// outgoing slot `s`, filled or not. Every end lies at exactly one position
/// of one thread.
pub(super) struct RibbonGraph {
    /// The thread and position of the end `(v, s)`, at index `slot(v, s)`.
    ends: Vec<(usize, usize)>,
    /// The ends at each thread.
    incident: Vec<Vec<End>>,
}

/// A closed walk, as the steps it takes in order.
pub(super) struct Cycle(Vec<Step>);

impl RibbonGraph {
    pub(super) fn new(shape: &Shape, permitted: &[GentleThread]) -> RibbonGraph {
        let vertices = shape.vertices() as usize;
        let mut ends = vec![None; 2 * vertices];
        let mut incident = Vec::with_capacity(permitted.len());
        for (thread, path) in permitted.iter().enumerate() {
            let positions = thread_ends(shape, path);
            for (position, &end) in positions.iter().enumerate() {
                let entry = &mut ends[slot(end)];
                assert!(
                    entry.is_none(),
                    "two thread positions share an end; library bug"
                );
                *entry = Some((thread, position));
            }
            incident.push(positions);
        }
        let ends = ends
            .into_iter()
            .map(|entry| entry.expect("every end lies on a permitted thread; library bug"))
            .collect();
        RibbonGraph { ends, incident }
    }

    fn position(&self, end: End) -> usize {
        self.ends[slot(end)].1
    }

    fn node(&self, end: End) -> usize {
        self.ends[slot(end)].0
    }

    /// The fundamental cycles of the breadth-first spanning tree from thread 0.
    ///
    /// Each visits every node at most once, so each is a simple closed curve
    /// on the surface. Together they form a basis of its first homology.
    pub(super) fn fundamental_cycles(&self) -> Vec<Cycle> {
        let parent = self.spanning_tree();
        let vertices = (self.ends.len() / 2) as u32;
        (0..vertices)
            .filter(|&vertex| {
                parent[self.node((vertex, Sign::Minus))] != Some((vertex, Sign::Plus))
                    && parent[self.node((vertex, Sign::Plus))] != Some((vertex, Sign::Minus))
            })
            .map(|vertex| self.close(&parent, vertex))
            .collect()
    }

    /// The step that reaches each node from its parent, `None` at the root.
    fn spanning_tree(&self) -> Vec<Option<Step>> {
        let mut parent = vec![None; self.incident.len()];
        let mut seen = vec![false; self.incident.len()];
        seen[0] = true;
        let mut queue = vec![0];
        let mut next = 0;
        while let Some(&node) = queue.get(next) {
            next += 1;
            for &(vertex, sign) in &self.incident[node] {
                let child = self.node((vertex, sign.negated()));
                if !seen[child] {
                    seen[child] = true;
                    parent[child] = Some((vertex, sign));
                    queue.push(child);
                }
            }
        }
        assert!(
            seen.iter().all(|&s| s),
            "the ribbon graph is disconnected; library bug"
        );
        parent
    }

    /// The cycle that crosses the arc of `vertex` from `+` to `-` and returns
    /// through the tree.
    fn close(&self, parent: &[Option<Step>], vertex: u32) -> Cycle {
        let mut back = self.to_root(parent, self.node((vertex, Sign::Minus)));
        let mut out = self.to_root(parent, self.node((vertex, Sign::Plus)));
        while !back.is_empty() && back.last() == out.last() {
            back.pop();
            out.pop();
        }
        let mut steps = vec![(vertex, Sign::Plus)];
        steps.extend(back);
        steps.extend(out.iter().rev().map(|&(v, s)| (v, s.negated())));
        Cycle(steps)
    }

    /// The steps from `node` up to the root.
    fn to_root(&self, parent: &[Option<Step>], mut node: usize) -> Vec<Step> {
        let mut steps = Vec::new();
        while let Some((vertex, sign)) = parent[node] {
            steps.push((vertex, sign.negated()));
            node = self.node((vertex, sign));
        }
        steps
    }

    /// The turns of `cycle`: at each node, the end it arrives by and the end
    /// it leaves by.
    fn turns(&self, cycle: &Cycle) -> Vec<(usize, End, End)> {
        let steps = &cycle.0;
        (0..steps.len())
            .map(|index| {
                let (vertex, sign) = steps[index];
                let arrive = (vertex, sign.negated());
                let leave = steps[(index + 1) % steps.len()];
                assert_eq!(
                    self.node(arrive),
                    self.node(leave),
                    "a cycle step does not continue at its node; library bug"
                );
                (self.node(arrive), arrive, leave)
            })
            .collect()
    }

    /// The winding number: turns to a later position count `+1`, turns to an
    /// earlier one `-1`.
    ///
    /// Amiot, Plamondon, and Schroll, Proposition 1.20 (3) and (4), and the
    /// proof of their Theorem 4.1.
    pub(super) fn winding(&self, cycle: &Cycle) -> i64 {
        self.turns(cycle)
            .iter()
            .map(|&(_, arrive, leave)| {
                let (from, to) = (self.position(arrive), self.position(leave));
                assert_ne!(from, to, "a cycle turns back on one end; library bug");
                if to > from { 1 } else { -1 }
            })
            .sum()
    }

    /// The intersection matrix of `cycles`.
    ///
    /// Panics when the matrix is not antisymmetric. The two entries of a
    /// pair come from different drawings, so that is a library bug.
    pub(super) fn pairing(&self, cycles: &[Cycle]) -> Vec<Vec<i64>> {
        let turns: Vec<_> = cycles.iter().map(|cycle| self.turns(cycle)).collect();
        let size = cycles.len();
        let mut matrix = vec![vec![0; size]; size];
        for (row, left) in turns.iter().enumerate() {
            for (column, right) in turns.iter().enumerate() {
                if row != column {
                    matrix[row][column] = self.intersection(left, right);
                }
            }
        }
        let antisymmetric =
            (0..size).all(|row| (0..row).all(|column| matrix[row][column] == -matrix[column][row]));
        assert!(
            antisymmetric,
            "the intersection pairing is not antisymmetric; library bug"
        );
        matrix
    }

    /// The algebraic intersection number of two cycles given by their turns.
    ///
    /// The first cycle runs on the center line of each arc. The second runs on
    /// a parallel copy, left of the arc oriented from `+` to `-`: half a
    /// position later at the `+` end and half a position earlier at the `-`
    /// end. The curves cross only near marked points, once for each pair of
    /// turns at one node whose endpoints interleave.
    fn intersection(&self, left: &[(usize, End, End)], right: &[(usize, End, End)]) -> i64 {
        let mut total = 0;
        for &(node, arrive, leave) in left {
            let (a, b) = (self.centered(arrive), self.centered(leave));
            for &(_, into, out) in right.iter().filter(|turn| turn.0 == node) {
                total += crossing(a, b, self.shifted(into), self.shifted(out));
            }
        }
        total
    }

    fn centered(&self, end: End) -> i64 {
        2 * self.position(end) as i64
    }

    fn shifted(&self, end: End) -> i64 {
        self.centered(end) + if end.1 == Sign::Plus { 1 } else { -1 }
    }
}

/// The sign of the crossing of a chord from `a` to `b` with a chord from
/// `c` to `d`, or 0 when the chords do not interleave.
fn crossing(a: i64, b: i64, c: i64, d: i64) -> i64 {
    let inside = |x: i64| a.min(b) < x && x < a.max(b);
    let direction = (b - a).signum();
    match (inside(c), inside(d)) {
        (true, false) => direction,
        (false, true) => -direction,
        _ => 0,
    }
}

/// The ends of the vertices of `thread`, in path order.
///
/// An inner vertex leaves through the slot of the next arrow. The last vertex
/// leaves through the empty slot `-ε` of the last arrow, where the thread
/// stops. A trivial thread occupies the slot `σ` it starts in.
fn thread_ends(shape: &Shape, thread: &GentleThread) -> Vec<End> {
    let mut ends: Vec<End> = thread
        .arrows()
        .iter()
        .map(|&arrow| (shape.source(arrow), shape.sigma(arrow)))
        .collect();
    let last = match thread.arrows().last() {
        Some(_) => thread.epsilon().negated(),
        None => thread.sigma(),
    };
    ends.push((thread.end(), last));
    ends
}

fn slot((vertex, sign): End) -> usize {
    2 * vertex as usize + usize::from(sign == Sign::Minus)
}

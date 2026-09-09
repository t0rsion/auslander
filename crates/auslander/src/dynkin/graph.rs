use rustc_hash::FxHashMap;

use crate::quiver::Quiver;

use super::types::{DynkinType, EuclideanType};

/// The number of vertices reachable from `start` in a finite adjacency list.
pub(crate) fn reachable_count(neighbours: &[Vec<usize>], start: usize) -> usize {
    if start >= neighbours.len() {
        return 0;
    }
    let mut seen = vec![false; neighbours.len()];
    let mut stack = vec![start];
    seen[start] = true;
    let mut count = 1;
    while let Some(vertex) = stack.pop() {
        for &next in &neighbours[vertex] {
            if !seen[next] {
                seen[next] = true;
                count += 1;
                stack.push(next);
            }
        }
    }
    count
}

/// The Dynkin type of the quiver's underlying graph, or `None` when that graph
/// is not a Dynkin diagram.
///
/// The type depends only on the underlying graph, never on the orientation,
/// and never on an ideal of relations, so this takes a [`Quiver`]. Pass
/// `algebra.quiver()` to classify an algebra's quiver.
///
/// ```
/// use auslander::dynkin::{DynkinType, dynkin_type};
/// use auslander::quiver::Quiver;
/// let q = Quiver::new(4, &[(0, 2), (1, 2), (3, 2)]).unwrap();
/// assert_eq!(dynkin_type(&q), Some(DynkinType::D(4)));
/// ```
pub fn dynkin_type(quiver: &Quiver) -> Option<DynkinType> {
    dynkin_shape(tree(quiver)?.shape()?)
}

fn dynkin_shape(shape: Shape) -> Option<DynkinType> {
    match shape {
        Shape::Path(n) => Some(DynkinType::A(n)),
        Shape::Star(arms) => dynkin_star(&arms),
        Shape::DoubleFork { .. } => None,
    }
}

fn dynkin_star(arms: &[usize]) -> Option<DynkinType> {
    if let [1, 1, length] = arms {
        return Some(DynkinType::D(length + 3));
    }
    [
        ([1, 2, 2], DynkinType::E6),
        ([1, 2, 3], DynkinType::E7),
        ([1, 2, 4], DynkinType::E8),
    ]
    .iter()
    .find_map(|(expected, kind)| (arms == expected).then_some(*kind))
}

enum EuclideanCase {
    Reject,
    MultipleEdge,
    Cycle,
    Tree,
}

fn euclidean_case(graph: &Underlying) -> EuclideanCase {
    if !euclidean_candidate(graph) {
        EuclideanCase::Reject
    } else if graph.max_multiplicity() > 1 {
        EuclideanCase::MultipleEdge
    } else if graph.num_edges() == graph.num_vertices {
        EuclideanCase::Cycle
    } else {
        EuclideanCase::Tree
    }
}

fn euclidean_candidate(graph: &Underlying) -> bool {
    graph.loops == 0 && graph.num_vertices > 0 && graph.is_connected()
}

fn multiple_edge_euclidean(graph: &Underlying) -> Option<EuclideanType> {
    (graph.num_vertices == 2 && graph.multiplicity.len() == 1 && graph.num_edges() == 2)
        .then_some(EuclideanType::A(1))
}

fn cycle_euclidean(graph: &Underlying) -> Option<EuclideanType> {
    let n = graph.num_vertices;
    let simple = graph.simple();
    (n >= 3 && (0..n).all(|vertex| simple.degree(vertex) == 2)).then_some(EuclideanType::A(n - 1))
}

fn euclidean_tree_type(quiver: &Quiver) -> Option<EuclideanType> {
    euclidean_tree_shape(tree(quiver)?.shape()?)
}

fn euclidean_tree_shape(shape: Shape) -> Option<EuclideanType> {
    match shape {
        Shape::Path(_) => None,
        Shape::Star(arms) => euclidean_star(&arms),
        Shape::DoubleFork { separation } => Some(EuclideanType::D(separation + 4)),
    }
}

fn euclidean_star(arms: &[usize]) -> Option<EuclideanType> {
    if arms == [1, 1, 1, 1] {
        return Some(EuclideanType::D(4));
    }
    [
        ([2, 2, 2], EuclideanType::E6),
        ([1, 3, 3], EuclideanType::E7),
        ([1, 2, 5], EuclideanType::E8),
    ]
    .iter()
    .find_map(|(expected, kind)| (arms == expected).then_some(*kind))
}

/// The Euclidean type of the quiver's underlying graph, or `None` when that
/// graph is not a Euclidean diagram.
///
/// ```
/// use auslander::dynkin::{EuclideanType, euclidean_type};
/// use auslander::quiver::Quiver;
/// let kronecker = Quiver::new(2, &[(0, 1), (0, 1)]).unwrap();
/// assert_eq!(euclidean_type(&kronecker), Some(EuclideanType::A(1)));
/// ```
pub fn euclidean_type(quiver: &Quiver) -> Option<EuclideanType> {
    let graph = Underlying::of(quiver);
    match euclidean_case(&graph) {
        EuclideanCase::Reject => None,
        EuclideanCase::MultipleEdge => multiple_edge_euclidean(&graph),
        EuclideanCase::Cycle => cycle_euclidean(&graph),
        EuclideanCase::Tree => euclidean_tree_type(quiver),
    }
}

/// The underlying undirected multigraph of a quiver.
pub(crate) struct Underlying {
    pub(crate) num_vertices: usize,
    pub(crate) loops: usize,
    /// Edge multiplicities keyed by `(min, max)`; loops are excluded.
    pub(crate) multiplicity: FxHashMap<(usize, usize), usize>,
}

/// A connected loopless simple graph, with sorted adjacency lists.
pub(crate) struct Simple {
    pub(crate) neighbours: Vec<Vec<usize>>,
}

/// The shape of a tree, as far as the Dynkin and Euclidean classifications
/// distinguish shapes.
pub(crate) enum Shape {
    /// A path on this many vertices.
    Path(usize),
    /// One branch vertex with arms of these lengths, sorted ascending.
    Star(Vec<usize>),
    /// Two branch vertices of degree three, each carrying two leaves, joined by
    /// a path with this many edges.
    DoubleFork { separation: usize },
}

impl Underlying {
    pub(crate) fn of(quiver: &Quiver) -> Underlying {
        let mut loops = 0usize;
        let mut multiplicity: FxHashMap<(usize, usize), usize> = FxHashMap::default();
        for &(s, t) in quiver.arrows() {
            let (u, v) = (s as usize, t as usize);
            if u == v {
                loops += 1;
            } else {
                *multiplicity.entry((u.min(v), u.max(v))).or_insert(0) += 1;
            }
        }
        Underlying {
            num_vertices: quiver.num_vertices() as usize,
            loops,
            multiplicity,
        }
    }

    accessor_methods! {
        num_edges() -> usize = |this| this.loops + this.multiplicity.values().sum::<usize>();
        max_multiplicity() -> usize = |this| this.multiplicity.values().copied().max().unwrap_or(0);
        simple() -> Simple = |this| {
            let mut neighbours = vec![Vec::new(); this.num_vertices];
            for &(u, v) in this.multiplicity.keys() {
                neighbours[u].push(v);
                neighbours[v].push(u);
            }
            for list in &mut neighbours {
                list.sort_unstable();
            }
            Simple { neighbours }
        };
    }

    fn is_connected(&self) -> bool {
        self.num_vertices > 0 && reachable_count(&self.simple().neighbours, 0) == self.num_vertices
    }
}

/// The underlying graph of `quiver` when it is a connected loopless simple
/// tree, which every Dynkin diagram is.
pub(crate) fn tree(quiver: &Quiver) -> Option<Simple> {
    let graph = Underlying::of(quiver);
    if graph.loops > 0 || graph.max_multiplicity() > 1 || graph.num_vertices == 0 {
        return None;
    }
    if graph.num_edges() != graph.num_vertices - 1 || !graph.is_connected() {
        return None;
    }
    Some(graph.simple())
}

impl Simple {
    fn degree(&self, v: usize) -> usize {
        self.neighbours[v].len()
    }

    /// Walks from `center` into `first` while degrees stay `2`. Returns the
    /// number of edges walked and the vertex where the walk stopped.
    fn arm(&self, center: usize, first: usize) -> (usize, usize) {
        let mut previous = center;
        let mut current = first;
        let mut length = 1usize;
        while self.degree(current) == 2 {
            let next = if self.neighbours[current][0] == previous {
                self.neighbours[current][1]
            } else {
                self.neighbours[current][0]
            };
            previous = current;
            current = next;
            length += 1;
        }
        (length, current)
    }

    /// The tree's shape, or `None` when it has a vertex of degree at least
    /// five, three or more branch vertices, or two branch vertices in any
    /// arrangement other than a double fork.
    fn shape(&self) -> Option<Shape> {
        let n = self.neighbours.len();
        let branch: Vec<usize> = (0..n).filter(|&v| self.degree(v) >= 3).collect();
        match branch[..] {
            [] => Some(Shape::Path(n)),
            [center] => self.star_shape(center),
            [first, second] => self.double_fork_shape(first, second),
            _ => None,
        }
    }

    fn star_shape(&self, center: usize) -> Option<Shape> {
        if self.degree(center) > 4 {
            return None;
        }
        let mut arms: Vec<usize> = self.neighbours[center]
            .iter()
            .map(|&neighbour| self.arm(center, neighbour).0)
            .collect();
        arms.sort_unstable();
        Some(Shape::Star(arms))
    }

    fn fork_center(&self, center: usize, other: usize) -> Option<usize> {
        if self.degree(center) != 3 {
            return None;
        }
        let mut separation = None;
        let mut leaves = 0;
        for &neighbour in &self.neighbours[center] {
            let (length, end) = self.arm(center, neighbour);
            if end == other {
                separation = Some(length);
            } else if length == 1 {
                leaves += 1;
            } else {
                return None;
            }
        }
        (leaves == 2).then_some(separation).flatten()
    }

    fn double_fork_shape(&self, first: usize, second: usize) -> Option<Shape> {
        let separation = self.fork_center(first, second)?;
        let reverse = self.fork_center(second, first)?;
        (separation == reverse).then_some(Shape::DoubleFork { separation })
    }
}

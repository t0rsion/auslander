use crate::quiver::ArrowId;

/// Rejected input for the checked gentle-tree classification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GentleError {
    /// The quiver has no vertices, so its underlying graph is not a tree.
    EmptyQuiver,
    /// Arrow `arrow` is a loop at `vertex`.
    Loop { arrow: ArrowId, vertex: u32 },
    /// Arrows `first` and `second` form a parallel undirected edge.
    MultipleEdges {
        first: ArrowId,
        second: ArrowId,
        endpoints: (u32, u32),
    },
    /// The loopless simple graph is disconnected.
    Disconnected { vertices: usize, reachable: usize },
    /// A connected simple graph has a cycle.
    Cycle { vertices: usize, edges: usize },
    /// Reduced relation `relation` has more than one term, so the ideal is not
    /// monomial in the checked presentation.
    NonMonomial { relation: usize, terms: usize },
    /// Reduced relation `relation` has a one-term path of length `length`, not
    /// a quadratic generator.
    NonQuadratic { relation: usize, length: usize },
    /// Vertex `vertex` has too many incoming arrows for a gentle quiver.
    IncomingDegree { vertex: u32, count: usize },
    /// Vertex `vertex` has too many outgoing arrows for a gentle quiver.
    OutgoingDegree { vertex: u32, count: usize },
    /// Arrow `arrow` has more than one permitted successor.
    MultiplePermittedSuccessors { arrow: ArrowId, count: usize },
    /// Arrow `arrow` has more than one forbidden successor.
    MultipleForbiddenSuccessors { arrow: ArrowId, count: usize },
    /// Arrow `arrow` has more than one permitted predecessor.
    MultiplePermittedPredecessors { arrow: ArrowId, count: usize },
    /// Arrow `arrow` has more than one forbidden predecessor.
    MultipleForbiddenPredecessors { arrow: ArrowId, count: usize },
}

display_error! { error GentleError {
    Self::EmptyQuiver => "the quiver has no vertices, so its underlying graph is not a tree";
    Self::Loop { arrow, vertex } => "arrow {} is a loop at vertex {vertex}", arrow.0;
    Self::MultipleEdges { first, second, endpoints } => "arrows {} and {} are parallel on the undirected edge {} -- {}", first.0, second.0, endpoints.0, endpoints.1;
    Self::Disconnected { vertices, reachable } => "the underlying graph reaches {reachable} of {vertices} vertices";
    Self::Cycle { vertices, edges } => "the connected underlying graph has {edges} edges on {vertices} vertices, so it has a cycle";
    Self::NonMonomial { relation, terms } => "reduced relation {relation} has {terms} terms; the gentle route needs a monomial ideal";
    Self::NonQuadratic { relation, length } => "reduced relation {relation} has path length {length}; the gentle route needs quadratic relations";
    Self::IncomingDegree { vertex, count } => "vertex {vertex} has {count} incoming arrows; a gentle quiver allows at most two";
    Self::OutgoingDegree { vertex, count } => "vertex {vertex} has {count} outgoing arrows; a gentle quiver allows at most two";
    Self::MultiplePermittedSuccessors { arrow, count } => "arrow {} has {count} permitted successors; a gentle quiver allows at most one", arrow.0;
    Self::MultipleForbiddenSuccessors { arrow, count } => "arrow {} has {count} forbidden successors; a gentle quiver allows at most one", arrow.0;
    Self::MultiplePermittedPredecessors { arrow, count } => "arrow {} has {count} permitted predecessors; a gentle quiver allows at most one", arrow.0;
    Self::MultipleForbiddenPredecessors { arrow, count } => "arrow {} has {count} forbidden predecessors; a gentle quiver allows at most one", arrow.0;
} }

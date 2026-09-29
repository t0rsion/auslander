use std::sync::Arc;

use crate::algebra::{Algebra, AlgebraBuildError, monomial_algebra};
use crate::field::PrimeField;
use crate::quiver::ArrowId;

use super::shape::{Kind, Shape, monomial_ideal};

/// The canonical form of a connected gentle presentation up to isomorphism
/// of bound quivers.
///
/// Two presentations have equal keys exactly when a vertex bijection and an
/// arrow bijection carry the quiver of one onto the other and the relation
/// set onto the relation set. The key is the presentation itself under one
/// canonical relabeling, so [`GentleKey::algebra`] rebuilds it.
///
/// Relabeling walks the arrows breadth first from a start arrow. From each
/// arrow it tries, in this order, the permitted successor, the forbidden
/// successor, the permitted predecessor, the forbidden predecessor, the
/// other arrow with the same source, and the other arrow with the same
/// target. Gentleness makes each of the six unique, so the walk depends on
/// the start arrow only. Vertices are numbered in order of first appearance.
/// The key is the least encoding over all start arrows. The cost is
/// quadratic in the arrow count.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct GentleKey {
    vertices: u32,
    arrows: Vec<(u32, u32)>,
    relations: Vec<(ArrowId, ArrowId)>,
}

impl GentleKey {
    accessor_methods! {
        /// The number of vertices.
        pub vertices() -> u32 = |this| this.vertices;
        /// The arrows as `(source, target)` pairs in canonical order.
        pub arrows() -> &[(u32, u32)] = |this| &this.arrows;
        /// Every relation `a·b` as the pair `(a, b)` of canonical arrows, sorted.
        pub relations() -> &[(ArrowId, ArrowId)] = |this| &this.relations;
    }

    /// The algebra of the canonical presentation over `field`.
    ///
    /// Errors only when completion runs out of its default budget
    /// ([`AlgebraBuildError::Truncated`]). A key comes from a
    /// finite-dimensional gentle presentation, so the quotient is finite.
    pub fn algebra(&self, field: PrimeField) -> Result<Arc<Algebra>, AlgebraBuildError> {
        let ideal = monomial_ideal(self.vertices, &self.arrows, &self.relations);
        monomial_algebra(&ideal, field)
    }
}

/// A canonical relabeling of one gentle presentation and its key.
///
/// Vertex `v` of the presentation is vertex `vertex_map()[v]` of the key.
/// Arrow `a` is arrow `arrow_map()[a.index()]` of the key. Composing the
/// labeling of one presentation with the inverse labeling of another gives
/// an isomorphism of bound quivers when the keys are equal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GentleLabeling {
    key: GentleKey,
    vertex_map: Vec<u32>,
    arrow_map: Vec<ArrowId>,
}

impl GentleLabeling {
    pub(crate) fn new(shape: &Shape) -> GentleLabeling {
        let starts = (0..shape.arrows().len() as u32).map(ArrowId);
        starts
            .map(|start| relabel(shape, start))
            .min_by(|left, right| left.key.cmp(&right.key))
            .unwrap_or_else(|| GentleLabeling {
                key: GentleKey {
                    vertices: shape.vertices(),
                    arrows: Vec::new(),
                    relations: Vec::new(),
                },
                vertex_map: (0..shape.vertices()).collect(),
                arrow_map: Vec::new(),
            })
    }

    accessor_methods! {
        /// The canonical key.
        pub key() -> &GentleKey = |this| &this.key;
        /// The canonical label of each vertex.
        pub vertex_map() -> &[u32] = |this| &this.vertex_map;
        /// The canonical label of each arrow.
        pub arrow_map() -> &[ArrowId] = |this| &this.arrow_map;
    }

    /// The canonical key, dropping the maps.
    pub fn into_key(self) -> GentleKey {
        self.key
    }
}

fn relabel(shape: &Shape, start: ArrowId) -> GentleLabeling {
    let order = walk(shape, start);
    let mut arrow_map = vec![ArrowId(0); order.len()];
    for (label, arrow) in order.iter().enumerate() {
        arrow_map[arrow.index()] = ArrowId(label as u32);
    }
    let vertex_map = vertex_labels(shape, &order);
    let arrows = order
        .iter()
        .map(|&arrow| {
            let (source, target) = shape.arrows()[arrow.index()];
            (vertex_map[source as usize], vertex_map[target as usize])
        })
        .collect();
    let relations = order
        .iter()
        .enumerate()
        .filter_map(|(label, &arrow)| {
            let next = shape.successor(Kind::Forbidden, arrow)?;
            Some((ArrowId(label as u32), arrow_map[next.index()]))
        })
        .collect();
    GentleLabeling {
        key: GentleKey {
            vertices: shape.vertices(),
            arrows,
            relations,
        },
        vertex_map,
        arrow_map,
    }
}

/// Every arrow in breadth-first order from `start`.
///
/// Panics when an arrow is unreachable. Recognition checked connectivity,
/// and the six moves join any two arrows that share a vertex.
fn walk(shape: &Shape, start: ArrowId) -> Vec<ArrowId> {
    let mut seen = vec![false; shape.arrows().len()];
    seen[start.index()] = true;
    let mut order = vec![start];
    let mut position = 0;
    while let Some(&arrow) = order.get(position) {
        for next in moves(shape, arrow).into_iter().flatten() {
            if !seen[next.index()] {
                seen[next.index()] = true;
                order.push(next);
            }
        }
        position += 1;
    }
    assert_eq!(
        order.len(),
        seen.len(),
        "the canonical walk missed an arrow of a connected quiver; library bug"
    );
    order
}

fn moves(shape: &Shape, arrow: ArrowId) -> [Option<ArrowId>; 6] {
    [
        shape.successor(Kind::Permitted, arrow),
        shape.successor(Kind::Forbidden, arrow),
        shape.predecessor(Kind::Permitted, arrow),
        shape.predecessor(Kind::Forbidden, arrow),
        shape.outgoing_sibling(arrow),
        shape.incoming_sibling(arrow),
    ]
}

fn vertex_labels(shape: &Shape, order: &[ArrowId]) -> Vec<u32> {
    let mut labels = vec![u32::MAX; shape.vertices() as usize];
    let mut next = 0;
    for &(source, target) in order.iter().map(|arrow| &shape.arrows()[arrow.index()]) {
        for vertex in [source, target] {
            if labels[vertex as usize] == u32::MAX {
                labels[vertex as usize] = next;
                next += 1;
            }
        }
    }
    assert_eq!(
        next,
        shape.vertices(),
        "a vertex of a connected quiver has no arrow; library bug"
    );
    labels
}

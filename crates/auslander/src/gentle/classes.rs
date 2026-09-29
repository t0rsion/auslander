use std::sync::Arc;

use rustc_hash::FxHashSet;

use crate::algebra::{Algebra, AlgebraBuildError};
use crate::field::PrimeField;
use crate::monomial::{MonomialError, MonomialPresentation};

use super::canonical::{GentleKey, GentleLabeling};
use super::shape::{Shape, Sign};

/// The canonical key of every connected gentle presentation with exactly
/// `vertices` vertices and a finite-dimensional algebra, sorted.
///
/// There is one key per isomorphism class of bound quiver. Loops, parallel
/// arrows, and full relation cycles are included. Zero vertices give an
/// empty list.
///
/// The search grows presentations from one vertex. Each step adds an arrow
/// between two empty slots, or a new vertex with one arrow. Removing an arrow
/// that is not a bridge, or a leaf vertex of a tree, keeps a presentation
/// connected, gentle, and finite dimensional, so every class is reached.
/// [`MonomialPresentation::new`] decides finite dimension. A presentation it
/// rejects with [`MonomialError::InfiniteDimensional`] is dropped with every
/// extension of it. `vertices = 1` gives 2 keys and `vertices = 4` gives
/// 894.
pub fn connected_gentle_keys(vertices: u32) -> Vec<GentleKey> {
    if vertices == 0 {
        return Vec::new();
    }
    let root = Shape::empty(1);
    let mut seen = FxHashSet::default();
    seen.insert(GentleLabeling::new(&root).into_key());
    let mut found = Vec::new();
    let mut pending = vec![root];
    while let Some(shape) = pending.pop() {
        if shape.vertices() == vertices {
            found.push(GentleLabeling::new(&shape).into_key());
        }
        for child in extensions(&shape, vertices) {
            if seen.insert(GentleLabeling::new(&child).into_key()) && is_finite(&child) {
                pending.push(child);
            }
        }
    }
    found.sort_unstable();
    found
}

/// The algebra over `field` of every key of [`connected_gentle_keys`], in
/// key order.
///
/// Errors only when completion runs out of its default budget.
pub fn connected_gentle_algebras(
    vertices: u32,
    field: PrimeField,
) -> Result<Vec<Arc<Algebra>>, AlgebraBuildError> {
    connected_gentle_keys(vertices)
        .iter()
        .map(|key| key.algebra(field))
        .collect()
}

fn is_finite(shape: &Shape) -> bool {
    match MonomialPresentation::new(shape.monomial_ideal()) {
        Ok(_) => true,
        Err(MonomialError::InfiniteDimensional) => false,
        Err(error) => panic!("a gentle shape gave an invalid monomial ideal: {error}; library bug"),
    }
}

/// Every one-step extension of `shape` with at most `limit` vertices.
///
/// A new vertex carries one arrow, so the sign of its slot is a free choice.
fn extensions(shape: &Shape, limit: u32) -> Vec<Shape> {
    let outgoing = empty_slots(shape, |vertex, sign| shape.outgoing(vertex, sign).is_none());
    let incoming = empty_slots(shape, |vertex, sign| shape.incoming(vertex, sign).is_none());
    let mut children = Vec::new();
    for &(source, sigma) in &outgoing {
        for &(target, epsilon) in &incoming {
            let mut child = shape.clone();
            child.push(source, sigma, target, epsilon);
            children.push(child);
        }
    }
    if shape.vertices() < limit {
        for &(source, sigma) in &outgoing {
            let mut child = shape.clone();
            let target = child.push_vertex();
            child.push(source, sigma, target, Sign::Plus);
            children.push(child);
        }
        for &(target, epsilon) in &incoming {
            let mut child = shape.clone();
            let source = child.push_vertex();
            child.push(source, Sign::Plus, target, epsilon);
            children.push(child);
        }
    }
    children
}

fn empty_slots(shape: &Shape, empty: impl Fn(u32, Sign) -> bool) -> Vec<(u32, Sign)> {
    (0..shape.vertices())
        .flat_map(|vertex| [(vertex, Sign::Plus), (vertex, Sign::Minus)])
        .filter(|&(vertex, sign)| empty(vertex, sign))
        .collect()
}

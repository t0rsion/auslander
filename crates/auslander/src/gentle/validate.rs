use std::sync::Arc;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::algebra::Algebra;
use crate::quiver::{ArrowId, Quiver};

use super::errors::GentleError;
use super::presentation::GentlePresentation;

/// The checked tree and the quadratic monomial relations used by enumeration.
pub(crate) struct ValidatedGentle {
    pub(crate) neighbours: Vec<Vec<(u32, ArrowId)>>,
    pub(crate) forbidden: FxHashSet<(ArrowId, ArrowId)>,
}

/// Checks a gentle tree: general recognition plus the tree condition.
///
/// The tree check runs between the relation check and the quiver checks of
/// [`GentlePresentation::new`]. That order fixes which error an input with
/// several failures reports.
pub(crate) fn validate(algebra: &Arc<Algebra>) -> Result<ValidatedGentle, GentleError> {
    let forbidden = reduced_quadratic_relations(algebra)?;
    let neighbours = simple_tree(algebra.quiver())?;
    GentlePresentation::from_relations(algebra, &forbidden)?;
    Ok(ValidatedGentle {
        neighbours,
        forbidden,
    })
}

/// The ordered pairs `(a, b)` with `a·b` a reduced relation, or the first
/// reduced relation that is not a quadratic monomial.
pub(crate) fn reduced_quadratic_relations(
    algebra: &Algebra,
) -> Result<FxHashSet<(ArrowId, ArrowId)>, GentleError> {
    let mut forbidden = FxHashSet::default();
    for (relation, checked) in algebra.relations().iter().enumerate() {
        if checked.terms().len() != 1 {
            return Err(GentleError::NonMonomial {
                relation,
                terms: checked.terms().len(),
            });
        }
        let word = checked.terms()[0].1.arrows();
        if word.len() != 2 {
            return Err(GentleError::NonQuadratic {
                relation,
                length: word.len(),
            });
        }
        forbidden.insert((word[0], word[1]));
    }
    Ok(forbidden)
}

/// Checks connectivity, degrees, and the continuation conditions, in that
/// order.
pub(crate) fn check_gentle_quiver(
    quiver: &Quiver,
    forbidden: &FxHashSet<(ArrowId, ArrowId)>,
) -> Result<(), GentleError> {
    check_connected(quiver)?;
    check_degrees(quiver)?;
    check_continuations(quiver, forbidden)
}

fn simple_tree(quiver: &Quiver) -> Result<Vec<Vec<(u32, ArrowId)>>, GentleError> {
    let vertices = quiver.num_vertices() as usize;
    if vertices == 0 {
        return Err(GentleError::EmptyQuiver);
    }
    let mut neighbours = vec![Vec::new(); vertices];
    let mut edges: FxHashMap<(u32, u32), ArrowId> = FxHashMap::default();
    for (index, &(source, target)) in quiver.arrows().iter().enumerate() {
        let arrow = ArrowId(index as u32);
        if source == target {
            return Err(GentleError::Loop {
                arrow,
                vertex: source,
            });
        }
        let endpoints = (source.min(target), source.max(target));
        if let Some(&first) = edges.get(&endpoints) {
            return Err(GentleError::MultipleEdges {
                first,
                second: arrow,
                endpoints,
            });
        }
        edges.insert(endpoints, arrow);
        neighbours[source as usize].push((target, arrow));
        neighbours[target as usize].push((source, arrow));
    }
    check_connected(quiver)?;
    if edges.len() != vertices.saturating_sub(1) {
        return Err(GentleError::Cycle {
            vertices,
            edges: edges.len(),
        });
    }
    Ok(neighbours)
}

fn check_connected(quiver: &Quiver) -> Result<(), GentleError> {
    let vertices = quiver.num_vertices() as usize;
    if vertices == 0 {
        return Err(GentleError::EmptyQuiver);
    }
    let mut seen = vec![false; vertices];
    let mut stack = vec![0u32];
    seen[0] = true;
    while let Some(vertex) = stack.pop() {
        let arrows = quiver
            .arrows_from(vertex)
            .iter()
            .chain(quiver.arrows_to(vertex));
        for &arrow in arrows {
            for next in [quiver.source(arrow), quiver.target(arrow)] {
                if !seen[next as usize] {
                    seen[next as usize] = true;
                    stack.push(next);
                }
            }
        }
    }
    let reachable = seen.iter().filter(|&&present| present).count();
    (reachable == vertices)
        .then_some(())
        .ok_or(GentleError::Disconnected {
            vertices,
            reachable,
        })
}

fn check_degrees(quiver: &Quiver) -> Result<(), GentleError> {
    for vertex in 0..quiver.num_vertices() {
        let incoming = quiver.arrows_to(vertex).len();
        if incoming > 2 {
            return Err(GentleError::IncomingDegree {
                vertex,
                count: incoming,
            });
        }
        let outgoing = quiver.arrows_from(vertex).len();
        if outgoing > 2 {
            return Err(GentleError::OutgoingDegree {
                vertex,
                count: outgoing,
            });
        }
    }
    Ok(())
}

fn check_continuations(
    quiver: &Quiver,
    forbidden: &FxHashSet<(ArrowId, ArrowId)>,
) -> Result<(), GentleError> {
    for arrow in 0..quiver.num_arrows() {
        let arrow = ArrowId(arrow as u32);
        let successors = quiver.arrows_from(quiver.target(arrow));
        check_successors(arrow, successors, forbidden)?;
        let predecessors = quiver.arrows_to(quiver.source(arrow));
        check_predecessors(arrow, predecessors, forbidden)?;
    }
    Ok(())
}

fn check_successors(
    arrow: ArrowId,
    successors: &[ArrowId],
    forbidden: &FxHashSet<(ArrowId, ArrowId)>,
) -> Result<(), GentleError> {
    let forbidden_count = successors
        .iter()
        .filter(|&&next| forbidden.contains(&(arrow, next)))
        .count();
    let permitted_count = successors.len() - forbidden_count;
    if permitted_count > 1 {
        return Err(GentleError::MultiplePermittedSuccessors {
            arrow,
            count: permitted_count,
        });
    }
    if forbidden_count > 1 {
        return Err(GentleError::MultipleForbiddenSuccessors {
            arrow,
            count: forbidden_count,
        });
    }
    Ok(())
}

fn check_predecessors(
    arrow: ArrowId,
    predecessors: &[ArrowId],
    forbidden: &FxHashSet<(ArrowId, ArrowId)>,
) -> Result<(), GentleError> {
    let forbidden_count = predecessors
        .iter()
        .filter(|&&previous| forbidden.contains(&(previous, arrow)))
        .count();
    let permitted_count = predecessors.len() - forbidden_count;
    if permitted_count > 1 {
        return Err(GentleError::MultiplePermittedPredecessors {
            arrow,
            count: permitted_count,
        });
    }
    if forbidden_count > 1 {
        return Err(GentleError::MultipleForbiddenPredecessors {
            arrow,
            count: forbidden_count,
        });
    }
    Ok(())
}

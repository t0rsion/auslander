use std::collections::VecDeque;

use rustc_hash::FxHashSet;

use crate::quiver::Quiver;

use super::graph::{Underlying, dynkin_type};

/// The generalized Cartan matrix of the quiver's underlying graph: `2` on the
/// diagonal and minus the number of edges joining `i` and `j` off it.
///
/// `None` exactly when the quiver has a loop, since a vertex carrying a loop
/// contributes no row with diagonal entry `2` (Kac, *Infinite dimensional Lie
/// algebras*, §1.1).
pub fn generalized_cartan_matrix(quiver: &Quiver) -> Option<Vec<Vec<i64>>> {
    let graph = Underlying::of(quiver);
    if graph.loops > 0 {
        return None;
    }
    let n = graph.num_vertices;
    let mut cartan = vec![vec![0i64; n]; n];
    for (i, row) in cartan.iter_mut().enumerate() {
        row[i] = 2;
    }
    for (&(u, v), &m) in &graph.multiplicity {
        cartan[u][v] = -(m as i64);
        cartan[v][u] = -(m as i64);
    }
    Some(cartan)
}

/// The positive roots of the quiver's underlying graph, in the quiver's own
/// vertex indexing, ordered by height and then lexicographically; `None` when
/// the graph is not a Dynkin diagram.
///
/// The roots are the closure of the simple roots under the simple reflections
/// `s_i(x) = x - (C x)_i e_i`, keeping only vectors with nonnegative entries.
/// Every positive root that is not simple admits a reflection lowering its
/// height while staying positive, so the closure reaches all of them, and it
/// is finite exactly because the diagram is Dynkin.
pub fn positive_roots(quiver: &Quiver) -> Option<Vec<Vec<usize>>> {
    dynkin_type(quiver)?;
    let cartan = generalized_cartan_matrix(quiver)?;
    let n = cartan.len();
    let mut seen: FxHashSet<Vec<i64>> = FxHashSet::default();
    let mut queue: VecDeque<Vec<i64>> = VecDeque::new();
    for i in 0..n {
        let mut simple = vec![0i64; n];
        simple[i] = 1;
        seen.insert(simple.clone());
        queue.push_back(simple);
    }
    let mut roots: Vec<Vec<i64>> = Vec::new();
    while let Some(root) = queue.pop_front() {
        for (i, row) in cartan.iter().enumerate() {
            let pairing: i64 = row.iter().zip(&root).map(|(a, x)| a * x).sum();
            if pairing == 0 {
                continue;
            }
            let mut next = root.clone();
            next[i] -= pairing;
            if next.iter().all(|&x| x >= 0) && seen.insert(next.clone()) {
                queue.push_back(next);
            }
        }
        roots.push(root);
    }
    roots.sort_by(|a, b| {
        let height = |r: &Vec<i64>| r.iter().sum::<i64>();
        height(a).cmp(&height(b)).then_with(|| a.cmp(b))
    });
    Some(
        roots
            .into_iter()
            .map(|r| r.into_iter().map(|x| x as usize).collect())
            .collect(),
    )
}

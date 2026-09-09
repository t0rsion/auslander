use std::sync::Arc;

use crate::algebra::Algebra;
use crate::decompose::{Certificate, decompose};
use crate::field::{Fp, PrimeField};
use crate::linalg::DenseMat;
use crate::module::Module;
use crate::quiver::Quiver;

use super::errors::DynkinError;
use super::graph::{dynkin_type, euclidean_type, tree};
use super::roots::positive_roots;

/// Every indecomposable right module of a hereditary path algebra `kQ` with `Q` of
/// Dynkin type, one per positive root of the underlying graph, ordered as
/// [`crate::dynkin::positive_roots`] orders the roots.
///
/// Gabriel's theorem is what makes the list complete: for `Q` of Dynkin type the
/// dimension vector is a bijection from isomorphism classes of indecomposables to
/// positive roots. The length of the list is
/// [`crate::dynkin::DynkinType::indecomposable_count`].
///
/// Each module is built from a simple module by a chain of
/// Bernstein-Gelfand-Ponomarev reflection functors. An admissible sequence of
/// sinks is applied to the root until it becomes simple, then the matching
/// functors `S_i^-` are applied back. Nothing is enumerated over the field.
///
/// Every module comes with the certificate [`decompose`] produced for it. The
/// construction already proves indecomposability, so that certificate is an
/// independent check rather than the source of the claim.
///
/// # Errors
/// [`DynkinError::NonzeroIdeal`] when the algebra is a proper quotient of
/// `kQ`, [`DynkinError::NotDynkin`] when the underlying graph is no Dynkin
/// diagram.
pub fn dynkin_indecomposables(
    algebra: &Arc<Algebra>,
) -> Result<Vec<(Module, Certificate)>, DynkinError> {
    let relations = algebra.relations().len();
    if relations > 0 {
        return Err(DynkinError::NonzeroIdeal { relations });
    }
    let field = algebra.field();
    let quiver = algebra.quiver();
    if dynkin_type(quiver).is_none() {
        return Err(DynkinError::NotDynkin {
            euclidean: euclidean_type(quiver),
        });
    }
    let roots = positive_roots(quiver).expect("a Dynkin graph has a finite root system");
    let sinks = admissible_sink_sequence(quiver).expect("a Dynkin quiver is acyclic");
    let adjacency = tree(quiver).expect("a Dynkin graph is a tree").neighbours;
    let mut out = Vec::with_capacity(roots.len());
    for root in &roots {
        let rep = reflect_up_from_simple(quiver, &sinks, &adjacency, root, roots.len(), field);
        assert_eq!(
            &rep.dims, root,
            "reflection chain landed on the wrong dimension vector; library bug"
        );
        let m = Module::new(algebra.clone(), rep.dims, rep.maps)
            .expect("a representation of kQ with no relations is a module");
        let d = decompose(&m);
        assert_eq!(
            d.summands().len(),
            1,
            "a module built from a positive root split into {} summands; library bug",
            d.summands().len()
        );
        out.push((m, d.certificates()[0]));
    }
    Ok(out)
}

/// A representation of a quiver with the arrow indexing of some orientation:
/// `maps[a]` has shape `dims[source(a)] × dims[target(a)]` and acts on row
/// vectors.
struct Rep {
    dims: Vec<usize>,
    maps: Vec<DenseMat>,
}

/// The indecomposable representation of `quiver` with dimension vector `root`.
///
/// `sinks` is an admissible sequence of sinks and `roots` the number of positive
/// roots, both supplied by the caller. The state of the reflection chain is the
/// pair (position in `sinks`, current root). After `sinks.len() * roots` steps
/// without reaching a simple root the chain would have repeated a state, and a
/// repeated state can never reach one. Bernstein-Gelfand-Ponomarev says the chain
/// does reach one, so exceeding that count is a library bug.
fn reflect_up_from_simple(
    quiver: &Quiver,
    sinks: &[u32],
    adjacency: &[Vec<usize>],
    root: &[usize],
    roots: usize,
    field: PrimeField,
) -> Rep {
    let mut endpoints: Vec<(u32, u32)> = quiver.arrows().to_vec();
    let mut dim: Vec<i64> = root.iter().map(|&d| d as i64).collect();
    let mut chain: Vec<(u32, Vec<(u32, u32)>)> = Vec::new();
    let mut simple_at = None;
    for step in 0..=sinks.len() * roots {
        let i = sinks[step % sinks.len()];
        if is_simple_root(&dim, i) {
            simple_at = Some(i);
            break;
        }
        reflect_dim(&mut dim, adjacency, i);
        assert!(
            dim.iter().all(|&d| d >= 0),
            "a reflection left the positive cone; library bug"
        );
        reflect_endpoints(&mut endpoints, i);
        chain.push((i, endpoints.clone()));
    }
    let vertex =
        simple_at.expect("reflections of a positive root reach a simple root within the bound");
    let mut rep = simple_rep(&endpoints, &dim, vertex);
    while let Some((i, source_endpoints)) = chain.pop() {
        rep = reflect_minus(&source_endpoints, i, &rep, field);
    }
    rep
}

fn is_simple_root(dim: &[i64], i: u32) -> bool {
    dim[i as usize] == 1
        && dim
            .iter()
            .enumerate()
            .all(|(v, &d)| v == i as usize || d == 0)
}

/// `s_i` on a dimension vector: `d_i ↦ -d_i + Σ_{j ~ i} d_j`, the reflection in
/// the simple root `e_i` for a simply laced diagram.
fn reflect_dim(dim: &mut [i64], adjacency: &[Vec<usize>], i: u32) {
    let neighbours: i64 = adjacency[i as usize].iter().map(|&j| dim[j]).sum();
    dim[i as usize] = neighbours - dim[i as usize];
}

/// Reverses every arrow incident to `i`; arrow ids are unchanged.
pub(crate) fn reflect_endpoints(endpoints: &mut [(u32, u32)], i: u32) {
    for e in endpoints.iter_mut() {
        if e.0 == i || e.1 == i {
            *e = (e.1, e.0);
        }
    }
}

fn simple_rep(endpoints: &[(u32, u32)], dim: &[i64], vertex: u32) -> Rep {
    let dims: Vec<usize> = (0..dim.len())
        .map(|v| usize::from(v == vertex as usize))
        .collect();
    let maps = endpoints
        .iter()
        .map(|&(s, t)| DenseMat::zero(dims[s as usize], dims[t as usize]))
        .collect();
    Rep { dims, maps }
}

fn cokernel_projection(phi: DenseMat, expected_rank: usize, field: PrimeField) -> DenseMat {
    let width = phi.cols();
    let (reduced, pivots) = phi.into_rref(&field);
    assert_eq!(
        pivots.len(),
        expected_rank,
        "the reflection functor met a non-injective structure map; library bug"
    );
    let mut is_pivot = vec![false; width];
    for &column in &pivots {
        is_pivot[column] = true;
    }
    let free: Vec<usize> = (0..width).filter(|&column| !is_pivot[column]).collect();
    // The free coordinates split off a complement of the reduced row space.
    let mut projection = DenseMat::zero(width, free.len());
    for (output, &column) in free.iter().enumerate() {
        projection.set(column, output, Fp::ONE);
        for (row, &pivot) in pivots.iter().enumerate() {
            projection.set(pivot, output, field.neg(reduced.get(row, column)));
        }
    }
    projection
}

fn reflected_maps(
    rep: &Rep,
    endpoints: &[(u32, u32)],
    outgoing: &[usize],
    offsets: &[usize],
    projection: &DenseMat,
) -> Vec<DenseMat> {
    let mut maps = rep.maps.clone();
    for (block_index, &arrow) in outgoing.iter().enumerate() {
        let rows = rep.dims[endpoints[arrow].1 as usize];
        let mut block = DenseMat::zero(rows, projection.cols());
        for row in 0..rows {
            for column in 0..projection.cols() {
                block.set(
                    row,
                    column,
                    projection.get(offsets[block_index] + row, column),
                );
            }
        }
        maps[arrow] = block;
    }
    maps
}

/// The reflection functor `S_i^-` applied to `rep`, a representation of
/// `source_endpoints` in which `i` is a source; the result is a representation
/// of the quiver obtained by reversing every arrow at `i`, in which `i` is a
/// sink.
///
/// With `φ: N_i → ⊕_{a: i→u} N_u` the map assembled from the outgoing arrows,
/// the new space at `i` is `coker φ` and the new map along `a: u → i` is the
/// inclusion of the `a`-block followed by the quotient projection
/// (Bernstein-Gelfand-Ponomarev, *Coxeter functors and Gabriel's theorem*).
///
/// `φ` must be injective, which holds for an indecomposable `rep` not
/// isomorphic to the simple module at `i`.
fn reflect_minus(source_endpoints: &[(u32, u32)], i: u32, rep: &Rep, field: PrimeField) -> Rep {
    let outgoing: Vec<usize> = (0..source_endpoints.len())
        .filter(|&arrow| source_endpoints[arrow].0 == i)
        .collect();
    let mut offsets = Vec::with_capacity(outgoing.len());
    let mut width = 0;
    for &arrow in &outgoing {
        offsets.push(width);
        width += rep.dims[source_endpoints[arrow].1 as usize];
    }
    let mut phi = DenseMat::zero(rep.dims[i as usize], width);
    for (block_index, &arrow) in outgoing.iter().enumerate() {
        let block = &rep.maps[arrow];
        for row in 0..block.rows() {
            for column in 0..block.cols() {
                phi.set(row, offsets[block_index] + column, block.get(row, column));
            }
        }
    }
    let projection = cokernel_projection(phi, rep.dims[i as usize], field);
    let mut dims = rep.dims.clone();
    dims[i as usize] = projection.cols();
    let maps = reflected_maps(rep, source_endpoints, &outgoing, &offsets, &projection);
    Rep { dims, maps }
}

/// A sequence `i_1, …, i_n` listing every vertex once, with `i_1` a sink of
/// `quiver` and `i_k` a sink after reversing at `i_1, …, i_{k-1}`; `None` when
/// the quiver has an oriented cycle. Reversing at all of them in order returns
/// the original orientation.
pub(crate) fn admissible_sink_sequence(quiver: &Quiver) -> Option<Vec<u32>> {
    let n = quiver.num_vertices();
    let mut endpoints: Vec<(u32, u32)> = quiver.arrows().to_vec();
    let mut used = vec![false; n as usize];
    let mut sequence = Vec::with_capacity(n as usize);
    for _ in 0..n {
        let sink = (0..n).find(|&v| !used[v as usize] && endpoints.iter().all(|&(s, _)| s != v))?;
        used[sink as usize] = true;
        sequence.push(sink);
        reflect_endpoints(&mut endpoints, sink);
    }
    Some(sequence)
}

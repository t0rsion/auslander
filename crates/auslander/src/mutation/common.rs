use crate::field::Fp;
use crate::hom::Morphism;
use crate::linalg::DenseMat;
use crate::module::{Module, same_representation};

/// The vertices where `m` has positive dimension, ascending.
pub(super) fn support(m: &Module) -> Vec<u32> {
    m.dim_vector()
        .iter()
        .enumerate()
        .filter_map(|(v, &d)| (d > 0).then_some(v as u32))
        .collect()
}

/// Whether `m` is the direct sum of `parts`, in that order, entry for entry.
///
/// Reassembles the sum and compares every arrow matrix. Dimension vectors
/// would not decide it: they are isomorphism invariants and not identifiers.
pub(super) fn is_direct_sum(m: &Module, parts: &[Module]) -> bool {
    same_representation(
        &crate::decompose::direct_sum_or_zero(m.algebra(), parts).0,
        m,
    )
}

/// The dimension of the sum of the images of `maps` at each vertex.
///
/// The images of a spanning set of `Hom(U, X)` sum to the trace submodule
/// `tr_U(X)`, and at one vertex that sum is the row span of the stacked vertex
/// matrices. So a rank per vertex decides `X in Fac U`.
pub(super) fn trace_dims(maps: &[Morphism], x: &Module) -> Vec<usize> {
    let field = x.field();
    (0..x.algebra().quiver().num_vertices())
        .map(|v| {
            if x.dim_at(v) == 0 {
                return 0;
            }
            let rows: Vec<Vec<Fp>> = maps
                .iter()
                .flat_map(|f| {
                    let block = f.map_at(v);
                    (0..block.rows()).map(move |r| block.row(r).to_vec())
                })
                .collect();
            DenseMat::from_rows(&rows).rank(&field)
        })
        .collect()
}

/// Whether `g` is a cokernel of `f`.
///
/// The checks are `f.then(g) = 0`, `g` onto at every vertex, and
/// `dim Y_v + rank f_v = dim B_v` at every vertex. Together those say
/// `im f = ker g` and `g` epi, which is the cokernel property.
pub(super) fn is_cokernel(f: &Morphism, g: &Morphism) -> bool {
    verify_guard!(g.source().ptr_eq(f.target()));
    let_or_false!(Ok(composite) = f.then(g));
    verify_guard!(composite.is_zero());
    let field = f.source().field();
    (0..f.source().algebra().quiver().num_vertices()).all(|v| {
        let dim_y = g.target().dim_at(v);
        g.map_at(v).rank(&field) == dim_y
            && dim_y + f.map_at(v).rank(&field) == f.target().dim_at(v)
    })
}

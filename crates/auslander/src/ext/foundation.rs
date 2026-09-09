//! Resolution and Yoneda-coordinate primitives for Ext computations.

use std::sync::Arc;

use crate::algebra::Algebra;
use crate::field::Fp;
use crate::hom::Morphism;
use crate::linalg::DenseMat;
use crate::module::Module;
use crate::radical::top;
use crate::resolution::{Bounded, ProjectiveResolution, projective_dimension, resolve};

/// Rejected Ext input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExtError {
    /// The modules live over different algebras (distinct [`Arc`]s).
    DifferentAlgebras,
    /// The requested degree has no representable successor.
    DegreeOverflow { degree: usize },
}

display_error! { error ExtError {
    Self::DifferentAlgebras => "modules live over different algebras";
    Self::DegreeOverflow { degree } => "degree {degree} has no representable successor";
} }

/// Summand layout of a projective term `(+)_v P_v^{t_v}` built by
/// [`projective_cover`](crate::resolution::projective_cover): generators are
/// ordered by vertex, then by copy. At each vertex the term's basis is the
/// concatenation of the summands' path bases in generator order.
pub(super) struct Layout {
    /// Vertex of each generator, in canonical order.
    pub(super) gen_vertex: Vec<u32>,
    /// `offsets[w][g]`: first row of generator `g`'s block in the term at vertex `w`.
    pub(super) offsets: Vec<Vec<usize>>,
}

/// Recovers the layout from the term alone: `t_v = dim (top P)_v`, because
/// `top P_v = S_v`. The block-total assertion holds for every resolution term
/// and for the zero module; a failure means the term is not a canonical
/// projective sum, which is a bug in auslander.
pub(super) fn layout(term: &Module) -> Layout {
    let algebra = term.algebra();
    let n = algebra.quiver().num_vertices();
    let (t, _) = top(term);
    let mut gen_vertex = Vec::new();
    for v in 0..n {
        for _ in 0..t.dim_at(v) {
            gen_vertex.push(v);
        }
    }
    let mut offsets = vec![Vec::with_capacity(gen_vertex.len()); n as usize];
    for w in 0..n {
        let mut off = 0;
        for &v in &gen_vertex {
            offsets[w as usize].push(off);
            off += algebra.paths_between(v, w).len();
        }
        assert_eq!(
            off,
            term.dim_at(w),
            "resolution term is not a canonical projective sum at vertex {w}; \
             this is a bug in auslander"
        );
    }
    Layout {
        gen_vertex,
        offsets,
    }
}

/// `dim Hom_A(term, n)`, which by Yoneda is the sum of `dim N_{v_g}` over the
/// generators `g`.
pub(super) fn hom_space_dim(lay: &Layout, n: &Module) -> usize {
    lay.gen_vertex.iter().map(|&v| n.dim_at(v)).sum()
}

/// The Yoneda basis of `Hom_A(term, n)`, in canonical (generator, index) order.
pub(super) fn yoneda_basis(term: &Module, lay: &Layout, n: &Module) -> Vec<Morphism> {
    let algebra = term.algebra();
    let nv = algebra.quiver().num_vertices();
    let mut basis = Vec::new();
    for (g, &v) in lay.gen_vertex.iter().enumerate() {
        for j in 0..n.dim_at(v) {
            let mut maps: Vec<DenseMat> = (0..nv)
                .map(|w| DenseMat::zero(term.dim_at(w), n.dim_at(w)))
                .collect();
            for w in 0..nv {
                for (r, &b) in algebra.paths_between(v, w).iter().enumerate() {
                    let action = n
                        .word_action(&algebra.basis()[b])
                        .expect("algebra basis words are valid in their own quiver");
                    for c in 0..n.dim_at(w) {
                        maps[w as usize].set(lay.offsets[w as usize][g] + r, c, action.get(j, c));
                    }
                }
            }
            basis.push(Morphism::new(term, n, maps).expect("Yoneda basis element is A-linear"));
        }
    }
    basis
}

/// Coordinates of `f: term -> n` in the Yoneda basis: the trivial path `e_v` is
/// the first basis path of every `(v, v)` block, so the coordinate block of
/// generator `g` is row `offsets[v_g][g]` of `f` at `v_g`.
pub(super) fn coordinates(f: &Morphism, lay: &Layout, n: &Module) -> Vec<Fp> {
    let mut coords = Vec::new();
    for (g, &v) in lay.gen_vertex.iter().enumerate() {
        let row = lay.offsets[v as usize][g];
        for j in 0..n.dim_at(v) {
            coords.push(f.map_at(v).get(row, j));
        }
    }
    coords
}

/// Rank of `delta^k: Hom(P_k, N) -> Hom(P_{k+1}, N)`, `f -> d.then(f)`, in the
/// Yoneda bases.
pub(super) fn delta_rank(
    d: &Morphism,
    term: &Module,
    lay: &Layout,
    next_lay: &Layout,
    n: &Module,
) -> usize {
    let rows = delta_rows(d, term, lay, next_lay, n);
    if rows.is_empty() {
        return 0;
    }
    DenseMat::from_rows(&rows).into_rank(&term.field())
}

pub(super) fn delta_rows(
    d: &Morphism,
    term: &Module,
    lay: &Layout,
    next_lay: &Layout,
    n: &Module,
) -> Vec<Vec<Fp>> {
    yoneda_basis(term, lay, n)
        .iter()
        .map(|f| {
            let composite = d
                .then(f)
                .expect("internal endpoint invariant: d targets the term f leaves");
            coordinates(&composite, next_lay, n)
        })
        .collect()
}

pub(super) fn check_pair(m: &Module, n: &Module) -> Result<(), ExtError> {
    Arc::ptr_eq(m.algebra(), n.algebra())
        .then_some(())
        .ok_or(ExtError::DifferentAlgebras)
}

/// `[dim Ext^0(m, n), ..., dim Ext^max_k(m, n)]`, every entry exact because the
/// resolution prefix is always long enough (see the module docs). Errors when
/// the modules do not share one algebra or `max_k + 1` is not representable.
pub fn ext_table(m: &Module, n: &Module, max_k: usize) -> Result<Vec<usize>, ExtError> {
    check_pair(m, n)?;
    let steps = max_k
        .checked_add(1)
        .ok_or(ExtError::DegreeOverflow { degree: max_k })?;
    let res = resolve(m, steps);
    Ok(ext_table_from_resolution(&res, n, max_k))
}

/// Ext dimensions from a resolution that reaches `max_k + 1` differentials
/// or ends finitely before that point.
///
/// The caller checks that `n` shares the source algebra and that `max_k + 1`
/// is representable.
pub(crate) fn ext_table_from_resolution(
    res: &ProjectiveResolution,
    n: &Module,
    max_k: usize,
) -> Vec<usize> {
    debug_assert!(Arc::ptr_eq(
        res.augmentation.target().algebra(),
        n.algebra()
    ));
    debug_assert!(
        matches!(res.end, crate::resolution::ResolutionEnd::Finite) || res.maps.len() > max_k
    );
    let layouts: Vec<Layout> = res.terms.iter().map(layout).collect();
    // A finite resolution continues with zero terms: past its end, Hom is zero
    // and delta is zero.
    let h: Vec<usize> = (0..=max_k)
        .map(|i| layouts.get(i).map_or(0, |lay| hom_space_dim(lay, n)))
        .collect();
    let ranks: Vec<usize> = (0..=max_k)
        .map(|i| {
            if i + 1 < res.terms.len() {
                delta_rank(&res.maps[i], &res.terms[i], &layouts[i], &layouts[i + 1], n)
            } else {
                0
            }
        })
        .collect();
    (0..=max_k)
        .map(|k| {
            let kernel_dim = h[k] - ranks[k];
            let boundary = if k == 0 { 0 } else { ranks[k - 1] };
            assert!(
                kernel_dim >= boundary,
                "im delta^{} is not contained in ker delta^{k}; this is a bug in auslander",
                k.wrapping_sub(1)
            );
            kernel_dim - boundary
        })
        .collect()
}

/// `dim Ext^k_A(m, n)`, exact for every `k`. `Ext^0` is `dim Hom_A(m, n)`.
/// Errors when the modules do not share one algebra or `k + 1` is not
/// representable.
pub fn ext_dim(m: &Module, n: &Module, k: usize) -> Result<usize, ExtError> {
    Ok(ext_table(m, n, k)?[k])
}

/// The global dimension of the algebra, resolved up to `bound` differentials.
///
/// For a finite-dimensional algebra `gldim A = pd (A/rad A) = max_v pd S_v`:
/// every module has a finite composition series with simple factors, so the
/// supremum of projective dimensions is attained on the simples. Returns
/// `Exact` when every simple resolves within `bound`, otherwise
/// `AtLeast(bound + 1)`, which says the minimal resolution of some simple still
/// has a nonzero syzygy past the bound.
/// At `usize::MAX`, the stored lower bound stays `usize::MAX`, the strongest
/// value this return type can represent.
///
/// The function does not fail: it builds the simples it resolves over the given
/// algebra itself, so no endpoint mismatch can arise.
pub fn global_dimension(algebra: &Arc<Algebra>, bound: usize) -> Bounded<usize> {
    let mut max = 0usize;
    let mut cut = false;
    for v in 0..algebra.quiver().num_vertices() {
        match projective_dimension(&Module::simple(algebra, v), bound) {
            Bounded::Exact(d) => max = max.max(d),
            Bounded::AtLeast(_) => cut = true,
        }
    }
    if cut {
        Bounded::AtLeast(bound.saturating_add(1))
    } else {
        Bounded::Exact(max)
    }
}

/// The cochain morphism `term -> n` whose canonical coordinates are `coords`:
/// generator `g` at vertex `v` takes the coordinate block of length
/// `dim N_v`, and the basis path `p: v -> w` of its summand maps to that
/// block times `N(p)`.
///
/// # Panics
/// Panics unless `coords` has one entry per (generator, basis vector) pair.
pub(super) fn cochain_from_coordinates(
    term: &Module,
    lay: &Layout,
    n: &Module,
    coords: &[Fp],
) -> Morphism {
    let algebra = term.algebra();
    let field = term.field();
    let nv = algebra.quiver().num_vertices();
    let mut maps: Vec<DenseMat> = (0..nv)
        .map(|w| DenseMat::zero(term.dim_at(w), n.dim_at(w)))
        .collect();
    let mut offset = 0;
    for (g, &v) in lay.gen_vertex.iter().enumerate() {
        let block = &coords[offset..offset + n.dim_at(v)];
        offset += n.dim_at(v);
        for w in 0..nv {
            for (r, &b) in algebra.paths_between(v, w).iter().enumerate() {
                let action = n
                    .word_action(&algebra.basis()[b])
                    .expect("algebra basis words are valid in their own quiver");
                for c in 0..n.dim_at(w) {
                    let mut acc = Fp::ZERO;
                    for (j, &x) in block.iter().enumerate() {
                        acc = field.add(acc, field.mul(x, action.get(j, c)));
                    }
                    maps[w as usize].set(lay.offsets[w as usize][g] + r, c, acc);
                }
            }
        }
    }
    assert_eq!(
        offset,
        coords.len(),
        "coords needs one entry per (generator, basis vector) pair"
    );
    Morphism::new(term, n, maps).expect("generator images extend to an A-linear map")
}

/// The matrix of `delta: Hom(term, N) -> Hom(next, N)`, `f -> d.then(f)`, in
/// Yoneda bases: one row per basis element of the source cochain space.
pub(super) fn delta_matrix(
    d: &Morphism,
    term: &Module,
    lay: &Layout,
    next_lay: &Layout,
    n: &Module,
) -> DenseMat {
    let rows = delta_rows(d, term, lay, next_lay, n);
    DenseMat::from_rows_with_cols(&rows, hom_space_dim(next_lay, n))
}

/// The lift `phi: term -> T` with `phi.then(through) = rhs`, for `through: T -> B`
/// and `rhs: term -> B` with `term` a canonical projective sum. Every generator
/// image solves with free variables zeroed, so the lift is deterministic.
///
/// All generators at one vertex solve against the same `through` matrix, so
/// they are grouped by vertex and one [`DenseMat::solve_many`] per vertex
/// replaces one `solve` per generator.
///
/// # Panics
/// Panics when a generator image of `rhs` lies outside the image of `through`;
/// callers only lift maps that land there.
pub(crate) fn lift_through(term: &Module, through: &Morphism, rhs: &Morphism) -> Morphism {
    debug_assert!(rhs.source().ptr_eq(term));
    debug_assert!(rhs.target().ptr_eq(through.target()));
    let field = term.field();
    let lay = layout(term);
    let vertices = term.algebra().quiver().num_vertices() as usize;
    let mut at_vertex: Vec<Vec<usize>> = vec![Vec::new(); vertices];
    for (g, &v) in lay.gen_vertex.iter().enumerate() {
        at_vertex[v as usize].push(g);
    }
    // Column `j` of `solved[v]` is the image of the `j`-th generator at `v`,
    // generators in index order.
    let solved: Vec<DenseMat> = (0..vertices)
        .map(|v| {
            let rows: Vec<Vec<Fp>> = at_vertex[v]
                .iter()
                .map(|&g| rhs.map_at(v as u32).row(lay.offsets[v][g]).to_vec())
                .collect();
            if rows.is_empty() {
                return DenseMat::zero(through.source().dim_at(v as u32), 0);
            }
            through
                .map_at(v as u32)
                .transpose()
                .solve_many(&DenseMat::from_rows(&rows).transpose(), &field)
                .expect("lift_through: the right side lands in the image of the lifted-through map")
        })
        .collect();
    let mut taken = vec![0usize; vertices];
    let mut coords = Vec::new();
    for &v in &lay.gen_vertex {
        let x = &solved[v as usize];
        let j = taken[v as usize];
        taken[v as usize] += 1;
        coords.extend((0..x.rows()).map(|i| x.get(i, j)));
    }
    cochain_from_coordinates(term, &lay, through.source(), &coords)
}

pub(super) fn chain_terms(
    resolution: &ProjectiveResolution,
    start: usize,
    end: usize,
    terminal: &Module,
    algebra: &Arc<Algebra>,
) -> Vec<Module> {
    (start..=end)
        .map(|degree| {
            resolution
                .terms
                .get(degree)
                .cloned()
                .or_else(|| (degree == end).then(|| terminal.clone()))
                .unwrap_or_else(|| Module::zero(algebra))
        })
        .collect()
}

pub(super) fn chain_maps(
    resolution: &ProjectiveResolution,
    start: usize,
    count: usize,
    terms: &[Module],
) -> Vec<Morphism> {
    (0..count)
        .map(|i| {
            resolution.maps.get(start + i).cloned().unwrap_or_else(|| {
                crate::hom::zero_morphism(&terms[i + 1], &terms[i])
                    .expect("chain terms share one algebra")
            })
        })
        .collect()
}

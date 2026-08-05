//! Ext dimensions and global dimension via minimal resolutions and Yoneda bases.
//!
//! `Ext^k(M, N)` is the cohomology of `Hom_A(P_•, N)` for a projective resolution
//! `P_• → M`. Every term produced by [`projective_cover`](crate::resolution::projective_cover) is `⊕_v P_v^{t_v}` in a
//! canonical layout, and Yoneda gives `Hom_A(e_v A, N) ≅ N_v`. So `Hom_A(P, N)` has
//! an explicit basis indexed by (generator, basis vector of `N` at its vertex). The
//! element for generator `g` at `v` and index `j` sends the summand basis path
//! `p: v → w` to the `j`-th row of `N(p)`. Coordinates of any morphism in this basis
//! are read off its generator rows. No linear system is solved.
//!
//! Sign convention: the induced cochain maps are `δ^i(f) = f ∘ d_{i+1}` with no
//! signs. Alternating signs only normalize `δ² = 0` under other differentials'
//! conventions. Here `δ² = 0` follows from `d² = 0`. Any sign choice rescales basis
//! vectors without changing ranks, so dimension computations are sign-free.
//!
//! Exactness: [`ext_dim`]`(m, n, k)` resolves `m` for `k + 1` steps. The result is
//! either a complete finite resolution or a prefix with differentials
//! `d_1, …, d_{k+1}`. Cohomology at position `k` needs only `d_k` and `d_{k+1}`,
//! so the answer is exact for every `k`, even when the projective dimension is
//! unknown.

use std::fmt;
use std::sync::Arc;

use crate::algebra::MonomialAlgebra;
use crate::field::{Fp, PrimeField};
use crate::hom::Morphism;
use crate::linalg::DenseMat;
use crate::module::Module;
use crate::radical::top;
use crate::resolution::{Bounded, projective_dimension, resolve};

/// Rejected Ext input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExtError {
    /// The modules live over different algebras (distinct [`Arc`]s).
    DifferentAlgebras,
    /// The modules live over different fields.
    DifferentFields,
}

impl fmt::Display for ExtError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DifferentAlgebras => f.write_str("modules live over different algebras"),
            Self::DifferentFields => f.write_str("modules live over different fields"),
        }
    }
}

impl std::error::Error for ExtError {}

/// Summand layout of a projective term `⊕_v P_v^{t_v}` built by [`projective_cover`](crate::resolution::projective_cover):
/// generators are ordered by vertex then copy. At each vertex the term's basis is the
/// concatenation of the summands' path bases in generator order.
struct Layout {
    /// Vertex of each generator, in canonical order.
    gen_vertex: Vec<u32>,
    /// `offsets[w][g]`: first row of generator `g`'s block in the term at vertex `w`.
    offsets: Vec<Vec<usize>>,
}

/// Recovers the layout from the term alone: `t_v = dim (top P)_v` because
/// `top P_v = S_v`. The block-total assertion fails only if the term is not built
/// by [`projective_cover`](crate::resolution::projective_cover), which never happens inside this module.
fn layout(term: &Module) -> Layout {
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

/// `dim Hom_A(term, n) = Σ_g dim N_{v_g}` by Yoneda.
fn hom_space_dim(lay: &Layout, n: &Module) -> usize {
    lay.gen_vertex.iter().map(|&v| n.dim_at(v)).sum()
}

/// The Yoneda basis of `Hom_A(term, n)`, in canonical (generator, index) order.
fn yoneda_basis(term: &Module, lay: &Layout, n: &Module) -> Vec<Morphism> {
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

/// Coordinates of `f: term → n` in the Yoneda basis: the trivial path `e_v` is the
/// first basis path of every `(v, v)` block, so the coordinate block of generator `g`
/// is row `offsets[v_g][g]` of `f` at `v_g`.
fn coordinates(f: &Morphism, lay: &Layout, n: &Module) -> Vec<Fp> {
    let mut coords = Vec::new();
    for (g, &v) in lay.gen_vertex.iter().enumerate() {
        let row = lay.offsets[v as usize][g];
        for j in 0..n.dim_at(v) {
            coords.push(f.map_at(v).get(row, j));
        }
    }
    coords
}

/// Rank of `δ^i: Hom(P_i, N) → Hom(P_{i+1}, N)`, `f ↦ d.then(f)`, in Yoneda bases.
fn delta_rank(d: &Morphism, term: &Module, lay: &Layout, next_lay: &Layout, n: &Module) -> usize {
    let field = term.field();
    if hom_space_dim(next_lay, n) == 0 {
        return 0;
    }
    let rows: Vec<Vec<Fp>> = yoneda_basis(term, lay, n)
        .iter()
        .map(|f| {
            let composite = d
                .then(f)
                .expect("internal endpoint invariant: d targets the term f leaves");
            coordinates(&composite, next_lay, n)
        })
        .collect();
    if rows.is_empty() {
        return 0;
    }
    DenseMat::from_rows(&rows).rank(&field)
}

fn check_pair(m: &Module, n: &Module) -> Result<(), ExtError> {
    if !Arc::ptr_eq(m.algebra(), n.algebra()) {
        return Err(ExtError::DifferentAlgebras);
    }
    if m.field() != n.field() {
        return Err(ExtError::DifferentFields);
    }
    Ok(())
}

/// `[dim Ext^0(m, n), …, dim Ext^max_k(m, n)]`, each entry exact (see the module
/// docs: the resolution prefix is always long enough). Errors when the modules
/// do not share one algebra and field.
pub fn ext_table(m: &Module, n: &Module, max_k: usize) -> Result<Vec<usize>, ExtError> {
    check_pair(m, n)?;
    let res = resolve(m, max_k + 1);
    let layouts: Vec<Layout> = res.terms.iter().map(layout).collect();
    // A finite resolution continues with zero terms: Hom = 0 and δ = 0 beyond it.
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
    Ok((0..=max_k)
        .map(|k| {
            let kernel_dim = h[k] - ranks[k];
            let boundary = if k == 0 { 0 } else { ranks[k - 1] };
            assert!(
                kernel_dim >= boundary,
                "im δ^{} ⊄ ker δ^{k}; this is a bug in auslander",
                k.wrapping_sub(1)
            );
            kernel_dim - boundary
        })
        .collect())
}

/// `dim Ext^k_A(m, n)`, exact for every `k`. `Ext^0` is `dim Hom_A(m, n)`.
/// Errors when the modules do not share one algebra and field.
pub fn ext_dim(m: &Module, n: &Module, k: usize) -> Result<usize, ExtError> {
    Ok(ext_table(m, n, k)?[k])
}

/// The global dimension of the algebra, resolved up to `bound` differentials.
///
/// Infallible on valid input: the simples it resolves are constructed here over
/// the given algebra and field, so no endpoint or field mismatch can arise.
/// For a finite-dimensional algebra `gldim A = pd (A/rad A) = max_v pd S_v`: every
/// module has a finite composition series with simple factors, so the supremum of
/// projective dimensions is attained on the simples. Returns `Exact` when every
/// simple resolves within `bound`, otherwise `AtLeast(bound + 1)` (the minimal
/// resolution of some simple has a nonzero syzygy past the bound).
pub fn global_dimension(
    algebra: &Arc<MonomialAlgebra>,
    field: PrimeField,
    bound: usize,
) -> Bounded<usize> {
    let mut max = 0usize;
    let mut cut = false;
    for v in 0..algebra.quiver().num_vertices() {
        match projective_dimension(&Module::simple(algebra, field, v), bound) {
            Bounded::Exact(d) => max = max.max(d),
            Bounded::AtLeast(_) => cut = true,
        }
    }
    if cut {
        Bounded::AtLeast(bound + 1)
    } else {
        Bounded::Exact(max)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{
        an_with_relations, dual_numbers, kronecker, linear_an, radical_square_zero_cycle,
        truncated_poly,
    };
    use crate::hom::hom_dim;
    use crate::module::direct_sum;

    fn f5() -> PrimeField {
        PrimeField::new(5).unwrap()
    }

    // Right modules over linearly oriented A_3 (arrows a: 0 → 1, b: 1 → 2). The
    // nonsplit extension realized by arrow a is 0 → S_1 → M → S_0 → 0 with
    // M = P_0/rad² of dimension vector (1, 1, 0), top S_0 and socle S_1, so the
    // nonzero Ext group is Ext¹(S_0, S_1). In general dim Ext¹(S_i, S_j) equals
    // the number of arrows i → j (same pairing as for left modules over A^op read
    // backwards; ASS III.2.12 states it for right modules).
    #[test]
    fn a3_ext_1_between_simples_counts_arrows_source_to_target() {
        let algebra = linear_an(3);
        let field = f5();
        let simples: Vec<Module> = (0..3).map(|v| Module::simple(&algebra, field, v)).collect();
        for i in 0..3 {
            for j in 0..3 {
                let expected = usize::from(j == i + 1);
                assert_eq!(
                    ext_dim(&simples[i], &simples[j], 1).unwrap(),
                    expected,
                    "Ext¹(S_{i}, S_{j})"
                );
                for k in 2..=4 {
                    assert_eq!(
                        ext_dim(&simples[i], &simples[j], k).unwrap(),
                        0,
                        "Ext^{k}(S_{i}, S_{j}) over a gldim-1 algebra"
                    );
                }
            }
        }
        assert_eq!(ext_dim(&simples[1], &simples[0], 1).unwrap(), 0);
        assert_eq!(global_dimension(&algebra, field, 5), Bounded::Exact(1));
    }

    // kA_3/(ab), right modules: pd S_0 = 2 via 0 → P_2 → P_1 → P_0 → S_0 → 0.
    // Ext¹(S_i, S_j) = #arrows i → j gives Ext¹(S_0, S_1) = Ext¹(S_1, S_2) = 1;
    // Ext² is detected by the relation, on the ordered pair (source, target) of the
    // forbidden path: Hom(P_2, S_2) = k sits in degree 2 of the resolution of S_0
    // with zero δ on both sides, so Ext²(S_0, S_2) = 1. These values match the
    // QPA-verified facts (Ext¹(S_0, S_1) = 1, Ext²(S_0, S_2) = 1) on the same
    // ordered pairs, with no right-vs-left discrepancy.
    #[test]
    fn a3_mod_ab_ext_1_and_2_among_simples() {
        let algebra = an_with_relations(3, &[(0, 2)]).unwrap();
        let field = f5();
        let simples: Vec<Module> = (0..3).map(|v| Module::simple(&algebra, field, v)).collect();
        for i in 0..3 {
            for j in 0..3 {
                let ext1 = usize::from(j == i + 1);
                let ext2 = usize::from(i == 0 && j == 2);
                assert_eq!(
                    ext_dim(&simples[i], &simples[j], 1).unwrap(),
                    ext1,
                    "Ext¹(S_{i}, S_{j})"
                );
                assert_eq!(
                    ext_dim(&simples[i], &simples[j], 2).unwrap(),
                    ext2,
                    "Ext²(S_{i}, S_{j})"
                );
                assert_eq!(ext_dim(&simples[i], &simples[j], 3).unwrap(), 0);
            }
        }
        assert_eq!(global_dimension(&algebra, field, 5), Bounded::Exact(2));
    }

    #[test]
    fn dual_numbers_ext_table_of_the_simple_is_all_ones() {
        let algebra = dual_numbers();
        let field = f5();
        let s = Module::simple(&algebra, field, 0);
        assert_eq!(ext_table(&s, &s, 4).unwrap(), vec![1, 1, 1, 1, 1]);
        assert_eq!(global_dimension(&algebra, field, 6), Bounded::AtLeast(7));
    }

    // k[x]/(x³) over F_3: the minimal resolution of S is Ω-periodic with period 2
    // (Ω S = rad P has dimension 2, Ω² S = soc P ≅ S), every term is P, and
    // Hom(P, S) = k with zero differentials throughout.
    #[test]
    fn truncated_poly_3_ext_table_of_the_simple_is_all_ones() {
        let algebra = truncated_poly(3).unwrap();
        let field = PrimeField::new(3).unwrap();
        let s = Module::simple(&algebra, field, 0);
        let res = resolve(&s, 5);
        for term in &res.terms {
            assert_eq!(term.dim_vector(), &[3]);
        }
        assert_eq!(ext_table(&s, &s, 4).unwrap(), vec![1, 1, 1, 1, 1]);
    }

    // Cycle 0 → 1 → 2 → 0 with rad² = 0, right modules: rad P_i = S_{i+1}, so
    // Ω S_i = S_{i+1} and the extension realized by the arrow i → i+1 gives
    // Ext¹(S_i, S_{i+1}) = 1 while Ext¹(S_i, S_{i-1}) = 0: the pairing again runs
    // from arrow source to arrow target.
    #[test]
    fn radical_square_zero_cycle_ext_1_follows_the_arrows() {
        let algebra = radical_square_zero_cycle(3);
        let field = f5();
        let simples: Vec<Module> = (0..3).map(|v| Module::simple(&algebra, field, v)).collect();
        for i in 0..3 {
            for j in 0..3 {
                let expected = usize::from(j == (i + 1) % 3);
                assert_eq!(
                    ext_dim(&simples[i], &simples[j], 1).unwrap(),
                    expected,
                    "Ext¹(S_{i}, S_{j})"
                );
            }
        }
        assert_eq!(global_dimension(&algebra, field, 4), Bounded::AtLeast(5));
    }

    // Regression against the old examples-db, which listed hereditary Kronecker
    // algebras as having infinite global dimension.
    #[test]
    fn kronecker_2_is_hereditary_with_global_dimension_1() {
        let algebra = kronecker(2);
        assert_eq!(global_dimension(&algebra, f5(), 5), Bounded::Exact(1));
    }

    fn assorted_pairs() -> Vec<(Module, Module)> {
        let field = f5();
        let mut pairs = Vec::new();
        for algebra in [
            linear_an(3),
            an_with_relations(3, &[(0, 2)]).unwrap(),
            dual_numbers(),
            radical_square_zero_cycle(3),
        ] {
            let n = algebra.quiver().num_vertices();
            for v in 0..n {
                let s = Module::simple(&algebra, field, v);
                let p = Module::projective(&algebra, field, v);
                let i = Module::injective(&algebra, field, v);
                pairs.push((s.clone(), i.clone()));
                pairs.push((i, s.clone()));
                pairs.push((s.clone(), p.clone()));
                pairs.push((p, s));
            }
            let s0 = Module::simple(&algebra, field, 0);
            let i_last = Module::injective(&algebra, field, n - 1);
            let (sum, _, _) = direct_sum(&[&s0, &i_last]);
            pairs.push((sum.clone(), s0));
            pairs.push((sum.clone(), sum));
        }
        pairs
    }

    #[test]
    fn ext_0_equals_hom_dim() {
        for (m, n) in assorted_pairs() {
            assert_eq!(
                ext_dim(&m, &n, 0).unwrap(),
                hom_dim(&m, &n).unwrap(),
                "Ext⁰ with dim m = {:?}, dim n = {:?}",
                m.dim_vector(),
                n.dim_vector()
            );
        }
    }

    // The Yoneda basis must agree with the generic commuting-square solver: same
    // dimension for Hom(P, N) on every resolution term, and the canonical
    // coordinates of the Yoneda basis form the identity matrix.
    #[test]
    fn yoneda_basis_agrees_with_generic_hom_on_resolution_terms() {
        let field = f5();
        for (m, n) in assorted_pairs() {
            let res = resolve(&m, 2);
            for term in &res.terms {
                let lay = layout(term);
                assert_eq!(hom_space_dim(&lay, &n), hom_dim(term, &n).unwrap());
                let basis = yoneda_basis(term, &lay, &n);
                for (i, f) in basis.iter().enumerate() {
                    let coords = coordinates(f, &lay, &n);
                    for (c, &val) in coords.iter().enumerate() {
                        let expected = if c == i { field.one() } else { field.zero() };
                        assert_eq!(val, expected, "coordinate {c} of basis element {i}");
                    }
                }
            }
        }
    }

    #[test]
    fn ext_beyond_a_finite_resolution_is_zero() {
        let algebra = an_with_relations(3, &[(0, 2)]).unwrap();
        let field = f5();
        let s0 = Module::simple(&algebra, field, 0);
        let s2 = Module::simple(&algebra, field, 2);
        assert_eq!(ext_table(&s0, &s2, 6).unwrap(), vec![0, 0, 1, 0, 0, 0, 0]);
    }
}

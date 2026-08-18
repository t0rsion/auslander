//! Projective covers and minimal projective resolutions with explicit status.
//!
//! The cover of `M` is `⊕_v P_v^{dim (top M)_v}`, so every syzygy inclusion lands
//! in the radical of its cover. The resolution [`resolve`] computes is therefore
//! minimal by construction: each differential induces the zero map on tops.
//!
//! A computed prefix always says how it ends. [`ResolutionEnd::Finite`] means the
//! resolution reaches zero. [`ResolutionEnd::Cut`] means the step budget runs out
//! with the next syzygy nonzero, and nothing is claimed past that point. Partial
//! homological invariants come back as [`Bounded`], never as a silently truncated
//! number.

use crate::field::Fp;
use crate::hom::{Morphism, kernel, zero_morphism};
use crate::linalg::DenseMat;
use crate::module::{Module, direct_sum};
use crate::opposite::ElementMatrix;
use crate::radical::top;

/// How a computed resolution prefix ends.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ResolutionEnd {
    /// The syzygy after the last term is zero. The sequence
    /// `0 → P_L → … → P_0 → M → 0` with `L = terms.len() − 1` is a complete minimal
    /// resolution. For nonzero `M`, `pd M = L` (a minimal cover of a nonzero module
    /// is nonzero, so every term counts).
    Finite,
    /// The prefix holds exactly `at` differentials and the next syzygy `Ω^{at+1} M`
    /// is nonzero. The prefix is a genuine initial segment of a minimal resolution.
    /// Nothing is claimed about any term beyond it.
    Cut { at: usize },
}

/// A value known exactly or bounded from below.
///
/// `AtLeast(n)` asserts one thing: the true value is at least `n`. It does not
/// claim the value is finite, and it does not claim the value is infinite. This
/// crate never uses `None` to mean infinity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Bounded<T> {
    Exact(T),
    AtLeast(T),
}

/// A minimal projective resolution prefix `… → P_1 → P_0 → M → 0`.
///
/// Layout: `terms[k]` is `P_k`; `maps[k]` is the differential `d_{k+1}: P_{k+1} → P_k`,
/// so `maps.len() == terms.len() − 1`; `augmentation` is the cover `P_0 → M`.
/// Minimality: each `d_{k+1}` factors as `P_{k+1} ↠ Ω^{k+1} M ↪ P_k` with the syzygy
/// contained in `rad P_k`, so the induced map `top P_{k+1} → top P_k` is zero.
pub struct ProjectiveResolution {
    pub terms: Vec<Module>,
    pub maps: Vec<Morphism>,
    pub augmentation: Morphism,
    pub end: ResolutionEnd,
}

/// The projective cover `P = ⊕_v P_v^{dim (top M)_v} ↠ M`.
///
/// The generator of the summand copy at `v` maps to a lift through `M ↠ top M` of the
/// corresponding top basis vector. The summand basis path `p: v → w` maps to
/// `lift · M(p)`. The cover induces an isomorphism on tops, so by Nakayama it is
/// surjective with kernel inside `rad P`. For the zero module the cover is the zero
/// module.
///
/// # Panics
/// Panics if the constructed map fails its surjectivity rank check. Such a failure
/// is a bug in this crate, not bad input.
pub fn projective_cover(m: &Module) -> (Module, Morphism) {
    let field = m.field();
    let algebra = m.algebra().clone();
    if m.is_zero() {
        let p = Module::zero(&algebra);
        let cover = zero_morphism(&p, m).expect("zero module shares its algebra with m");
        return (p, cover);
    }
    let quiver = algebra.quiver();
    let n = quiver.num_vertices();
    let (top_m, projection) = top(m);
    // One generator per top basis vector: a row vector x ∈ M_v with x · projection_v
    // equal to the unit vector, i.e. projection_vᵀ · xᵀ = e_j. The unit vectors
    // at one vertex are the identity, so all of them lift in one elimination.
    let mut generators: Vec<(u32, Vec<Fp>)> = Vec::new();
    for v in 0..n {
        if top_m.dim_at(v) == 0 {
            continue;
        }
        let lifts = projection
            .map_at(v)
            .transpose()
            .solve_many(&DenseMat::identity(top_m.dim_at(v)), &field)
            .expect("top projection is surjective, so every unit vector lifts");
        for j in 0..top_m.dim_at(v) {
            generators.push((v, (0..lifts.rows()).map(|i| lifts.get(i, j)).collect()));
        }
    }
    let projectives: Vec<Module> = (0..n).map(|v| Module::projective(&algebra, v)).collect();
    let parts: Vec<&Module> = generators
        .iter()
        .map(|&(v, _)| &projectives[v as usize])
        .collect();
    let (p, _, _) = direct_sum(&parts);
    let mut maps: Vec<DenseMat> = (0..n)
        .map(|w| DenseMat::zero(p.dim_at(w), m.dim_at(w)))
        .collect();
    let mut cursor = vec![0usize; n as usize];
    for (v, lift) in &generators {
        for w in 0..n {
            for &b in algebra.paths_between(*v, w) {
                // Row for basis path p: v → w of this summand is lift · M(p).
                let row = m
                    .word_action(&algebra.basis()[b])
                    .expect("algebra basis words are valid in their own quiver")
                    .transpose()
                    .mul_vec(lift, &field);
                for (c, &val) in row.iter().enumerate() {
                    maps[w as usize].set(cursor[w as usize], c, val);
                }
                cursor[w as usize] += 1;
            }
        }
    }
    for w in 0..n {
        assert_eq!(
            maps[w as usize].rank(&field),
            m.dim_at(w),
            "projective_cover: cover map fails to surject at vertex {w}; \
             this is a bug in auslander"
        );
    }
    let cover = Morphism::new(&p, m, maps).expect("cover map satisfies the commuting squares");
    (p, cover)
}

/// A minimal projective resolution of `m` with at most `steps` differentials
/// (`terms.len() ≤ steps + 1`).
///
/// Iterates cover → kernel → cover. It stops with [`ResolutionEnd::Finite`] as soon
/// as a syzygy is zero, including at the step boundary, so `Cut { at: steps }` always
/// means the `(steps + 1)`-st syzygy is genuinely nonzero.
///
/// Two guarantees hold by construction, not by a later check. Exactness: the
/// augmentation is onto `m`, and every `d_{k+1}` is a cover of `Ω^{k+1} m` followed
/// by the inclusion of that syzygy, so its image is exactly the kernel of the map
/// before it (the augmentation when `k = 0`, otherwise `d_k`). Minimality:
/// covers are built from tops, so each syzygy lies in the radical of its cover and
/// each differential induces the zero map on tops.
pub fn resolve(m: &Module, steps: usize) -> ProjectiveResolution {
    let (p0, augmentation) = projective_cover(m);
    let mut terms = vec![p0];
    let mut maps: Vec<Morphism> = Vec::new();
    let (mut syzygy, mut inclusion) = kernel(&augmentation);
    let end = loop {
        if syzygy.is_zero() {
            break ResolutionEnd::Finite;
        }
        if maps.len() == steps {
            break ResolutionEnd::Cut { at: steps };
        }
        let (p, cover) = projective_cover(&syzygy);
        let differential = cover
            .then(&inclusion)
            .expect("internal endpoint invariant: cover targets the syzygy the inclusion leaves");
        let (next_syzygy, next_inclusion) = kernel(&cover);
        terms.push(p);
        maps.push(differential);
        syzygy = next_syzygy;
        inclusion = next_inclusion;
    };
    ProjectiveResolution {
        terms,
        maps,
        augmentation,
        end,
    }
}

/// The projective dimension of `m`, resolved up to `bound` differentials.
///
/// Returns `Exact(n)` with `n ≤ bound` when the minimal resolution reaches zero by
/// step `bound`, and `AtLeast(bound + 1)` otherwise. The lower bound is genuine: the
/// resolution is minimal, so a nonzero `(bound + 1)`-st syzygy proves `pd m > bound`.
/// `AtLeast(bound + 1)` says nothing more than that; it is not a claim that `pd m`
/// is infinite. Convention: the zero module is projective (the empty sum), so
/// `pd 0 = Exact(0)`.
pub fn projective_dimension(m: &Module, bound: usize) -> Bounded<usize> {
    match resolve(m, bound) {
        ProjectiveResolution {
            end: ResolutionEnd::Finite,
            terms,
            ..
        } => Bounded::Exact(terms.len() - 1),
        ProjectiveResolution {
            end: ResolutionEnd::Cut { at },
            ..
        } => Bounded::AtLeast(at + 1),
    }
}

/// The minimal presentation differential `d_1: P_1 → P_0` of `m` in element-matrix
/// form.
///
/// The source summands are the cover summands of `Ω¹ m`, the target summands those
/// of `m`. Each side is `⊕_v P_v^{dim (top −)_v}` in increasing vertex order, the
/// layout of [`projective_cover`]. The entry at `(k, l)` is the element whose left
/// multiplication is the `(k, l)` component of `d_1`. A projective `m` has no source
/// summands.
pub fn minimal_presentation_matrix(m: &Module) -> ElementMatrix {
    let resolution = resolve(m, 1);
    let targets = cover_summands(m);
    match resolution.maps.first() {
        None => ElementMatrix::new(m.algebra().clone(), Vec::new(), targets, Vec::new())
            .expect("cover summand vertices are in range"),
        Some(d1) => {
            // P_1 covers Ω¹ m and shares its top, so its summands are read off
            // top P_1.
            let sources = cover_summands(&resolution.terms[1]);
            ElementMatrix::of_morphism(d1, &sources, &targets)
                .expect("covers are laid out as the standard direct sums")
        }
    }
}

/// Vertex `v` repeated `dim (top m)_v` times, in increasing vertex order: the
/// summand vertices of the cover of `m`.
fn cover_summands(m: &Module) -> Vec<u32> {
    let (top_m, _) = top(m);
    let mut vertices = Vec::new();
    for v in 0..m.algebra().quiver().num_vertices() {
        for _ in 0..top_m.dim_at(v) {
            vertices.push(v);
        }
    }
    vertices
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{
        an_with_relations, dual_numbers, linear_an, radical_square_zero_cycle, truncated_poly,
    };
    use crate::field::PrimeField;
    use crate::hom::image;

    fn f5() -> PrimeField {
        PrimeField::new(5).unwrap()
    }

    #[test]
    fn cover_of_a_simple_is_the_indecomposable_projective() {
        let field = f5();
        for algebra in [
            linear_an(3, field),
            an_with_relations(3, &[(0, 2)], field).unwrap(),
        ] {
            for v in 0..algebra.quiver().num_vertices() {
                let s = Module::simple(&algebra, v);
                let (p, cover) = projective_cover(&s);
                let pv = Module::projective(&algebra, v);
                assert_eq!(p.dim_vector(), pv.dim_vector(), "cover of S_{v}");
                assert!(!cover.is_zero());
            }
        }
    }

    #[test]
    fn cover_of_the_zero_module_is_zero() {
        let algebra = linear_an(3, f5());
        let z = Module::zero(&algebra);
        let (p, cover) = projective_cover(&z);
        assert!(p.is_zero());
        assert!(cover.is_zero());
        let res = resolve(&z, 4);
        assert_eq!(res.end, ResolutionEnd::Finite);
        assert_eq!(res.terms.len(), 1);
        assert_eq!(projective_dimension(&z, 4), Bounded::Exact(0));
    }

    #[test]
    fn a3_simples_have_pd_1_1_0() {
        let field = f5();
        let algebra = linear_an(3, field);
        let expected = [1usize, 1, 0];
        for v in 0..3u32 {
            let s = Module::simple(&algebra, v);
            assert_eq!(
                projective_dimension(&s, 5),
                Bounded::Exact(expected[v as usize]),
                "pd S_{v}"
            );
        }
    }

    #[test]
    fn a3_projectives_resolve_finitely_in_one_term() {
        let field = f5();
        let algebra = linear_an(3, field);
        for v in 0..3u32 {
            let p = Module::projective(&algebra, v);
            let res = resolve(&p, 5);
            assert_eq!(res.end, ResolutionEnd::Finite, "P_{v}");
            assert_eq!(res.terms.len(), 1, "P_{v}");
            assert!(res.maps.is_empty());
        }
    }

    // Over kA_3/(ab) with arrows a: 0 → 1, b: 1 → 2 (right modules): P_0 = e_0 A has
    // basis {e_0, a}, so rad P_0 = S_1; the cover of S_1 is P_1 with rad P_1 = S_2 =
    // P_2. Hence 0 → P_2 → P_1 → P_0 → S_0 → 0 and pd S_0 = 2.
    #[test]
    fn a3_mod_ab_simple_0_has_pd_2_with_terms_p0_p1_p2() {
        let field = f5();
        let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
        let s0 = Module::simple(&algebra, 0);
        let res = resolve(&s0, 5);
        assert_eq!(res.end, ResolutionEnd::Finite);
        let dims: Vec<&[usize]> = res.terms.iter().map(Module::dim_vector).collect();
        assert_eq!(dims, vec![&[1, 1, 0][..], &[0, 1, 1], &[0, 0, 1]]);
        assert_eq!(projective_dimension(&s0, 5), Bounded::Exact(2));
        let s1 = Module::simple(&algebra, 1);
        let s2 = Module::simple(&algebra, 2);
        assert_eq!(projective_dimension(&s1, 5), Bounded::Exact(1));
        assert_eq!(projective_dimension(&s2, 5), Bounded::Exact(0));
    }

    // k[x]/(x²): Ω S = S forever, so the minimal resolution is … → P → P → S with
    // every term the regular module of dimension 2.
    #[test]
    fn dual_numbers_simple_resolves_periodically_and_pd_is_at_least_bound_plus_1() {
        let field = f5();
        let algebra = dual_numbers(field);
        let s = Module::simple(&algebra, 0);
        let res = resolve(&s, 6);
        assert_eq!(res.end, ResolutionEnd::Cut { at: 6 });
        assert_eq!(res.terms.len(), 7);
        for term in &res.terms {
            assert_eq!(term.dim_vector(), &[2]);
        }
        assert_eq!(projective_dimension(&s, 10), Bounded::AtLeast(11));
    }

    #[test]
    fn resolve_with_zero_steps_reports_cut_for_a_nonprojective_module() {
        let field = f5();
        let algebra = dual_numbers(field);
        let s = Module::simple(&algebra, 0);
        let res = resolve(&s, 0);
        assert_eq!(res.end, ResolutionEnd::Cut { at: 0 });
        assert_eq!(res.terms.len(), 1);
        let p = Module::projective(&algebra, 0);
        assert_eq!(resolve(&p, 0).end, ResolutionEnd::Finite);
    }

    #[test]
    fn radical_square_zero_cycle_simples_have_unbounded_pd() {
        let field = f5();
        let algebra = radical_square_zero_cycle(3, field);
        for v in 0..3u32 {
            let s = Module::simple(&algebra, v);
            assert_eq!(projective_dimension(&s, 7), Bounded::AtLeast(8), "pd S_{v}");
        }
    }

    fn assorted_modules() -> Vec<Module> {
        let field = f5();
        let mut modules = Vec::new();
        for algebra in [
            linear_an(3, field),
            an_with_relations(3, &[(0, 2)], field).unwrap(),
            dual_numbers(field),
            truncated_poly(3, field).unwrap(),
            radical_square_zero_cycle(3, field),
        ] {
            for v in 0..algebra.quiver().num_vertices() {
                modules.push(Module::simple(&algebra, v));
                modules.push(Module::injective(&algebra, v));
            }
            let s0 = Module::simple(&algebra, 0);
            let i_last = Module::injective(&algebra, algebra.quiver().num_vertices() - 1);
            let (sum, _, _) = direct_sum(&[&s0, &i_last]);
            modules.push(sum);
        }
        modules
    }

    #[test]
    fn resolution_prefixes_are_complexes_and_exact() {
        let field = f5();
        for m in assorted_modules() {
            let res = resolve(&m, 4);
            for v in 0..m.algebra().quiver().num_vertices() {
                assert_eq!(
                    res.augmentation.map_at(v).rank(&field),
                    m.dim_at(v),
                    "augmentation surjective at vertex {v}"
                );
            }
            for pair in res.maps.windows(2) {
                assert!(pair[1].then(&pair[0]).unwrap().is_zero(), "d² = 0");
            }
            if let Some(d1) = res.maps.first() {
                assert!(
                    d1.then(&res.augmentation).unwrap().is_zero(),
                    "aug ∘ d_1 = 0"
                );
            }
            for k in 0..res.terms.len() {
                let (ker, _) = if k == 0 {
                    kernel(&res.augmentation)
                } else {
                    kernel(&res.maps[k - 1])
                };
                if k + 1 < res.terms.len() {
                    let (im, _) = image(&res.maps[k]);
                    assert_eq!(ker.dim_vector(), im.dim_vector(), "exactness at P_{k}");
                } else if res.end == ResolutionEnd::Finite {
                    assert!(ker.is_zero(), "finite resolution ends exactly");
                }
            }
        }
    }

    #[test]
    fn minimal_presentation_matrix_realizes_the_first_differential() {
        for m in assorted_modules() {
            let res = resolve(&m, 1);
            let matrix = minimal_presentation_matrix(&m);
            let f = matrix.morphism();
            let (p0, _) = projective_cover(&m);
            assert_eq!(f.target().dim_vector(), p0.dim_vector());
            match res.maps.first() {
                None => {
                    assert!(matrix.sources().is_empty());
                    assert!(f.source().is_zero());
                }
                Some(d1) => {
                    for v in 0..m.algebra().quiver().num_vertices() {
                        assert_eq!(f.map_at(v), d1.map_at(v), "d_1 at vertex {v}");
                    }
                }
            }
        }
    }

    #[test]
    fn minimal_presentation_matrix_of_a_projective_has_no_source_summands() {
        let algebra = linear_an(3, f5());
        let p1 = Module::projective(&algebra, 1);
        let matrix = minimal_presentation_matrix(&p1);
        assert!(matrix.sources().is_empty());
        assert_eq!(matrix.targets(), &[1]);
    }

    // Minimality is exactly "differentials land in the radical", i.e. the induced
    // maps top P_{k+1} → top P_k vanish.
    #[test]
    fn differentials_induce_zero_on_tops() {
        for m in assorted_modules() {
            let res = resolve(&m, 4);
            for (k, d) in res.maps.iter().enumerate() {
                let (_, projection) = top(&res.terms[k]);
                assert!(
                    d.then(&projection).unwrap().is_zero(),
                    "d_{} lands in the radical",
                    k + 1
                );
            }
        }
    }
}

//! Projective covers and minimal projective resolutions with explicit status.
//!
//! The cover of `M` is `⊕_v P_v^{dim (top M)_v}`, so every syzygy inclusion lands in
//! the radical of its cover and the resolution computed by [`resolve`] is minimal by
//! construction: the differentials induce zero maps on tops. A computed prefix always
//! says how it ended: [`ResolutionEnd::Finite`] when the resolution reached zero,
//! [`ResolutionEnd::Cut`] when the step budget ran out. Partial homological invariants
//! are reported through [`Bounded`], never as silently truncated numbers.

use crate::field::Fp;
use crate::hom::{Morphism, kernel, zero_morphism};
use crate::linalg::DenseMat;
use crate::module::{Module, direct_sum};
use crate::radical::top;

/// How a computed resolution prefix ends.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResolutionEnd {
    /// The syzygy after the last term is zero: the sequence
    /// `0 → P_L → … → P_0 → M → 0` with `L = terms.len() − 1` is a complete minimal
    /// resolution, and `pd M = L` for nonzero `M` (a minimal cover of a nonzero
    /// module is nonzero, so every term counts).
    Finite,
    /// Exactly `at` differentials were computed and the next syzygy `Ω^{at+1} M` is
    /// nonzero. The prefix is a genuine initial segment of a minimal resolution;
    /// nothing is claimed about any term beyond it.
    Cut { at: usize },
}

/// A value known exactly or bounded from below.
///
/// `AtLeast(n)` asserts only that the true value is `≥ n`; in particular it does not
/// claim the value finite or infinite. `None`-means-infinite conventions are banned
/// from this crate.
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
/// corresponding top basis vector, and the summand basis path `p: v → w` to
/// `lift · M(p)`; the cover induces an isomorphism on tops, so by Nakayama it is
/// surjective with kernel inside `rad P`. For the zero module the cover is the zero
/// module.
///
/// # Panics
/// Panics if the constructed map fails its surjectivity rank check; that would be a
/// bug in this crate, not bad input.
pub fn projective_cover(m: &Module) -> (Module, Morphism) {
    let field = m.field();
    let algebra = m.algebra().clone();
    if m.is_zero() {
        let p = Module::zero(&algebra, field);
        let cover = zero_morphism(&p, m).expect("zero module shares algebra and field with m");
        return (p, cover);
    }
    let quiver = algebra.quiver();
    let n = quiver.num_vertices();
    let (top_m, projection) = top(m);
    // One generator per top basis vector: a row vector x ∈ M_v with x · projection_v
    // equal to the unit vector, i.e. projection_vᵀ · xᵀ = e_j.
    let mut generators: Vec<(u32, Vec<Fp>)> = Vec::new();
    for v in 0..n {
        let pt = projection.map_at(v).transpose();
        for j in 0..top_m.dim_at(v) {
            let mut unit = vec![field.zero(); top_m.dim_at(v)];
            unit[j] = field.one();
            let lift = pt
                .solve(&unit, &field)
                .expect("top projection is surjective, so every unit vector lifts");
            generators.push((v, lift));
        }
    }
    let projectives: Vec<Module> = (0..n)
        .map(|v| Module::projective(&algebra, field, v))
        .collect();
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
/// Iterates cover → kernel → cover; stops with [`ResolutionEnd::Finite`] as soon as a
/// syzygy is zero, including at the step boundary, so `Cut { at: steps }` always
/// means the `(steps + 1)`-st syzygy is genuinely nonzero. Minimality holds by
/// construction: covers are built from tops, so each syzygy lies in the radical of
/// its cover.
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
/// step `bound`, and `AtLeast(bound + 1)` otherwise. The lower bound is genuine, not
/// a shrug: the resolution is minimal, so a nonzero `(bound + 1)`-st syzygy proves
/// `pd m > bound`. Hitting the bound is never conflated with infinite dimension.
/// Convention: the zero module is projective (the empty sum), so `pd 0 = Exact(0)`.
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
        for algebra in [linear_an(3), an_with_relations(3, &[(0, 2)]).unwrap()] {
            for v in 0..algebra.quiver().num_vertices() {
                let s = Module::simple(&algebra, field, v);
                let (p, cover) = projective_cover(&s);
                let pv = Module::projective(&algebra, field, v);
                assert_eq!(p.dim_vector(), pv.dim_vector(), "cover of S_{v}");
                assert!(!cover.is_zero());
            }
        }
    }

    #[test]
    fn cover_of_the_zero_module_is_zero() {
        let algebra = linear_an(3);
        let z = Module::zero(&algebra, f5());
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
        let algebra = linear_an(3);
        let field = f5();
        let expected = [1usize, 1, 0];
        for v in 0..3u32 {
            let s = Module::simple(&algebra, field, v);
            assert_eq!(
                projective_dimension(&s, 5),
                Bounded::Exact(expected[v as usize]),
                "pd S_{v}"
            );
        }
    }

    #[test]
    fn a3_projectives_resolve_finitely_in_one_term() {
        let algebra = linear_an(3);
        let field = f5();
        for v in 0..3u32 {
            let p = Module::projective(&algebra, field, v);
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
        let algebra = an_with_relations(3, &[(0, 2)]).unwrap();
        let field = f5();
        let s0 = Module::simple(&algebra, field, 0);
        let res = resolve(&s0, 5);
        assert_eq!(res.end, ResolutionEnd::Finite);
        let dims: Vec<&[usize]> = res.terms.iter().map(Module::dim_vector).collect();
        assert_eq!(dims, vec![&[1, 1, 0][..], &[0, 1, 1], &[0, 0, 1]]);
        assert_eq!(projective_dimension(&s0, 5), Bounded::Exact(2));
        let s1 = Module::simple(&algebra, field, 1);
        let s2 = Module::simple(&algebra, field, 2);
        assert_eq!(projective_dimension(&s1, 5), Bounded::Exact(1));
        assert_eq!(projective_dimension(&s2, 5), Bounded::Exact(0));
    }

    // k[x]/(x²): Ω S = S forever, so the minimal resolution is … → P → P → S with
    // every term the regular module of dimension 2.
    #[test]
    fn dual_numbers_simple_resolves_periodically_and_pd_is_at_least_bound_plus_1() {
        let algebra = dual_numbers();
        let field = f5();
        let s = Module::simple(&algebra, field, 0);
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
        let algebra = dual_numbers();
        let field = f5();
        let s = Module::simple(&algebra, field, 0);
        let res = resolve(&s, 0);
        assert_eq!(res.end, ResolutionEnd::Cut { at: 0 });
        assert_eq!(res.terms.len(), 1);
        let p = Module::projective(&algebra, field, 0);
        assert_eq!(resolve(&p, 0).end, ResolutionEnd::Finite);
    }

    #[test]
    fn radical_square_zero_cycle_simples_have_unbounded_pd() {
        let algebra = radical_square_zero_cycle(3);
        let field = f5();
        for v in 0..3u32 {
            let s = Module::simple(&algebra, field, v);
            assert_eq!(projective_dimension(&s, 7), Bounded::AtLeast(8), "pd S_{v}");
        }
    }

    fn assorted_modules() -> Vec<Module> {
        let field = f5();
        let mut modules = Vec::new();
        for algebra in [
            linear_an(3),
            an_with_relations(3, &[(0, 2)]).unwrap(),
            dual_numbers(),
            truncated_poly(3).unwrap(),
            radical_square_zero_cycle(3),
        ] {
            for v in 0..algebra.quiver().num_vertices() {
                modules.push(Module::simple(&algebra, field, v));
                modules.push(Module::injective(&algebra, field, v));
            }
            let s0 = Module::simple(&algebra, field, 0);
            let i_last = Module::injective(&algebra, field, algebra.quiver().num_vertices() - 1);
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

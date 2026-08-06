//! Injective envelopes and minimal injective coresolutions, dual to
//! [`crate::resolution`].
//!
//! Each construction here is the image under the k-dual `D` of the matching
//! projective construction over the opposite algebra. `D` preserves dimension
//! vectors and transposes every arrow matrix (see [`crate::opposite::dual`]), so
//! it is exact. It carries the projective cover of `D(M)` over `A^op` to the
//! injective envelope of `M`, and a minimal projective resolution of `D(M)` to a
//! minimal injective coresolution of `M`. Minimality transports with it: a
//! superfluous epimorphism dualizes to an essential monomorphism, so `soc I^k`
//! lies in the kernel of `d^k` at every step. Partial coresolutions carry the
//! same typed status as projective resolutions, [`ResolutionEnd`] and
//! [`Bounded`].

use crate::algebra::AlgebraBuildError;
use crate::hom::Morphism;
use crate::module::Module;
use crate::opposite::{dual, dual_morphism, opposite};
use crate::resolution::{Bounded, ResolutionEnd, projective_cover, resolve};

/// The injective envelope `M ↪ I(M)` with `I(M) ≅ ⊕_v I_v^{dim (soc M)_v}`.
///
/// The map is a monomorphism with essential image, dual to the minimality of
/// [`projective_cover`]: it is `D` of the projective cover of `D(M)` over the
/// opposite algebra. The returned morphism has `m` itself as its source.
/// For the zero module both the envelope and the map are zero. Errors when
/// building the opposite algebra fails (see [`opposite`]).
///
/// # Panics
/// Panics if the dual of the cover fails one of the duality checks of
/// [`dual_morphism`]. Such a failure is a bug in this crate, not bad input.
pub fn injective_envelope(m: &Module) -> Result<(Module, Morphism), AlgebraBuildError> {
    let op = opposite(m.algebra())?;
    let dm = dual(m, &op).expect("m lives over the algebra side of its own opposite pair");
    let (cover_term, cover) = projective_cover(&dm);
    let envelope =
        dual(&cover_term, &op).expect("the cover of D(m) lives over the opposite side of the pair");
    let embedding = dual_morphism(&cover, m, &envelope, &op)
        .expect("D(D(m)) is m entry for entry, and the envelope is D of the cover term");
    Ok((envelope, embedding))
}

/// A minimal injective coresolution prefix `0 → M → I^0 → I^1 → …`.
///
/// Layout: `terms[k]` is `I^k`; `maps[k]` is the differential `d^k: I^k → I^{k+1}`,
/// so `maps.len() == terms.len() − 1`; `coaugmentation` is the envelope `M ↪ I^0`.
/// Minimality: each `d^k` factors as `I^k ↠ C^{k+1} ↪ I^{k+1}` with the cosyzygy
/// `C^{k+1}` essential in `I^{k+1}`, so `soc I^k` lies in `ker d^k`.
pub struct InjectiveCoresolution {
    pub terms: Vec<Module>,
    pub maps: Vec<Morphism>,
    pub coaugmentation: Morphism,
    pub end: ResolutionEnd,
}

/// A minimal injective coresolution of `m` with at most `steps` differentials
/// (`terms.len() ≤ steps + 1`).
///
/// The dual of [`resolve`] applied to `D(m)` over the opposite algebra, term by
/// term and map by map. [`ResolutionEnd::Finite`] means the cosyzygy after the
/// last term is zero, so `0 → M → I^0 → … → I^L → 0` is exact.
/// `Cut { at: steps }` means the `(steps + 1)`-st cosyzygy is genuinely nonzero.
/// Errors when building the opposite algebra fails (see [`opposite`]).
pub fn coresolve(m: &Module, steps: usize) -> Result<InjectiveCoresolution, AlgebraBuildError> {
    let op = opposite(m.algebra())?;
    let dm = dual(m, &op).expect("m lives over the algebra side of its own opposite pair");
    let resolution = resolve(&dm, steps);
    let terms: Vec<Module> = resolution
        .terms
        .iter()
        .map(|p| dual(p, &op).expect("resolution terms live over the opposite side of the pair"))
        .collect();
    let coaugmentation = dual_morphism(&resolution.augmentation, m, &terms[0], &op)
        .expect("D(D(m)) is m entry for entry, and terms[0] is D(P_0)");
    let maps = resolution
        .maps
        .iter()
        .enumerate()
        .map(|(k, d)| {
            dual_morphism(d, &terms[k], &terms[k + 1], &op)
                .expect("terms[k] is D(P_k) and terms[k + 1] is D(P_{k+1})")
        })
        .collect();
    Ok(InjectiveCoresolution {
        terms,
        maps,
        coaugmentation,
        end: resolution.end,
    })
}

/// The injective dimension of `m`, coresolved up to `bound` differentials.
///
/// Returns `Exact(n)` with `n ≤ bound` when the minimal coresolution reaches
/// zero by step `bound`, and `AtLeast(bound + 1)` otherwise. The lower bound is
/// genuine: the coresolution is minimal, so a nonzero `(bound + 1)`-st cosyzygy
/// proves `id m > bound`. Convention: the zero module is injective, so
/// `id 0 = Exact(0)`. Errors when building the opposite algebra fails (see
/// [`opposite`]).
pub fn injective_dimension(m: &Module, bound: usize) -> Result<Bounded<usize>, AlgebraBuildError> {
    let coresolution = coresolve(m, bound)?;
    Ok(match coresolution.end {
        ResolutionEnd::Finite => Bounded::Exact(coresolution.terms.len() - 1),
        ResolutionEnd::Cut { at } => Bounded::AtLeast(at + 1),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{
        Algebra, an_with_relations, commutative_square, cyclic_nakayama, dual_numbers, linear_an,
        linear_nakayama, radical_square_zero_cycle, truncated_poly,
    };
    use crate::field::PrimeField;
    use crate::hom::{image, kernel};
    use crate::iso::{IsoOutcome, is_isomorphic};
    use crate::module::direct_sum;
    use crate::radical::socle;
    use std::sync::Arc;

    fn fields() -> [PrimeField; 3] {
        [
            PrimeField::new(2).unwrap(),
            PrimeField::new(5).unwrap(),
            PrimeField::new(32003).unwrap(),
        ]
    }

    /// `⊕_v I_v^{dim (soc m)_v}`, built from the socle without any duality.
    fn socle_injective_sum(m: &Module) -> Module {
        let algebra = m.algebra();
        let (soc, _) = socle(m);
        let mut parts = Vec::new();
        for v in 0..algebra.quiver().num_vertices() {
            for _ in 0..soc.dim_at(v) {
                parts.push(Module::injective(algebra, v));
            }
        }
        if parts.is_empty() {
            return Module::zero(algebra);
        }
        let refs: Vec<&Module> = parts.iter().collect();
        direct_sum(&refs).0
    }

    fn is_mono(f: &Morphism) -> bool {
        let field = f.source().field();
        (0..f.source().algebra().quiver().num_vertices())
            .all(|v| f.map_at(v).rank(&field) == f.source().dim_at(v))
    }

    fn fixtures(field: PrimeField) -> Vec<Arc<Algebra>> {
        vec![
            linear_an(3, field),
            an_with_relations(3, &[(0, 2)], field).unwrap(),
            dual_numbers(field),
            truncated_poly(3, field).unwrap(),
            radical_square_zero_cycle(3, field),
            cyclic_nakayama(&[3, 3, 3], field).unwrap(),
            commutative_square(field),
        ]
    }

    fn assorted_modules(algebra: &Arc<Algebra>) -> Vec<Module> {
        let n = algebra.quiver().num_vertices();
        let mut modules = vec![Module::zero(algebra)];
        for v in 0..n {
            modules.push(Module::simple(algebra, v));
            modules.push(Module::projective(algebra, v));
            modules.push(Module::injective(algebra, v));
        }
        let s0 = Module::simple(algebra, 0);
        let p_last = Module::projective(algebra, n - 1);
        modules.push(direct_sum(&[&s0, &p_last]).0);
        modules
    }

    #[test]
    fn envelope_of_a_simple_is_the_indecomposable_injective() {
        for field in fields() {
            for algebra in fixtures(field) {
                for v in 0..algebra.quiver().num_vertices() {
                    let s = Module::simple(&algebra, v);
                    let (envelope, embedding) = injective_envelope(&s).unwrap();
                    let i_v = Module::injective(&algebra, v);
                    assert_eq!(envelope.dim_vector(), i_v.dim_vector(), "I(S_{v})");
                    assert!(is_mono(&embedding));
                    assert!(embedding.source().ptr_eq(&s));
                }
            }
        }
    }

    #[test]
    fn envelope_of_the_zero_module_is_zero() {
        let algebra = linear_an(3, PrimeField::new(5).unwrap());
        let z = Module::zero(&algebra);
        let (envelope, embedding) = injective_envelope(&z).unwrap();
        assert!(envelope.is_zero());
        assert!(embedding.is_zero());
        assert_eq!(injective_dimension(&z, 4).unwrap(), Bounded::Exact(0));
    }

    // Cross-check of the duality route against the socle construction: the
    // envelope is ⊕_v I_v^{dim (soc M)_v}, the embedding is a monomorphism, and
    // its image is essential (a monomorphism whose source and target have equal
    // socle dimensions has soc I inside the image, so it meets every nonzero
    // submodule).
    #[test]
    fn envelope_agrees_with_the_socle_direct_sum_and_is_essential() {
        for field in fields() {
            for algebra in fixtures(field) {
                for m in assorted_modules(&algebra) {
                    let (envelope, embedding) = injective_envelope(&m).unwrap();
                    let by_socle = socle_injective_sum(&m);
                    assert_eq!(
                        envelope.dim_vector(),
                        by_socle.dim_vector(),
                        "envelope of {:?} over F_{}",
                        m.dim_vector(),
                        field.modulus()
                    );
                    assert!(is_mono(&embedding));
                    assert_eq!(
                        socle(&envelope).0.dim_vector(),
                        socle(&m).0.dim_vector(),
                        "essential image for {:?}",
                        m.dim_vector()
                    );
                }
            }
        }
    }

    #[test]
    fn envelope_is_isomorphic_to_the_socle_direct_sum() {
        for field in fields() {
            for algebra in [
                linear_an(3, field),
                an_with_relations(3, &[(0, 2)], field).unwrap(),
            ] {
                for m in assorted_modules(&algebra) {
                    let (envelope, _) = injective_envelope(&m).unwrap();
                    let by_socle = socle_injective_sum(&m);
                    assert!(
                        matches!(
                            is_isomorphic(&envelope, &by_socle).unwrap(),
                            IsoOutcome::Isomorphic(_)
                        ),
                        "envelope of {:?} over F_{}",
                        m.dim_vector(),
                        field.modulus()
                    );
                }
            }
        }
    }

    // Over kA_3 the injectives are I_0 = (1,0,0), I_1 = (1,1,0), I_2 = (1,1,1),
    // so S_0 = I_0 is injective while S_1 and S_2 embed in I_1 and I_2 with
    // cokernels I_0 and I_1.
    #[test]
    fn a3_simples_have_injective_dimensions_0_1_1() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let expected = [0usize, 1, 1];
            for v in 0..3u32 {
                let s = Module::simple(&algebra, v);
                assert_eq!(
                    injective_dimension(&s, 5).unwrap(),
                    Bounded::Exact(expected[v as usize]),
                    "id S_{v}"
                );
            }
        }
    }

    // Over kA_3/(ab) the injectives are I_0 = (1,0,0), I_1 = (1,1,0),
    // I_2 = (0,1,1). The socle of S_2 sits at vertex 2, so I^0 = I_2 and the
    // cokernel is S_1, whose envelope is I_1 with cokernel S_0 = I_0.
    #[test]
    fn a3_mod_ab_simple_2_coresolves_through_i2_i1_i0() {
        for field in fields() {
            let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
            let s2 = Module::simple(&algebra, 2);
            let coresolution = coresolve(&s2, 5).unwrap();
            assert_eq!(coresolution.end, ResolutionEnd::Finite);
            let dims: Vec<&[usize]> = coresolution.terms.iter().map(Module::dim_vector).collect();
            assert_eq!(dims, vec![&[0, 1, 1][..], &[1, 1, 0], &[1, 0, 0]]);
            assert_eq!(injective_dimension(&s2, 5).unwrap(), Bounded::Exact(2));
            let s1 = Module::simple(&algebra, 1);
            let s0 = Module::simple(&algebra, 0);
            assert_eq!(injective_dimension(&s1, 5).unwrap(), Bounded::Exact(1));
            assert_eq!(injective_dimension(&s0, 5).unwrap(), Bounded::Exact(0));
        }
    }

    // k[x]/(xⁿ) is self-injective: the regular module is the unique
    // indecomposable projective and equals the unique indecomposable injective.
    #[test]
    fn truncated_poly_projectives_are_injective() {
        for field in fields() {
            for n in 2..5 {
                let algebra = truncated_poly(n, field).unwrap();
                let p = Module::projective(&algebra, 0);
                assert_eq!(
                    injective_dimension(&p, 6).unwrap(),
                    Bounded::Exact(0),
                    "id A for x^{n}"
                );
                let i = Module::injective(&algebra, 0);
                assert_eq!(p.dim_vector(), i.dim_vector());
            }
        }
    }

    // Ω S = S over k[x]/(x²) dualizes to a periodic cosyzygy, so the minimal
    // coresolution of the simple never stops.
    #[test]
    fn dual_numbers_simple_coresolves_periodically() {
        for field in fields() {
            let algebra = dual_numbers(field);
            let s = Module::simple(&algebra, 0);
            let coresolution = coresolve(&s, 6).unwrap();
            assert_eq!(coresolution.end, ResolutionEnd::Cut { at: 6 });
            assert_eq!(coresolution.terms.len(), 7);
            for term in &coresolution.terms {
                assert_eq!(term.dim_vector(), &[2]);
            }
            assert_eq!(injective_dimension(&s, 10).unwrap(), Bounded::AtLeast(11));
        }
    }

    // A cyclic Nakayama algebra with constant Kupisch series is self-injective;
    // the linear one with series [3, 2, 1] is kA_3, where P_1 = (0,1,1) is not
    // injective and embeds in I_2 = (1,1,1) with cokernel I_0.
    #[test]
    fn cyclic_nakayama_is_self_injective_and_linear_nakayama_is_not() {
        for field in fields() {
            let cyclic = cyclic_nakayama(&[3, 3, 3], field).unwrap();
            for v in 0..3u32 {
                let p = Module::projective(&cyclic, v);
                assert_eq!(
                    injective_dimension(&p, 6).unwrap(),
                    Bounded::Exact(0),
                    "id P_{v}"
                );
            }
            let linear = linear_nakayama(&[3, 2, 1], field).unwrap();
            let p1 = Module::projective(&linear, 1);
            assert_eq!(p1.dim_vector(), &[0, 1, 1]);
            assert_eq!(injective_dimension(&p1, 6).unwrap(), Bounded::Exact(1));
        }
    }

    #[test]
    fn coresolve_with_zero_steps_reports_cut_for_a_noninjective_module() {
        let field = PrimeField::new(32003).unwrap();
        let algebra = linear_an(3, field);
        let s2 = Module::simple(&algebra, 2);
        let coresolution = coresolve(&s2, 0).unwrap();
        assert_eq!(coresolution.end, ResolutionEnd::Cut { at: 0 });
        assert_eq!(coresolution.terms.len(), 1);
        let i0 = Module::injective(&algebra, 0);
        assert_eq!(coresolve(&i0, 0).unwrap().end, ResolutionEnd::Finite);
    }

    #[test]
    fn coresolution_prefixes_are_complexes_and_exact() {
        for field in fields() {
            for algebra in fixtures(field) {
                for m in assorted_modules(&algebra) {
                    let coresolution = coresolve(&m, 4).unwrap();
                    assert!(is_mono(&coresolution.coaugmentation));
                    if let Some(d0) = coresolution.maps.first() {
                        assert!(
                            coresolution.coaugmentation.then(d0).unwrap().is_zero(),
                            "d^0 ∘ ι = 0"
                        );
                    }
                    for pair in coresolution.maps.windows(2) {
                        assert!(pair[0].then(&pair[1]).unwrap().is_zero(), "d² = 0");
                    }
                    for k in 0..coresolution.terms.len() {
                        let (incoming, _) = if k == 0 {
                            image(&coresolution.coaugmentation)
                        } else {
                            image(&coresolution.maps[k - 1])
                        };
                        if k + 1 < coresolution.terms.len() {
                            let (ker, _) = kernel(&coresolution.maps[k]);
                            assert_eq!(
                                ker.dim_vector(),
                                incoming.dim_vector(),
                                "exactness at I^{k}"
                            );
                        } else if coresolution.end == ResolutionEnd::Finite {
                            assert_eq!(
                                incoming.dim_vector(),
                                coresolution.terms[k].dim_vector(),
                                "a finite coresolution ends onto its last term"
                            );
                        }
                    }
                }
            }
        }
    }

    // Minimality dualizes "differentials land in the radical" to "soc I^k lies
    // in ker d^k".
    #[test]
    fn differentials_vanish_on_socles() {
        for field in fields() {
            for algebra in fixtures(field) {
                for m in assorted_modules(&algebra) {
                    let coresolution = coresolve(&m, 4).unwrap();
                    for (k, d) in coresolution.maps.iter().enumerate() {
                        let (_, inclusion) = socle(&coresolution.terms[k]);
                        assert!(
                            inclusion.then(d).unwrap().is_zero(),
                            "soc I^{k} survives d^{k}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn every_first_term_is_the_injective_envelope() {
        for field in fields() {
            for algebra in fixtures(field) {
                for m in assorted_modules(&algebra) {
                    let coresolution = coresolve(&m, 3).unwrap();
                    let (envelope, _) = injective_envelope(&m).unwrap();
                    assert_eq!(coresolution.terms[0].dim_vector(), envelope.dim_vector());
                    assert_eq!(
                        injective_dimension(&coresolution.terms[0], 3).unwrap(),
                        Bounded::Exact(0),
                        "I^0 of {:?} is injective",
                        m.dim_vector()
                    );
                }
            }
        }
    }
}

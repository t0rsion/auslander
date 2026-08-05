//! Injective envelopes and minimal injective coresolutions over F_2, F_5 and
//! F_32003, against hand-derived values and against constructions independent
//! of the duality route the library takes.
//!
//! Derivations used below (right modules, arrows composed left to right).
//! Over `kA_n` the injectives are `I_j = D(A e_j)` with dimension vector
//! `(1, …, 1, 0, …, 0)` supported on `0..=j`, so `S_0 = I_0` is injective and
//! every other simple embeds in `I_j` with cokernel `I_{j-1}`: the injective
//! dimensions of the simples are `0, 1, …, 1`. Over `kA_3/(ab)` the injectives
//! are `I_0 = (1,0,0)`, `I_1 = (1,1,0)`, `I_2 = (0,1,1)`; the socle of `S_2`
//! sits at vertex 2, so `S_2` embeds in `I_2` with cokernel `S_1`, which embeds
//! in `I_1` with cokernel `S_0 = I_0`. `k[x]/(xⁿ)` is self-injective, since the
//! regular module is the only indecomposable projective and the only
//! indecomposable injective. A cyclic Nakayama algebra is self-injective
//! exactly when its Kupisch series is constant. For the non-constant series
//! `[2, 2, 3]` on the cycle `0 → 1 → 2 → 0` the projectives are
//! `P_0 = (1,1,0)`, `P_1 = (0,1,1)`, `P_2 = (1,1,1)` and the injectives
//! `I_0 = (1,0,1)`, `I_1 = (1,1,1)`, `I_2 = (0,1,1)`; `soc P_0 = S_1`, so `P_0`
//! coresolves as `0 → P_0 → I_1 → I_2 → I_1 → I_0 → 0` with successive
//! cokernels `S_2`, `S_1`, `I_0`, and `id P_0 = 3`.

use std::sync::Arc;

use auslander::algebra::{
    MonomialAlgebra, an_with_relations, cyclic_nakayama, dual_numbers, kronecker, linear_an,
    linear_nakayama, radical_square_zero_cycle, truncated_poly,
};
use auslander::ext::global_dimension;
use auslander::field::PrimeField;
use auslander::hom::{Morphism, image, kernel};
use auslander::injective::{coresolve, injective_dimension, injective_envelope};
use auslander::iso::{IsoOutcome, is_isomorphic};
use auslander::module::{Module, direct_sum};
use auslander::opposite::{dual, opposite};
use auslander::quiver::ArrowId;
use auslander::radical::socle;
use auslander::resolution::{Bounded, ResolutionEnd, projective_dimension, resolve};

fn fields() -> [PrimeField; 3] {
    [
        PrimeField::new(2).unwrap(),
        PrimeField::new(5).unwrap(),
        PrimeField::new(32003).unwrap(),
    ]
}

fn fixtures() -> Vec<Arc<MonomialAlgebra>> {
    vec![
        linear_an(3),
        an_with_relations(3, &[(0, 2)]).unwrap(),
        kronecker(2),
        dual_numbers(),
        truncated_poly(3).unwrap(),
        radical_square_zero_cycle(3),
        cyclic_nakayama(&[3, 3, 3]).unwrap(),
        cyclic_nakayama(&[2, 2, 3]).unwrap(),
        linear_nakayama(&[3, 2, 1]).unwrap(),
        linear_nakayama(&[2, 2, 1]).unwrap(),
    ]
}

fn assorted(algebra: &Arc<MonomialAlgebra>, field: PrimeField) -> Vec<Module> {
    let n = algebra.quiver().num_vertices();
    let mut modules = vec![Module::zero(algebra, field)];
    for v in 0..n {
        modules.push(Module::simple(algebra, field, v));
        modules.push(Module::projective(algebra, field, v));
        modules.push(Module::injective(algebra, field, v));
    }
    let s0 = Module::simple(algebra, field, 0);
    let i_last = Module::injective(algebra, field, n - 1);
    modules.push(direct_sum(&[&s0, &i_last]).0);
    modules
}

/// `⊕_v I_v^{dim (soc m)_v}`, the injective envelope read off the socle instead
/// of off a projective cover over the opposite algebra.
fn socle_injective_sum(m: &Module) -> Module {
    let algebra = m.algebra();
    let field = m.field();
    let (soc, _) = socle(m);
    let mut parts = Vec::new();
    for v in 0..algebra.quiver().num_vertices() {
        for _ in 0..soc.dim_at(v) {
            parts.push(Module::injective(algebra, field, v));
        }
    }
    if parts.is_empty() {
        return Module::zero(algebra, field);
    }
    let refs: Vec<&Module> = parts.iter().collect();
    direct_sum(&refs).0
}

fn is_mono(f: &Morphism) -> bool {
    let field = f.source().field();
    (0..f.source().algebra().quiver().num_vertices())
        .all(|v| f.map_at(v).rank(&field) == f.source().dim_at(v))
}

#[test]
fn envelope_agrees_with_the_socle_construction_on_every_fixture() {
    for algebra in fixtures() {
        for field in fields() {
            for m in assorted(&algebra, field) {
                let (envelope, embedding) = injective_envelope(&m);
                let by_socle = socle_injective_sum(&m);
                assert_eq!(
                    envelope.dim_vector(),
                    by_socle.dim_vector(),
                    "envelope of {:?} over F_{}",
                    m.dim_vector(),
                    field.modulus()
                );
                assert!(
                    is_mono(&embedding),
                    "envelope of {:?} is not a monomorphism",
                    m.dim_vector()
                );
                assert!(embedding.source().ptr_eq(&m));
                assert!(embedding.target().ptr_eq(&envelope));
            }
        }
    }
}

// A monomorphism whose source and target have the same socle dimensions has
// soc I inside its image, hence meets every nonzero submodule: the image is
// essential and the envelope is minimal.
#[test]
fn envelope_embeddings_have_essential_image() {
    for algebra in fixtures() {
        for field in fields() {
            for m in assorted(&algebra, field) {
                let (envelope, embedding) = injective_envelope(&m);
                assert!(is_mono(&embedding));
                assert_eq!(
                    socle(&envelope).0.dim_vector(),
                    socle(&m).0.dim_vector(),
                    "socle grew for {:?} over F_{}",
                    m.dim_vector(),
                    field.modulus()
                );
            }
        }
    }
}

#[test]
fn envelope_is_isomorphic_to_the_socle_construction() {
    for algebra in [
        linear_an(3),
        an_with_relations(3, &[(0, 2)]).unwrap(),
        cyclic_nakayama(&[2, 2, 3]).unwrap(),
    ] {
        for field in fields() {
            for m in assorted(&algebra, field) {
                let (envelope, _) = injective_envelope(&m);
                assert!(
                    matches!(
                        is_isomorphic(&envelope, &socle_injective_sum(&m)).unwrap(),
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

#[test]
fn linear_an_simples_have_injective_dimensions_0_then_1() {
    for n in 2..6 {
        let algebra = linear_an(n);
        for field in fields() {
            for v in 0..algebra.quiver().num_vertices() {
                let expected = usize::from(v > 0);
                assert_eq!(
                    injective_dimension(&Module::simple(&algebra, field, v), 5),
                    Bounded::Exact(expected),
                    "id S_{v} over A_{n}, F_{}",
                    field.modulus()
                );
            }
        }
    }
}

#[test]
fn a3_mod_ab_simples_coresolve_through_the_hand_derived_injectives() {
    for field in fields() {
        let algebra = an_with_relations(3, &[(0, 2)]).unwrap();
        let expected: [Vec<Vec<usize>>; 3] = [
            vec![vec![1, 0, 0]],
            vec![vec![1, 1, 0], vec![1, 0, 0]],
            vec![vec![0, 1, 1], vec![1, 1, 0], vec![1, 0, 0]],
        ];
        for v in 0..3u32 {
            let s = Module::simple(&algebra, field, v);
            let coresolution = coresolve(&s, 5);
            assert_eq!(coresolution.end, ResolutionEnd::Finite, "S_{v}");
            let dims: Vec<Vec<usize>> = coresolution
                .terms
                .iter()
                .map(|t| t.dim_vector().to_vec())
                .collect();
            assert_eq!(dims, expected[v as usize], "coresolution of S_{v}");
            assert_eq!(
                injective_dimension(&s, 5),
                Bounded::Exact(expected[v as usize].len() - 1),
                "id S_{v}"
            );
        }
    }
}

#[test]
fn truncated_poly_is_self_injective() {
    for field in fields() {
        for n in 2..5 {
            let algebra = truncated_poly(n).unwrap();
            let p = Module::projective(&algebra, field, 0);
            let i = Module::injective(&algebra, field, 0);
            assert_eq!(injective_dimension(&p, 6), Bounded::Exact(0), "id A, x^{n}");
            assert_eq!(projective_dimension(&i, 6), Bounded::Exact(0), "pd D(A)");
            let s = Module::simple(&algebra, field, 0);
            assert_eq!(
                injective_dimension(&s, 6),
                Bounded::AtLeast(7),
                "id S, x^{n}"
            );
        }
    }
}

#[test]
fn cyclic_nakayama_with_constant_kupisch_is_self_injective() {
    for field in fields() {
        for kupisch in [vec![3, 3, 3], vec![2, 2, 2], vec![2, 2, 2, 2]] {
            let algebra = cyclic_nakayama(&kupisch).unwrap();
            for v in 0..algebra.quiver().num_vertices() {
                assert_eq!(
                    injective_dimension(&Module::projective(&algebra, field, v), 6),
                    Bounded::Exact(0),
                    "id P_{v} for {kupisch:?}"
                );
                assert_eq!(
                    projective_dimension(&Module::injective(&algebra, field, v), 6),
                    Bounded::Exact(0),
                    "pd I_{v} for {kupisch:?}"
                );
            }
        }
    }
}

#[test]
fn cyclic_nakayama_2_2_3_coresolves_p0_in_three_steps() {
    for field in fields() {
        let algebra = cyclic_nakayama(&[2, 2, 3]).unwrap();
        let p0 = Module::projective(&algebra, field, 0);
        assert_eq!(p0.dim_vector(), &[1, 1, 0]);
        let coresolution = coresolve(&p0, 6);
        assert_eq!(coresolution.end, ResolutionEnd::Finite);
        let dims: Vec<Vec<usize>> = coresolution
            .terms
            .iter()
            .map(|t| t.dim_vector().to_vec())
            .collect();
        assert_eq!(
            dims,
            vec![vec![1, 1, 1], vec![0, 1, 1], vec![1, 1, 1], vec![1, 0, 1]]
        );
        assert_eq!(injective_dimension(&p0, 6), Bounded::Exact(3));
        // P_1 = I_2 and P_2 ≅ I_1, so only P_0 fails to be injective.
        assert_eq!(
            injective_dimension(&Module::projective(&algebra, field, 1), 6),
            Bounded::Exact(0)
        );
        assert_eq!(
            injective_dimension(&Module::projective(&algebra, field, 2), 6),
            Bounded::Exact(0)
        );
    }
}

#[test]
fn linear_nakayama_3_2_1_has_a_non_injective_projective() {
    for field in fields() {
        let algebra = linear_nakayama(&[3, 2, 1]).unwrap();
        let p1 = Module::projective(&algebra, field, 1);
        assert_eq!(p1.dim_vector(), &[0, 1, 1]);
        let coresolution = coresolve(&p1, 5);
        let dims: Vec<Vec<usize>> = coresolution
            .terms
            .iter()
            .map(|t| t.dim_vector().to_vec())
            .collect();
        assert_eq!(dims, vec![vec![1, 1, 1], vec![1, 0, 0]]);
        assert_eq!(injective_dimension(&p1, 5), Bounded::Exact(1));
    }
}

#[test]
fn coresolution_prefixes_are_exact_and_minimal() {
    for algebra in fixtures() {
        for field in fields() {
            for m in assorted(&algebra, field) {
                let coresolution = coresolve(&m, 4);
                assert!(is_mono(&coresolution.coaugmentation));
                assert_eq!(coresolution.maps.len() + 1, coresolution.terms.len());
                if let Some(d0) = coresolution.maps.first() {
                    assert!(coresolution.coaugmentation.then(d0).unwrap().is_zero());
                }
                for pair in coresolution.maps.windows(2) {
                    assert!(pair[0].then(&pair[1]).unwrap().is_zero(), "d² = 0");
                }
                for (k, term) in coresolution.terms.iter().enumerate() {
                    let (incoming, _) = if k == 0 {
                        image(&coresolution.coaugmentation)
                    } else {
                        image(&coresolution.maps[k - 1])
                    };
                    if k + 1 < coresolution.terms.len() {
                        let (ker, _) = kernel(&coresolution.maps[k]);
                        assert_eq!(ker.dim_vector(), incoming.dim_vector(), "exact at I^{k}");
                    } else if coresolution.end == ResolutionEnd::Finite {
                        assert_eq!(
                            incoming.dim_vector(),
                            term.dim_vector(),
                            "a finite coresolution ends onto its last term"
                        );
                    }
                    // Minimality: soc I^k lies in the kernel of the next map.
                    if let Some(d) = coresolution.maps.get(k) {
                        assert!(
                            socle(term).1.then(d).unwrap().is_zero(),
                            "soc I^{k} survives d^{k}"
                        );
                    }
                }
            }
        }
    }
}

// Exactness of a finite coresolution forces the alternating sum of the term
// dimension vectors to be the dimension vector of the module.
#[test]
fn finite_coresolutions_have_the_euler_characteristic_of_the_module() {
    for algebra in fixtures() {
        for field in fields() {
            for m in assorted(&algebra, field) {
                let coresolution = coresolve(&m, 6);
                if coresolution.end != ResolutionEnd::Finite {
                    continue;
                }
                for v in 0..algebra.quiver().num_vertices() {
                    let alternating: isize = coresolution
                        .terms
                        .iter()
                        .enumerate()
                        .map(|(k, t)| {
                            let d = t.dim_at(v) as isize;
                            if k % 2 == 0 { d } else { -d }
                        })
                        .sum();
                    assert_eq!(alternating, m.dim_at(v) as isize, "Euler at vertex {v}");
                }
            }
        }
    }
}

// gldim A = sup_v pd S_v = sup_v id S_v. Independent machinery computes the two
// suprema here.
#[test]
fn injective_dimensions_of_the_simples_attain_the_global_dimension() {
    for algebra in fixtures() {
        for field in fields() {
            let bound = 6;
            let mut max = 0usize;
            let mut cut = false;
            for v in 0..algebra.quiver().num_vertices() {
                match injective_dimension(&Module::simple(&algebra, field, v), bound) {
                    Bounded::Exact(d) => max = max.max(d),
                    Bounded::AtLeast(_) => cut = true,
                }
            }
            let from_injectives = if cut {
                Bounded::AtLeast(bound + 1)
            } else {
                Bounded::Exact(max)
            };
            assert_eq!(
                from_injectives,
                global_dimension(&algebra, field, bound),
                "gldim over F_{}",
                field.modulus()
            );
        }
    }
}

fn entrywise_equal(a: &Module, b: &Module) -> bool {
    Arc::ptr_eq(a.algebra(), b.algebra())
        && a.dim_vector() == b.dim_vector()
        && (0..a.algebra().quiver().num_arrows())
            .all(|i| a.map(ArrowId(i as u32)) == b.map(ArrowId(i as u32)))
}

// D of a minimal injective coresolution of M is a minimal projective
// resolution of D(M) over the opposite algebra, degreewise: same status, same
// terms, and the transposed differentials.
#[test]
fn dualizing_a_coresolution_gives_the_projective_resolution_of_the_dual() {
    for algebra in fixtures() {
        let op = opposite(&algebra);
        for field in fields() {
            for m in assorted(&algebra, field) {
                let coresolution = coresolve(&m, 4);
                let resolution = resolve(&dual(&m, &op).unwrap(), 4);
                assert_eq!(coresolution.end, resolution.end);
                assert_eq!(coresolution.terms.len(), resolution.terms.len());
                for (k, term) in coresolution.terms.iter().enumerate() {
                    assert!(
                        entrywise_equal(&dual(term, &op).unwrap(), &resolution.terms[k]),
                        "D(I^{k}) is P_{k}"
                    );
                }
                for v in 0..algebra.quiver().num_vertices() {
                    assert_eq!(
                        coresolution.coaugmentation.map_at(v).transpose(),
                        *resolution.augmentation.map_at(v),
                        "D(ι) is the cover at vertex {v}"
                    );
                    for (k, d) in coresolution.maps.iter().enumerate() {
                        assert_eq!(
                            d.map_at(v).transpose(),
                            *resolution.maps[k].map_at(v),
                            "D(d^{k}) is the differential at vertex {v}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn injective_dimension_of_a_module_equals_the_projective_dimension_of_its_dual() {
    for algebra in fixtures() {
        let op = opposite(&algebra);
        for field in fields() {
            for m in assorted(&algebra, field) {
                assert_eq!(
                    injective_dimension(&m, 5),
                    projective_dimension(&dual(&m, &op).unwrap(), 5),
                    "id {:?} over F_{}",
                    m.dim_vector(),
                    field.modulus()
                );
            }
        }
    }
}

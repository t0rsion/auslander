//! Randomized property tests for the v0.2 module arithmetic, over
//! deterministically seeded xorshift streams in the style of
//! `random_modules.rs`: (a) decompose-and-reassemble is isomorphic to the
//! original with every summand certified; (b) Krull–Schmidt class
//! multiplicities are invariant under permutation and re-association of
//! direct sums; (c) τ's two routes agree on random modules (enforced inside
//! [`tau`]) and τ distributes over direct sums up to the `Zero` conventions.
//!
//! Modules are random direct sums of projectives, simples, and injectives
//! followed by a random vertexwise change of basis (`M'(a) = G_{s(a)} · M(a) ·
//! G_{t(a)}⁻¹`), so decompositions never see the standard summand basis.
//! Every case prints its seed before asserting, so a failing case reproduces
//! by seeding [`XorShift64`] with the printed value.

use std::sync::Arc;

use auslander::algebra::{
    MonomialAlgebra, an_with_relations, cyclic_nakayama, dual_numbers, linear_an,
};
use auslander::ar::{Tau, tau};
use auslander::decompose::{Certificate, IsoClass, KrullSchmidtOutcome, decompose, krull_schmidt};
use auslander::field::{Fp, PrimeField};
use auslander::hom::Morphism;
use auslander::iso::{IsoOutcome, is_isomorphic};
use auslander::linalg::DenseMat;
use auslander::module::{Module, direct_sum};
use auslander::quiver::ArrowId;

const MAX_TOTAL_DIM: usize = 8;
/// Cases per (algebra, field) pair. 4 algebras × 3 fields keeps every test
/// under 50 cases.
const CASES: usize = 4;
const SEED_BASE: u64 = 0x0002_d0d0_5eed_b0b5;

struct XorShift64(u64);

impl XorShift64 {
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
}

/// Distinct nonzero seed per (test, field, algebra, case), splittable from the
/// printed value alone.
fn case_seed(test: u64, p: u64, algebra_idx: usize, case: usize) -> u64 {
    let raw = SEED_BASE
        ^ test.wrapping_mul(0x9e37_79b9_7f4a_7c15)
        ^ p.wrapping_mul(0xd1b5_4a32_d192_ed03)
        ^ (algebra_idx as u64).wrapping_mul(0x94d0_49bb_1331_11eb)
        ^ (case as u64).wrapping_mul(0x2545_f491_4f6c_dd1d);
    if raw == 0 { SEED_BASE } else { raw }
}

fn fields() -> [PrimeField; 3] {
    [
        PrimeField::new(2).unwrap(),
        PrimeField::new(3).unwrap(),
        PrimeField::new(5).unwrap(),
    ]
}

fn algebras() -> Vec<(&'static str, Arc<MonomialAlgebra>)> {
    vec![
        ("linear_an_3", linear_an(3)),
        ("a3_mod_ab", an_with_relations(3, &[(0, 2)]).unwrap()),
        (
            "cyclic_nakayama_3_3_3",
            cyclic_nakayama(&[3, 3, 3]).unwrap(),
        ),
        ("dual_numbers", dual_numbers()),
    ]
}

fn rand_elem(rng: &mut XorShift64, field: &PrimeField) -> Fp {
    field.elem(rng.below(field.modulus()) as i64)
}

/// A random direct sum of projectives, simples, and injectives with total
/// dimension at most `budget`.
fn random_sum_module(
    rng: &mut XorShift64,
    algebra: &Arc<MonomialAlgebra>,
    field: PrimeField,
    budget: usize,
) -> Module {
    let n = algebra.quiver().num_vertices();
    let mut parts: Vec<Module> = Vec::new();
    let mut total = 0usize;
    for _ in 0..1 + rng.below(3) {
        let v = rng.below(u64::from(n)) as u32;
        let part = match rng.below(3) {
            0 => Module::simple(algebra, field, v),
            1 => Module::projective(algebra, field, v),
            _ => Module::injective(algebra, field, v),
        };
        if total + part.total_dim() > budget {
            break;
        }
        total += part.total_dim();
        parts.push(part);
    }
    if parts.is_empty() {
        parts.push(Module::simple(algebra, field, 0));
    }
    let refs: Vec<&Module> = parts.iter().collect();
    direct_sum(&refs).0
}

/// An invertible `d × d` matrix built from random elementary row operations on
/// the identity.
fn random_invertible(rng: &mut XorShift64, field: &PrimeField, d: usize) -> DenseMat {
    let mut g = DenseMat::identity(d);
    if d == 0 {
        return g;
    }
    for _ in 0..2 * d + 2 {
        let i = rng.below(d as u64) as usize;
        match rng.below(3) {
            0 if d >= 2 => {
                let j = (i + 1 + rng.below(d as u64 - 1) as usize) % d;
                for c in 0..d {
                    let (a, b) = (g.get(i, c), g.get(j, c));
                    g.set(i, c, b);
                    g.set(j, c, a);
                }
            }
            1 => {
                let c = field.elem(1 + rng.below(field.modulus() - 1) as i64);
                for k in 0..d {
                    g.set(i, k, field.mul(g.get(i, k), c));
                }
            }
            _ if d >= 2 => {
                let j = (i + 1 + rng.below(d as u64 - 1) as usize) % d;
                let c = rand_elem(rng, field);
                for k in 0..d {
                    g.set(i, k, field.add(g.get(i, k), field.mul(c, g.get(j, k))));
                }
            }
            _ => {}
        }
    }
    g
}

/// `G⁻¹`, column by column from `G x = e_j`.
fn inverse(g: &DenseMat, field: &PrimeField) -> DenseMat {
    let d = g.rows();
    let mut inv = DenseMat::zero(d, d);
    for j in 0..d {
        let mut unit = vec![field.zero(); d];
        unit[j] = field.one();
        let col = g
            .solve(&unit, field)
            .expect("G is a product of elementary matrices");
        for (i, &v) in col.iter().enumerate() {
            inv.set(i, j, v);
        }
    }
    inv
}

/// `M'(a) = G_{s(a)} · M(a) · G_{t(a)}⁻¹` for random invertible `G_v`, so the
/// result is isomorphic to `m` but not in the standard summand basis.
fn random_basis_change(rng: &mut XorShift64, m: &Module) -> Module {
    let field = m.field();
    let quiver = m.algebra().quiver();
    let g: Vec<DenseMat> = m
        .dim_vector()
        .iter()
        .map(|&d| random_invertible(rng, &field, d))
        .collect();
    let g_inv: Vec<DenseMat> = g.iter().map(|x| inverse(x, &field)).collect();
    let maps: Vec<DenseMat> = (0..quiver.num_arrows())
        .map(|i| {
            let a = ArrowId(i as u32);
            let (s, t) = (quiver.source(a) as usize, quiver.target(a) as usize);
            g[s].mul(m.map(a), &field).mul(&g_inv[t], &field)
        })
        .collect();
    Module::new(m.algebra().clone(), field, m.dim_vector().to_vec(), maps)
        .expect("a vertexwise basis change preserves the relations")
}

fn for_each_case(
    test: u64,
    mut body: impl FnMut(&mut XorShift64, &Arc<MonomialAlgebra>, PrimeField, &str),
) {
    for field in fields() {
        for (algebra_idx, (name, algebra)) in algebras().iter().enumerate() {
            for case in 0..CASES {
                let seed = case_seed(test, field.modulus(), algebra_idx, case);
                println!(
                    "{name} over F_{} case {case}: seed {seed:#018x}",
                    field.modulus()
                );
                let mut rng = XorShift64(seed);
                body(&mut rng, algebra, field, name);
            }
        }
    }
}

fn certified_isomorphic(m: &Module, n: &Module, context: &str) -> Morphism {
    match is_isomorphic(m, n).expect("modules share one algebra and field") {
        IsoOutcome::Isomorphic(witness) => witness,
        other => panic!("{context}: expected an isomorphism, got {other:?}"),
    }
}

fn iso_classes(m: &Module, context: &str) -> Vec<IsoClass> {
    match krull_schmidt(m) {
        KrullSchmidtOutcome::Classes(classes) => classes,
        KrullSchmidtOutcome::Unknown { reason } => panic!("{context}: {reason}"),
    }
}

/// Whether the two class lists carry the same multiset of (class,
/// multiplicity) pairs, matching classes by certified isomorphism of
/// representatives.
fn same_class_multiset(a: &[IsoClass], b: &[IsoClass]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut used = vec![false; b.len()];
    a.iter().all(|ca| {
        match b.iter().enumerate().find(|(j, cb)| {
            !used[*j]
                && cb.multiplicity == ca.multiplicity
                && matches!(
                    is_isomorphic(&ca.representative, &cb.representative)
                        .expect("representatives share one algebra and field"),
                    IsoOutcome::Isomorphic(_)
                )
        }) {
            Some((j, _)) => {
                used[j] = true;
                true
            }
            None => false,
        }
    })
}

#[test]
fn decompose_certifies_every_summand_and_reassembles_to_the_original() {
    for_each_case(1, |rng, algebra, field, name| {
        let base = random_sum_module(rng, algebra, field, MAX_TOTAL_DIM);
        let m = random_basis_change(rng, &base);
        let d = decompose(&m);
        assert!(d.split().total().ptr_eq(&m), "{name}: split total is not m");
        for (k, certificate) in d.certificates().iter().enumerate() {
            assert_eq!(
                *certificate,
                Certificate::Indecomposable,
                "{name}: summand {k} not certified indecomposable"
            );
        }
        let summed: Vec<usize> = (0..algebra.quiver().num_vertices())
            .map(|v| d.summands().iter().map(|s| s.dim_at(v)).sum())
            .collect();
        assert_eq!(summed, m.dim_vector(), "{name}: summand dimensions");
        let refs: Vec<&Module> = d.summands().iter().collect();
        let reassembled = direct_sum(&refs).0;
        let witness = certified_isomorphic(&reassembled, &m, name);
        assert!(
            witness.is_isomorphism(),
            "{name}: witness must be invertible"
        );
    });
}

#[test]
fn krull_schmidt_classes_are_invariant_under_permutation_and_reassociation() {
    // A smaller budget than elsewhere: the triple sums grow to three times it,
    // and endomorphism algebras get expensive quickly.
    for_each_case(2, |rng, algebra, field, name| {
        let m = random_sum_module(rng, algebra, field, 4);
        let n = random_sum_module(rng, algebra, field, 4);
        let l = random_sum_module(rng, algebra, field, 4);
        let mn = direct_sum(&[&m, &n]).0;
        let nm = direct_sum(&[&n, &m]).0;
        assert!(
            same_class_multiset(&iso_classes(&mn, name), &iso_classes(&nm, name)),
            "{name}: M ⊕ N and N ⊕ M decompose into different class multisets"
        );
        let nl = direct_sum(&[&n, &l]).0;
        let left_assoc = direct_sum(&[&mn, &l]).0;
        let right_assoc = direct_sum(&[&m, &nl]).0;
        assert!(
            same_class_multiset(
                &iso_classes(&left_assoc, name),
                &iso_classes(&right_assoc, name)
            ),
            "{name}: (M ⊕ N) ⊕ L and M ⊕ (N ⊕ L) decompose into different class multisets"
        );
    });
}

#[test]
fn tau_routes_agree_and_tau_distributes_over_direct_sums() {
    for_each_case(3, |rng, algebra, field, name| {
        let base_m = random_sum_module(rng, algebra, field, MAX_TOTAL_DIM);
        let m = random_basis_change(rng, &base_m);
        let base_n = random_sum_module(rng, algebra, field, MAX_TOTAL_DIM);
        let n = random_basis_change(rng, &base_n);
        // tau() itself runs both routes and errors on disagreement, so every
        // unwrap here is a broad route-agreement check.
        let tau_m = tau(&m).unwrap_or_else(|e| panic!("{name}: τM routes disagree: {e}"));
        let tau_n = tau(&n).unwrap_or_else(|e| panic!("{name}: τN routes disagree: {e}"));
        let sum = direct_sum(&[&m, &n]).0;
        let tau_sum = tau(&sum).unwrap_or_else(|e| panic!("{name}: τ(M ⊕ N) routes disagree: {e}"));
        let parts: Vec<&Module> = [&tau_m, &tau_n]
            .into_iter()
            .filter_map(|t| match t {
                Tau::Module(x) => Some(x),
                Tau::Zero => None,
            })
            .collect();
        match tau_sum {
            Tau::Zero => assert!(
                parts.is_empty(),
                "{name}: τ(M ⊕ N) is zero but τM ⊕ τN is not"
            ),
            Tau::Module(t) => {
                assert!(
                    !parts.is_empty(),
                    "{name}: τM and τN are zero but τ(M ⊕ N) is not"
                );
                let expected = direct_sum(&parts).0;
                certified_isomorphic(&t, &expected, name);
            }
        }
    });
}

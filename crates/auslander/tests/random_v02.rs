//! Randomized property tests for the v0.2 module arithmetic, over
//! deterministically seeded xorshift streams in the style of
//! `random_modules.rs`: (a) decompose-and-reassemble is isomorphic to the
//! original with every summand certified; (b) Krull-Schmidt class
//! multiplicities are invariant under permutation and re-association of
//! direct sums; (c) τ's two routes agree on random modules (enforced inside
//! [`tau`]) and τ distributes over direct sums once the zero translates are
//! dropped from both sides.
//!
//! Modules are random direct sums of projectives, simples, and injectives
//! followed by a random vertexwise change of basis (`M'(a) = G_{s(a)} · M(a) ·
//! G_{t(a)}⁻¹`), so decompositions never see the standard summand basis.
//! Every case prints its seed before asserting, so a failing case reproduces
//! by seeding [`XorShift64`] with the printed value.

use std::sync::Arc;

use auslander::algebra::{
    Algebra, an_with_relations, commutative_square, cyclic_nakayama, dual_numbers, kronecker,
    linear_an,
};
use auslander::ar::tau;
use auslander::decompose::{Certificate, IsoClass, KrullSchmidtOutcome, decompose, krull_schmidt};
use auslander::field::PrimeField;
use auslander::hom::Morphism;
use auslander::iso::{IsoOutcome, is_isomorphic};
use auslander::module::{Module, direct_sum};

mod common;

use common::{XorShift64, case_seed, random_basis_change, random_sum_module};

const MAX_TOTAL_DIM: usize = 8;
/// Cases per (algebra, field) pair. With the 6 algebras and 3 fields below,
/// each test runs 72 cases.
const CASES: usize = 4;
const SEED_BASE: u64 = 0x0002_d0d0_5eed_b0b5;

fn fields() -> [PrimeField; 3] {
    [
        PrimeField::new(2).unwrap(),
        PrimeField::new(3).unwrap(),
        PrimeField::new(5).unwrap(),
    ]
}

fn algebras(field: PrimeField) -> Vec<(&'static str, Arc<Algebra>)> {
    vec![
        ("linear_an_3", linear_an(3, field)),
        ("a3_mod_ab", an_with_relations(3, &[(0, 2)], field).unwrap()),
        (
            "cyclic_nakayama_3_3_3",
            cyclic_nakayama(&[3, 3, 3], field).unwrap(),
        ),
        ("dual_numbers", dual_numbers(field)),
        ("commutative_square", commutative_square(field)),
        ("kronecker_2", kronecker(2, field)),
    ]
}

fn for_each_case(test: u64, mut body: impl FnMut(&mut XorShift64, &Arc<Algebra>, &str)) {
    for field in fields() {
        for (algebra_idx, (name, algebra)) in algebras(field).iter().enumerate() {
            for case in 0..CASES {
                let seed = case_seed(SEED_BASE, test, field.modulus(), algebra_idx, case);
                println!(
                    "{name} over F_{} case {case}: seed {seed:#018x}",
                    field.modulus()
                );
                let mut rng = XorShift64(seed);
                body(&mut rng, algebra, name);
            }
        }
    }
}

fn certified_isomorphic(m: &Module, n: &Module, context: &str) -> Morphism {
    match is_isomorphic(m, n).expect("modules share one algebra") {
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
                        .expect("representatives share one algebra"),
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
    for_each_case(1, |rng, algebra, name| {
        let base = random_sum_module(rng, algebra, MAX_TOTAL_DIM);
        let (m, _) = random_basis_change(rng, &base);
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
    for_each_case(2, |rng, algebra, name| {
        let m = random_sum_module(rng, algebra, 4);
        let n = random_sum_module(rng, algebra, 4);
        let l = random_sum_module(rng, algebra, 4);
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
    for_each_case(3, |rng, algebra, name| {
        let base_m = random_sum_module(rng, algebra, MAX_TOTAL_DIM);
        let (m, _) = random_basis_change(rng, &base_m);
        let base_n = random_sum_module(rng, algebra, MAX_TOTAL_DIM);
        let (n, _) = random_basis_change(rng, &base_n);
        // tau() itself runs both routes and errors on disagreement, so every
        // unwrap here is a broad route-agreement check.
        let tau_m = tau(&m).unwrap_or_else(|e| panic!("{name}: τM routes disagree: {e}"));
        let tau_n = tau(&n).unwrap_or_else(|e| panic!("{name}: τN routes disagree: {e}"));
        let sum = direct_sum(&[&m, &n]).0;
        let tau_sum = tau(&sum).unwrap_or_else(|e| panic!("{name}: τ(M ⊕ N) routes disagree: {e}"));
        let parts: Vec<&Module> = [&tau_m, &tau_n]
            .into_iter()
            .filter(|t| !t.is_zero())
            .collect();
        if tau_sum.is_zero() {
            assert!(
                parts.is_empty(),
                "{name}: τ(M ⊕ N) is zero but τM ⊕ τN is not"
            );
        } else {
            assert!(
                !parts.is_empty(),
                "{name}: τM and τN are zero but τ(M ⊕ N) is not"
            );
            let expected = direct_sum(&parts).0;
            certified_isomorphic(&tau_sum, &expected, name);
        }
    });
}

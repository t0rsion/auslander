use super::*;
use crate::algebra::{
    an_with_relations, cyclic_nakayama, dual_numbers, kronecker, linear_an,
    radical_square_zero_cycle, truncated_poly,
};
use crate::field::{Fp, PrimeField};
use crate::hom::{Morphism, express_in_row_basis, identity};
use crate::homspace::flat_row;
use crate::linalg::{DenseMat, RowReducer};
use crate::module::{Module, direct_sum};

use super::polynomial::split_squarefree_roots;
use super::radical::{char_poly, morphism_char_poly, trace_form};

fn f5() -> PrimeField {
    PrimeField::new(5).unwrap()
}

fn unit(dim: usize, k: usize, field: &PrimeField) -> Vec<Fp> {
    let mut v = vec![field.zero(); dim];
    v[k] = field.one();
    v
}

// Modules with radicals, matrix blocks, and repeated summands, over every
// field of `fields()`. The endomorphism-algebra fixture set.
fn fixture_modules() -> Vec<Module> {
    let mut out = Vec::new();
    for field in fields() {
        let a3 = linear_an(3, field);
        let dn = dual_numbers(field);
        let tp = truncated_poly(3, field).unwrap();
        let rel = an_with_relations(3, &[(0, 2)], field).unwrap();
        let singles = [
            Module::projective(&a3, 0),
            Module::simple(&a3, 1),
            Module::projective(&dn, 0),
            Module::projective(&tp, 0),
            Module::projective(&rel, 0),
            Module::projective(&kronecker(2, field), 0),
        ];
        for m in &singles {
            let (double, _, _) = direct_sum(&[m, m]);
            out.push(m.clone());
            out.push(double);
        }
        let (mixed, _, _) = direct_sum(&[
            &Module::projective(&a3, 0),
            &Module::simple(&a3, 0),
            &Module::simple(&a3, 2),
        ]);
        out.push(mixed);
        out.push(kronecker_f4_module());
    }
    out
}

#[test]
fn end_of_a_simple_is_one_dimensional() {
    let a = linear_an(3, f5());
    let e = EndoAlgebra::new(&Module::simple(&a, 0));
    assert_eq!(e.dim(), 1);
    assert_eq!(e.multiply(e.one(), e.one()), e.one().to_vec());
}

#[test]
fn field_is_the_field_of_the_module() {
    let a = linear_an(3, f5());
    let e = EndoAlgebra::new(&Module::simple(&a, 0));
    assert_eq!(e.field(), f5());
}

#[test]
fn end_of_the_zero_module_is_zero_dimensional() {
    let a = linear_an(3, f5());
    let e = EndoAlgebra::new(&Module::zero(&a));
    assert_eq!(e.dim(), 0);
    assert!(e.one().is_empty());
}

#[test]
fn end_of_the_dual_numbers_regular_module_has_dimension_2() {
    let a = dual_numbers(f5());
    let e = EndoAlgebra::new(&Module::projective(&a, 0));
    assert_eq!(e.dim(), 2);
}

#[test]
fn structure_constants_reproduce_composition() {
    let field = f5();
    let a = linear_an(2, field);
    let p0 = Module::projective(&a, 0);
    let p1 = Module::projective(&a, 1);
    let (sum, _, _) = direct_sum(&[&p0, &p1]);
    let e = EndoAlgebra::new(&sum);
    assert_eq!(e.dim(), 3);
    for i in 0..e.dim() {
        for j in 0..e.dim() {
            let product = e.basis()[i].then(&e.basis()[j]).unwrap();
            assert_eq!(
                e.multiply(&unit(e.dim(), i, &field), &unit(e.dim(), j, &field)),
                e.coords(&product),
                "b_{i} · b_{j}"
            );
        }
    }
}

#[test]
fn one_is_neutral_and_multiplication_is_associative_on_basis_triples() {
    let field = f5();
    let a = dual_numbers(field);
    let p = Module::projective(&a, 0);
    let (sum, _, _) = direct_sum(&[&p, &p]);
    let e = EndoAlgebra::new(&sum);
    let units: Vec<Vec<Fp>> = (0..e.dim()).map(|k| unit(e.dim(), k, &field)).collect();
    for x in &units {
        assert_eq!(e.multiply(e.one(), x), *x);
        assert_eq!(e.multiply(x, e.one()), *x);
        for y in &units {
            for z in &units {
                assert_eq!(
                    e.multiply(&e.multiply(x, y), z),
                    e.multiply(x, &e.multiply(y, z))
                );
            }
        }
    }
}

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

fn fields() -> [PrimeField; 3] {
    [
        PrimeField::new(2).unwrap(),
        PrimeField::new(3).unwrap(),
        PrimeField::new(5).unwrap(),
    ]
}

#[test]
fn char_poly_of_a_companion_matrix_recovers_its_polynomial() {
    let field = f5();
    // Companion matrix of x³ + 2x² + 3x + 4 in the row convention.
    let rows = vec![
        vec![field.elem(0), field.elem(1), field.elem(0)],
        vec![field.elem(0), field.elem(0), field.elem(1)],
        vec![field.elem(-4), field.elem(-3), field.elem(-2)],
    ];
    assert_eq!(
        char_poly(&DenseMat::from_rows(&rows), &field),
        vec![field.elem(4), field.elem(3), field.elem(2), field.elem(1)]
    );
    assert_eq!(char_poly(&DenseMat::zero(0, 0), &field), vec![field.one()]);
}

#[test]
fn char_poly_satisfies_cayley_hamilton_on_random_matrices() {
    let mut rng = XorShift64(0x0005_eed0_c4a1_e401);
    for field in fields() {
        let p = field.modulus();
        for _ in 0..25 {
            let n = 1 + rng.below(6) as usize;
            let mut a = DenseMat::zero(n, n);
            for r in 0..n {
                for c in 0..n {
                    a.set(r, c, field.elem(rng.below(p) as i64));
                }
            }
            let cp = char_poly(&a, &field);
            let mut acc = DenseMat::zero(n, n);
            for &coeff in cp.iter().rev() {
                acc = acc.mul(&a, &field);
                for i in 0..n {
                    acc.set(i, i, field.add(acc.get(i, i), coeff));
                }
            }
            assert_eq!(acc, DenseMat::zero(n, n), "p = {p}, n = {n}");
        }
    }
}

#[test]
fn radical_of_end_of_a_simple_is_zero() {
    for field in fields() {
        let a = linear_an(3, field);
        let e = EndoAlgebra::new(&Module::simple(&a, 1));
        assert_eq!(e.radical_dim(), 0, "p = {}", field.modulus());
    }
}

// End(P_v) ≅ e_v A e_v; for these fixtures the only path v → v is trivial,
// so every End(P_v) is k and the radical vanishes.
#[test]
fn radical_of_end_of_indecomposable_projectives_matches_path_counts() {
    for field in fields() {
        for algebra in [
            linear_an(3, field),
            kronecker(2, field),
            cyclic_nakayama(&[3, 3, 3], field).unwrap(),
            radical_square_zero_cycle(3, field),
        ] {
            for v in 0..algebra.quiver().num_vertices() {
                let e = EndoAlgebra::new(&Module::projective(&algebra, v));
                assert_eq!(e.dim(), 1, "End P_{v} over F_{}", field.modulus());
                assert_eq!(e.radical_dim(), 0, "rad End P_{v}");
            }
        }
    }
}

// End of the regular module k[x]/(xⁿ) is k[x]/(xⁿ) itself: radical (x).
#[test]
fn radical_of_end_of_truncated_polynomial_regular_modules_has_codimension_1() {
    for field in fields() {
        for n in 2..=4 {
            let a = truncated_poly(n, field).unwrap();
            let e = EndoAlgebra::new(&Module::projective(&a, 0));
            assert_eq!(e.dim(), n, "p = {}", field.modulus());
            assert_eq!(e.radical_dim(), n - 1, "p = {}", field.modulus());
        }
    }
}

// The quotient module k[x]/(x²) over k[x]/(x³) has End = k[x]/(x²).
#[test]
fn radical_of_end_of_a_truncated_polynomial_quotient_module_is_known() {
    for field in fields() {
        let a = truncated_poly(3, field).unwrap();
        let x = DenseMat::from_rows(&[
            vec![field.zero(), field.one()],
            vec![field.zero(), field.zero()],
        ]);
        let m = Module::new(a, vec![2], vec![x]).unwrap();
        let e = EndoAlgebra::new(&m);
        assert_eq!(e.dim(), 2);
        assert_eq!(e.radical_dim(), 1);
    }
}

#[test]
fn radical_of_end_of_a_sum_of_distinct_simples_is_zero() {
    for field in fields() {
        let a = linear_an(3, field);
        let s0 = Module::simple(&a, 0);
        let s1 = Module::simple(&a, 1);
        let (sum, _, _) = direct_sum(&[&s0, &s1]);
        let e = EndoAlgebra::new(&sum);
        assert_eq!(e.dim(), 2);
        assert_eq!(e.radical_dim(), 0);
    }
}

// End(S ⊕ S) ≅ M_2(F_p) is semisimple. On M_2(F_2) the trace form of the
// regular representation vanishes identically, because it is twice the matrix
// trace form. A radical test built on that form would return the whole algebra
// at p = 2; the chain used here returns 0.
#[test]
fn radical_of_a_2x2_matrix_algebra_is_zero() {
    for field in fields() {
        let a = linear_an(3, field);
        let s = Module::simple(&a, 0);
        let (sum, _, _) = direct_sum(&[&s, &s]);
        let e = EndoAlgebra::new(&sum);
        assert_eq!(e.dim(), 4);
        assert_eq!(e.radical_dim(), 0, "p = {}", field.modulus());
    }
}

// End(A ⊕ A) ≅ M_2(k[ε]) for the dual numbers: radical M_2(εk).
#[test]
fn radical_of_end_of_a_doubled_dual_numbers_module_has_dimension_4() {
    for field in fields() {
        let a = dual_numbers(field);
        let p = Module::projective(&a, 0);
        let (sum, _, _) = direct_sum(&[&p, &p]);
        let e = EndoAlgebra::new(&sum);
        assert_eq!(e.dim(), 8);
        assert_eq!(e.radical_dim(), 4, "p = {}", field.modulus());
    }
}

#[test]
fn radical_elements_are_nilpotent_and_the_radical_is_an_ideal() {
    for field in fields() {
        let a = an_with_relations(3, &[(0, 2)], field).unwrap();
        let p0 = Module::projective(&a, 0);
        let s0 = Module::simple(&a, 0);
        let (sum, _, _) = direct_sum(&[&p0, &s0]);
        let e = EndoAlgebra::new(&sum);
        assert!(e.radical_dim() > 0);
        for r in 0..e.radical_dim() {
            let x = e.morphism(e.radical_basis().row(r));
            let mut power = x.clone();
            for _ in 1..sum.total_dim() {
                power = power.then(&x).unwrap();
            }
            assert!(power.is_zero(), "radical element is nilpotent");
            for k in 0..e.dim() {
                let b = &e.basis()[k];
                assert!(e.in_radical(&e.coords(&b.then(&x).unwrap())));
                assert!(e.in_radical(&e.coords(&x.then(b).unwrap())));
            }
        }
        assert!(!e.in_radical(e.one()));
    }
}

#[test]
fn end_of_a_simple_and_of_uniserial_projectives_is_local() {
    for field in fields() {
        let a3 = linear_an(3, field);
        assert!(EndoAlgebra::new(&Module::simple(&a3, 0)).is_local());
        assert!(EndoAlgebra::new(&Module::projective(&a3, 0)).is_local());
        for n in 2..=4 {
            let a = truncated_poly(n, field).unwrap();
            let e = EndoAlgebra::new(&Module::projective(&a, 0));
            assert!(e.is_local(), "k[x]/(x^{n}) over F_{}", field.modulus());
            assert!(e.quotient_is_commutative());
            assert_eq!(e.semisimple_factor_count(), 1);
        }
    }
}

#[test]
fn end_of_a_sum_of_distinct_simples_has_two_commutative_factors() {
    for field in fields() {
        let a = linear_an(3, field);
        let s0 = Module::simple(&a, 0);
        let s1 = Module::simple(&a, 1);
        let (sum, _, _) = direct_sum(&[&s0, &s1]);
        let e = EndoAlgebra::new(&sum);
        assert!(e.quotient_is_commutative());
        assert_eq!(e.semisimple_factor_count(), 2);
        assert!(!e.is_local());
    }
}

// End(S ⊕ S) ≅ M_2(F_p): radical zero yet neither commutative nor local,
// and a single Wedderburn factor.
#[test]
fn a_2x2_matrix_algebra_is_semisimple_but_neither_commutative_nor_local() {
    for field in fields() {
        let a = linear_an(3, field);
        let s = Module::simple(&a, 0);
        let (sum, _, _) = direct_sum(&[&s, &s]);
        let e = EndoAlgebra::new(&sum);
        assert_eq!(e.radical_dim(), 0);
        assert!(!e.quotient_is_commutative());
        assert_eq!(e.semisimple_factor_count(), 1);
        assert!(!e.is_local());
    }
}

#[test]
fn end_of_p0_plus_s0_has_a_radical_and_two_factors() {
    for field in fields() {
        let a = linear_an(3, field);
        let p0 = Module::projective(&a, 0);
        let s0 = Module::simple(&a, 0);
        let (sum, _, _) = direct_sum(&[&p0, &s0]);
        let e = EndoAlgebra::new(&sum);
        assert_eq!(e.dim(), 3);
        assert_eq!(e.radical_dim(), 1);
        assert!(e.quotient_is_commutative());
        assert_eq!(e.semisimple_factor_count(), 2);
        assert!(!e.is_local());
    }
}

#[test]
fn the_zero_endomorphism_algebra_is_not_local() {
    let a = linear_an(3, f5());
    let e = EndoAlgebra::new(&Module::zero(&a));
    assert!(!e.is_local());
    assert_eq!(e.semisimple_factor_count(), 0);
}

#[test]
fn split_idempotent_is_exact_nontrivial_and_deterministic() {
    for field in fields() {
        let a = linear_an(3, field);
        let p0 = Module::projective(&a, 0);
        let s0 = Module::simple(&a, 0);
        let (sum, _, _) = direct_sum(&[&p0, &s0]);
        let e = EndoAlgebra::new(&sum);
        let first = e.split_idempotent(&mut SplitMix64(7)).unwrap();
        let again = e.split_idempotent(&mut SplitMix64(7)).unwrap();
        assert_eq!(first, again, "seeded run is reproducible");
        assert_eq!(e.multiply(&first, &first), first);
        assert!(first.iter().any(|c| !c.is_zero()));
        assert_ne!(first, e.one().to_vec());
    }
}

#[test]
fn singular_element_is_a_non_unit_that_is_not_nilpotent() {
    // End(P ⊕ P) = M_2(k[x]/(x²)), whose semisimple quotient M_2(k) is a
    // single Wedderburn factor, so split_idempotent declines and this is
    // the only route to a split.
    for field in [f5(), PrimeField::new(32003).unwrap()] {
        let a = dual_numbers(field);
        let p = Module::projective(&a, 0);
        let (sum, _, _) = direct_sum(&[&p, &p]);
        let e = EndoAlgebra::new(&sum);
        assert_eq!(e.semisimple_factor_count(), 1);
        assert!(e.split_idempotent(&mut SplitMix64(7)).is_none());

        let coords = e
            .singular_element(&mut SplitMix64(7), 64)
            .expect("M_2(k) contains non-units that are not nilpotent");
        let phi = e.morphism(&coords);
        assert!(
            !phi.is_isomorphism(),
            "a unit gives the trivial Fitting split"
        );
        let mut power = phi.clone();
        for _ in 0..sum.total_dim() {
            power = power.then(&phi).expect("endomorphisms compose");
        }
        assert!(
            !power.is_zero(),
            "a nilpotent gives the trivial Fitting split"
        );
        let again = e.singular_element(&mut SplitMix64(7), 64).unwrap();
        assert_eq!(coords, again, "seeded run is reproducible");
    }
}

#[test]
fn singular_element_is_none_for_a_local_algebra() {
    for field in fields() {
        let a = dual_numbers(field);
        let p = Module::projective(&a, 0);
        let e = EndoAlgebra::new(&p);
        assert!(e.is_local());
        assert!(e.singular_element(&mut SplitMix64(11), 64).is_none());
    }
}

#[test]
fn split_idempotent_is_none_for_local_and_single_factor_algebras() {
    let field = f5();
    let a = linear_an(3, field);
    let p0 = Module::projective(&a, 0);
    assert!(
        EndoAlgebra::new(&p0)
            .split_idempotent(&mut SplitMix64(7))
            .is_none()
    );
    let s = Module::simple(&a, 0);
    let (sum, _, _) = direct_sum(&[&s, &s]);
    // M_2(F_p) has one factor: the central route cannot split it.
    assert!(
        EndoAlgebra::new(&sum)
            .split_idempotent(&mut SplitMix64(7))
            .is_none()
    );
}

// p = 1000003 is past the 4096 scan threshold, so this forces the
// Cantor-Zassenhaus path through gcd(m, (x + δ)^{(p−1)/2} − 1).
#[test]
fn split_idempotent_works_over_a_large_prime_via_cantor_zassenhaus() {
    let field = PrimeField::new(1_000_003).unwrap();
    let a = linear_an(2, field);
    let s0 = Module::simple(&a, 0);
    let s1 = Module::simple(&a, 1);
    let (sum, _, _) = direct_sum(&[&s0, &s1]);
    let e = EndoAlgebra::new(&sum);
    assert_eq!(e.semisimple_factor_count(), 2);
    let idem = e.split_idempotent(&mut SplitMix64(7)).unwrap();
    assert_eq!(e.multiply(&idem, &idem), idem);
    assert!(idem.iter().any(|c| !c.is_zero()));
    assert_ne!(idem, e.one().to_vec());
}

#[test]
fn split_squarefree_roots_recovers_all_roots() {
    let field = f5();
    // (x − 1)(x − 3) = x² − 4x + 3.
    let poly = vec![field.elem(3), field.elem(-4), field.one()];
    let mut roots = split_squarefree_roots(&poly, &field, &mut SplitMix64(1)).unwrap();
    roots.sort_by_key(|r| r.raw());
    assert_eq!(roots, vec![field.elem(1), field.elem(3)]);
    let big = PrimeField::new(1_000_003).unwrap();
    // (x − 2)(x − 123456) over a prime past the scan threshold.
    let c0 = big.mul(big.elem(2), big.elem(123_456));
    let c1 = big.neg(big.add(big.elem(2), big.elem(123_456)));
    let mut roots = split_squarefree_roots(&[c0, c1, big.one()], &big, &mut SplitMix64(1)).unwrap();
    roots.sort_by_key(|r| r.raw());
    assert_eq!(roots, vec![big.elem(2), big.elem(123_456)]);
}

#[test]
fn coords_and_morphism_round_trip() {
    let field = f5();
    let a = linear_an(2, field);
    let p0 = Module::projective(&a, 0);
    let p1 = Module::projective(&a, 1);
    let (sum, _, _) = direct_sum(&[&p0, &p1]);
    let e = EndoAlgebra::new(&sum);
    let coords: Vec<Fp> = (0..e.dim() as i64).map(|i| field.elem(i + 1)).collect();
    assert_eq!(e.coords(&e.morphism(&coords)), coords);
    assert_eq!(e.coords(&identity(&sum)), e.one().to_vec());
}

/// The Kronecker representation (a, b) ↦ (I₂, C) with C the companion
/// matrix of x² + x + 1, irreducible over F_2.
fn kronecker_f4_module() -> Module {
    let field = PrimeField::new(2).unwrap();
    let a = kronecker(2, field);
    let id = DenseMat::from_rows(&[
        vec![field.one(), field.zero()],
        vec![field.zero(), field.one()],
    ]);
    let c = DenseMat::from_rows(&[
        vec![field.zero(), field.one()],
        vec![field.one(), field.one()],
    ]);
    Module::new(a, vec![2, 2], vec![id, c]).unwrap()
}

// End(M) ≅ F_4 = F_2[C]: a non-split residue field, so the single
// Frobenius-fixed factor comes from the extension-field branch of the
// factor count, not from a copy of F_p.
#[test]
fn end_of_the_f4_kronecker_module_is_the_field_with_four_elements() {
    let e = EndoAlgebra::new(&kronecker_f4_module());
    assert_eq!(e.dim(), 2);
    assert_eq!(e.radical_dim(), 0);
    assert_eq!(e.semisimple_factor_count(), 1);
    assert!(e.quotient_is_commutative());
    assert!(e.is_local());
}

// The claim `express` rests on: the hom basis carries the identity at its
// free columns, so no submatrix inverse is ever needed.
#[test]
fn the_flattened_basis_carries_the_identity_at_the_coordinate_columns() {
    for m in fixture_modules() {
        let e = EndoAlgebra::new(&m);
        assert!(
            e.coord_inverse.is_none(),
            "dim {} needed a submatrix inverse",
            e.dim()
        );
        for (r, &c) in e.coord_cols.iter().enumerate() {
            for k in 0..e.dim() {
                let expected = if k == r { Fp::ONE } else { Fp::ZERO };
                assert_eq!(e.flat.get(k, c), expected, "flat[{k}][{c}]");
            }
        }
    }
}

// Selecting coordinates off the flat row must agree with solving for them.
#[test]
fn coordinates_agree_with_solving_the_flattened_system() {
    for m in fixture_modules() {
        let e = EndoAlgebra::new(&m);
        let field = e.field();
        let mut targets: Vec<Morphism> = vec![identity(&m)];
        for i in 0..e.dim() {
            for j in 0..e.dim() {
                targets.push(e.basis[i].then(&e.basis[j]).unwrap());
            }
        }
        for f in &targets {
            let mut row = DenseMat::zero(1, e.flat.cols());
            for (c, &v) in flat_row(f).iter().enumerate() {
                row.set(0, c, v);
            }
            let solved = express_in_row_basis(&e.flat, &row, &field).row(0).to_vec();
            assert_eq!(e.coords(f), solved);
        }
    }
}

// The closed-form first round must reproduce the general
// characteristic-polynomial round, entry for entry.
#[test]
fn the_trace_form_matches_the_characteristic_polynomial_round() {
    for m in fixture_modules() {
        if m.total_dim() == 0 {
            continue;
        }
        let e = EndoAlgebra::new(&m);
        let field = e.field();
        let n = m.total_dim();
        let mut expected = DenseMat::zero(e.dim(), e.dim());
        for j in 0..e.dim() {
            for k in 0..e.dim() {
                let product = e.basis[j].then(&e.basis[k]).unwrap();
                let cp = morphism_char_poly(&product, &field);
                expected.set(k, j, cp[n - 1]);
            }
        }
        assert_eq!(trace_form(&e), expected, "dim vector {:?}", m.dim_vector());
    }
}

// Membership by reduction must agree with the rank test.
#[test]
fn radical_membership_agrees_with_the_rank_test() {
    let mut rng = XorShift64(0x0005_eed0_c4a1_e402);
    for m in fixture_modules() {
        let e = EndoAlgebra::new(&m);
        let field = e.field();
        let p = field.modulus();
        for _ in 0..8 {
            let coords: Vec<Fp> = (0..e.dim())
                .map(|_| field.elem(rng.below(p) as i64))
                .collect();
            let mut stacked = DenseMat::zero(e.radical_dim() + 1, e.dim());
            for r in 0..e.radical_dim() {
                for c in 0..e.dim() {
                    stacked.set(r, c, e.radical_basis().get(r, c));
                }
            }
            for (c, &v) in coords.iter().enumerate() {
                stacked.set(e.radical_dim(), c, v);
            }
            assert_eq!(
                e.in_radical(&coords),
                stacked.rank(&field) == e.radical_dim()
            );
        }
    }
}

// Quotient coordinates by the stored map must agree with solving against
// the radical rows stacked over the complement rows.
#[test]
fn quotient_coordinates_agree_with_the_change_of_basis() {
    let mut rng = XorShift64(0x0005_eed0_c4a1_e403);
    for m in fixture_modules() {
        let e = EndoAlgebra::new(&m);
        let field = e.field();
        let p = field.modulus();
        let full: Vec<Vec<Fp>> = (0..e.radical_dim())
            .map(|r| e.radical_basis().row(r).to_vec())
            .chain((0..e.quotient_dim()).map(|r| e.complement.row(r).to_vec()))
            .collect();
        if full.is_empty() {
            continue;
        }
        let full = DenseMat::from_rows(&full);
        for _ in 0..8 {
            let coords: Vec<Fp> = (0..e.dim())
                .map(|_| field.elem(rng.below(p) as i64))
                .collect();
            let mut row = DenseMat::zero(1, e.dim());
            for (c, &v) in coords.iter().enumerate() {
                row.set(0, c, v);
            }
            let expressed = express_in_row_basis(&full, &row, &field);
            let expected: Vec<Fp> = (e.radical_dim()..e.dim())
                .map(|c| expressed.get(0, c))
                .collect();
            assert_eq!(e.reduce(&coords), expected);
        }
    }
}

#[test]
fn the_quotient_dimension_is_the_codimension_of_the_radical() {
    for m in fixture_modules() {
        let e = EndoAlgebra::new(&m);
        assert_eq!(e.quotient_dim(), e.dim() - e.radical_dim());
    }
}

#[path = "tests/structural.rs"]
mod structural;

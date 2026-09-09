use super::*;
use crate::algebra::{
    an_with_relations, dual_numbers, kronecker, linear_an, radical_square_zero_cycle,
    truncated_poly,
};
use crate::field::PrimeField;
use crate::hom::hom_dim;
use crate::module::direct_sum;

fn f5() -> PrimeField {
    PrimeField::new(5).unwrap()
}

// Right modules over linearly oriented A_3 (arrows a: 0 -> 1, b: 1 -> 2).
// The non-split extension realized by arrow a is 0 -> S_1 -> M -> S_0 -> 0
// with M = P_0/rad^2 of dimension vector (1, 1, 0), top S_0 and socle S_1,
// so the nonzero Ext group is Ext^1(S_0, S_1). In general
// dim Ext^1(S_i, S_j) is the number of arrows i -> j (the same pairing as
// for left modules over A^op read backwards; ASS III.2.12 states it for
// right modules).
#[test]
fn a3_ext_1_between_simples_counts_arrows_source_to_target() {
    let field = f5();
    let algebra = linear_an(3, field);
    let simples: Vec<Module> = (0..3).map(|v| Module::simple(&algebra, v)).collect();
    for i in 0..3 {
        for j in 0..3 {
            let expected = usize::from(j == i + 1);
            assert_eq!(
                ext_dim(&simples[i], &simples[j], 1).unwrap(),
                expected,
                "Ext^1(S_{i}, S_{j})"
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
    assert_eq!(global_dimension(&algebra, 5), Bounded::Exact(1));
}

// kA_3/(ab), right modules: pd S_0 = 2 via 0 -> P_2 -> P_1 -> P_0 -> S_0 -> 0.
// Counting arrows i -> j gives Ext^1(S_0, S_1) = Ext^1(S_1, S_2) = 1. The
// relation detects Ext^2 on the ordered pair (source, target) of the
// forbidden path: Hom(P_2, S_2) = k sits in degree 2 of the resolution of
// S_0 with zero delta on both sides, so Ext^2(S_0, S_2) = 1. These values
// match the QPA-verified facts (Ext^1(S_0, S_1) = 1, Ext^2(S_0, S_2) = 1)
// on the same ordered pairs, with no right-versus-left discrepancy.
#[test]
fn a3_mod_ab_ext_1_and_2_among_simples() {
    let field = f5();
    let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
    let simples: Vec<Module> = (0..3).map(|v| Module::simple(&algebra, v)).collect();
    for i in 0..3 {
        for j in 0..3 {
            let ext1 = usize::from(j == i + 1);
            let ext2 = usize::from(i == 0 && j == 2);
            assert_eq!(
                ext_dim(&simples[i], &simples[j], 1).unwrap(),
                ext1,
                "Ext^1(S_{i}, S_{j})"
            );
            assert_eq!(
                ext_dim(&simples[i], &simples[j], 2).unwrap(),
                ext2,
                "Ext^2(S_{i}, S_{j})"
            );
            assert_eq!(ext_dim(&simples[i], &simples[j], 3).unwrap(), 0);
        }
    }
    assert_eq!(global_dimension(&algebra, 5), Bounded::Exact(2));
}

#[test]
fn dual_numbers_ext_table_of_the_simple_is_all_ones() {
    let field = f5();
    let algebra = dual_numbers(field);
    let s = Module::simple(&algebra, 0);
    assert_eq!(ext_table(&s, &s, 4).unwrap(), vec![1, 1, 1, 1, 1]);
    assert_eq!(global_dimension(&algebra, 6), Bounded::AtLeast(7));
}

// k[x]/(x^3) over F_3: the minimal resolution of S has syzygy period 2
// (Omega S = rad P has dimension 2, Omega^2 S = soc P is isomorphic to S),
// every term is P, and Hom(P, S) = k with zero differentials throughout.
#[test]
fn truncated_poly_3_ext_table_of_the_simple_is_all_ones() {
    let field = PrimeField::new(3).unwrap();
    let algebra = truncated_poly(3, field).unwrap();
    let s = Module::simple(&algebra, 0);
    let res = resolve(&s, 5);
    for term in &res.terms {
        assert_eq!(term.dim_vector(), &[3]);
    }
    assert_eq!(ext_table(&s, &s, 4).unwrap(), vec![1, 1, 1, 1, 1]);
}

// Cycle 0 -> 1 -> 2 -> 0 with rad^2 = 0, right modules: rad P_i = S_{i+1},
// so Omega S_i = S_{i+1} and the extension realized by the arrow i -> i+1
// gives Ext^1(S_i, S_{i+1}) = 1 while Ext^1(S_i, S_{i-1}) = 0. The pairing
// again runs from arrow source to arrow target.
#[test]
fn radical_square_zero_cycle_ext_1_follows_the_arrows() {
    let field = f5();
    let algebra = radical_square_zero_cycle(3, field);
    let simples: Vec<Module> = (0..3).map(|v| Module::simple(&algebra, v)).collect();
    for i in 0..3 {
        for j in 0..3 {
            let expected = usize::from(j == (i + 1) % 3);
            assert_eq!(
                ext_dim(&simples[i], &simples[j], 1).unwrap(),
                expected,
                "Ext^1(S_{i}, S_{j})"
            );
        }
    }
    assert_eq!(global_dimension(&algebra, 4), Bounded::AtLeast(5));
}

// Regression against the old examples-db, which listed hereditary Kronecker
// algebras as having infinite global dimension.
#[test]
fn kronecker_2_is_hereditary_with_global_dimension_1() {
    let algebra = kronecker(2, f5());
    assert_eq!(global_dimension(&algebra, 5), Bounded::Exact(1));
}

fn assorted_pairs() -> Vec<(Module, Module)> {
    let field = f5();
    let mut pairs = Vec::new();
    for algebra in [
        linear_an(3, field),
        an_with_relations(3, &[(0, 2)], field).unwrap(),
        dual_numbers(field),
        radical_square_zero_cycle(3, field),
    ] {
        let n = algebra.quiver().num_vertices();
        for v in 0..n {
            let s = Module::simple(&algebra, v);
            let p = Module::projective(&algebra, v);
            let i = Module::injective(&algebra, v);
            pairs.push((s.clone(), i.clone()));
            pairs.push((i, s.clone()));
            pairs.push((s.clone(), p.clone()));
            pairs.push((p, s));
        }
        let s0 = Module::simple(&algebra, 0);
        let i_last = Module::injective(&algebra, n - 1);
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
            "Ext^0 with dim m = {:?}, dim n = {:?}",
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
    let field = f5();
    let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
    let s0 = Module::simple(&algebra, 0);
    let s2 = Module::simple(&algebra, 2);
    assert_eq!(ext_table(&s0, &s2, 6).unwrap(), vec![0, 0, 1, 0, 0, 0, 0]);
}

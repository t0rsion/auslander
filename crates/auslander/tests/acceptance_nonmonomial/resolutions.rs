use auslander::ext::{ext_table, global_dimension};
use auslander::injective::injective_dimension;
use auslander::module::Module;
use auslander::resolution::{Bounded, projective_dimension, resolve};

use super::common::preprojective_a3;
use super::fixtures::{dim_vecs, square};

/// Row 3. Hand derivation for A: `S_3 = P_3` is projective. For `S_1` the
/// cover is `P_1` with kernel `rad P_1 = S_3 = P_3`, so `pd S_1 = 1`;
/// `S_2` is symmetric. For `S_0` the cover is `P_0` with kernel
/// `rad P_0 = [0, 1, 1, 1]`, whose top is `S_1 ⊕ S_2` (only `ab` is in
/// `rad² P_0`), so the next term is `P_1 ⊕ P_2 = [0, 1, 1, 2]`; the kernel
/// has dimension vector `[0, 1, 1, 2] - [0, 1, 1, 1] = [0, 0, 0, 1] = P_3`.
/// Hence `pd S_0 = 2` and `gldim A = 2`.
#[test]
fn square_simple_resolutions_and_global_dimension() {
    let a = square();
    let expected_terms: [&[[usize; 4]]; 4] = [
        &[[1, 1, 1, 1], [0, 1, 1, 2], [0, 0, 0, 1]],
        &[[0, 1, 0, 1], [0, 0, 0, 1]],
        &[[0, 0, 1, 1], [0, 0, 0, 1]],
        &[[0, 0, 0, 1]],
    ];
    for (v, expected) in expected_terms.iter().enumerate() {
        let s = Module::simple(&a, v as u32);
        let res = resolve(&s, 5);
        let terms: Vec<Vec<usize>> = dim_vecs(&res.terms);
        let expected: Vec<Vec<usize>> = expected.iter().map(|row| row.to_vec()).collect();
        assert_eq!(terms, expected, "resolution terms of S_{v}");
        assert_eq!(
            projective_dimension(&s, 5),
            Bounded::Exact(expected.len() - 1),
            "pd S_{v}"
        );
    }
    assert_eq!(global_dimension(&a, 5), Bounded::Exact(2));
}

/// Row 3. The resolutions above are minimal and `Hom(P_v, S_j) = δ_{vj} k`,
/// so `dim Ext^k(S_i, S_j)` is the multiplicity of `P_j` in term `k` of the
/// resolution of `S_i`: `Ext^1(S_0, S_1) = Ext^1(S_0, S_2) = 1`,
/// `Ext^2(S_0, S_3) = 1`, `Ext^1(S_1, S_3) = Ext^1(S_2, S_3) = 1`, nothing
/// else besides `Ext^0(S_i, S_i) = 1`. These values equal the oracle's `ext`
/// table.
#[test]
fn square_ext_dimensions_of_simples_up_to_degree_3() {
    let a = square();
    let mut expected = vec![vec![vec![0usize; 4]; 4]; 4];
    for (i, row) in expected.iter_mut().enumerate() {
        row[i][0] = 1;
    }
    expected[0][1][1] = 1;
    expected[0][2][1] = 1;
    expected[0][3][2] = 1;
    expected[1][3][1] = 1;
    expected[2][3][1] = 1;
    let simples: Vec<Module> = (0..4).map(|v| Module::simple(&a, v)).collect();
    for (i, si) in simples.iter().enumerate() {
        for (j, sj) in simples.iter().enumerate() {
            assert_eq!(
                ext_table(si, sj, 3).unwrap(),
                expected[i][j],
                "Ext^k(S_{i}, S_{j})"
            );
        }
    }
}

/// Row 3. B is self-injective and not semisimple, so no simple has finite
/// projective or injective dimension. Bound 6 matches the oracle's
/// `at_least 7` entries.
#[test]
fn preprojective_simples_have_pd_and_injdim_at_least_7() {
    let b = preprojective_a3();
    for v in 0..3 {
        let s = Module::simple(&b, v);
        assert_eq!(projective_dimension(&s, 6), Bounded::AtLeast(7), "pd S_{v}");
        assert_eq!(
            injective_dimension(&s, 6).unwrap(),
            Bounded::AtLeast(7),
            "id S_{v}"
        );
    }
}

/// Row 3 cross-check for B against the oracle's `ext` table, `k ≤ 3`.
#[test]
fn preprojective_ext_dimensions_match_the_oracle() {
    let b = preprojective_a3();
    let expected: [[[usize; 4]; 3]; 3] = [
        [[1, 0, 1, 0], [0, 1, 0, 0], [0, 0, 0, 1]],
        [[0, 1, 0, 0], [1, 0, 1, 1], [0, 1, 0, 0]],
        [[0, 0, 0, 1], [0, 1, 0, 0], [1, 0, 1, 0]],
    ];
    let simples: Vec<Module> = (0..3).map(|v| Module::simple(&b, v)).collect();
    for (i, si) in simples.iter().enumerate() {
        for (j, sj) in simples.iter().enumerate() {
            assert_eq!(
                ext_table(si, sj, 3).unwrap(),
                expected[i][j],
                "Ext^k(S_{i}, S_{j})"
            );
        }
    }
}

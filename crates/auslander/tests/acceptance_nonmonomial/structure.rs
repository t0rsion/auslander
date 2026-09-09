use auslander::module::Module;
use auslander::quiver::PathWord;
use auslander::radical::{loewy_length, radical_series, socle_series};

use super::common::{f5, ids, inhomogeneous, preprojective_a3};
use super::fixtures::{PREPROJECTIVE_CARTAN, SQUARE_CARTAN, dim_vecs, square};

/// Row 1. Normal words from `u` to `v` count `dim e_u A e_v`, so Cartan row
/// `v` is `dim P_v` and column `v` is `dim I_v`. For A the rows are the
/// path counts of the square with `ab = cd` identified.
#[test]
fn square_projectives_and_injectives_match_cartan_rows_and_columns() {
    let a = square();
    assert_eq!(a.dim(), 9);
    let cartan: Vec<Vec<usize>> = SQUARE_CARTAN.iter().map(|row| row.to_vec()).collect();
    assert_eq!(a.cartan_matrix(), cartan);
    for (v, row) in SQUARE_CARTAN.iter().enumerate() {
        let p = Module::projective(&a, v as u32);
        assert_eq!(p.dim_vector(), row, "dim P_{v}");
        let i = Module::injective(&a, v as u32);
        let column: Vec<usize> = SQUARE_CARTAN.iter().map(|r| r[v]).collect();
        assert_eq!(i.dim_vector(), column, "dim I_{v}");
    }
}

/// Row 1. B is self-injective, so the injective columns repeat the
/// projective rows; the Cartan matrix is the symmetric one of the oracle.
#[test]
fn preprojective_projectives_and_injectives_match_cartan_rows_and_columns() {
    let b = preprojective_a3();
    assert_eq!(b.dim(), 10);
    let cartan: Vec<Vec<usize>> = PREPROJECTIVE_CARTAN
        .iter()
        .map(|row| row.to_vec())
        .collect();
    assert_eq!(b.cartan_matrix(), cartan);
    for (v, row) in PREPROJECTIVE_CARTAN.iter().enumerate() {
        let p = Module::projective(&b, v as u32);
        assert_eq!(p.dim_vector(), row, "dim P_{v}");
        let i = Module::injective(&b, v as u32);
        let column: Vec<usize> = PREPROJECTIVE_CARTAN.iter().map(|r| r[v]).collect();
        assert_eq!(i.dim_vector(), column, "dim I_{v}");
    }
}

/// Row 2. Hand derivation for A: `rad P_0 = span{a, c, ab}`,
/// `rad² P_0 = span{ab}` (both `a·b` and `c·d` reduce to `ab`), `J³ = 0`.
/// `soc P_0 = span{ab}` because `a·b` and `c·d` are nonzero;
/// `soc² P_0 = span{a, c, ab}` because `e_1 J² = e_2 J² = 0` while
/// `e_0·ab ≠ 0`.
#[test]
fn square_radical_and_socle_series_of_the_regular_summands() {
    let a = square();
    let expected_rad: [&[[usize; 4]]; 4] = [
        &[[1, 1, 1, 1], [0, 1, 1, 1], [0, 0, 0, 1], [0, 0, 0, 0]],
        &[[0, 1, 0, 1], [0, 0, 0, 1], [0, 0, 0, 0]],
        &[[0, 0, 1, 1], [0, 0, 0, 1], [0, 0, 0, 0]],
        &[[0, 0, 0, 1], [0, 0, 0, 0]],
    ];
    for (v, expected) in expected_rad.iter().enumerate() {
        let p = Module::projective(&a, v as u32);
        let series: Vec<Vec<usize>> = dim_vecs(&radical_series(&p));
        let expected: Vec<Vec<usize>> = expected.iter().map(|row| row.to_vec()).collect();
        assert_eq!(series, expected, "radical series of P_{v}");
        assert_eq!(
            loewy_length(&p),
            expected.len() - 1,
            "Loewy length of P_{v}"
        );
    }
    let p0 = Module::projective(&a, 0);
    let socle: Vec<Vec<usize>> = dim_vecs(&socle_series(&p0));
    assert_eq!(
        socle,
        vec![
            vec![0, 0, 0, 0],
            vec![0, 0, 0, 1],
            vec![0, 1, 1, 1],
            vec![1, 1, 1, 1],
        ],
        "socle series of P_0"
    );
    assert_eq!(a.nilpotency_degree(), 3);
}

/// Row 2. Exact chains for B, hand-derived from the completed basis
/// `{a·abar, abar·a + b·bbar, bbar·b, a·b·bbar, b·bbar·abar}` over F_2.
/// `P_0 = {e_0, a, ab}` with `ab·bbar = 0`; `P_1 = {e_1, abar, b, b·bbar}`
/// with `abar·a = b·bbar` and `b·bbar·J = 0`; `P_2 = {e_2, bbar,
/// bbar·abar}` with `bbar·b = 0` and `bbar·abar·a = bbar·b·bbar = 0`. B is
/// self-injective, so each socle series is the reversed radical series.
#[test]
fn preprojective_radical_and_socle_series_of_the_projectives() {
    let b = preprojective_a3();
    let expected_rad: [&[[usize; 3]]; 3] = [
        &[[1, 1, 1], [0, 1, 1], [0, 0, 1], [0, 0, 0]],
        &[[1, 2, 1], [1, 1, 1], [0, 1, 0], [0, 0, 0]],
        &[[1, 1, 1], [1, 1, 0], [1, 0, 0], [0, 0, 0]],
    ];
    let expected_soc: [&[[usize; 3]]; 3] = [
        &[[0, 0, 0], [0, 0, 1], [0, 1, 1], [1, 1, 1]],
        &[[0, 0, 0], [0, 1, 0], [1, 1, 1], [1, 2, 1]],
        &[[0, 0, 0], [1, 0, 0], [1, 1, 0], [1, 1, 1]],
    ];
    for v in 0..3usize {
        let p = Module::projective(&b, v as u32);
        let rad: Vec<Vec<usize>> = dim_vecs(&radical_series(&p));
        let expected: Vec<Vec<usize>> = expected_rad[v].iter().map(|row| row.to_vec()).collect();
        assert_eq!(rad, expected, "radical series of P_{v}");
        let soc: Vec<Vec<usize>> = dim_vecs(&socle_series(&p));
        let expected: Vec<Vec<usize>> = expected_soc[v].iter().map(|row| row.to_vec()).collect();
        assert_eq!(soc, expected, "socle series of P_{v}");
        assert_eq!(loewy_length(&p), 3, "Loewy length of P_{v}");
    }
}

/// Row 2. Exact chains for C's `P_0 = {e_0, a, c, ab, cd}` with
/// `NF(cde) = ab`, hand-derived. Radical: `J P_0 = {a, c, ab, cd}`,
/// `J² P_0 = {ab, cd}` (from `a·b`, `c·d`), `J³ P_0 = {ab}` (from
/// `cd·e`), `J⁴ P_0 = 0`. Socle: `ab·J = 0`; `a·J² = cd·J² = 0` because no
/// length-2 path leaves vertex 1 or vertex 3, while `c·(de) = ab ≠ 0` keeps
/// `c` out of `soc²`; `c·J³ = 0` because `J³ = span{ab}` starts at vertex 0.
#[test]
fn inhomogeneous_radical_and_socle_series_of_p0() {
    let c = inhomogeneous();
    let p0 = Module::projective(&c, 0);
    assert_eq!(
        dim_vecs(&radical_series(&p0)),
        vec![
            vec![1, 1, 1, 1, 1],
            vec![0, 1, 1, 1, 1],
            vec![0, 0, 0, 1, 1],
            vec![0, 0, 0, 0, 1],
            vec![0, 0, 0, 0, 0],
        ],
        "radical series of P_0"
    );
    assert_eq!(
        dim_vecs(&socle_series(&p0)),
        vec![
            vec![0, 0, 0, 0, 0],
            vec![0, 0, 0, 0, 1],
            vec![0, 1, 0, 1, 1],
            vec![0, 1, 1, 1, 1],
            vec![1, 1, 1, 1, 1],
        ],
        "socle series of P_0"
    );
    assert_eq!(loewy_length(&p0), 4);
}

/// Row 2. Over C the relation forces `NF(cde) = ab`. Row-space iteration
/// gives `J² = span{ab, cd, de}` and `J³ = span{cd·e} = span{ab}`, so the
/// length-2 normal word `ab` spans `J³` while `J⁴ = 0`. Word length does not
/// decide the radical layer.
#[test]
fn inhomogeneous_normal_word_of_length_2_spans_j_cubed() {
    let c = inhomogeneous();
    assert_eq!(c.dim(), 13);
    let ab = PathWord::from_arrows(c.quiver(), &ids(&[0, 1])).unwrap();
    let cde = PathWord::from_arrows(c.quiver(), &ids(&[2, 3, 4])).unwrap();
    let ab_index = c.path_index(&ab).unwrap().expect("ab is a normal word");
    assert_eq!(c.path_index(&cde), Ok(None));
    assert_eq!(c.nf_word(&cde), Ok(vec![(ab_index, f5().one())]));
    assert_eq!(c.paths_between(0, 4), &[ab_index]);
    let j3 = c.radical_power_matrix(0, 4, 3);
    assert_eq!(j3.rows(), 1, "ab spans e_0 J³ e_4");
    assert_eq!(j3.row(0), &[f5().one()]);
    assert_eq!(c.radical_power_matrix(0, 4, 4).rows(), 0);
    assert_eq!(c.nilpotency_degree(), 4);
}

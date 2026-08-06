//! v0.3 acceptance matrix over genuinely non-monomial quotients.
//!
//! Fixtures:
//!
//! - A: the commutative square `kQ/(ab - cd)` over F_5, arrows `a: 0 → 1`
//!   (id 0), `b: 1 → 3` (1), `c: 0 → 2` (2), `d: 2 → 3` (3). Under
//!   `deglex-arrowid-v1` the leading word of `ab - cd` is `cd`, so the
//!   reduced Groebner basis is `{cd - ab}` and the normal words are
//!   `{e_0..e_3, a, c, b, d, ab}`: dim 9.
//! - B: the preprojective algebra of A_3 over F_2, the double quiver
//!   `a: 0 → 1` (0), `b: 1 → 2` (1), `abar: 1 → 0` (2), `bbar: 2 → 1` (3)
//!   with relations `a·abar`, `abar·a - b·bbar`, `bbar·b`: dim 10,
//!   self-injective. Its presentation and all pinned values come from
//!   `tests/qpa-oracle/README.md` and the committed `qpa_expected.json`.
//! - C: the inhomogeneous algebra `kQ/(ab - cde)` over F_5, arrows
//!   `a: 0 → 1` (0), `b: 1 → 4` (1), `c: 0 → 2` (2), `d: 2 → 3` (3),
//!   `e: 3 → 4` (4): dim 13. The relation mixes path lengths, so a short
//!   normal word sits inside a deep radical power.
//!
//! Every pinned value for A is hand-derived on the test that uses it. The
//! same values appear in the committed QPA oracle for the
//! `commutative-square` `f5` fixture.

use std::sync::Arc;

use auslander::algebra::{
    Algebra, AlgebraBuildError, commutative_square, linear_an, linear_nakayama,
};
use auslander::ar::{Tau, tau};
use auslander::certificate::FinitenessData;
use auslander::completion::{CompletionLimits, TruncationReason};
use auslander::decompose::{Certificate, KrullSchmidtOutcome, decompose, krull_schmidt};
use auslander::dynkin::{DynkinError, dynkin_indecomposables};
use auslander::endo::EndoAlgebra;
use auslander::enumerate::nakayama_indecomposables;
use auslander::ext::{ext_dim, ext_table, global_dimension};
use auslander::field::PrimeField;
use auslander::hom::kernel;
use auslander::injective::injective_dimension;
use auslander::iso::{IsoOutcome, Obstruction, is_isomorphic};
use auslander::linalg::DenseMat;
use auslander::module::{Module, ModuleError, direct_sum};
use auslander::opposite::{dual, nu_of_presentation_map, opposite};
use auslander::quiver::{ArrowId, PathWord, Quiver};
use auslander::radical::{loewy_length, radical, radical_series, socle_series};
use auslander::relation::{Presentation, Relation, RelationError};
use auslander::resolution::{Bounded, minimal_presentation_matrix, projective_dimension, resolve};
use auslander::verify::{VerifyError, verify};

fn f5() -> PrimeField {
    PrimeField::new(5).unwrap()
}

fn f2() -> PrimeField {
    PrimeField::new(2).unwrap()
}

fn ids(raw: &[u32]) -> Vec<ArrowId> {
    raw.iter().copied().map(ArrowId).collect()
}

fn square() -> Arc<Algebra> {
    commutative_square(f5())
}

fn preprojective_a3() -> Arc<Algebra> {
    let field = f2();
    let quiver = Quiver::new(3, &[(0, 1), (1, 2), (1, 0), (2, 1)]).unwrap();
    let relations = vec![
        Relation::new(&quiver, field, vec![(field.one(), ids(&[0, 2]))]).unwrap(),
        Relation::new(
            &quiver,
            field,
            vec![(field.one(), ids(&[2, 0])), (field.elem(-1), ids(&[1, 3]))],
        )
        .unwrap(),
        Relation::new(&quiver, field, vec![(field.one(), ids(&[3, 1]))]).unwrap(),
    ];
    let presentation = Presentation::new(quiver, field, relations).unwrap();
    Algebra::new(presentation, &CompletionLimits::default()).unwrap()
}

fn inhomogeneous_quiver() -> Quiver {
    Quiver::new(5, &[(0, 1), (1, 4), (0, 2), (2, 3), (3, 4)]).unwrap()
}

fn inhomogeneous() -> Arc<Algebra> {
    let field = f5();
    let quiver = inhomogeneous_quiver();
    let relation = Relation::new(
        &quiver,
        field,
        vec![
            (field.one(), ids(&[0, 1])),
            (field.elem(-1), ids(&[2, 3, 4])),
        ],
    )
    .unwrap();
    let presentation = Presentation::new(quiver, field, vec![relation]).unwrap();
    Algebra::new(presentation, &CompletionLimits::default()).unwrap()
}

fn dim_vecs(modules: &[Module]) -> Vec<Vec<usize>> {
    modules.iter().map(|m| m.dim_vector().to_vec()).collect()
}

const SQUARE_CARTAN: [[usize; 4]; 4] = [[1, 1, 1, 1], [0, 1, 0, 1], [0, 0, 1, 1], [0, 0, 0, 1]];

const PREPROJECTIVE_CARTAN: [[usize; 3]; 3] = [[1, 1, 1], [1, 2, 1], [1, 1, 1]];

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
/// `cd·e`), `J⁴ P_0 = 0`. Socle: `ab·J = 0`; `cd·J² = 0` because no
/// length-2 path leaves vertex 3, while `c·(de) = ab ≠ 0` keeps `c` out
/// of `soc²`; `c·J³ = 0` because `J³ = span{ab}` starts at vertex 0.
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
    let j3 = c.radical_power_component(0, 4, 3);
    assert_eq!(j3, vec![vec![f5().one()]], "ab spans e_0 J³ e_4");
    assert!(c.radical_power_component(0, 4, 4).is_empty());
    assert_eq!(c.nilpotency_degree(), 4);
}

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

/// Row 4. `D` is exact and contravariant, so `D(P_v)` is an indecomposable
/// injective over the opposite with socle `S_v`: `D(P_v) ≅ I_v` and
/// `D(I_v) ≅ P_v` over `A^op`.
#[test]
fn square_dual_swaps_projectives_and_injectives() {
    let a = square();
    let op = opposite(&a).unwrap();
    for v in 0..4 {
        let dp = dual(&Module::projective(&a, v), &op).unwrap();
        let i_op = Module::injective(op.opposite(), v);
        assert_eq!(dp.dim_vector(), i_op.dim_vector(), "dim D(P_{v})");
        assert!(
            matches!(
                is_isomorphic(&dp, &i_op).unwrap(),
                IsoOutcome::Isomorphic(_)
            ),
            "D(P_{v}) ≅ I_{v} over the opposite"
        );
        let di = dual(&Module::injective(&a, v), &op).unwrap();
        let p_op = Module::projective(op.opposite(), v);
        assert_eq!(di.dim_vector(), p_op.dim_vector(), "dim D(I_{v})");
        assert!(
            matches!(
                is_isomorphic(&di, &p_op).unwrap(),
                IsoOutcome::Isomorphic(_)
            ),
            "D(I_{v}) ≅ P_{v} over the opposite"
        );
    }
}

/// Row 4. `dual` preserves dimension vectors, so the double dual does too,
/// over both non-monomial fixtures.
#[test]
fn double_dual_preserves_dimension_vectors_over_square_and_preprojective() {
    for algebra in [square(), preprojective_a3()] {
        let op = opposite(&algebra).unwrap();
        let n = algebra.quiver().num_vertices();
        let mut modules = Vec::new();
        for v in 0..n {
            modules.push(Module::simple(&algebra, v));
            modules.push(Module::projective(&algebra, v));
            modules.push(Module::injective(&algebra, v));
            modules.push(radical(&Module::projective(&algebra, v)).0);
        }
        for m in &modules {
            let dd = dual(&dual(m, &op).unwrap(), &op).unwrap();
            assert!(Arc::ptr_eq(dd.algebra(), m.algebra()));
            assert_eq!(dd.dim_vector(), m.dim_vector());
        }
    }
}

/// Row 5. The minimal presentation of `S_0` over A is
/// `P_1 ⊕ P_2 → P_0 → S_0 → 0`: sources `[1, 2]`, target `[0]`. Each entry
/// lives in `e_0 A e_v`, a line spanned by `a` (resp. `c`), so it is one
/// nonzero coefficient. `ν` sends the map to `I_1 ⊕ I_2 → I_0`
/// (`[2, 1, 1, 0] → [1, 0, 0, 0]`) whose kernel is `τS_0 = [1, 1, 1, 0]`
/// (see the tau row). Transposing over the opposite twice restores the
/// matrix.
#[test]
fn square_minimal_presentation_of_s0_nakayama_map_and_transpose_round_trip() {
    let a = square();
    let s0 = Module::simple(&a, 0);
    let matrix = minimal_presentation_matrix(&s0);
    assert_eq!(matrix.sources(), &[1, 2]);
    assert_eq!(matrix.targets(), &[0]);
    for k in 0..2 {
        let entry = matrix.entry(k, 0);
        assert_eq!(entry.len(), 1, "e_0 A e_{} is a line", k + 1);
        assert!(!entry[0].is_zero(), "entry ({k}, 0) is nonzero");
    }
    let nu = nu_of_presentation_map(&matrix);
    assert_eq!(nu.source().dim_vector(), &[2, 1, 1, 0]);
    assert_eq!(nu.target().dim_vector(), &[1, 0, 0, 0]);
    assert_eq!(kernel(&nu).0.dim_vector(), &[1, 1, 1, 0]);
    let op = opposite(&a).unwrap();
    let transposed = matrix.transpose_over(&op).unwrap();
    assert_eq!(transposed.sources(), matrix.targets());
    assert_eq!(transposed.targets(), matrix.sources());
    let back = transposed.transpose_over(&op).unwrap();
    assert_eq!(back.sources(), matrix.sources());
    assert_eq!(back.targets(), matrix.targets());
    for k in 0..2 {
        assert_eq!(back.entry(k, 0), matrix.entry(k, 0), "entry ({k}, 0)");
    }
}

/// Row 6. Over A every `e_v A e_v` is the line `k·e_v`, so `End(P_v) = k`:
/// dimension 1, radical 0, local. `rad P_0 = [0, 1, 1, 1]` is
/// indecomposable (oracle decomposition), so its endomorphism algebra is
/// local with radical codimension 1. Over B, `End(P_1) = e_1 B e_1` has
/// dimension 2 (Cartan entry) and is local with radical dimension 1.
#[test]
fn endo_of_indecomposables_is_local() {
    let a = square();
    for v in 0..4 {
        let endo = EndoAlgebra::new(&Module::projective(&a, v));
        assert_eq!(endo.dim(), 1, "dim End(P_{v})");
        assert_eq!(endo.radical_dim(), 0, "rad End(P_{v})");
        assert!(endo.is_local(), "End(P_{v}) is local");
    }
    let rad_p0 = radical(&Module::projective(&a, 0)).0;
    let endo = EndoAlgebra::new(&rad_p0);
    assert!(endo.is_local(), "End(rad P_0) is local");
    assert_eq!(endo.dim() - endo.radical_dim(), 1, "radical codimension 1");
    let b = preprojective_a3();
    let endo = EndoAlgebra::new(&Module::projective(&b, 1));
    assert_eq!(endo.dim(), 2, "dim End(P_1) = dim e_1 B e_1");
    assert_eq!(endo.radical_dim(), 1);
    assert!(endo.is_local());
}

/// Row 6. `End(P_0 ⊕ P_0) = M_2(e_0 A e_0) = M_2(k)`: dimension 4,
/// semisimple (radical 0), one Wedderburn factor, not commutative, not
/// local.
#[test]
fn square_endo_of_p0_squared_is_a_two_by_two_matrix_algebra() {
    let a = square();
    let p0 = Module::projective(&a, 0);
    let p0_again = Module::projective(&a, 0);
    let (sum, _, _) = direct_sum(&[&p0, &p0_again]);
    let endo = EndoAlgebra::new(&sum);
    assert_eq!(endo.dim(), 4);
    assert_eq!(endo.radical_dim(), 0);
    assert!(!endo.quotient_is_commutative());
    assert_eq!(endo.semisimple_factor_count(), 1);
    assert!(!endo.is_local());
}

/// Row 7. `P_0 ⊕ S_1 ⊕ S_1` groups into two isomorphism classes with
/// multiplicities 1 and 2.
#[test]
fn square_krull_schmidt_of_p0_plus_two_s1() {
    let a = square();
    let p0 = Module::projective(&a, 0);
    let s1_first = Module::simple(&a, 1);
    let s1_second = Module::simple(&a, 1);
    let (sum, _, _) = direct_sum(&[&p0, &s1_first, &s1_second]);
    let classes = match krull_schmidt(&sum) {
        KrullSchmidtOutcome::Classes(classes) => classes,
        KrullSchmidtOutcome::Unknown { reason } => panic!("grouping failed: {reason}"),
    };
    let mut found: Vec<(Vec<usize>, usize)> = classes
        .iter()
        .map(|c| (c.representative.dim_vector().to_vec(), c.multiplicity))
        .collect();
    found.sort();
    assert_eq!(found, vec![(vec![0, 1, 0, 0], 2), (vec![1, 1, 1, 1], 1)]);
}

/// Row 7. The regular module `A = ⊕_v P_v` decomposes into the four
/// pairwise non-isomorphic projectives, every summand certified.
#[test]
fn square_regular_module_decomposes_into_the_four_projectives() {
    let a = square();
    let projectives: Vec<Module> = (0..4).map(|v| Module::projective(&a, v)).collect();
    let refs: Vec<&Module> = projectives.iter().collect();
    let (regular, _, _) = direct_sum(&refs);
    let d = decompose(&regular);
    assert_eq!(d.summands().len(), 4);
    assert!(
        d.certificates()
            .iter()
            .all(|c| *c == Certificate::Indecomposable)
    );
    let mut found = dim_vecs(d.summands());
    found.sort();
    let mut expected: Vec<Vec<usize>> = SQUARE_CARTAN.iter().map(|row| row.to_vec()).collect();
    expected.sort();
    assert_eq!(found, expected);
    let classes = match krull_schmidt(&regular) {
        KrullSchmidtOutcome::Classes(classes) => classes,
        KrullSchmidtOutcome::Unknown { reason } => panic!("grouping failed: {reason}"),
    };
    assert_eq!(classes.len(), 4);
    assert!(classes.iter().all(|c| c.multiplicity == 1));
}

/// Row 8. Two separate constructions of `P_0` are isomorphic, and so is the
/// double dual of `P_0`.
#[test]
fn square_is_isomorphic_accepts_p0_copies_and_the_double_dual() {
    let a = square();
    let p0 = Module::projective(&a, 0);
    let p0_again = Module::projective(&a, 0);
    assert!(matches!(
        is_isomorphic(&p0, &p0_again).unwrap(),
        IsoOutcome::Isomorphic(_)
    ));
    let op = opposite(&a).unwrap();
    let dd = dual(&dual(&p0, &op).unwrap(), &op).unwrap();
    assert!(matches!(
        is_isomorphic(&p0, &dd).unwrap(),
        IsoOutcome::Isomorphic(_)
    ));
}

/// Row 8. `S_0` and `S_1` differ already in the dimension vector, and the
/// obstruction is typed.
#[test]
fn square_is_isomorphic_rejects_s0_vs_s1_with_a_dimension_obstruction() {
    let a = square();
    let s0 = Module::simple(&a, 0);
    let s1 = Module::simple(&a, 1);
    match is_isomorphic(&s0, &s1).unwrap() {
        IsoOutcome::NotIsomorphic(Obstruction::DimensionVector { source, target }) => {
            assert_eq!(source, vec![1, 0, 0, 0]);
            assert_eq!(target, vec![0, 1, 0, 0]);
        }
        other => panic!("expected a dimension-vector obstruction, got {other:?}"),
    }
}

/// Row 8. `P_1` and `S_1 ⊕ S_3` share the dimension vector `[0, 1, 0, 1]`
/// but not the radical series: `rad P_1 = S_3` is nonzero while the sum is
/// semisimple.
#[test]
fn square_equal_dimension_vector_pair_p1_vs_s1_plus_s3_is_not_isomorphic() {
    let a = square();
    let p1 = Module::projective(&a, 1);
    let s1 = Module::simple(&a, 1);
    let s3 = Module::simple(&a, 3);
    let (sum, _, _) = direct_sum(&[&s1, &s3]);
    assert_eq!(p1.dim_vector(), sum.dim_vector());
    match is_isomorphic(&p1, &sum).unwrap() {
        IsoOutcome::NotIsomorphic(Obstruction::LoewySeries { source, target }) => {
            assert_eq!(source, vec![vec![0, 0, 0, 1]]);
            assert_eq!(target, Vec::<Vec<usize>>::new());
        }
        other => panic!("expected a Loewy-series obstruction, got {other:?}"),
    }
}

/// Row 9. Hand derivation of `τS_0` over A via the AR formula: the minimal
/// presentation is `P_1 ⊕ P_2 → P_0`, and `ν` turns it into
/// `I_1 ⊕ I_2 → I_0`. `Hom(S_0, A) = 0` because every `soc P_v = S_3`, so
/// `νS_0 = 0`, the map is surjective, and
/// `τS_0 = [2, 1, 1, 0] - [1, 0, 0, 0] = [1, 1, 1, 0]`. The other values
/// are the oracle's `tau` entries. `tau` itself cross-checks the Nakayama
/// kernel against the transpose dual, so `Ok` certifies both routes.
#[test]
fn square_tau_of_simples_matches_the_hand_and_oracle_values() {
    let a = square();
    let expected: [&[usize]; 3] = [&[1, 1, 1, 0], &[0, 0, 1, 1], &[0, 1, 0, 1]];
    for (v, dims) in expected.iter().enumerate() {
        match tau(&Module::simple(&a, v as u32)).unwrap() {
            Tau::Module(t) => assert_eq!(t.dim_vector(), *dims, "τS_{v}"),
            Tau::Zero => panic!("S_{v} is not projective"),
        }
    }
    assert!(matches!(tau(&Module::simple(&a, 3)).unwrap(), Tau::Zero));
}

/// Row 9. Over the self-injective B no simple is projective; the dimension
/// vectors are the oracle's `tau` entries.
#[test]
fn preprojective_tau_of_simples_matches_the_oracle() {
    let b = preprojective_a3();
    let expected: [&[usize]; 3] = [&[0, 1, 1], &[1, 1, 1], &[1, 1, 0]];
    for (v, dims) in expected.iter().enumerate() {
        match tau(&Module::simple(&b, v as u32)).unwrap() {
            Tau::Module(t) => assert_eq!(t.dim_vector(), *dims, "τS_{v}"),
            Tau::Zero => panic!("S_{v} is not projective over a self-injective algebra"),
        }
    }
}

/// Row 10. The v0.2 enumerator counts still hold, and the Dynkin enumerator
/// rejects a nonzero ideal with the typed error.
#[test]
fn enumerators_keep_v02_counts_and_reject_the_square() {
    let nakayama = linear_nakayama(&[3, 2, 1], f5()).unwrap();
    let modules = nakayama_indecomposables(&nakayama).unwrap();
    assert_eq!(modules.len(), 6);
    assert!(
        modules
            .iter()
            .all(|(_, c)| *c == Certificate::Indecomposable)
    );
    let a3 = linear_an(3, f5());
    let modules = dynkin_indecomposables(&a3).unwrap();
    assert_eq!(modules.len(), 6);
    assert!(
        modules
            .iter()
            .all(|(_, c)| *c == Certificate::Indecomposable)
    );
    match dynkin_indecomposables(&square()) {
        Err(DynkinError::NonzeroIdeal { relations }) => assert_eq!(relations, 1),
        other => panic!("expected NonzeroIdeal, got {other:?}"),
    }
}

/// Row 11. Over `kA_2` the sequence `0 → S_1 → P_0 → S_0 → 0` does not
/// split. `Ext¹(S_0, S_1) = 1`, and the middle term `P_0` is not isomorphic
/// to `S_0 ⊕ S_1`. That second fact is the witness the public API certifies.
#[test]
fn ka2_nonsplit_extension_witnessed_by_the_middle_term() {
    let a2 = linear_an(2, f5());
    let s0 = Module::simple(&a2, 0);
    let s1 = Module::simple(&a2, 1);
    assert_eq!(ext_dim(&s0, &s1, 1).unwrap(), 1);
    let p0 = Module::projective(&a2, 0);
    let (split_sum, _, _) = direct_sum(&[&s0, &s1]);
    assert_eq!(p0.dim_vector(), split_sum.dim_vector());
    assert!(matches!(
        is_isomorphic(&p0, &split_sum).unwrap(),
        IsoOutcome::NotIsomorphic(_)
    ));
}

/// Row 11 over A. `Ext¹(S_0, S_1) = 1`; the extension is realized by the
/// module `M = [1, 1, 0, 0]` with `a` acting as the identity (the relation
/// holds because `b` and `d` act on zero spaces). `M` is not isomorphic to
/// `S_0 ⊕ S_1` because `rad M ≠ 0`.
#[test]
fn square_nonsplit_extension_of_s0_by_s1() {
    let a = square();
    let s0 = Module::simple(&a, 0);
    let s1 = Module::simple(&a, 1);
    assert_eq!(ext_dim(&s0, &s1, 1).unwrap(), 1);
    let one = f5().one();
    let middle = Module::new(
        a.clone(),
        vec![1, 1, 0, 0],
        vec![
            DenseMat::from_rows(&[vec![one]]),
            DenseMat::zero(1, 0),
            DenseMat::zero(1, 0),
            DenseMat::zero(0, 0),
        ],
    )
    .unwrap();
    let (split_sum, _, _) = direct_sum(&[&s0, &s1]);
    assert_eq!(middle.dim_vector(), split_sum.dim_vector());
    assert!(matches!(
        is_isomorphic(&middle, &split_sum).unwrap(),
        IsoOutcome::NotIsomorphic(_)
    ));
}

/// Row 12. Dump the certificate, verify the bytes independently, rebuild
/// the algebra from the verified token, and compare the invariants.
#[test]
fn square_certificate_dump_verify_rebuild_round_trip() {
    let a = square();
    let bytes = a.certificate().to_canonical_json();
    let verified = verify(&bytes).unwrap();
    let rebuilt = Algebra::from_verified(verified);
    assert_eq!(rebuilt.dim(), a.dim());
    assert_eq!(rebuilt.basis(), a.basis());
    assert_eq!(rebuilt.cartan_matrix(), a.cartan_matrix());
    assert_eq!(rebuilt.certificate().to_canonical_json(), bytes);
}

/// Row 13. A tight step budget on B's presentation surfaces
/// `Truncated` with diagnostics instead of a silent partial answer.
#[test]
fn preprojective_with_tight_limits_is_truncated_with_diagnostics() {
    let field = f2();
    let quiver = Quiver::new(3, &[(0, 1), (1, 2), (1, 0), (2, 1)]).unwrap();
    let relations = vec![
        Relation::new(&quiver, field, vec![(field.one(), ids(&[0, 2]))]).unwrap(),
        Relation::new(
            &quiver,
            field,
            vec![(field.one(), ids(&[2, 0])), (field.elem(-1), ids(&[1, 3]))],
        )
        .unwrap(),
        Relation::new(&quiver, field, vec![(field.one(), ids(&[3, 1]))]).unwrap(),
    ];
    let presentation = Presentation::new(quiver, field, relations).unwrap();
    let limits = CompletionLimits {
        max_basis: 4096,
        max_word_len: 64,
        max_steps: 5,
    };
    match Algebra::new(presentation.clone(), &limits) {
        Err(AlgebraBuildError::Truncated(diagnostics)) => {
            assert_eq!(diagnostics.reason, TruncationReason::StepBudget);
            assert!(diagnostics.steps_used <= 5);
        }
        other => panic!("expected Truncated, got {other:?}"),
    }
    let limits = CompletionLimits {
        max_basis: 1,
        max_word_len: 64,
        max_steps: 1_000_000,
    };
    match Algebra::new(presentation, &limits) {
        Err(AlgebraBuildError::Truncated(diagnostics)) => {
            assert_eq!(diagnostics.reason, TruncationReason::BasisBudget);
        }
        other => panic!("expected Truncated, got {other:?}"),
    }
}

/// Row 13. The free loop has infinitely many normal words. The error
/// carries the completed certificate plus a cycle witness, and re-verifying
/// the certificate bytes reproduces the same proof.
#[test]
fn free_loop_presentation_is_infinite_dimensional_with_a_witness() {
    let field = f5();
    let quiver = Quiver::new(1, &[(0, 0)]).unwrap();
    let presentation = Presentation::new(quiver, field, Vec::new()).unwrap();
    match Algebra::new(presentation, &CompletionLimits::default()) {
        Err(AlgebraBuildError::InfiniteDimensional {
            certificate,
            witness,
        }) => {
            assert!(!witness.cycle.is_empty(), "the witness names a cycle");
            assert_eq!(
                certificate.finiteness,
                FinitenessData::Infinite {
                    prefix: witness.prefix.clone(),
                    cycle: witness.cycle.clone(),
                },
                "the error's witness is the certificate's finiteness witness"
            );
            match verify(&certificate.to_canonical_json()) {
                Err(VerifyError::InfiniteDimensional { witness: again }) => {
                    assert_eq!(again, witness);
                }
                other => panic!("expected InfiniteDimensional from verify, got {other:?}"),
            }
        }
        other => panic!("expected InfiniteDimensional, got {other:?}"),
    }
}

/// Row 13. Rejected relation input keeps its typed errors: mixed targets,
/// a length-1 word, a coefficient made for another field.
#[test]
fn relation_errors_are_typed() {
    let quiver = inhomogeneous_quiver();
    let field = f5();
    assert_eq!(
        Relation::new(
            &quiver,
            field,
            vec![(field.one(), ids(&[0, 1])), (field.one(), ids(&[2, 3]))],
        ),
        Err(RelationError::MixedTarget { index: 1 })
    );
    assert_eq!(
        Relation::new(&quiver, field, vec![(field.one(), ids(&[0]))]),
        Err(RelationError::WordTooShort { index: 0, len: 1 })
    );
    let foreign = PrimeField::new(7).unwrap().elem(6);
    assert_eq!(
        Relation::new(&quiver, field, vec![(foreign, ids(&[0, 1]))]),
        Err(RelationError::NonCanonicalCoefficient { index: 0 })
    );
}

/// Row 13. A representation with `M(a)M(b) ≠ M(c)M(d)` is a `kQ`-
/// representation but not a module over A, and construction says which
/// relation acts nonzero.
#[test]
fn square_module_validation_rejects_a_relation_violation() {
    let a = square();
    let one = f5().one();
    let zero = f5().zero();
    let result = Module::new(
        a.clone(),
        vec![1, 1, 1, 1],
        vec![
            DenseMat::from_rows(&[vec![one]]),
            DenseMat::from_rows(&[vec![one]]),
            DenseMat::from_rows(&[vec![one]]),
            DenseMat::from_rows(&[vec![zero]]),
        ],
    );
    assert_eq!(
        result.unwrap_err(),
        ModuleError::RelationActsNonzero { index: 0 }
    );
}

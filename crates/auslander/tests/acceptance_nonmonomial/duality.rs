use std::sync::Arc;

use auslander::hom::kernel;
use auslander::iso::{IsoOutcome, is_isomorphic};
use auslander::module::Module;
use auslander::opposite::{dual, nu_of_presentation_map, opposite};
use auslander::radical::radical;
use auslander::resolution::minimal_presentation_matrix;

use super::common::preprojective_a3;
use super::fixtures::square;

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

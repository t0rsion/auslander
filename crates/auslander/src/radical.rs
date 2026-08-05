//! Radical, top, socle, and Loewy series of right modules.
//!
//! In the row-vector convention (see [`crate::module`]):
//! `rad(M)_v = M·J at v` is the sum over arrows `a: u → v` of the row spaces of
//! `M(a)`. The images of the row actions `x ↦ x M(a)` land at the arrow's target.
//! `soc(M)_v = {x ∈ M_v : x M(a) = 0 for every arrow a with source v}`, because
//! every nontrivial path begins with an arrow leaving its source vertex.

use crate::field::Fp;
use crate::hom::{Morphism, quotient_with_projection, submodule_with_inclusion};
use crate::linalg::DenseMat;
use crate::module::Module;
use crate::quiver::PathWord;

/// Rows stacked into a matrix with an explicit column count (so zero rows keep the
/// right width).
fn stacked(rows: &[Vec<Fp>], cols: usize) -> DenseMat {
    let mut out = DenseMat::zero(rows.len(), cols);
    for (r, row) in rows.iter().enumerate() {
        for (c, &v) in row.iter().enumerate() {
            out.set(r, c, v);
        }
    }
    out
}

fn radical_bases(m: &Module) -> Vec<DenseMat> {
    let field = m.field();
    let quiver = m.algebra().quiver();
    (0..quiver.num_vertices())
        .map(|v| {
            let mut rows: Vec<Vec<Fp>> = Vec::new();
            for &a in quiver.arrows_to(v) {
                let map = m.map(a);
                for r in 0..map.rows() {
                    rows.push(map.row(r).to_vec());
                }
            }
            stacked(&rows, m.dim_at(v)).row_space_basis(&field)
        })
        .collect()
}

/// At each vertex, a row basis of the joint kernel of the actions of all standard
/// paths of length exactly `k` leaving that vertex. For `k ≥ 1` this is
/// `{x : x J^k = 0}`: a path word with a forbidden factor acts as zero on a valid
/// module, so the standard paths span the image of `J^k`.
fn joint_kernel_bases(m: &Module, k: usize) -> Vec<DenseMat> {
    let field = m.field();
    let quiver = m.algebra().quiver();
    (0..quiver.num_vertices())
        .map(|v| {
            let mut rows: Vec<Vec<Fp>> = Vec::new();
            for path in m.algebra().basis() {
                if path.len() != k || path.source() != v {
                    continue;
                }
                // x · A = 0 iff x is orthogonal to every column of A.
                let columns = m
                    .word_action(path)
                    .expect("algebra basis words are valid in their own quiver")
                    .transpose();
                for r in 0..columns.rows() {
                    rows.push(columns.row(r).to_vec());
                }
            }
            stacked(&rows, m.dim_at(v)).kernel_basis(&field)
        })
        .collect()
}

/// `rad M = M·J` as a submodule with its inclusion.
pub fn radical(m: &Module) -> (Module, Morphism) {
    submodule_with_inclusion(m, radical_bases(m))
}

/// `top M = M / rad M` with its projection.
pub fn top(m: &Module) -> (Module, Morphism) {
    quotient_with_projection(m, &radical_bases(m))
}

/// `soc M`, the largest submodule killed by `J`, with its inclusion.
pub fn socle(m: &Module) -> (Module, Morphism) {
    submodule_with_inclusion(m, joint_kernel_bases(m, 1))
}

/// The descending chain `M ⊇ rad M ⊇ rad² M ⊇ …`, ending with the zero module.
pub fn radical_series(m: &Module) -> Vec<Module> {
    let mut series = vec![m.clone()];
    while !series.last().expect("series is nonempty").is_zero() {
        let (rad, _) = radical(series.last().expect("series is nonempty"));
        series.push(rad);
    }
    series
}

/// The ascending chain `0 = soc⁰ M ⊆ soc M ⊆ soc² M ⊆ …`, ending with `M` itself
/// (each entry as an abstract module, not embedded in `m`).
pub fn socle_series(m: &Module) -> Vec<Module> {
    // soc^k M = {x : x J^k = 0}. Once k exceeds the longest standard path, J^k = 0
    // and the condition is vacuous, so the loop reaches M.
    let max_len = m
        .algebra()
        .basis()
        .iter()
        .map(PathWord::len)
        .max()
        .unwrap_or(0);
    let mut series = Vec::new();
    for k in 0..=max_len + 1 {
        let (sub, _) = submodule_with_inclusion(m, joint_kernel_bases(m, k));
        let reached_m = sub.dim_vector() == m.dim_vector();
        series.push(sub);
        if reached_m {
            break;
        }
    }
    series
}

/// The Loewy length: the least `l` with `rad^l M = 0` (0 for the zero module).
pub fn loewy_length(m: &Module) -> usize {
    radical_series(m).len() - 1
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{an_with_relations, dual_numbers, linear_an};
    use crate::field::PrimeField;
    use crate::hom::cokernel;

    fn f5() -> PrimeField {
        PrimeField::new(5).unwrap()
    }

    #[test]
    fn radical_series_of_p0_over_a3_descends_3_2_1_0() {
        let algebra = linear_an(3);
        let p0 = Module::projective(&algebra, f5(), 0);
        let series = radical_series(&p0);
        let totals: Vec<usize> = series.iter().map(Module::total_dim).collect();
        assert_eq!(totals, vec![3, 2, 1, 0]);
        assert_eq!(series[1].dim_vector(), &[0, 1, 1]);
        assert_eq!(series[2].dim_vector(), &[0, 0, 1]);
        assert_eq!(loewy_length(&p0), 3);
    }

    #[test]
    fn dual_numbers_regular_module_has_loewy_length_2() {
        let algebra = dual_numbers();
        let regular = Module::projective(&algebra, f5(), 0);
        assert_eq!(loewy_length(&regular), 2);
        let (rad, _) = radical(&regular);
        assert_eq!(rad.dim_vector(), &[1]);
    }

    #[test]
    fn top_of_a_projective_is_the_simple_at_its_vertex() {
        let field = f5();
        for algebra in [linear_an(3), an_with_relations(3, &[(0, 2)]).unwrap()] {
            for v in 0..algebra.quiver().num_vertices() {
                let p = Module::projective(&algebra, field, v);
                let (t, projection) = top(&p);
                let simple = Module::simple(&algebra, field, v);
                assert_eq!(t.dim_vector(), simple.dim_vector(), "top P_{v}");
                assert!(!projection.is_zero());
            }
        }
    }

    #[test]
    fn socle_of_an_injective_is_the_simple_at_its_vertex() {
        let field = f5();
        for algebra in [linear_an(3), an_with_relations(3, &[(0, 2)]).unwrap()] {
            for v in 0..algebra.quiver().num_vertices() {
                let i = Module::injective(&algebra, field, v);
                let (s, inclusion) = socle(&i);
                let simple = Module::simple(&algebra, field, v);
                assert_eq!(s.dim_vector(), simple.dim_vector(), "soc I_{v}");
                assert!(!inclusion.is_zero());
            }
        }
    }

    #[test]
    fn socle_of_p0_over_a3_is_s2() {
        let algebra = linear_an(3);
        let p0 = Module::projective(&algebra, f5(), 0);
        let (s, _) = socle(&p0);
        assert_eq!(s.dim_vector(), &[0, 0, 1]);
    }

    #[test]
    fn radical_of_a_simple_is_zero() {
        let algebra = an_with_relations(3, &[(0, 2)]).unwrap();
        let s1 = Module::simple(&algebra, f5(), 1);
        let (rad, _) = radical(&s1);
        assert!(rad.is_zero());
        assert_eq!(loewy_length(&s1), 1);
    }

    #[test]
    fn cokernel_of_the_radical_inclusion_is_the_top() {
        let algebra = linear_an(3);
        let field = f5();
        let p0 = Module::projective(&algebra, field, 0);
        let (rad, inclusion) = radical(&p0);
        assert!(rad.ptr_eq(inclusion.source()));
        assert!(p0.ptr_eq(inclusion.target()));
        let (coker, _) = cokernel(&inclusion);
        let (t, _) = top(&p0);
        assert_eq!(coker.dim_vector(), t.dim_vector());
        assert_eq!(coker.dim_vector(), &[1, 0, 0]);
    }

    #[test]
    fn socle_series_ascends_from_zero_to_the_module() {
        let field = f5();
        for algebra in [
            linear_an(3),
            an_with_relations(3, &[(0, 2)]).unwrap(),
            dual_numbers(),
        ] {
            for v in 0..algebra.quiver().num_vertices() {
                let p = Module::projective(&algebra, field, v);
                let series = socle_series(&p);
                assert!(series.first().expect("nonempty").is_zero());
                assert_eq!(
                    series.last().expect("nonempty").dim_vector(),
                    p.dim_vector()
                );
                assert_eq!(series.len(), radical_series(&p).len(), "P_{v}");
                for pair in series.windows(2) {
                    assert!(pair[0].total_dim() < pair[1].total_dim());
                }
            }
        }
    }

    #[test]
    fn loewy_length_of_the_zero_module_is_zero() {
        let algebra = linear_an(3);
        let z = Module::zero(&algebra, f5());
        assert_eq!(loewy_length(&z), 0);
        assert_eq!(socle_series(&z).len(), 1);
    }
}

//! Radical, top, socle, and Loewy series of right modules.
//!
//! The formulas come out of the row-vector convention (see [`crate::module`]).
//! The part of `rad M = M·J` at `v` is the sum over arrows `a: u → v` of the row
//! spaces of `M(a)`, because the row action `x ↦ x M(a)` lands at the arrow's
//! target. The part of `soc M` at `v` is
//! `{x ∈ M_v : x M(a) = 0 for every arrow a out of v}`, because every nontrivial
//! path starts with an arrow leaving its source vertex.

use crate::field::Fp;
use crate::hom::{Morphism, quotient_with_projection, submodule_with_inclusion};
use crate::linalg::DenseMat;
use crate::module::Module;

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
            stacked(&rows, m.dim_at(v)).into_row_space_basis(&field)
        })
        .collect()
}

/// At each vertex `v`, a row basis of `{x ∈ M_v : x J^k = 0}`.
///
/// A spanning set of `e_v J^k` comes from
/// [`crate::algebra::Algebra::radical_power_matrix`] over every target vertex,
/// one spanning row per matrix row, each acting through
/// [`Module::element_action`]. Word length decides nothing: `J^k` is not the
/// span of the normal words of length `k` or more, because an inhomogeneous
/// relation can put a short normal word in a deep radical power.
fn joint_kernel_bases(m: &Module, k: usize) -> Vec<DenseMat> {
    let field = m.field();
    let algebra = m.algebra();
    let quiver = algebra.quiver();
    (0..quiver.num_vertices())
        .map(|v| {
            let mut rows: Vec<Vec<Fp>> = Vec::new();
            for w in 0..quiver.num_vertices() {
                let component = algebra.paths_between(v, w);
                let power = algebra.radical_power_matrix(v, w, k);
                for r in 0..power.rows() {
                    let terms: Vec<(usize, Fp)> = power
                        .row(r)
                        .iter()
                        .enumerate()
                        .filter(|(_, c)| !c.is_zero())
                        .map(|(pos, &c)| (component[pos], c))
                        .collect();
                    if terms.is_empty() {
                        continue;
                    }
                    // x · A = 0 iff x is orthogonal to every column of A.
                    let columns = m.element_action(&terms).transpose();
                    for i in 0..columns.rows() {
                        rows.push(columns.row(i).to_vec());
                    }
                }
            }
            stacked(&rows, m.dim_at(v)).into_kernel_basis(&field)
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
    // soc^k M = {x : x J^k = 0}. At k = nilpotency_degree, J^k = 0 and the
    // condition is vacuous, so the loop reaches M.
    let degree = m.algebra().nilpotency_degree();
    let mut series = Vec::new();
    for k in 0..=degree {
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
        let algebra = linear_an(3, f5());
        let p0 = Module::projective(&algebra, 0);
        let series = radical_series(&p0);
        let totals: Vec<usize> = series.iter().map(Module::total_dim).collect();
        assert_eq!(totals, vec![3, 2, 1, 0]);
        assert_eq!(series[1].dim_vector(), &[0, 1, 1]);
        assert_eq!(series[2].dim_vector(), &[0, 0, 1]);
        assert_eq!(loewy_length(&p0), 3);
    }

    #[test]
    fn dual_numbers_regular_module_has_loewy_length_2() {
        let algebra = dual_numbers(f5());
        let regular = Module::projective(&algebra, 0);
        assert_eq!(loewy_length(&regular), 2);
        let (rad, _) = radical(&regular);
        assert_eq!(rad.dim_vector(), &[1]);
    }

    #[test]
    fn top_of_a_projective_is_the_simple_at_its_vertex() {
        let field = f5();
        for algebra in [
            linear_an(3, field),
            an_with_relations(3, &[(0, 2)], field).unwrap(),
        ] {
            for v in 0..algebra.quiver().num_vertices() {
                let p = Module::projective(&algebra, v);
                let (t, projection) = top(&p);
                let simple = Module::simple(&algebra, v);
                assert_eq!(t.dim_vector(), simple.dim_vector(), "top P_{v}");
                assert!(!projection.is_zero());
            }
        }
    }

    #[test]
    fn socle_of_an_injective_is_the_simple_at_its_vertex() {
        let field = f5();
        for algebra in [
            linear_an(3, field),
            an_with_relations(3, &[(0, 2)], field).unwrap(),
        ] {
            for v in 0..algebra.quiver().num_vertices() {
                let i = Module::injective(&algebra, v);
                let (s, inclusion) = socle(&i);
                let simple = Module::simple(&algebra, v);
                assert_eq!(s.dim_vector(), simple.dim_vector(), "soc I_{v}");
                assert!(!inclusion.is_zero());
            }
        }
    }

    #[test]
    fn socle_of_p0_over_a3_is_s2() {
        let algebra = linear_an(3, f5());
        let p0 = Module::projective(&algebra, 0);
        let (s, _) = socle(&p0);
        assert_eq!(s.dim_vector(), &[0, 0, 1]);
    }

    #[test]
    fn radical_of_a_simple_is_zero() {
        let algebra = an_with_relations(3, &[(0, 2)], f5()).unwrap();
        let s1 = Module::simple(&algebra, 1);
        let (rad, _) = radical(&s1);
        assert!(rad.is_zero());
        assert_eq!(loewy_length(&s1), 1);
    }

    #[test]
    fn cokernel_of_the_radical_inclusion_is_the_top() {
        let algebra = linear_an(3, f5());
        let p0 = Module::projective(&algebra, 0);
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
            linear_an(3, field),
            an_with_relations(3, &[(0, 2)], field).unwrap(),
            dual_numbers(field),
        ] {
            for v in 0..algebra.quiver().num_vertices() {
                let p = Module::projective(&algebra, v);
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
        let algebra = linear_an(3, f5());
        let z = Module::zero(&algebra);
        assert_eq!(loewy_length(&z), 0);
        assert_eq!(socle_series(&z).len(), 1);
    }
}

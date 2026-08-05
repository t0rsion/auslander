//! AR-translate and Nakayama-enumeration coverage over F_2 and F_5: τ against
//! hand-derived values, projectivity both directions, route agreement, the
//! Coxeter transformation on hereditary fixtures, and τ as a permutation of
//! the enumerated non-projective Nakayama indecomposables.
//!
//! Hand derivations reused from tests/duality.rs: over a Nakayama algebra τ of
//! a non-projective uniserial of length `l` with top `S_i` is the uniserial of
//! length `l` with top `S_{i+1}`. Over the Kronecker algebra τ S_0 = (3, 2).

use std::sync::Arc;

use auslander::algebra::{
    MonomialAlgebra, an_with_relations, cyclic_nakayama, dual_numbers, kronecker, linear_an,
    linear_nakayama, radical_square_zero_cycle, truncated_poly,
};
use auslander::ar::{Tau, tau, tau_via_nakayama_kernel, tau_via_transpose_dual};
use auslander::decompose::{Certificate, KrullSchmidtOutcome, decompose, krull_schmidt};
use auslander::enumerate::nakayama_indecomposables;
use auslander::field::PrimeField;
use auslander::iso::{IsoOutcome, is_isomorphic};
use auslander::module::{Module, direct_sum};
use auslander::quiver::Quiver;
use auslander::resolution::minimal_presentation_matrix;

fn fields() -> [PrimeField; 2] {
    [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()]
}

/// `D_4` with the three arrows leaving the central vertex 0. It is hereditary, and
/// the vertex order is topological, so the Cartan matrix is upper unitriangular.
fn d4() -> Arc<MonomialAlgebra> {
    let quiver = Quiver::new(4, &[(0, 1), (0, 2), (0, 3)]).unwrap();
    MonomialAlgebra::new(quiver, Vec::new()).unwrap()
}

fn fixtures() -> Vec<Arc<MonomialAlgebra>> {
    vec![
        linear_an(4),
        an_with_relations(3, &[(0, 2)]).unwrap(),
        kronecker(2),
        dual_numbers(),
        truncated_poly(3).unwrap(),
        linear_nakayama(&[3, 2, 1]).unwrap(),
        cyclic_nakayama(&[3, 3, 3]).unwrap(),
        radical_square_zero_cycle(3),
        d4(),
    ]
}

fn isomorphic(m: &Module, n: &Module) -> bool {
    matches!(is_isomorphic(m, n).unwrap(), IsoOutcome::Isomorphic(_))
}

fn tau_module(m: &Module) -> Module {
    match tau(m).unwrap() {
        Tau::Module(t) => t,
        Tau::Zero => panic!("expected a non-projective module, dim {:?}", m.dim_vector()),
    }
}

/// Whether the indecomposable `m` is projective, decided independently of τ:
/// isomorphic to some `P_v`.
fn is_projective_indecomposable(m: &Module) -> bool {
    (0..m.algebra().quiver().num_vertices())
        .any(|v| isomorphic(m, &Module::projective(m.algebra(), m.field(), v)))
}

fn indecomposable_samples(algebra: &Arc<MonomialAlgebra>, field: PrimeField) -> Vec<Module> {
    let mut modules = Vec::new();
    for v in 0..algebra.quiver().num_vertices() {
        modules.push(Module::simple(algebra, field, v));
        modules.push(Module::injective(algebra, field, v));
    }
    modules
}

#[test]
fn tau_of_every_indecomposable_projective_is_zero() {
    for algebra in fixtures() {
        for field in fields() {
            for v in 0..algebra.quiver().num_vertices() {
                let p = Module::projective(&algebra, field, v);
                assert!(
                    matches!(tau(&p).unwrap(), Tau::Zero),
                    "τ P_{v} over F_{}",
                    field.modulus()
                );
            }
        }
    }
}

#[test]
fn tau_matches_the_hand_derived_translates_of_duality_tests() {
    for field in fields() {
        let a3 = linear_an(3);
        assert_eq!(
            tau_module(&Module::simple(&a3, field, 0)).dim_vector(),
            &[0, 1, 0]
        );
        assert_eq!(
            tau_module(&Module::simple(&a3, field, 1)).dim_vector(),
            &[0, 0, 1]
        );
        let kron = kronecker(2);
        assert_eq!(
            tau_module(&Module::simple(&kron, field, 0)).dim_vector(),
            &[3, 2]
        );
        let dn = dual_numbers();
        assert_eq!(
            tau_module(&Module::simple(&dn, field, 0)).dim_vector(),
            &[1]
        );
        for algebra in [
            radical_square_zero_cycle(3),
            cyclic_nakayama(&[3, 3, 3]).unwrap(),
        ] {
            for i in 0..3u32 {
                let t = tau_module(&Module::simple(&algebra, field, i));
                let next = Module::simple(&algebra, field, (i + 1) % 3);
                assert!(isomorphic(&t, &next), "τ S_{i} over F_{}", field.modulus());
            }
        }
    }
}

#[test]
fn both_routes_are_certified_isomorphic_on_every_sample() {
    for algebra in fixtures() {
        for field in fields() {
            for m in indecomposable_samples(&algebra, field) {
                let left = tau_via_nakayama_kernel(&m);
                let right = tau_via_transpose_dual(&m);
                assert!(
                    isomorphic(&left, &right),
                    "routes disagree on dim {:?} over F_{}",
                    m.dim_vector(),
                    field.modulus()
                );
                assert!(tau(&m).is_ok());
            }
        }
    }
}

/// The Coxeter transformation for this crate's conventions, derived once:
///
/// Right modules, dimension vectors as row vectors, Cartan matrix
/// `C[i][j] = dim e_i A e_j`, so row `i` of `C` is `dim P_i` and row `i` of
/// `Cᵀ` is `dim I_i`. The Nakayama functor sends `P_i` to `I_i`, so on the
/// dimension vector of a projective sum `X` with multiplicity row `m`
/// (`dim X = m·C`) it acts by `dim νX = m·Cᵀ = dim X · C⁻¹Cᵀ`. For hereditary
/// `A` and indecomposable non-projective `M` the presentation is short exact
/// (`0 → P_1 → P_0 → M → 0`, so `dim M = dim P_0 − dim P_1`) and
/// `Hom(M, A) = 0` (a nonzero image in a projective would be a projective
/// quotient, splitting off), hence `νM = 0` and
/// `0 → τM → νP_1 → νP_0 → 0` gives
/// `dim τM = (dim P_1 − dim P_0)·C⁻¹Cᵀ = dim M · Φ` with `Φ = −C⁻¹Cᵀ`.
///
/// All hereditary fixtures here list vertices in topological order, so `C` is
/// upper unitriangular and `C⁻¹` is exact over the integers by back
/// substitution.
fn coxeter_matrix(algebra: &MonomialAlgebra) -> Vec<Vec<i64>> {
    let cartan = algebra.cartan_matrix();
    let n = cartan.len();
    let c: Vec<Vec<i64>> = cartan
        .iter()
        .map(|row| row.iter().map(|&x| x as i64).collect())
        .collect();
    for (i, row) in c.iter().enumerate() {
        assert_eq!(row[i], 1, "Cartan diagonal");
        assert!(row[..i].iter().all(|&x| x == 0), "Cartan not unitriangular");
    }
    let mut inv = vec![vec![0i64; n]; n];
    for i in (0..n).rev() {
        inv[i][i] = 1;
        for k in i + 1..n {
            let factor = c[i][k];
            let row_k = inv[k].clone();
            for (entry, &below) in inv[i].iter_mut().zip(&row_k) {
                *entry -= factor * below;
            }
        }
    }
    let mut phi = vec![vec![0i64; n]; n];
    for i in 0..n {
        for j in 0..n {
            phi[i][j] = -(0..n).map(|k| inv[i][k] * c[j][k]).sum::<i64>();
        }
    }
    phi
}

fn apply_coxeter(phi: &[Vec<i64>], dim: &[usize]) -> Vec<i64> {
    let n = phi.len();
    (0..n)
        .map(|j| (0..n).map(|i| dim[i] as i64 * phi[i][j]).sum())
        .collect()
}

#[test]
fn coxeter_matrices_match_hand_computed_examples() {
    // A_3: C = [[1,1,1],[0,1,1],[0,0,1]], C⁻¹ = [[1,-1,0],[0,1,-1],[0,0,1]],
    // Φ = −C⁻¹Cᵀ = [[0,1,0],[0,0,1],[-1,-1,-1]]; check τ S_0 = S_1 on it.
    let phi = coxeter_matrix(&linear_an(3));
    assert_eq!(phi, vec![vec![0, 1, 0], vec![0, 0, 1], vec![-1, -1, -1]]);
    assert_eq!(apply_coxeter(&phi, &[1, 0, 0]), vec![0, 1, 0]);
    // Kronecker: C = [[1,2],[0,1]], Φ = [[3,2],[-2,-1]]; τ S_0 = (3,2).
    let phi = coxeter_matrix(&kronecker(2));
    assert_eq!(phi, vec![vec![3, 2], vec![-2, -1]]);
    assert_eq!(apply_coxeter(&phi, &[1, 0]), vec![3, 2]);
}

#[test]
fn tau_dimension_vectors_follow_the_coxeter_transformation_on_hereditary_fixtures() {
    for algebra in [linear_an(4), kronecker(2), d4()] {
        let phi = coxeter_matrix(&algebra);
        for field in fields() {
            for m in indecomposable_samples(&algebra, field) {
                if is_projective_indecomposable(&m) {
                    continue;
                }
                let expected = apply_coxeter(&phi, m.dim_vector());
                let got: Vec<i64> = tau_module(&m)
                    .dim_vector()
                    .iter()
                    .map(|&x| x as i64)
                    .collect();
                assert_eq!(
                    got,
                    expected,
                    "Φ·dim for dim {:?} over F_{}",
                    m.dim_vector(),
                    field.modulus()
                );
            }
        }
    }
}

#[test]
fn tau_is_zero_exactly_on_the_projective_samples() {
    for algebra in fixtures() {
        for field in fields() {
            for m in indecomposable_samples(&algebra, field) {
                let projective = is_projective_indecomposable(&m);
                match tau(&m).unwrap() {
                    Tau::Zero => assert!(
                        projective,
                        "τ = 0 on non-projective dim {:?} over F_{}",
                        m.dim_vector(),
                        field.modulus()
                    ),
                    Tau::Module(t) => {
                        assert!(
                            !projective,
                            "τ ≠ 0 on projective dim {:?} over F_{}",
                            m.dim_vector(),
                            field.modulus()
                        );
                        assert!(!t.is_zero());
                    }
                }
            }
        }
    }
}

fn is_injective_indecomposable(m: &Module) -> bool {
    (0..m.algebra().quiver().num_vertices())
        .any(|v| isomorphic(m, &Module::injective(m.algebra(), m.field(), v)))
}

#[test]
fn tau_of_a_nonprojective_indecomposable_is_indecomposable_and_noninjective() {
    for algebra in fixtures() {
        for field in fields() {
            for m in indecomposable_samples(&algebra, field) {
                if is_projective_indecomposable(&m) {
                    continue;
                }
                let t = tau_module(&m);
                let d = decompose(&t);
                assert_eq!(d.summands().len(), 1, "τ of dim {:?}", m.dim_vector());
                assert_eq!(d.certificates(), &[Certificate::Indecomposable]);
                assert!(
                    !is_injective_indecomposable(&t),
                    "τ of dim {:?} is injective over F_{}",
                    m.dim_vector(),
                    field.modulus()
                );
            }
        }
    }
}

/// The oracle's `tau_injectives` rows exercise multi-summand presentations that
/// the simples cannot. This pins that on the Kronecker injective `I_1`
/// (dims (2, 1)): its minimal presentation is `P_1³ → P_0² → I_1`, a multi-entry
/// element matrix on both sides.
#[test]
fn the_kronecker_injective_presentation_has_multiple_projective_summands() {
    for field in fields() {
        let a = kronecker(2);
        let i1 = Module::injective(&a, field, 1);
        assert_eq!(i1.dim_vector(), &[2, 1]);
        let d1 = minimal_presentation_matrix(&i1);
        assert_eq!(d1.targets(), &[0, 0]);
        assert_eq!(d1.sources(), &[1, 1, 1]);
    }
}

/// The enumerated list orders `P_i / rad^l P_i` by vertex `i`, then by length
/// `l = 1, …, c_i`, so index `(i, l)` is `Σ_{j<i} c_j + (l − 1)`.
fn enumerated_index(kupisch: &[usize], i: usize, l: usize) -> usize {
    kupisch[..i].iter().sum::<usize>() + l - 1
}

/// The enumerated modules. Asserts the certificate that the API promises.
fn enumerated(algebra: &Arc<MonomialAlgebra>, field: PrimeField) -> Vec<Module> {
    nakayama_indecomposables(algebra, field)
        .unwrap()
        .into_iter()
        .map(|(m, c)| {
            assert_eq!(c, Certificate::Indecomposable);
            m
        })
        .collect()
}

#[test]
fn tau_cycles_the_nonprojective_uniserials_of_the_cyclic_nakayama_algebra() {
    let kupisch = [3usize, 3, 3];
    let algebra = cyclic_nakayama(&kupisch).unwrap();
    for field in fields() {
        let modules = enumerated(&algebra, field);
        for i in 0..3 {
            for l in 1..=2 {
                let m = &modules[enumerated_index(&kupisch, i, l)];
                let expected = &modules[enumerated_index(&kupisch, (i + 1) % 3, l)];
                let t = tau_module(m);
                assert!(
                    isomorphic(&t, expected),
                    "τ of P_{i}/rad^{l} over F_{}",
                    field.modulus()
                );
            }
        }
    }
}

#[test]
fn tau_shifts_the_nonprojective_uniserials_of_the_linear_nakayama_algebra() {
    let kupisch = [3usize, 2, 1];
    let algebra = linear_nakayama(&kupisch).unwrap();
    for field in fields() {
        let modules = enumerated(&algebra, field);
        // Non-projective uniserials have l < c_i. τ moves the top one step
        // down the quiver and keeps the length: (i, l) ↦ (i + 1, l).
        for (i, l) in [(0usize, 1usize), (0, 2), (1, 1)] {
            let m = &modules[enumerated_index(&kupisch, i, l)];
            let expected = &modules[enumerated_index(&kupisch, i + 1, l)];
            let t = tau_module(m);
            assert!(
                isomorphic(&t, expected),
                "τ of P_{i}/rad^{l} over F_{}",
                field.modulus()
            );
        }
        for (i, l) in [(0usize, 3usize), (1, 2), (2, 1)] {
            let m = &modules[enumerated_index(&kupisch, i, l)];
            assert!(matches!(tau(m).unwrap(), Tau::Zero), "P_{i}/rad^{l}");
        }
    }
}

#[test]
fn every_enumerated_nakayama_module_is_certified_indecomposable() {
    for (algebra, kupisch) in [
        (linear_nakayama(&[3, 2, 1]).unwrap(), vec![3usize, 2, 1]),
        (cyclic_nakayama(&[3, 3, 3]).unwrap(), vec![3, 3, 3]),
        (radical_square_zero_cycle(3), vec![2, 2, 2]),
        (truncated_poly(3).unwrap(), vec![3]),
    ] {
        for field in fields() {
            let modules = enumerated(&algebra, field);
            assert_eq!(modules.len(), kupisch.iter().sum::<usize>());
            for m in &modules {
                let d = decompose(m);
                assert_eq!(d.summands().len(), 1, "dim {:?}", m.dim_vector());
                assert_eq!(d.certificates(), &[Certificate::Indecomposable]);
            }
        }
    }
}

#[test]
fn krull_schmidt_of_structured_sums_lands_in_the_enumerated_list() {
    for algebra in [
        linear_nakayama(&[3, 2, 1]).unwrap(),
        cyclic_nakayama(&[3, 3, 3]).unwrap(),
    ] {
        for field in fields() {
            let modules = enumerated(&algebra, field);
            let p0 = Module::projective(&algebra, field, 0);
            let s1 = Module::simple(&algebra, field, 1);
            let i2 = Module::injective(&algebra, field, 2);
            let sums = [
                direct_sum(&[&p0, &s1, &s1]).0,
                direct_sum(&[&i2, &p0, &modules[1]]).0,
                direct_sum(&[&modules[0], &modules[1], &modules[2], &modules[3]]).0,
            ];
            for (which, sum) in sums.iter().enumerate() {
                let classes = match krull_schmidt(sum) {
                    KrullSchmidtOutcome::Classes(classes) => classes,
                    KrullSchmidtOutcome::Unknown { reason } => panic!("unknown: {reason}"),
                };
                let mut total = 0usize;
                for class in &classes {
                    assert!(
                        modules.iter().any(|m| isomorphic(&class.representative, m)),
                        "sum {which}: class dim {:?} not enumerated over F_{}",
                        class.representative.dim_vector(),
                        field.modulus()
                    );
                    total += class.multiplicity;
                }
                assert_eq!(total, 3 + usize::from(which == 2), "sum {which}");
            }
        }
    }
}

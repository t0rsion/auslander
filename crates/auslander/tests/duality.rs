//! Duality and Nakayama-functor coverage over F_2 and F_5: opposite involution,
//! double duals, contravariance on compositions, ν(P_v) against I_v, and
//! Nakayama kernels against hand-derived AR translates.
//!
//! AR derivations used below (right modules, arrows composed left to right):
//! for a Nakayama algebra, τ of a non-projective uniserial of length `l` with
//! top `S_i` is the uniserial of length `l` with top `S_{i+1}`, from the
//! almost split sequences `0 → rad P → P ⊕ rad P/soc P → P/soc P → 0`. In
//! particular τ S_i = S_{i+1} on the fixtures below. Over the Kronecker
//! algebra `S_0 = I_0` starts the preinjective component `(1,0), (2,1), (3,2),
//! …` and τ moves it one step inward: τ S_0 = (3, 2).

use std::sync::Arc;

use auslander::algebra::{
    Algebra, commutative_square, cyclic_nakayama, dual_numbers, kronecker, linear_an,
    radical_square_zero_cycle,
};
use auslander::field::PrimeField;
use auslander::hom::{cokernel, hom, kernel};
use auslander::linalg::DenseMat;
use auslander::module::{Module, direct_sum};
use auslander::opposite::{ElementMatrix, dual, dual_morphism, nu_of_presentation_map, opposite};
use auslander::quiver::ArrowId;
use auslander::resolution::minimal_presentation_matrix;

fn fields() -> [PrimeField; 2] {
    [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()]
}

fn fixtures(field: PrimeField) -> Vec<Arc<Algebra>> {
    vec![
        linear_an(3, field),
        kronecker(2, field),
        dual_numbers(field),
        cyclic_nakayama(&[3, 3, 3], field).unwrap(),
        radical_square_zero_cycle(3, field),
        commutative_square(field),
    ]
}

fn entrywise_equal(a: &Module, b: &Module) -> bool {
    Arc::ptr_eq(a.algebra(), b.algebra())
        && a.dim_vector() == b.dim_vector()
        && (0..a.algebra().quiver().num_arrows())
            .all(|i| a.map(ArrowId(i as u32)) == b.map(ArrowId(i as u32)))
}

fn assorted(algebra: &Arc<Algebra>) -> Vec<Module> {
    let n = algebra.quiver().num_vertices();
    let mut modules = Vec::new();
    for v in 0..n {
        modules.push(Module::simple(algebra, v));
        modules.push(Module::projective(algebra, v));
        modules.push(Module::injective(algebra, v));
    }
    let refs: Vec<&Module> = modules.iter().take(3).collect();
    modules.push(direct_sum(&refs).0);
    modules
}

#[test]
fn opposite_involution_and_dimension_on_fixtures() {
    for field in fields() {
        for algebra in fixtures(field) {
            let op = opposite(&algebra).unwrap();
            assert_eq!(op.opposite().dim(), algebra.dim());
            let double = opposite(op.opposite()).unwrap();
            assert_eq!(double.opposite().quiver(), algebra.quiver());
            assert_eq!(double.opposite().relations(), algebra.relations());
            assert_eq!(double.opposite().dim(), algebra.dim());
        }
    }
}

#[test]
fn double_dual_restores_every_module_entry_for_entry() {
    for field in fields() {
        for algebra in fixtures(field) {
            let op = opposite(&algebra).unwrap();
            for m in assorted(&algebra) {
                let dd = dual(&dual(&m, &op).unwrap(), &op).unwrap();
                assert!(entrywise_equal(&dd, &m), "dim {:?}", m.dim_vector());
            }
        }
    }
}

#[test]
fn dual_is_contravariant_on_fixture_compositions() {
    for field in fields() {
        for algebra in fixtures(field) {
            let op = opposite(&algebra).unwrap();
            let n = algebra.quiver().num_vertices();
            for v in 0..n {
                let p = Module::projective(&algebra, v);
                let m = Module::injective(&algebra, (v + 1) % n);
                let l = Module::simple(&algebra, v);
                let dp = dual(&p, &op).unwrap();
                let dm = dual(&m, &op).unwrap();
                let dl = dual(&l, &op).unwrap();
                for f in hom(&p, &m).unwrap() {
                    for g in hom(&m, &l).unwrap() {
                        let left = dual_morphism(&f.then(&g).unwrap(), &dl, &dp, &op).unwrap();
                        let right = dual_morphism(&g, &dl, &dm, &op)
                            .unwrap()
                            .then(&dual_morphism(&f, &dm, &dp, &op).unwrap())
                            .unwrap();
                        assert_eq!(left, right, "vertex {v}, F_{}", field.modulus());
                    }
                }
            }
        }
    }
}

fn identity_element_matrix(algebra: &Arc<Algebra>, v: u32) -> ElementMatrix {
    let field = algebra.field();
    let component = algebra.paths_between(v, v);
    let mut coefficients = vec![field.zero(); component.len()];
    let position = component
        .iter()
        .position(|&b| b == algebra.vertex_idempotent(v))
        .expect("the trivial path lies in its own component");
    coefficients[position] = field.one();
    ElementMatrix::new(algebra.clone(), vec![v], vec![v], vec![vec![coefficients]]).unwrap()
}

#[test]
fn nu_of_each_projective_is_the_matching_injective() {
    for field in fields() {
        for algebra in fixtures(field) {
            for v in 0..algebra.quiver().num_vertices() {
                let nu = nu_of_presentation_map(&identity_element_matrix(&algebra, v));
                let injective = Module::injective(&algebra, v);
                assert!(entrywise_equal(nu.source(), &injective), "ν(P_{v}) source");
                assert!(entrywise_equal(nu.target(), &injective), "ν(P_{v}) target");
                for w in 0..algebra.quiver().num_vertices() {
                    assert_eq!(
                        *nu.map_at(w),
                        DenseMat::identity(injective.dim_at(w)),
                        "ν(id) of P_{v} at vertex {w}"
                    );
                }
            }
        }
    }
}

fn tau_dims(m: &Module) -> Vec<usize> {
    let nu = nu_of_presentation_map(&minimal_presentation_matrix(m));
    kernel(&nu).0.dim_vector().to_vec()
}

#[test]
fn nakayama_kernels_recover_hand_derived_ar_translates() {
    for field in fields() {
        let a3 = linear_an(3, field);
        assert_eq!(tau_dims(&Module::simple(&a3, 0)), vec![0, 1, 0]);
        assert_eq!(tau_dims(&Module::simple(&a3, 1)), vec![0, 0, 1]);
        for v in 0..3 {
            assert_eq!(tau_dims(&Module::projective(&a3, v)), vec![0, 0, 0]);
        }
        let kron = kronecker(2, field);
        assert_eq!(tau_dims(&Module::simple(&kron, 0)), vec![3, 2]);
        let dn = dual_numbers(field);
        assert_eq!(tau_dims(&Module::simple(&dn, 0)), vec![1]);
        for algebra in [
            radical_square_zero_cycle(3, field),
            cyclic_nakayama(&[3, 3, 3], field).unwrap(),
        ] {
            for i in 0..3u32 {
                let expected: Vec<usize> =
                    (0..3u32).map(|w| usize::from(w == (i + 1) % 3)).collect();
                assert_eq!(
                    tau_dims(&Module::simple(&algebra, i)),
                    expected,
                    "τ S_{i} over F_{}",
                    field.modulus()
                );
            }
        }
    }
}

#[test]
fn transpose_route_agrees_with_the_nakayama_kernel_route() {
    for field in fields() {
        for algebra in [
            linear_an(3, field),
            dual_numbers(field),
            radical_square_zero_cycle(3, field),
            commutative_square(field),
        ] {
            let op = opposite(&algebra).unwrap();
            for v in 0..algebra.quiver().num_vertices() {
                let s = Module::simple(&algebra, v);
                let matrix = minimal_presentation_matrix(&s);
                let kernel_route = tau_dims(&s);
                let transposed = matrix.transpose_over(&op).unwrap();
                let (tr, _) = cokernel(&transposed.morphism());
                let tau = dual(&tr, &op).unwrap();
                assert_eq!(
                    tau.dim_vector(),
                    kernel_route.as_slice(),
                    "τ S_{v} over F_{}",
                    field.modulus()
                );
            }
        }
    }
}

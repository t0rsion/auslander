use super::{
    HomError, Morphism, cokernel, express_in_row_basis, hom, hom_dim, identity, image, kernel,
    zero_morphism,
};
use crate::algebra::{an_with_relations, dual_numbers, linear_an};
use crate::field::PrimeField;
use crate::linalg::DenseMat;
use crate::module::{Module, direct_sum};
use crate::quiver::ArrowId;

fn f5() -> PrimeField {
    PrimeField::new(5).unwrap()
}

// dim Hom(P_v, M) = dim M_v: Yoneda, Hom(e_v A, M) ≅ M e_v.
#[test]
fn hom_from_projective_has_the_dimension_of_the_module_at_the_vertex() {
    let field = f5();
    for algebra in [
        linear_an(3, field),
        an_with_relations(3, &[(0, 2)], field).unwrap(),
        dual_numbers(field),
    ] {
        let n = algebra.quiver().num_vertices();
        let mut modules: Vec<Module> = Vec::new();
        for v in 0..n {
            modules.push(Module::simple(&algebra, v));
            modules.push(Module::projective(&algebra, v));
            modules.push(Module::injective(&algebra, v));
        }
        let parts: Vec<&Module> = modules.iter().take(3).collect();
        let (sum, _, _) = direct_sum(&parts);
        modules.push(sum);
        for v in 0..n {
            let pv = Module::projective(&algebra, v);
            for m in &modules {
                assert_eq!(
                    hom(&pv, m).unwrap().len(),
                    m.dim_at(v),
                    "hom(P_{v}, M) with dim M = {:?}",
                    m.dim_vector()
                );
            }
        }
    }
}

#[test]
fn hom_between_simples_is_delta() {
    let field = f5();
    let algebra = linear_an(3, field);
    for i in 0..3 {
        for j in 0..3 {
            let si = Module::simple(&algebra, i);
            let sj = Module::simple(&algebra, j);
            assert_eq!(
                hom_dim(&si, &sj).unwrap(),
                usize::from(i == j),
                "hom(S_{i}, S_{j})"
            );
        }
    }
}

// Yoneda gives Hom(P_v, M) ≅ M_v. For linearly oriented A_2 (arrow
// 0 → 1), P_0 = e_0 A has dimension vector (1, 1) and P_1 has (0, 1), so
// Hom(P_0, P_1) ≅ (P_1)_0 = 0 while Hom(P_1, P_0) ≅ (P_0)_1 = k: the nonzero map
// sends e_1 to the path a, so it runs P_1 → P_0, opposite to the left-module
// convention. Hence End(P_0 ⊕ P_1) = End(P_0) ⊕ End(P_1) ⊕ Hom(P_1, P_0) = k³.
#[test]
fn endomorphisms_of_p0_plus_p1_over_a2_have_dimension_3() {
    let field = f5();
    let algebra = linear_an(2, field);
    let p0 = Module::projective(&algebra, 0);
    let p1 = Module::projective(&algebra, 1);
    assert_eq!(hom_dim(&p0, &p1).unwrap(), 0);
    assert_eq!(hom_dim(&p1, &p0).unwrap(), 1);
    let (sum, _, _) = direct_sum(&[&p0, &p1]);
    assert_eq!(hom_dim(&sum, &sum).unwrap(), 3);
}

#[test]
fn hom_rejects_modules_over_different_algebras() {
    let field = f5();
    let a = linear_an(3, field);
    let b = linear_an(3, field);
    let m = Module::simple(&a, 0);
    let n = Module::simple(&b, 0);
    assert_eq!(hom(&m, &n).unwrap_err(), HomError::DifferentAlgebras);
}

#[test]
fn hom_rejects_modules_over_different_fields() {
    // The field lives on the algebra, so modules over different fields
    // always live over different algebra values.
    let a = linear_an(3, f5());
    let b = linear_an(3, PrimeField::new(7).unwrap());
    let m = Module::simple(&a, 0);
    let n = Module::simple(&b, 0);
    assert_eq!(hom(&m, &n).unwrap_err(), HomError::DifferentAlgebras);
}

#[test]
fn then_rejects_mismatched_endpoints() {
    let field = f5();
    let algebra = linear_an(3, field);
    let p0 = Module::projective(&algebra, 0);
    let s0 = Module::simple(&algebra, 0);
    let f = hom(&p0, &s0).unwrap().remove(0);
    let s0_copy = Module::simple(&algebra, 0);
    assert_eq!(
        f.then(&identity(&s0_copy)).unwrap_err(),
        HomError::EndpointMismatch
    );
    assert!(f.then(&identity(&s0)).is_ok());
}

#[test]
fn morphism_equality_requires_pointer_identical_endpoints() {
    let field = f5();
    let algebra = linear_an(3, field);
    let p0 = Module::projective(&algebra, 0);
    let p0_copy = Module::projective(&algebra, 0);
    assert!(!p0.ptr_eq(&p0_copy));
    assert!(p0.ptr_eq(&p0.clone()));
    assert_ne!(identity(&p0), identity(&p0_copy));
    assert_eq!(identity(&p0), identity(&p0.clone()));
}

#[test]
fn morphism_new_rejects_a_non_canonical_entry() {
    let algebra = linear_an(2, PrimeField::new(2).unwrap());
    let p0 = Module::projective(&algebra, 0);
    // The entry 3 comes from F_5; it is not a canonical F_2 representative.
    let bad = DenseMat::from_rows(&[vec![f5().elem(3)]]);
    let maps = vec![bad, DenseMat::identity(1)];
    assert_eq!(
        Morphism::new(&p0, &p0, maps).unwrap_err(),
        HomError::NonCanonicalEntry {
            vertex: 0,
            row: 0,
            col: 0,
        }
    );
}

#[test]
fn morphism_new_rejects_a_noncommuting_square() {
    let field = f5();
    let algebra = linear_an(2, field);
    let p0 = Module::projective(&algebra, 0);
    let p1 = Module::projective(&algebra, 1);
    // The square at arrow 0 needs f_0 · N(a) = M(a) · f_1 = [1], but f_0 is 1x0,
    // so the left side is the 1x1 zero matrix.
    let maps = vec![DenseMat::zero(1, 0), DenseMat::identity(1)];
    assert_eq!(
        Morphism::new(&p0, &p1, maps).unwrap_err(),
        HomError::SquareViolated { arrow: ArrowId(0) }
    );
}

#[test]
fn identity_is_neutral_for_composition() {
    let field = f5();
    let algebra = linear_an(3, field);
    let p0 = Module::projective(&algebra, 0);
    let s0 = Module::simple(&algebra, 0);
    let f = hom(&p0, &s0).unwrap().remove(0);
    assert_eq!(identity(&p0).then(&f).unwrap(), f);
    assert_eq!(f.then(&identity(&s0)).unwrap(), f);
    assert!(zero_morphism(&p0, &s0).unwrap().is_zero());
    assert!(!f.is_zero());
}

#[test]
fn the_nonzero_map_p0_to_i2_over_a3_is_an_isomorphism() {
    // Over linearly oriented A_3 both P_0 and I_2 are the unique uniserial with
    // dimension vector (1, 1, 1), so the one-dimensional Hom is spanned by an iso.
    let field = f5();
    let algebra = linear_an(3, field);
    let p0 = Module::projective(&algebra, 0);
    let i2 = Module::injective(&algebra, 2);
    let basis = hom(&p0, &i2).unwrap();
    assert_eq!(basis.len(), 1);
    assert!(basis[0].is_isomorphism());
    assert!(!zero_morphism(&p0, &p0).unwrap().is_isomorphism());
    assert!(identity(&p0).is_isomorphism());
}

#[test]
fn apply_maps_row_vectors_through_the_vertex_matrices() {
    let field = f5();
    let algebra = linear_an(2, field);
    let p0 = Module::projective(&algebra, 0);
    let p1 = Module::projective(&algebra, 1);
    let f = hom(&p1, &p0).unwrap().remove(0);
    let element = vec![vec![], vec![field.elem(2)]];
    let image = f.apply(&element);
    assert_eq!(image[0], vec![field.zero()]);
    let expected = field.mul(field.elem(2), f.map_at(1).get(0, 0));
    assert_eq!(image[1], vec![expected]);
}

#[test]
fn kernel_image_cokernel_satisfy_rank_nullity_and_compose_correctly() {
    let field = f5();
    let cases: Vec<(Module, Module)> = {
        let a3 = linear_an(3, field);
        let dn = dual_numbers(field);
        let p0 = Module::projective(&a3, 0);
        let p1 = Module::projective(&a3, 1);
        let s0 = Module::simple(&a3, 0);
        let i2 = Module::injective(&a3, 2);
        let (sum, _, _) = direct_sum(&[&p0, &p1]);
        let dp = Module::projective(&dn, 0);
        vec![
            (p0.clone(), s0),
            (p0.clone(), i2),
            (sum, p0),
            (dp.clone(), dp),
        ]
    };
    for (m, n) in &cases {
        for f in hom(m, n).unwrap() {
            let (ker, ker_incl) = kernel(&f);
            let (im, im_incl) = image(&f);
            let (coker, coker_proj) = cokernel(&f);
            for v in 0..m.algebra().quiver().num_vertices() {
                assert_eq!(ker.dim_at(v) + im.dim_at(v), m.dim_at(v), "vertex {v}");
                assert_eq!(im.dim_at(v) + coker.dim_at(v), n.dim_at(v), "vertex {v}");
            }
            assert_eq!(ker_incl.then(&f).unwrap(), zero_morphism(&ker, n).unwrap());
            assert_eq!(
                f.then(&coker_proj).unwrap(),
                zero_morphism(m, &coker).unwrap()
            );
            // The corestriction c: m → im recovers f as c.then(im_incl). This
            // certifies that im carries the image with its inclusion.
            let corestriction_maps = (0..m.algebra().quiver().num_vertices())
                .map(|v| express_in_row_basis(im_incl.map_at(v), f.map_at(v), &field))
                .collect();
            let corestriction = Morphism::new(m, &im, corestriction_maps).unwrap();
            assert_eq!(corestriction.then(&im_incl).unwrap(), f);
        }
    }
}

use super::*;
use crate::algebra::{
    an_with_relations, commutative_square, dual_numbers, linear_an, truncated_poly,
};
use crate::decompose::add_morphisms;
use crate::field::PrimeField;
use crate::hom::{hom_dim, zero_morphism};
use crate::homspace::scale_morphism;
use crate::module::direct_sum;

fn f5() -> PrimeField {
    PrimeField::new(5).unwrap()
}

fn f2() -> PrimeField {
    PrimeField::new(2).unwrap()
}

fn unit(dim: usize, k: usize, field: &PrimeField) -> Vec<Fp> {
    let mut v = vec![field.zero(); dim];
    v[k] = field.one();
    v
}

fn basis_class(space: &ExtSpace, k: usize) -> ExtClass {
    let field = space.source().field();
    space
        .class_from_coordinates(&unit(space.dim(), k, &field))
        .unwrap()
}

#[test]
fn ext_space_dim_matches_ext_dim_and_hom_dim_on_fixtures() {
    let field = f5();
    for algebra in [
        truncated_poly(3, field).unwrap(),
        commutative_square(field),
        linear_an(3, field),
        an_with_relations(3, &[(0, 2)], field).unwrap(),
        dual_numbers(field),
    ] {
        let nv = algebra.quiver().num_vertices();
        let mut modules: Vec<Module> = (0..nv).map(|v| Module::simple(&algebra, v)).collect();
        modules.push(Module::projective(&algebra, 0));
        modules.push(Module::injective(&algebra, nv - 1));
        let s0 = Module::simple(&algebra, 0);
        let i_last = Module::injective(&algebra, nv - 1);
        modules.push(direct_sum(&[&s0, &i_last]).0);
        for m in &modules {
            for n in &modules {
                for k in 0..=3 {
                    let space = ExtSpace::new(m, n, k).unwrap();
                    assert_eq!(
                        space.dim(),
                        ext_dim(m, n, k).unwrap(),
                        "dim m = {:?}, dim n = {:?}, k = {k}",
                        m.dim_vector(),
                        n.dim_vector()
                    );
                    if k == 0 {
                        assert_eq!(space.dim(), hom_dim(m, n).unwrap());
                    }
                }
            }
        }
    }
}

#[test]
fn truncated_poly_3_ext_spaces_are_one_dimensional_over_f5_and_f2() {
    for field in [f5(), f2()] {
        let algebra = truncated_poly(3, field).unwrap();
        let s = Module::simple(&algebra, 0);
        for k in 0..=4 {
            let space = ExtSpace::new(&s, &s, k).unwrap();
            assert_eq!(space.dim(), 1, "Ext^{k}(S, S) over F_{}", field.modulus());
            assert_eq!(space.dim(), ext_dim(&s, &s, k).unwrap());
        }
    }
}

#[test]
fn identity_classes_are_yoneda_units() {
    let field = f5();
    let x3 = truncated_poly(3, field).unwrap();
    let s = Module::simple(&x3, 0);
    let a3 = an_with_relations(3, &[(0, 2)], field).unwrap();
    let s0 = Module::simple(&a3, 0);
    let s1 = Module::simple(&a3, 1);
    let s2 = Module::simple(&a3, 2);
    let cases: Vec<(Module, Module, usize)> = vec![
        (s.clone(), s.clone(), 0),
        (s.clone(), s.clone(), 1),
        (s.clone(), s.clone(), 2),
        (s0.clone(), s1.clone(), 1),
        (s0.clone(), s2.clone(), 2),
        (s1.clone(), s2.clone(), 1),
    ];
    for (m, n, k) in cases {
        let space = ExtSpace::new(&m, &n, k).unwrap();
        assert!(space.dim() > 0, "fixture case has a nonzero space");
        let alpha = basis_class(&space, 0);
        let id_m = ExtSpace::new(&m, &m, 0).unwrap().identity_class().unwrap();
        let id_n = ExtSpace::new(&n, &n, 0).unwrap().identity_class().unwrap();
        let left = id_m.then(&alpha).unwrap();
        let right = alpha.then(&id_n).unwrap();
        assert!(left.equals(&alpha).unwrap(), "left unit at degree {k}");
        assert!(right.equals(&alpha).unwrap(), "right unit at degree {k}");
    }
}

// Over k[x]/(x^3) the differentials of the minimal resolution of S
// alternate right multiplication by x and by x^2. The degree-1 lift of
// the Ext^1 generator sends the generator of P_2 into the radical, so
// composing with a cocycle P_1 -> S kills it: the Yoneda square of the
// degree-1 class is zero in every characteristic. The Ext algebra is
// k[z] tensor the exterior algebra on y, so every product involving the
// degree-2 generator z is nonzero.
#[test]
fn truncated_poly_3_yoneda_products_match_the_ext_algebra() {
    for field in [f5(), f2()] {
        let algebra = truncated_poly(3, field).unwrap();
        let s = Module::simple(&algebra, 0);
        let ext1 = ExtSpace::new(&s, &s, 1).unwrap();
        let ext2 = ExtSpace::new(&s, &s, 2).unwrap();
        let xi = basis_class(&ext1, 0);
        let chi = basis_class(&ext2, 0);
        assert!(
            xi.then(&xi).unwrap().is_zero(),
            "y^2 = 0 over F_{}",
            field.modulus()
        );
        assert!(!xi.then(&chi).unwrap().is_zero(), "y z is nonzero");
        assert!(!chi.then(&xi).unwrap().is_zero(), "z y is nonzero");
        assert!(!chi.then(&chi).unwrap().is_zero(), "z^2 is nonzero");
        let (product, witness) = xi.then_with_witness(&chi).unwrap();
        assert!(witness.verify(&xi, &chi, &product));
    }
}

// Over k[x]/(x^2) the Ext algebra of the simple is the polynomial ring
// on the degree-1 class, so every Yoneda power is nonzero.
#[test]
fn dual_numbers_yoneda_powers_of_the_degree_one_class_are_nonzero() {
    let algebra = dual_numbers(f5());
    let s = Module::simple(&algebra, 0);
    let ext1 = ExtSpace::new(&s, &s, 1).unwrap();
    let xi = basis_class(&ext1, 0);
    let square = xi.then(&xi).unwrap();
    assert!(!square.is_zero(), "y^2 is nonzero over k[x]/(x^2)");
    assert!(!square.then(&xi).unwrap().is_zero(), "y^3 is nonzero");
}

// Ext^1(S_0, S_1) x Ext^1(S_1, S_2) -> Ext^2(S_0, S_2) over kA_3/(ab):
// both lifts are identities on the shared projective terms, so the
// product is the Ext^2 generator detected by the relation. On the
// commutative square the product Ext^1(S_0, S_1) x Ext^1(S_1, S_3) ->
// Ext^2(S_0, S_3) has rank 1 (QPA-verified).
#[test]
fn ext1_times_ext1_is_nonzero_on_relation_detected_pairs() {
    let field = f5();
    let a3 = an_with_relations(3, &[(0, 2)], field).unwrap();
    let s0 = Module::simple(&a3, 0);
    let s1 = Module::simple(&a3, 1);
    let s2 = Module::simple(&a3, 2);
    let alpha = basis_class(&ExtSpace::new(&s0, &s1, 1).unwrap(), 0);
    let beta = basis_class(&ExtSpace::new(&s1, &s2, 1).unwrap(), 0);
    let product = alpha.then(&beta).unwrap();
    assert_eq!(product.space().dim(), 1);
    assert!(!product.is_zero(), "Ext^1 . Ext^1 -> Ext^2 over kA_3/(ab)");
    let square = commutative_square(field);
    let t0 = Module::simple(&square, 0);
    let t1 = Module::simple(&square, 1);
    let t3 = Module::simple(&square, 3);
    let a = basis_class(&ExtSpace::new(&t0, &t1, 1).unwrap(), 0);
    let b = basis_class(&ExtSpace::new(&t1, &t3, 1).unwrap(), 0);
    let ab = a.then(&b).unwrap();
    assert_eq!(ab.space().dim(), 1);
    assert!(
        !ab.is_zero(),
        "the commutative square relation pairs 0 -> 3"
    );
}

#[test]
fn yoneda_products_are_bilinear_on_small_cases() {
    let field = f5();
    let a3 = an_with_relations(3, &[(0, 2)], field).unwrap();
    let dn = dual_numbers(field);
    let cases: Vec<(ExtClass, ExtClass)> = {
        let s0 = Module::simple(&a3, 0);
        let s1 = Module::simple(&a3, 1);
        let s2 = Module::simple(&a3, 2);
        let s = Module::simple(&dn, 0);
        vec![
            (
                basis_class(&ExtSpace::new(&s0, &s1, 1).unwrap(), 0),
                basis_class(&ExtSpace::new(&s1, &s2, 1).unwrap(), 0),
            ),
            (
                basis_class(&ExtSpace::new(&s, &s, 1).unwrap(), 0),
                basis_class(&ExtSpace::new(&s, &s, 1).unwrap(), 0),
            ),
        ]
    };
    for (alpha, beta) in cases {
        let two = field.elem(2);
        let three = field.elem(3);
        let product = alpha.then(&beta).unwrap();
        let doubled = alpha.scale(two);
        let sum = alpha.add(&doubled).unwrap();
        let left = sum.then(&beta).unwrap();
        let right = product.add(&doubled.then(&beta).unwrap()).unwrap();
        assert!(left.equals(&right).unwrap(), "additivity on the left");
        let scaled_left = alpha.scale(three).then(&beta).unwrap();
        assert!(scaled_left.equals(&product.scale(three)).unwrap());
        let scaled_right = alpha.then(&beta.scale(three)).unwrap();
        assert!(scaled_right.equals(&product.scale(three)).unwrap());
        let negated = alpha.neg().then(&beta).unwrap();
        assert!(negated.equals(&product.neg()).unwrap());
        let zero = alpha.space().zero_class().then(&beta).unwrap();
        assert!(zero.is_zero(), "the zero class annihilates products");
    }
}

#[test]
fn adding_a_coboundary_does_not_change_the_class() {
    let field = f5();
    let mut saw_nonzero_coboundary = false;
    for algebra in [
        truncated_poly(3, field).unwrap(),
        an_with_relations(3, &[(0, 2)], field).unwrap(),
        commutative_square(field),
    ] {
        let nv = algebra.quiver().num_vertices();
        for v in 0..nv {
            let s = Module::simple(&algebra, v);
            for w in 0..nv {
                for n in [
                    Module::projective(&algebra, w),
                    Module::injective(&algebra, w),
                ] {
                    for k in 1..=2 {
                        let space = ExtSpace::new(&s, &n, k).unwrap();
                        let cob = space.coboundary_basis();
                        if cob.rows() == 0 {
                            continue;
                        }
                        saw_nonzero_coboundary = true;
                        let lay = layout(space.cochain_term());
                        let mut classes = vec![space.zero_class()];
                        for i in 0..space.dim() {
                            classes.push(basis_class(&space, i));
                        }
                        for class in &classes {
                            let rep = class.representative();
                            for r in 0..cob.rows() {
                                let boundary = cochain_from_coordinates(
                                    space.cochain_term(),
                                    &lay,
                                    space.target(),
                                    cob.row(r),
                                );
                                let shifted = add_morphisms(&rep, &boundary);
                                let recovered = space.class_from_cocycle(&shifted).unwrap();
                                assert!(recovered.equals(class).unwrap());
                            }
                        }
                    }
                }
            }
        }
    }
    assert!(saw_nonzero_coboundary, "the fixtures exercise nonzero B^k");
}

#[test]
fn class_from_cocycle_rejects_wrong_endpoints_and_non_cocycles() {
    let field = f5();
    let algebra = truncated_poly(3, field).unwrap();
    let s = Module::simple(&algebra, 0);
    let p = Module::projective(&algebra, 0);
    let space = ExtSpace::new(&s, &p, 1).unwrap();
    let other = ExtSpace::new(&s, &p, 1).unwrap();
    let wrong_source = zero_morphism(other.cochain_term(), &p).unwrap();
    assert_eq!(
        space.class_from_cocycle(&wrong_source).unwrap_err(),
        ExtClassError::SourceMismatch
    );
    let p_copy = Module::projective(&algebra, 0);
    let wrong_target = zero_morphism(space.cochain_term(), &p_copy).unwrap();
    assert_eq!(
        space.class_from_cocycle(&wrong_target).unwrap_err(),
        ExtClassError::TargetMismatch
    );
    let lay = layout(space.cochain_term());
    let non_cocycle = yoneda_basis(space.cochain_term(), &lay, &p).remove(0);
    match space.class_from_cocycle(&non_cocycle).unwrap_err() {
        ExtClassError::NotCocycle { composite } => {
            assert!(composite.iter().any(|c| !c.is_zero()));
        }
        other => panic!("expected NotCocycle, got {other:?}"),
    }
}

#[test]
fn class_from_coordinates_rejects_wrong_length_and_non_canonical_entries() {
    let algebra = truncated_poly(3, f2()).unwrap();
    let s = Module::simple(&algebra, 0);
    let space = ExtSpace::new(&s, &s, 1).unwrap();
    assert_eq!(space.dim(), 1);
    assert_eq!(
        space.class_from_coordinates(&[]).unwrap_err(),
        ExtClassError::CoordinateCountMismatch {
            expected: 1,
            got: 0
        }
    );
    let one = f2().one();
    assert_eq!(
        space.class_from_coordinates(&[one, one]).unwrap_err(),
        ExtClassError::CoordinateCountMismatch {
            expected: 1,
            got: 2
        }
    );
    // The entry 3 comes from F_5; it is not a canonical F_2 representative.
    assert_eq!(
        space.class_from_coordinates(&[f5().elem(3)]).unwrap_err(),
        ExtClassError::NonCanonicalCoordinate { index: 0 }
    );
}

#[test]
fn arithmetic_rejects_incompatible_spaces_and_products_reject_bad_middles() {
    let field = f5();
    let algebra = truncated_poly(3, field).unwrap();
    let s = Module::simple(&algebra, 0);
    let s_copy = Module::simple(&algebra, 0);
    let deg1 = ExtSpace::new(&s, &s, 1).unwrap();
    let deg2 = ExtSpace::new(&s, &s, 2).unwrap();
    let copied = ExtSpace::new(&s_copy, &s_copy, 1).unwrap();
    let a = basis_class(&deg1, 0);
    let b = basis_class(&deg2, 0);
    let c = basis_class(&copied, 0);
    assert_eq!(a.add(&b).unwrap_err(), ExtClassError::IncompatibleSpaces);
    assert_eq!(a.equals(&b).unwrap_err(), ExtClassError::IncompatibleSpaces);
    assert_eq!(a.add(&c).unwrap_err(), ExtClassError::IncompatibleSpaces);
    assert_eq!(a.equals(&c).unwrap_err(), ExtClassError::IncompatibleSpaces);
    assert_eq!(a.then(&c).unwrap_err(), ExtClassError::MiddleMismatch);
}

#[test]
fn identity_class_needs_degree_zero_and_equal_endpoints() {
    let field = f5();
    let algebra = truncated_poly(3, field).unwrap();
    let s = Module::simple(&algebra, 0);
    let p = Module::projective(&algebra, 0);
    assert_eq!(
        ExtSpace::new(&s, &s, 1)
            .unwrap()
            .identity_class()
            .unwrap_err(),
        ExtClassError::NotDegreeZeroEndo
    );
    assert_eq!(
        ExtSpace::new(&s, &p, 0)
            .unwrap()
            .identity_class()
            .unwrap_err(),
        ExtClassError::NotDegreeZeroEndo
    );
}

#[test]
fn zero_modules_give_zero_spaces() {
    let field = f5();
    let algebra = truncated_poly(3, field).unwrap();
    let s = Module::simple(&algebra, 0);
    let z = Module::zero(&algebra);
    for k in 0..=2 {
        let left = ExtSpace::new(&z, &s, k).unwrap();
        let right = ExtSpace::new(&s, &z, k).unwrap();
        assert_eq!(left.dim(), 0);
        assert_eq!(right.dim(), 0);
        assert!(left.zero_class().is_zero());
        assert!(right.zero_class().representative().is_zero());
    }
}

#[test]
fn a_finite_resolution_ending_before_the_degree_gives_the_zero_space() {
    let field = f5();
    let algebra = linear_an(3, field);
    let s0 = Module::simple(&algebra, 0);
    let s1 = Module::simple(&algebra, 1);
    let space = ExtSpace::new(&s0, &s1, 3).unwrap();
    assert_eq!(space.dim(), 0);
    assert!(space.cochain_term().is_zero());
    assert!(space.zero_class().representative().is_zero());
    let empty = space.class_from_coordinates(&[]).unwrap();
    assert!(empty.is_zero());
    let zero = zero_morphism(space.cochain_term(), space.target()).unwrap();
    assert!(space.class_from_cocycle(&zero).unwrap().is_zero());
}

#[test]
fn product_witness_accepts_the_genuine_triple_and_rejects_tampering() {
    let field = f5();
    let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
    let s0 = Module::simple(&algebra, 0);
    let s1 = Module::simple(&algebra, 1);
    let s2 = Module::simple(&algebra, 2);
    let alpha = basis_class(&ExtSpace::new(&s0, &s1, 1).unwrap(), 0);
    let beta = basis_class(&ExtSpace::new(&s1, &s2, 1).unwrap(), 0);
    let (product, witness) = alpha.then_with_witness(&beta).unwrap();
    assert!(witness.verify(&alpha, &beta, &product));
    // A Morphism is checked at construction, so the tamper scales one
    // lift: every nonzero entry changes and one lift identity breaks.
    assert!(!witness.lifts()[0].is_zero());
    let scaled = scale_morphism(&witness.lifts()[0], field.elem(2));
    let mut tampered_lifts = witness.lifts().to_vec();
    tampered_lifts[0] = scaled;
    let tampered = ProductWitness {
        lifts: tampered_lifts,
    };
    assert!(!tampered.verify(&alpha, &beta, &product));
    let wrong_product = ExtClass {
        space: product.space().clone(),
        coords: vec![field.elem(2)],
    };
    assert!(!witness.verify(&alpha, &beta, &wrong_product));
    assert!(!witness.verify(&alpha.scale(field.elem(2)), &beta, &product));
}

#[test]
fn recomputed_spaces_carry_identical_bases_and_representatives() {
    let field = f5();
    let algebra = commutative_square(field);
    let s0 = Module::simple(&algebra, 0);
    let p0 = Module::projective(&algebra, 0);
    for (m, n, k) in [(&s0, &p0, 1), (&s0, &p0, 2), (&s0, &s0, 0)] {
        let first = ExtSpace::new(m, n, k).unwrap();
        let second = ExtSpace::new(m, n, k).unwrap();
        assert!(first.is_compatible(&second));
        assert_eq!(
            first.cocycle_basis().entries_u64(),
            second.cocycle_basis().entries_u64()
        );
        assert_eq!(
            first.coboundary_basis().entries_u64(),
            second.coboundary_basis().entries_u64()
        );
        assert_eq!(
            first.complement_basis().entries_u64(),
            second.complement_basis().entries_u64()
        );
        for (a, b) in first.representatives().iter().zip(second.representatives()) {
            for v in 0..algebra.quiver().num_vertices() {
                assert_eq!(a.map_at(v), b.map_at(v));
            }
        }
    }
}

#[test]
fn ext_space_new_rejects_modules_over_different_algebras() {
    let a = linear_an(3, f5());
    let b = linear_an(3, f5());
    let m = Module::simple(&a, 0);
    let n = Module::simple(&b, 0);
    assert_eq!(
        ExtSpace::new(&m, &n, 1).unwrap_err(),
        ExtError::DifferentAlgebras
    );
}

#[test]
fn an_unrepresentable_successor_degree_is_typed() {
    let algebra = linear_an(1, f5());
    let simple = Module::simple(&algebra, 0);
    let expected = ExtError::DegreeOverflow { degree: usize::MAX };
    assert_eq!(
        ext_table(&simple, &simple, usize::MAX),
        Err(expected.clone())
    );
    assert_eq!(ext_dim(&simple, &simple, usize::MAX), Err(expected.clone()));
    assert_eq!(
        ExtSpace::new(&simple, &simple, usize::MAX).unwrap_err(),
        expected
    );
}

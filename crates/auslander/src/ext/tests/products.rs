use super::*;
use crate::algebra::{an_with_relations, dual_numbers, truncated_poly};
use crate::decompose::add_morphisms;
use crate::field::PrimeField;
use crate::homspace::scale_morphism;
use crate::radical::radical;
use crate::sequence::ShortExactSequence;

fn f5() -> PrimeField {
    PrimeField::new(5).unwrap()
}

fn f2() -> PrimeField {
    PrimeField::new(2).unwrap()
}

fn basis_class(space: &ExtSpace, k: usize) -> ExtClass {
    let field = space.source().field();
    let mut coords = vec![field.zero(); space.dim()];
    coords[k] = field.one();
    space.class_from_coordinates(&coords).unwrap()
}

/// The cochain morphism of `row` over the cochain term of `space`.
fn cocycle_of_row(space: &ExtSpace, row: &[Fp]) -> Morphism {
    let inner = &space.0;
    let lay = layout(&inner.term);
    cochain_from_coordinates(&inner.term, &lay, &inner.target, row)
}

/// The degree 1 x degree 1 product class computed by the lift
/// construction from an arbitrary left cocycle `P^M_1 -> N`, not from
/// the canonical representative: transport the cocycle onto the product
/// resolution, lift it through the augmentation of N's resolution, push
/// one differential further, compose with the right cocycle, and
/// reduce.
fn product_from_cocycles(
    left_cocycle: &Morphism,
    beta: &ExtClass,
    right_cocycle: &Morphism,
    product_space: &ExtSpace,
) -> ExtClass {
    let deep = &product_space.0.resolution;
    let res_n = &beta.space().0.resolution;
    let nv = product_space.0.source.algebra().quiver().num_vertices();
    let maps: Vec<DenseMat> = (0..nv).map(|v| left_cocycle.map_at(v).clone()).collect();
    let f = Morphism::new(&deep.terms[1], &beta.space().0.source, maps)
        .expect("the recomputed resolution prefix matches, so the cocycle transports");
    let phi0 = lift_through(&deep.terms[1], &res_n.augmentation, &f);
    let rhs = deep.maps[1].then(&phi0).unwrap();
    let phi1 = lift_through(&deep.terms[2], &res_n.maps[0], &rhs);
    let h = phi1.then(right_cocycle).unwrap();
    product_space.class_from_cocycle(&h).unwrap()
}

/// Over A = k[x]/(x^3) with S the simple and R = rad P = A/(x^2): the
/// resolution of S has d_1 = x and d_2 = x^2, so B^1(S, R) is the line
/// spanned by 1 -> x while B^1 into any simple target vanishes. The
/// products Ext^1(S, R) x Ext^1(R, S) -> Ext^2(S, S) and
/// Ext^1(R, S) x Ext^1(S, R) -> Ext^2(R, R) are both nonzero: the
/// spliced 2-extensions 0 -> S -> P -> P -> S -> 0 (middle map x) and
/// 0 -> R -> P -> P -> R -> 0 (middle map x^2) have nonzero connecting
/// cocycles against the minimal resolutions.
fn x3_pairs(field: PrimeField) -> Vec<(ExtSpace, ExtSpace)> {
    let algebra = truncated_poly(3, field).unwrap();
    let s = Module::simple(&algebra, 0);
    let r = radical(&Module::projective(&algebra, 0)).0;
    vec![
        (
            ExtSpace::new(&s, &r, 1).unwrap(),
            ExtSpace::new(&r, &s, 1).unwrap(),
        ),
        (
            ExtSpace::new(&r, &s, 1).unwrap(),
            ExtSpace::new(&s, &r, 1).unwrap(),
        ),
    ]
}

#[test]
fn a_left_cocycle_shifted_by_a_coboundary_lifts_to_the_same_product() {
    for field in [f5(), f2()] {
        let mut shifted_cases = 0usize;
        for (left, right) in x3_pairs(field) {
            let alpha = basis_class(&left, 0);
            let beta = basis_class(&right, 0);
            let canonical = alpha.then(&beta).unwrap();
            assert!(!canonical.is_zero(), "the fixture products are nonzero");
            let cob = left.coboundary_basis();
            if cob.rows() == 0 {
                continue;
            }
            let rep = alpha.representative();
            let g = beta.representative();
            let product_space = canonical.space();
            for k in 0..cob.rows() {
                let boundary = cocycle_of_row(&left, cob.row(k));
                assert!(!boundary.is_zero());
                let shifted = add_morphisms(&rep, &boundary);
                assert!(shifted != rep, "the altered representative differs");
                let from_shifted = product_from_cocycles(&shifted, &beta, &g, product_space);
                assert!(from_shifted.equals(&canonical).unwrap());
                shifted_cases += 1;
            }
        }
        assert!(
            shifted_cases > 0,
            "some left factor space has nonzero coboundaries"
        );
    }
}

#[test]
fn a_right_cocycle_shifted_by_a_coboundary_composes_to_the_same_product() {
    for field in [f5(), f2()] {
        let mut shifted_cases = 0usize;
        for (left, right) in x3_pairs(field) {
            let alpha = basis_class(&left, 0);
            let beta = basis_class(&right, 0);
            let (canonical, witness) = alpha.then_with_witness(&beta).unwrap();
            assert!(!canonical.is_zero(), "the fixture products are nonzero");
            let cob = right.coboundary_basis();
            if cob.rows() == 0 {
                continue;
            }
            let g = beta.representative();
            for k in 0..cob.rows() {
                let boundary = cocycle_of_row(&right, cob.row(k));
                assert!(!boundary.is_zero());
                let shifted = add_morphisms(&g, &boundary);
                assert!(shifted != g, "the altered representative differs");
                let h = witness.lifts()[1].then(&shifted).unwrap();
                let reduced = canonical.space().class_from_cocycle(&h).unwrap();
                assert!(reduced.equals(&canonical).unwrap());
                shifted_cases += 1;
            }
        }
        assert!(
            shifted_cases > 0,
            "some right factor space has nonzero coboundaries"
        );
    }
}

/// Re-solves the connecting cocycle of `alpha`'s realized extension,
/// the pre-reduction morphism of the `ext1_class` recovery: lift the
/// augmentation through the projection, push it one differential
/// further, and pull the result back through the inclusion.
fn recovered_cocycle(alpha: &ExtClass) -> Morphism {
    let ses = ShortExactSequence::from_ext1(alpha).unwrap();
    let res = &alpha.space().0.resolution;
    let h = lift_through(&res.terms[0], ses.projection(), &res.augmentation);
    let d1h = res.maps[0].then(&h).unwrap();
    lift_through(&res.terms[1], ses.inclusion(), &d1h)
}

#[test]
fn the_cocycle_recovered_from_the_extension_splices_to_the_product() {
    let field = f5();
    let a3 = an_with_relations(3, &[(0, 2)], field).unwrap();
    let s0 = Module::simple(&a3, 0);
    let s1 = Module::simple(&a3, 1);
    let s2 = Module::simple(&a3, 2);
    let dn = dual_numbers(field);
    let ds = Module::simple(&dn, 0);
    let mut pairs = vec![
        (
            ExtSpace::new(&s0, &s1, 1).unwrap(),
            ExtSpace::new(&s1, &s2, 1).unwrap(),
        ),
        (
            ExtSpace::new(&ds, &ds, 1).unwrap(),
            ExtSpace::new(&ds, &ds, 1).unwrap(),
        ),
    ];
    pairs.extend(x3_pairs(field));
    let mut perturbed_cases = 0usize;
    for (left, right) in pairs {
        let alpha = basis_class(&left, 0);
        let beta = basis_class(&right, 0);
        let canonical = alpha.then(&beta).unwrap();
        assert!(!canonical.is_zero(), "the fixture products are nonzero");
        let recovered = recovered_cocycle(&alpha);
        assert!(
            left.class_from_cocycle(&recovered)
                .unwrap()
                .equals(&alpha)
                .unwrap()
        );
        let rep = alpha.representative();
        let cocycle = if recovered == rep {
            // A route through the same morphism proves nothing, so
            // perturb by a coboundary. When B^1 is zero every class
            // has one cocycle and the coincidence is forced.
            let cob = left.coboundary_basis();
            if cob.rows() == 0 {
                recovered
            } else {
                let shifted = add_morphisms(&recovered, &cocycle_of_row(&left, cob.row(0)));
                assert!(shifted != rep, "the perturbed cocycle differs");
                perturbed_cases += 1;
                shifted
            }
        } else {
            perturbed_cases += 1;
            recovered
        };
        let g = beta.representative();
        let spliced = product_from_cocycles(&cocycle, &beta, &g, canonical.space());
        assert!(spliced.equals(&canonical).unwrap());
    }
    assert!(
        perturbed_cases > 0,
        "some case runs the splice on a cocycle other than the canonical representative"
    );
}

fn rows_of(mat: &DenseMat) -> Vec<Vec<Fp>> {
    (0..mat.rows()).map(|r| mat.row(r).to_vec()).collect()
}

// Section 15 of the design: a complement row replaced by a coboundary.
// The stored witness reduces the product cocycle against the tampered
// complement, and the mismatch is not a coboundary, so verify rejects.
#[test]
fn a_complement_row_replaced_by_a_coboundary_fails_product_verification() {
    let field = f5();
    let mut pairs = x3_pairs(field);
    let (left, right) = pairs.remove(1);
    let alpha = basis_class(&left, 0);
    let beta = basis_class(&right, 0);
    let (product, witness) = alpha.then_with_witness(&beta).unwrap();
    assert!(!product.is_zero());
    assert!(witness.verify(&alpha, &beta, &product));
    let inner = &product.space().0;
    assert!(
        inner.coboundaries.rows() > 0,
        "Ext^2(R, R) has nonzero coboundaries"
    );
    let mut rows = rows_of(&inner.complement);
    rows[0] = inner.coboundaries.row(0).to_vec();
    let tampered = product.space().with_bases(
        inner.cocycles.clone(),
        inner.coboundaries.clone(),
        DenseMat::from_rows(&rows),
    );
    let bad = ExtClass {
        space: tampered,
        coords: product.coordinates().to_vec(),
    };
    assert!(!witness.verify(&alpha, &beta, &bad));
}

// Section 15 of the design: a product reduced against a tampered
// coboundary basis. A basis grown by a cocycle outside B^2 would let
// any class label pass the membership solve, so verify must compare
// the stored basis against the recomputation and reject.
#[test]
fn a_tampered_coboundary_basis_fails_product_verification() {
    let field = f5();
    let mut pairs = x3_pairs(field);
    let (left, right) = pairs.remove(1);
    let alpha = basis_class(&left, 0);
    let beta = basis_class(&right, 0);
    let (product, witness) = alpha.then_with_witness(&beta).unwrap();
    assert!(witness.verify(&alpha, &beta, &product));
    let inner = &product.space().0;
    assert!(
        inner.coboundaries.rows() > 0,
        "Ext^2(R, R) has nonzero coboundaries"
    );
    let mut rows = rows_of(&inner.coboundaries);
    rows.push(inner.complement.row(0).to_vec());
    let grown = DenseMat::from_rows(&rows).into_row_space_basis(&field);
    assert_ne!(grown, inner.coboundaries);
    let tampered =
        product
            .space()
            .with_bases(inner.cocycles.clone(), grown, inner.complement.clone());
    let bad = ExtClass {
        space: tampered,
        coords: product.coordinates().to_vec(),
    };
    assert!(!witness.verify(&alpha, &beta, &bad));
    let wrong_label = ExtClass {
        space: bad.space.clone(),
        coords: vec![field.zero(); product.coordinates().len()],
    };
    assert!(!witness.verify(&alpha, &beta, &wrong_label));
}

// The space recheck of C1: an untampered space matches its recomputation,
// a space with any one stored matrix replaced does not.
#[test]
fn a_space_matches_its_recomputation_and_no_tampered_copy_does() {
    let field = f5();
    let algebra = truncated_poly(3, field).unwrap();
    let s = Module::simple(&algebra, 0);
    let space = ExtSpace::new(&s, &s, 2).unwrap();
    assert!(space.matches_recomputation());
    assert!(space.matches(&ExtSpace::new(&s, &s, 2).unwrap()));
    assert!(!space.matches(&ExtSpace::new(&s, &s, 1).unwrap()));
    let width = space.cocycle_basis().cols();
    let tampered = [
        space.with_bases(
            DenseMat::zero(0, width),
            space.coboundary_basis().clone(),
            space.complement_basis().clone(),
        ),
        space.with_bases(
            space.cocycle_basis().clone(),
            space.complement_basis().clone(),
            space.complement_basis().clone(),
        ),
        space.with_bases(
            space.cocycle_basis().clone(),
            space.coboundary_basis().clone(),
            DenseMat::zero(0, width),
        ),
        space.with_representatives(
            space
                .representatives()
                .iter()
                .map(|rep| scale_morphism(rep, field.elem(2)))
                .collect(),
        ),
    ];
    for bad in &tampered {
        assert!(!bad.matches_recomputation());
        assert!(!space.matches(bad));
    }
}

// then_in reuses the caller's space; the coordinates are the ones then
// returns, because recomputed compatible spaces carry identical bases.
#[test]
fn then_in_agrees_with_then_and_rejects_an_unrelated_space() {
    let field = f5();
    let algebra = truncated_poly(3, field).unwrap();
    let s = Module::simple(&algebra, 0);
    let alpha = basis_class(&ExtSpace::new(&s, &s, 1).unwrap(), 0);
    let beta = basis_class(&ExtSpace::new(&s, &s, 2).unwrap(), 0);
    let product_space = alpha.product_space(&beta).unwrap();
    assert_eq!(product_space.degree(), 3);
    let plain = alpha.then(&beta).unwrap();
    let reused = alpha.then_in(&beta, &product_space).unwrap();
    assert_eq!(reused.coordinates(), plain.coordinates());
    assert!(reused.space().matches(plain.space()));
    let (again, witness) = alpha.then_with_witness_in(&beta, &product_space).unwrap();
    assert!(witness.verify(&alpha, &beta, &again));
    assert!(witness.verify_against(&alpha, &beta, &again, &product_space));
    let wrong_degree = ExtSpace::new(&s, &s, 2).unwrap();
    assert_eq!(
        alpha.then_in(&beta, &wrong_degree).unwrap_err(),
        ExtClassError::IncompatibleSpaces
    );
    let other_target = Module::projective(&algebra, 0);
    let wrong_target = ExtSpace::new(&s, &other_target, 3).unwrap();
    assert_eq!(
        alpha.then_in(&beta, &wrong_target).unwrap_err(),
        ExtClassError::IncompatibleSpaces
    );
}

// verify_against takes the recomputation from the caller, so it must
// reject one that is not a recomputation of the product space.
#[test]
fn verify_against_rejects_a_space_that_is_not_the_recomputation() {
    let field = f5();
    let algebra = truncated_poly(3, field).unwrap();
    let s = Module::simple(&algebra, 0);
    let alpha = basis_class(&ExtSpace::new(&s, &s, 1).unwrap(), 0);
    let beta = basis_class(&ExtSpace::new(&s, &s, 1).unwrap(), 0);
    let (product, witness) = alpha.then_with_witness(&beta).unwrap();
    assert!(witness.verify(&alpha, &beta, &product));
    let inner = product.space();
    let grown = stack_rows(
        &[inner.coboundary_basis(), inner.complement_basis()],
        inner.complement_basis().cols(),
    )
    .into_row_space_basis(&field);
    let forged = inner.with_bases(
        inner.cocycle_basis().clone(),
        grown,
        inner.complement_basis().clone(),
    );
    assert!(!witness.verify_against(&alpha, &beta, &product, &forged));
}

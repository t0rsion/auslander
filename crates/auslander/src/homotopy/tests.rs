use std::sync::Arc;

use super::complex::zero_between;
use super::*;
use crate::algebra::linear_an;
use crate::field::PrimeField;
use crate::hom::{Morphism, identity};
use crate::module::Module;

fn f5() -> PrimeField {
    PrimeField::new(5).unwrap()
}

fn one_term() -> (Arc<crate::algebra::Algebra>, Module) {
    let algebra = linear_an(1, f5());
    let module = Module::simple(&algebra, 0);
    (algebra, module)
}

fn zero_differential(m: &Module) -> Morphism {
    zero_between(m, m)
}

#[test]
fn constructor_uses_homological_degree_order() {
    let (_algebra, simple) = one_term();
    let complex = BoundedComplex::new(
        -1,
        vec![simple.clone(), simple.clone()],
        vec![zero_differential(&simple)],
    )
    .unwrap();
    assert_eq!(complex.range(), DegreeRange::new(-1, 0).unwrap());
    assert!(complex.differential(0).unwrap().source().ptr_eq(&simple));
    assert!(complex.verify());
}

#[test]
fn odd_shift_negates_differentials_and_moves_degrees() {
    let (_algebra, simple) = one_term();
    let differential = zero_differential(&simple);
    let complex = BoundedComplex::new(0, vec![simple.clone(), simple], vec![differential]).unwrap();
    let shifted = complex.shift(1).unwrap();
    assert_eq!(shifted.range(), DegreeRange::new(1, 2).unwrap());
    assert!(shifted.verify());
    assert!(shifted.differential(2).unwrap().is_zero());
}

#[test]
fn identity_and_zero_chain_maps_check_composition() {
    let (_algebra, simple) = one_term();
    let complex = BoundedComplex::new(
        0,
        vec![simple.clone(), simple.clone()],
        vec![zero_differential(&simple)],
    )
    .unwrap();
    let identity = ChainMap::identity(&complex);
    let zero = ChainMap::zero(&complex, &complex).unwrap();
    assert!(identity.then(&identity).unwrap().agrees_with(&identity));
    assert!(zero.then(&identity).unwrap().agrees_with(&zero));
    assert_eq!(
        ChainMap::new(&complex, &complex, vec![identity.components()[0].clone()]).unwrap_err(),
        ChainMapError::ComponentCount {
            expected: 2,
            got: 1
        }
    );
    assert!(identity.verify());
}

#[test]
fn composition_rejects_same_terms_with_different_differentials() {
    let (_algebra, simple) = one_term();
    let zero = BoundedComplex::new(
        0,
        vec![simple.clone(), simple.clone()],
        vec![zero_differential(&simple)],
    )
    .unwrap();
    let nonzero = BoundedComplex::new(
        0,
        vec![simple.clone(), simple.clone()],
        vec![identity(&simple)],
    )
    .unwrap();
    let left = ChainMap::identity(&nonzero);
    let right = ChainMap::identity(&zero);
    assert_eq!(
        left.then(&right).unwrap_err(),
        ChainMapError::CompositionMismatch
    );
}

#[test]
fn zero_homotopy_has_zero_boundary() {
    let (_algebra, simple) = one_term();
    let complex = BoundedComplex::new(
        0,
        vec![simple.clone(), simple.clone()],
        vec![zero_differential(&simple)],
    )
    .unwrap();
    let h = ChainHomotopy::new(
        &complex,
        &complex,
        vec![zero_differential(&complex.terms()[0])],
    )
    .unwrap();
    assert!(
        h.boundary()
            .unwrap()
            .components()
            .iter()
            .all(Morphism::is_zero)
    );
}

#[test]
fn cone_of_zero_map_has_signed_square_zero() {
    let (_algebra, simple) = one_term();
    let complex = BoundedComplex::new(
        0,
        vec![simple.clone(), simple.clone()],
        vec![zero_differential(&simple)],
    )
    .unwrap();
    let zero = ChainMap::zero(&complex, &complex).unwrap();
    let cone = zero.mapping_cone().unwrap();
    assert_eq!(cone.range(), DegreeRange::new(0, 2).unwrap());
    assert!(cone.verify());
}

#[test]
fn chain_hom_quotient_reduces_a_null_homotopic_map() {
    let (_algebra, simple) = one_term();
    let complex = BoundedComplex::new(
        0,
        vec![simple.clone(), simple.clone()],
        vec![zero_differential(&simple)],
    )
    .unwrap();
    let space = ChainHomSpace::new(&complex, &complex).unwrap();
    let quotient = space.quotient().unwrap();
    assert_eq!(quotient.dim(), space.dim());
    let map = space.basis_morphism(0);
    let (coordinates, remainder) = quotient.reduce(&map).unwrap();
    assert_eq!(coordinates.len(), quotient.dim());
    let rebuilt = quotient
        .representative(&coordinates)
        .add(&remainder)
        .unwrap();
    assert!(map.agrees_with(&rebuilt));
}

#[test]
fn identity_differential_complex_is_zero_in_the_homotopy_category() {
    let (_algebra, simple) = one_term();
    let identity = identity(&simple);
    let complex = BoundedComplex::new(0, vec![simple.clone(), simple], vec![identity]).unwrap();
    let space = ChainHomSpace::new(&complex, &complex).unwrap();
    let quotient = space.quotient().unwrap();
    assert_eq!(space.dim(), 1);
    assert_eq!(quotient.null_homotopic_basis().rows(), 1);
    assert_eq!(quotient.dim(), 0);
    for map in space.basis_iter() {
        assert!(map.is_null_homotopic().unwrap());
    }
}

#[test]
fn chain_maps_pad_different_supports_to_the_union() {
    let algebra = linear_an(1, f5());
    let simple = Module::simple(&algebra, 0);
    let zero = Module::zero(&algebra);
    let short = BoundedComplex::new(0, vec![simple.clone()], Vec::new()).unwrap();
    let target_differential = zero_between(&simple, &zero);
    let long =
        BoundedComplex::new(-1, vec![zero, simple.clone()], vec![target_differential]).unwrap();
    let source = short.padded_to(DegreeRange::new(-1, 0).unwrap()).unwrap();
    let components = vec![
        zero_between(&source.terms()[0], &long.terms()[0]),
        identity(&simple),
    ];
    let map = ChainMap::new(&short, &long, components).unwrap();
    assert_eq!(map.range(), DegreeRange::new(-1, 0).unwrap());
    assert!(map.source().verify());
    assert!(map.target().verify());
    assert!(map.verify());
}

#[test]
fn fresh_padding_rebases_hom_coordinates_and_reduction() {
    let algebra = linear_an(1, f5());
    let simple = Module::simple(&algebra, 0);
    let zero = Module::zero(&algebra);
    let short = BoundedComplex::new(0, vec![simple.clone()], Vec::new()).unwrap();
    let long = BoundedComplex::new(
        -1,
        vec![zero.clone(), simple.clone()],
        vec![zero_between(&simple, &zero)],
    )
    .unwrap();
    let fresh_zero = Module::zero(&algebra);
    let fresh_source = BoundedComplex::new(
        -1,
        vec![fresh_zero.clone(), simple.clone()],
        vec![zero_between(&simple, &fresh_zero)],
    )
    .unwrap();
    let fresh_map = ChainMap::new(
        &short,
        &long,
        vec![
            zero_between(&fresh_zero, &long.terms()[0]),
            identity(&simple),
        ],
    )
    .unwrap();
    assert!(fresh_source.agrees_with(&fresh_map.source().clone()));
    let space = ChainHomSpace::new(&short, &long).unwrap();
    assert!(space.coords(&fresh_map).is_ok());
    let quotient = space.quotient().unwrap();
    let (coordinates, remainder) = quotient.reduce(&fresh_map).unwrap();
    let rebuilt = quotient
        .representative(&coordinates)
        .add(&remainder)
        .unwrap();
    assert!(fresh_map.agrees_with(&rebuilt));
}

#[test]
fn nonzero_cones_and_shift_signs_hold_in_characteristics_two_and_five() {
    for modulus in [2, 5] {
        let field = PrimeField::new(modulus).unwrap();
        let algebra = linear_an(1, field);
        let simple = Module::simple(&algebra, 0);
        let complex = BoundedComplex::new(
            0,
            vec![simple.clone(), simple.clone()],
            vec![identity(&simple)],
        )
        .unwrap();
        let cone = ChainMap::identity(&complex).mapping_cone().unwrap();
        assert!(cone.verify());
        assert!(!cone.differential(1).unwrap().is_zero());
        let shifted = complex.shift(1).unwrap();
        assert_eq!(
            shifted.differential(2).unwrap().map_at(0).get(0, 0),
            field.neg(field.one())
        );
    }
}

#[test]
fn direct_sum_pads_support_and_rechecks_each_block() {
    let algebra = linear_an(1, f5());
    let simple = Module::simple(&algebra, 0);
    let zero = Module::zero(&algebra);
    let left = BoundedComplex::new(0, vec![simple.clone()], Vec::new()).unwrap();
    let right = BoundedComplex::new(
        -1,
        vec![zero.clone(), simple.clone()],
        vec![zero_between(&simple, &zero)],
    )
    .unwrap();
    let sum = BoundedComplex::direct_sum(&[&left, &right]).unwrap();
    assert_eq!(sum.range(), DegreeRange::new(-1, 0).unwrap());
    assert_eq!(sum.term(-1).unwrap().dim_at(0), 0);
    assert_eq!(sum.term(0).unwrap().dim_at(0), 2);
    assert!(sum.verify());
}

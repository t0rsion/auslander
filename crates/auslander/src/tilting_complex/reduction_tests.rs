use super::reduction::is_minimal;
use super::*;
use crate::algebra::{kronecker, linear_an};
use crate::control::ComputationControl;
use crate::equivalence_discovery::{DiscoveryLimits, discover_equivalences};
use crate::field::PrimeField;
use crate::hom::identity;
use crate::module::direct_sum;

fn projective_complex(terms: Vec<Module>, differentials: Vec<Morphism>) -> ProjectiveComplex {
    ProjectiveComplex::new(BoundedComplex::new(0, terms, differentials).unwrap()).unwrap()
}

fn reduce(complex: &ProjectiveComplex) -> Option<MinimalReduction> {
    MinimalReduction::new(complex, &mut WorkMeter::default()).unwrap()
}

/// `P_0 → P_0 ⊕ P_1` over `A_2` is the contractible `P_0 → P_0` plus the
/// stalk `P_1` in degree zero.
#[test]
fn elimination_splits_off_an_isomorphism_component() {
    let algebra = linear_an(2, PrimeField::new(5).unwrap());
    let (p0, p1) = (
        Module::projective(&algebra, 0),
        Module::projective(&algebra, 1),
    );
    let (sum, inclusions, _) = direct_sum(&[&p0, &p1]);
    let complex = projective_complex(vec![sum, p0], vec![inclusions[0].clone()]);
    assert!(!is_minimal(&complex));
    let reduction = reduce(&complex).expect("the stalk P_1 remains");
    let minimal = reduction.minimal().complex();
    assert_eq!((minimal.lower(), minimal.upper()), (0, 0));
    assert_eq!(minimal.terms()[0].dim_vector(), p1.dim_vector());
    assert!(reduction.verify(complex.complex()));
    let tampered = MinimalReduction {
        minimal: complex.clone(),
        forward: ChainMap::identity(complex.complex()),
        backward: ChainMap::identity(complex.complex()),
    };
    assert!(!tampered.verify(complex.complex()));
}

#[test]
fn contractible_complexes_reduce_to_nothing() {
    let algebra = linear_an(2, PrimeField::new(5).unwrap());
    let p0 = Module::projective(&algebra, 0);
    let complex = projective_complex(vec![p0.clone(), p0.clone()], vec![identity(&p0)]);
    assert!(reduce(&complex).is_none());
}

/// A reduction of one complex is no witness for another: the stalk `P_0`
/// has homology where the reduced stalk `P_1` has none.
#[test]
fn a_reduction_checks_its_source_complex() {
    let algebra = linear_an(2, PrimeField::new(5).unwrap());
    let (p0, p1) = (
        Module::projective(&algebra, 0),
        Module::projective(&algebra, 1),
    );
    let (sum, inclusions, _) = direct_sum(&[&p0, &p1]);
    let complex = projective_complex(vec![sum, p0.clone()], vec![inclusions[0].clone()]);
    let reduction = reduce(&complex).unwrap();
    let other = projective_complex(vec![p0], Vec::new());
    assert!(!reduction.verify(other.complex()));
}

/// Every indecomposable object of `K^b(proj)` over the hereditary Kronecker
/// algebra is a shifted projective resolution, so its minimal complex has at
/// most two terms.
#[test]
fn kronecker_vertices_keep_minimal_two_term_summands() {
    let algebra = kronecker(2, PrimeField::new(2).unwrap());
    let limits = DiscoveryLimits {
        max_directed_mutations: 24,
        ..DiscoveryLimits::default()
    };
    let graph = discover_equivalences(&algebra, limits, &ComputationControl::new()).unwrap();
    for summand in graph
        .vertices()
        .iter()
        .flat_map(|vertex| vertex.candidate().summands())
    {
        assert!(is_minimal(summand));
        assert!(summand.complex().len() <= 2);
    }
}

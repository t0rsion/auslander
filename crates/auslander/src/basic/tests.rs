use std::sync::Arc;

use super::*;
use crate::algebra::{Algebra, commutative_square, kronecker, linear_an, truncated_poly};
use crate::arquiver::IndecomposableCatalog;
use crate::dynkin::{DynkinType, dynkin_quiver};
use crate::field::PrimeField;
use crate::indec::IndecomposableModule;
use crate::linalg::DenseMat;
use crate::module::{Module, direct_sum};
use crate::quiver::{ArrowId, Quiver};
use crate::supporttau::enumerate_over_catalog;

fn f2() -> PrimeField {
    PrimeField::new(2).unwrap()
}

fn f5() -> PrimeField {
    PrimeField::new(5).unwrap()
}

fn fields() -> [PrimeField; 2] {
    [f2(), f5()]
}

fn path_algebra(quiver: Quiver, field: PrimeField) -> Arc<Algebra> {
    crate::algebra::path_algebra(quiver, field)
        .expect("the zero ideal over an acyclic quiver completes")
}

// D_4 as dynkin_quiver builds it: vertex 0 is the center, arrows 0 -> 1,
// 0 -> 2, 0 -> 3.
fn d4(field: PrimeField) -> Arc<Algebra> {
    path_algebra(
        dynkin_quiver(DynkinType::D(4)).expect("D_4 has a quiver"),
        field,
    )
}

fn basic(m: &Module) -> BasicDecomposition {
    BasicDecomposition::new(m).expect("the fixture module is basic")
}

fn support(algebra: &Arc<Algebra>, vertices: &[u32]) -> ProjectiveSupport {
    ProjectiveSupport::new(algebra, vertices).expect("the fixture vertices are in range")
}

fn sum(parts: &[&Module]) -> Module {
    let (total, _, _) = direct_sum(parts);
    total
}

fn expect_witness(outcome: SupportPairIsoOutcome) -> SupportPairIsoWitness {
    match outcome {
        SupportPairIsoOutcome::Isomorphic(witness) => witness,
        SupportPairIsoOutcome::NotIsomorphic(obstruction) => {
            panic!("expected an isomorphism, got {obstruction:?}")
        }
    }
}

fn expect_obstruction(outcome: SupportPairIsoOutcome) -> SupportPairObstruction {
    match outcome {
        SupportPairIsoOutcome::NotIsomorphic(obstruction) => obstruction,
        SupportPairIsoOutcome::Isomorphic(witness) => {
            panic!("expected an obstruction, got {witness:?}")
        }
    }
}

// The three Kronecker representations of dimension vector [1, 1] over
// F_2: the arrow pair (a, b) takes the values (1, 0), (0, 1), and (1, 1),
// which are the three points of P^1(F_2). All three are indecomposable
// and pairwise non-isomorphic.
fn kronecker_line(algebra: &Arc<Algebra>, field: PrimeField, a: i64, b: i64) -> Module {
    Module::new(
        algebra.clone(),
        vec![1, 1],
        vec![
            DenseMat::from_rows(&[vec![field.elem(a)]]),
            DenseMat::from_rows(&[vec![field.elem(b)]]),
        ],
    )
    .expect("a Kronecker representation is a module")
}

#[path = "closure_tests.rs"]
mod closure_tests;
#[path = "decomposition_tests.rs"]
mod decomposition_tests;
#[path = "fingerprint_tests.rs"]
mod fingerprint_tests;
#[path = "pair_iso_tests.rs"]
mod pair_iso_tests;
#[path = "support_tests.rs"]
mod support_tests;

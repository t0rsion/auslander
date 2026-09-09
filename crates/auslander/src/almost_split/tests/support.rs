use std::sync::Arc;

use crate::algebra::{Algebra, kronecker, truncated_poly};
use crate::arquiver::IndecomposableCatalog;
use crate::completion::CompletionLimits;
use crate::decompose::{KrullSchmidtOutcome, krull_schmidt};
use crate::field::PrimeField;
use crate::indec::IndecomposableModule;
use crate::linalg::DenseMat;
use crate::module::Module;
use crate::quiver::{ArrowId, Quiver};
use crate::relation::{Presentation, Relation};

use super::super::{
    AlmostSplitOutcome, AlmostSplitSequence, AlmostSplitWitness, ArDualityWitness, CatalogWitness,
    almost_split, almost_split_via_catalog,
};

pub(super) fn f2() -> PrimeField {
    PrimeField::new(2).unwrap()
}

pub(super) fn f5() -> PrimeField {
    PrimeField::new(5).unwrap()
}

pub(super) fn indec(m: &Module) -> IndecomposableModule {
    IndecomposableModule::new(m).unwrap()
}

pub(super) fn sequence_of(m: &IndecomposableModule) -> AlmostSplitSequence {
    match almost_split(m).unwrap() {
        AlmostSplitOutcome::Sequence(sequence) => sequence,
        AlmostSplitOutcome::Projective => panic!("expected a sequence, got Projective"),
    }
}

pub(super) fn catalog_sequence_of(
    m: &IndecomposableModule,
    catalog: &IndecomposableCatalog,
) -> AlmostSplitSequence {
    match almost_split_via_catalog(m, catalog).unwrap() {
        AlmostSplitOutcome::Sequence(sequence) => sequence,
        AlmostSplitOutcome::Projective => panic!("expected a sequence, got Projective"),
    }
}

pub(super) fn duality_witness(sequence: &AlmostSplitSequence) -> &ArDualityWitness {
    match sequence.witness() {
        AlmostSplitWitness::ArDuality(witness) => witness,
        AlmostSplitWitness::ExhaustiveCatalog(_) => panic!("expected the AR duality witness"),
    }
}

pub(super) fn catalog_witness(sequence: &AlmostSplitSequence) -> &CatalogWitness {
    match sequence.witness() {
        AlmostSplitWitness::ExhaustiveCatalog(witness) => witness,
        AlmostSplitWitness::ArDuality(_) => panic!("expected the catalog witness"),
    }
}

/// Krull-Schmidt classes of the middle term as sorted
/// (dimension vector, multiplicity) pairs.
pub(super) fn middle_classes(middle: &Module) -> Vec<(Vec<usize>, usize)> {
    match krull_schmidt(middle) {
        KrullSchmidtOutcome::Classes(classes) => {
            let mut dims: Vec<(Vec<usize>, usize)> = classes
                .iter()
                .map(|c| (c.representative.dim_vector().to_vec(), c.multiplicity))
                .collect();
            dims.sort();
            dims
        }
        KrullSchmidtOutcome::Unknown { reason } => panic!("krull_schmidt failed: {reason}"),
    }
}

pub(super) fn ids(raw: &[u32]) -> Vec<ArrowId> {
    raw.iter().copied().map(ArrowId).collect()
}

/// The preprojective algebra of A_3 over F_2, the constructor of
/// tests/acceptance_nonmonomial.rs: double quiver a: 0 -> 1 (id 0),
/// b: 1 -> 2 (1), abar: 1 -> 0 (2), bbar: 2 -> 1 (3) with relations
/// a.abar, abar.a - b.bbar, bbar.b. Dimension 10, self-injective.
pub(super) fn preprojective_a3() -> Arc<Algebra> {
    let field = f2();
    let quiver = Quiver::new(3, &[(0, 1), (1, 2), (1, 0), (2, 1)]).unwrap();
    let relations = vec![
        Relation::new(&quiver, field, vec![(field.one(), ids(&[0, 2]))]).unwrap(),
        Relation::new(
            &quiver,
            field,
            vec![(field.one(), ids(&[2, 0])), (field.elem(-1), ids(&[1, 3]))],
        )
        .unwrap(),
        Relation::new(&quiver, field, vec![(field.one(), ids(&[3, 1]))]).unwrap(),
    ];
    let presentation = Presentation::new(quiver, field, relations).unwrap();
    Algebra::new(presentation, &CompletionLimits::default()).unwrap()
}

/// The Kronecker representation `(I_6, J)` over F_2, for `J` the block
/// matrix with the companion matrix `C` of `x^3 + x + 1` on the diagonal
/// and the identity above it. `C` is irreducible over F_2, so `(I_3, C)`
/// has endomorphism field F_8; this module is the quasi-length-2 member
/// of the same tube, and its endomorphism algebra is `F_8[t]/(t^2)`.
pub(super) fn quasi_length_two_in_the_f8_tube() -> Module {
    let field = f2();
    let algebra = kronecker(2, field);
    let mut j = DenseMat::zero(6, 6);
    for (r, c) in [(0, 1), (1, 2), (2, 0), (2, 1)] {
        j.set(r, c, field.one());
        j.set(3 + r, 3 + c, field.one());
    }
    for r in 0..3 {
        j.set(r, 3 + r, field.one());
    }
    Module::new(algebra, vec![6, 6], vec![DenseMat::identity(6), j])
        .expect("the Kronecker representation is a module")
}

pub(super) fn simple_over_truncated_poly_3() -> IndecomposableModule {
    let algebra = truncated_poly(3, f5()).unwrap();
    indec(&Module::simple(&algebra, 0))
}

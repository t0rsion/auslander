use crate::algebra::Algebra;
use crate::certificate::RelationData;
use crate::field::{Fp, PrimeField};
use crate::linalg::DenseMat;
use crate::quiver::{ArrowId, PathWord, Quiver};
use crate::tilting::{ClassicalTiltingModule, ClassicalTiltingResult};
use crate::verify::verify_certificate;

use super::coordinate::{
    CoordinateAlgebra, CoordinateTargetData, ProductCounter, normal_word_images, path_image,
    radical_chain, target_paths, target_quiver,
};
use super::presentation::{idempotents, source_data};
use super::{TargetLimits, TargetWork, VerifiedTargetPresentation};

fn add_scaled_row(target: &mut [Fp], source: &[Fp], scale: Fp, field: &PrimeField) {
    for (out, &value) in target.iter_mut().zip(source) {
        *out = field.add(*out, field.mul(scale, value));
    }
}

fn relation_image<A: CoordinateAlgebra>(
    relation: &RelationData,
    quiver: &Quiver,
    idempotents: &[Vec<Fp>],
    arrows: &DenseMat,
    endo: &A,
) -> Option<Vec<Fp>> {
    let field = endo.field();
    let mut image = vec![Fp::ZERO; endo.dim()];
    for (coefficient, raw) in relation {
        let ids: Vec<ArrowId> = raw.iter().copied().map(ArrowId).collect();
        let path = PathWord::from_arrows(quiver, &ids).ok()?;
        let term = path_image(&path, idempotents, arrows, endo)?;
        add_scaled_row(&mut image, &term, field.elem(*coefficient as i64), &field);
    }
    Some(image)
}

fn same_algebra_data(left: &Algebra, right: &Algebra) -> bool {
    left.field() == right.field()
        && left.quiver() == right.quiver()
        && left.basis() == right.basis()
        && left.relations() == right.relations()
}

pub(super) fn verify_idempotents<A: CoordinateAlgebra>(endo: &A, ids: &[Vec<Fp>]) -> bool {
    let field = endo.field();
    let mut sum = vec![Fp::ZERO; endo.dim()];
    for (i, left) in ids.iter().enumerate() {
        add_scaled_row(&mut sum, left, Fp::ONE, &field);
        for (j, right) in ids.iter().enumerate() {
            let product = endo.multiply(left, right);
            if (i == j && product != *left)
                || (i != j && product.iter().any(|value| !value.is_zero()))
            {
                return false;
            }
        }
    }
    sum == endo.one()
}

fn unlimited_radical_chain<A: CoordinateAlgebra>(endo: &A) -> Option<(Vec<DenseMat>, usize)> {
    let mut products = ProductCounter {
        used: 0,
        limit: usize::MAX,
    };
    let powers = radical_chain(endo, &mut products).ok()?;
    powers
        .last()
        .is_some_and(|power| power.rows() == 0)
        .then_some((powers, products.used))
}

fn expected_arrow_images<A: CoordinateAlgebra>(
    endo: &A,
    ids: &[Vec<Fp>],
    powers: &[DenseMat],
) -> Option<(Quiver, DenseMat, usize)> {
    let mut products = ProductCounter {
        used: 0,
        limit: usize::MAX,
    };
    let built = target_quiver(endo, ids, powers, &mut products).ok()?;
    Some((built.quiver, built.arrow_images, products.used))
}

fn initial_coordinate_data_valid<A: CoordinateAlgebra>(
    endo: &A,
    ids: &[Vec<Fp>],
    limits: &TargetLimits,
    value: &CoordinateTargetData,
) -> bool {
    endo.dim().checked_mul(endo.dim()).is_some()
        && endo.dim() <= limits.max_endo_dimension
        && value.work.endo_dimension <= limits.max_endo_dimension
        && value.work.radical_products <= limits.max_radical_products
        && value.work.paths <= limits.max_paths
        && value.work.relation_terms <= limits.max_relation_terms
        && verify_idempotents(endo, ids)
        && value.idempotent_images
            == DenseMat::from_rows_with_cols(ids, value.normal_word_images.cols())
}

struct ExpectedCoordinateTarget {
    quiver: Quiver,
    arrows: DenseMat,
    radical_products: usize,
    paths: usize,
}

fn expected_coordinate_target<A: CoordinateAlgebra>(
    endo: &A,
    ids: &[Vec<Fp>],
    lambda: usize,
) -> Option<ExpectedCoordinateTarget> {
    let (powers, chain_products) = unlimited_radical_chain(endo)?;
    if powers.len() != lambda {
        return None;
    }
    let (quiver, arrows, corner_products) = expected_arrow_images(endo, ids, &powers)?;
    let radical_products = chain_products.checked_add(corner_products)?;
    let paths = target_paths(&quiver, &arrows, endo, powers.len(), usize::MAX).ok()?;
    Some(ExpectedCoordinateTarget {
        quiver,
        arrows,
        radical_products,
        paths: paths.count,
    })
}

fn recovered_structure_valid<A: CoordinateAlgebra>(
    endo: &A,
    ids: &[Vec<Fp>],
    value: &CoordinateTargetData,
) -> bool {
    let Some(expected) = expected_coordinate_target(endo, ids, value.radical_nilpotency_index)
    else {
        return false;
    };
    let work = TargetWork {
        endo_dimension: endo.dim(),
        radical_products: expected.radical_products,
        paths: expected.paths,
        relation_terms: value.completion.input_relations.iter().flatten().count(),
    };
    expected.quiver == *value.target.quiver()
        && expected.arrows == value.arrow_images
        && work == value.work
}

fn relations_vanish<A: CoordinateAlgebra>(
    value: &CoordinateTargetData,
    ids: &[Vec<Fp>],
    endo: &A,
) -> bool {
    value.completion.input_relations.iter().all(|relation| {
        relation_image(
            relation,
            value.target.quiver(),
            ids,
            &value.arrow_images,
            endo,
        )
        .is_some_and(|image| image.iter().all(|coefficient| coefficient.is_zero()))
    })
}

fn certificate_valid<A: CoordinateAlgebra>(
    endo: &A,
    ids: &[Vec<Fp>],
    limits: &TargetLimits,
    value: &CoordinateTargetData,
) -> bool {
    if value.completion != *value.target.certificate() {
        return false;
    }
    let Ok(completion) = verify_certificate(value.completion.clone()) else {
        return false;
    };
    let Ok(rebuilt) = Algebra::from_verified_with_limits(completion, &limits.completion) else {
        return false;
    };
    same_algebra_data(&rebuilt, &value.target) && relations_vanish(value, ids, endo)
}

fn coordinate_matrices_valid<A: CoordinateAlgebra>(
    endo: &A,
    ids: &[Vec<Fp>],
    value: &CoordinateTargetData,
) -> bool {
    let Some(images) = normal_word_images(&value.target, ids, &value.arrow_images, endo) else {
        return false;
    };
    let Some(preimages) = images.inverse(&endo.field()) else {
        return false;
    };
    if images != value.normal_word_images
        || preimages != value.normal_word_preimages
        || images.rows() != images.cols()
        || images.cols() != endo.dim()
    {
        return false;
    }
    let mut unit = vec![Fp::ZERO; endo.dim()];
    for vertex in 0..value.target.quiver().num_vertices() as usize {
        add_scaled_row(
            &mut unit,
            value.normal_word_images.row(vertex),
            Fp::ONE,
            &endo.field(),
        );
    }
    unit == endo.one()
}

fn multiplication_valid<A: CoordinateAlgebra>(endo: &A, value: &CoordinateTargetData) -> bool {
    for left in 0..value.target.dim() {
        for right in 0..value.target.dim() {
            let images = &value.normal_word_images;
            let mut expected = vec![Fp::ZERO; images.cols()];
            for (basis, coefficient) in value.target.mul_basis(left, right) {
                add_scaled_row(
                    &mut expected,
                    images.row(basis),
                    coefficient,
                    &value.target.field(),
                );
            }
            if endo.multiply(images.row(right), images.row(left)) != expected {
                return false;
            }
        }
    }
    true
}

pub(crate) fn verify_coordinate_target_data<A: CoordinateAlgebra>(
    endo: &A,
    ids: &[Vec<Fp>],
    limits: &TargetLimits,
    value: &CoordinateTargetData,
) -> bool {
    initial_coordinate_data_valid(endo, ids, limits, value)
        && recovered_structure_valid(endo, ids, value)
        && certificate_valid(endo, ids, limits, value)
        && coordinate_matrices_valid(endo, ids, value)
        && multiplication_valid(endo, value)
}

pub(crate) fn verify_target(value: &VerifiedTargetPresentation) -> bool {
    let Ok(ClassicalTiltingResult::Tilting(tilting)) =
        ClassicalTiltingModule::classify(&value.source, value.tilting_limits)
    else {
        return false;
    };
    if !tilting.verify()
        || !value.split.verify()
        || !value.split.total().ptr_eq(&value.source)
        || !value.endo.module().ptr_eq(&value.source)
    {
        return false;
    }
    let Ok((endo, decomposition, basic)) = source_data(&value.source) else {
        return false;
    };
    if basic
        .summands()
        .iter()
        .any(|summand| summand.residue_degree() != 1)
    {
        return false;
    }
    if decomposition.split().summands().len() != value.split.summands().len() {
        return false;
    }
    let ids = idempotents(&endo, decomposition.split());
    verify_coordinate_target_data(
        &endo,
        &ids,
        &value.limits,
        &CoordinateTargetData {
            target: value.target.clone(),
            completion: value.completion.clone(),
            idempotent_images: value.idempotent_images.clone(),
            arrow_images: value.arrow_images.clone(),
            normal_word_images: value.normal_word_images.clone(),
            normal_word_preimages: value.normal_word_preimages.clone(),
            radical_nilpotency_index: value.radical_nilpotency_index,
            work: value.work,
        },
    )
}

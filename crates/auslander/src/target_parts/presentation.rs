use crate::algebra::Algebra;
use crate::basic::BasicDecomposition;
use crate::decompose::{Decomposition, Split, decompose_with_root_endo};
use crate::endo::EndoAlgebra;
use crate::field::Fp;
use crate::linalg::DenseMat;
use crate::module::Module;
use crate::tilting::ClassicalTiltingModule;

use super::construction::{
    build_radical_chain, checked_target_paths, checked_target_relations, completed_target,
    target_defect,
};
use super::coordinate::{
    CoordinateAlgebra, CoordinateTargetData, CoordinateTargetOutcome, QuiverBuild,
    TargetErrorOrCut, normal_word_images,
};
use super::verification::verify_idempotents;
use super::{
    NonSplitTarget, TargetBudgetCut, TargetCutReason, TargetCutStage, TargetError, TargetLimits,
    TargetPresentationCut, TargetPresentationOutcome, TargetWork, VerifiedTargetPresentation,
};

pub(super) fn source_data(
    module: &Module,
) -> Result<(EndoAlgebra, Decomposition, BasicDecomposition), TargetError> {
    let endo = EndoAlgebra::new(module);
    let decomposition = decompose_with_root_endo(module, Some(endo.clone()));
    let basic = BasicDecomposition::from_decomposition(module, &decomposition)
        .map_err(TargetError::from)?;
    Ok((endo, decomposition, basic))
}

fn bounded_source_data(
    module: &Module,
    limit: usize,
) -> Result<(EndoAlgebra, Decomposition, BasicDecomposition), TargetErrorOrCut> {
    let endo = EndoAlgebra::new(module);
    endo.dim()
        .checked_mul(endo.dim())
        .ok_or(TargetError::SizeOverflow {
            stage: TargetCutStage::EndoDimension,
        })?;
    if endo.dim() > limit {
        return Err(TargetCutReason::Budget(TargetBudgetCut {
            stage: TargetCutStage::EndoDimension,
            used: 0,
            requested: endo.dim(),
            limit,
        })
        .into());
    }
    let decomposition = decompose_with_root_endo(module, Some(endo.clone()));
    let basic = BasicDecomposition::from_decomposition(module, &decomposition)
        .map_err(TargetError::from)?;
    Ok((endo, decomposition, basic))
}
pub(super) fn idempotents(endo: &EndoAlgebra, split: &Split) -> Vec<Vec<Fp>> {
    split
        .projections()
        .iter()
        .zip(split.inclusions())
        .map(|(projection, inclusion)| {
            endo.coords(
                &projection
                    .then(inclusion)
                    .expect("a split projection ends at its inclusion source"),
            )
        })
        .collect()
}
fn coordinate_matrices<A: CoordinateAlgebra>(
    target: &Algebra,
    ids: &[Vec<Fp>],
    arrows: &DenseMat,
    endo: &A,
) -> Result<(DenseMat, DenseMat), TargetErrorOrCut> {
    let Some(images) = normal_word_images(target, ids, arrows, endo) else {
        return Err(target_defect("a verified target normal word has no algebra image").into());
    };
    let Some(preimages) = images.inverse(&endo.field()) else {
        return Err(target_defect("the normal-word image matrix is singular").into());
    };
    Ok((images, preimages))
}

fn coordinate_target_data<A: CoordinateAlgebra>(
    endo: &A,
    ids: &[Vec<Fp>],
    limits: &TargetLimits,
) -> Result<CoordinateTargetData, TargetErrorOrCut> {
    endo.dim()
        .checked_mul(endo.dim())
        .ok_or(TargetError::SizeOverflow {
            stage: TargetCutStage::EndoDimension,
        })?;
    if endo.dim() > limits.max_endo_dimension {
        return Err(TargetCutReason::Budget(TargetBudgetCut {
            stage: TargetCutStage::EndoDimension,
            used: 0,
            requested: endo.dim(),
            limit: limits.max_endo_dimension,
        })
        .into());
    }
    if !verify_idempotents(endo, ids) {
        return Err(target_defect("the coordinate idempotents do not form the identity").into());
    }
    let (powers, mut products) = build_radical_chain(endo, limits.max_radical_products)?;
    let (quiver_build, paths) = checked_target_paths(endo, ids, &powers, &mut products, limits)?;
    let square_dim = powers.get(1).map_or(0, DenseMat::rows);
    let (relations, relation_terms) = checked_target_relations(
        &quiver_build.quiver,
        endo.field(),
        endo.dim(),
        &paths,
        square_dim,
        limits.max_relation_terms,
    )?;
    let QuiverBuild {
        quiver,
        arrow_images,
    } = quiver_build;
    let target = completed_target(quiver, endo.field(), relations, &limits.completion)?;
    let (images, preimages) = coordinate_matrices(&target, ids, &arrow_images, endo)?;
    let completion = target.certificate().clone();
    Ok(CoordinateTargetData {
        target,
        completion,
        idempotent_images: DenseMat::from_rows_with_cols(ids, images.cols()),
        arrow_images,
        normal_word_images: images,
        normal_word_preimages: preimages,
        radical_nilpotency_index: powers.len(),
        work: TargetWork {
            endo_dimension: endo.dim(),
            radical_products: products.used,
            paths: paths.count,
            relation_terms,
        },
    })
}

pub(crate) fn recover_coordinate_target<A: CoordinateAlgebra>(
    endo: &A,
    ids: &[Vec<Fp>],
    limits: &TargetLimits,
) -> Result<CoordinateTargetOutcome, TargetError> {
    match coordinate_target_data(endo, ids, limits) {
        Ok(value) => Ok(CoordinateTargetOutcome::Presented(Box::new(value))),
        Err(TargetErrorOrCut::Cut(reason)) => Ok(CoordinateTargetOutcome::Cut(reason)),
        Err(TargetErrorOrCut::Error(error)) => Err(error),
    }
}

/// Recovers and verifies the split target presentation of `tilting`.
pub fn present_target(
    tilting: &ClassicalTiltingModule,
    limits: &TargetLimits,
) -> Result<TargetPresentationOutcome, TargetError> {
    let module = tilting.module();
    let wrap_cut = |reason| {
        TargetPresentationOutcome::Cut(TargetPresentationCut {
            source: module.clone(),
            tilting_limits: tilting.limits(),
            limits: limits.clone(),
            reason,
        })
    };
    let (endo, decomposition, basic) = match bounded_source_data(module, limits.max_endo_dimension)
    {
        Ok(value) => value,
        Err(TargetErrorOrCut::Cut(reason)) => return Ok(wrap_cut(reason)),
        Err(TargetErrorOrCut::Error(error)) => return Err(error),
    };
    if let Some((summand, non_split)) = basic
        .summands()
        .iter()
        .enumerate()
        .find(|(_, summand)| summand.residue_degree() != 1)
    {
        return Ok(TargetPresentationOutcome::Unsupported(NonSplitTarget {
            module: module.clone(),
            tilting_limits: tilting.limits(),
            limits: limits.clone(),
            summand,
            residue_degree: non_split.residue_degree(),
        }));
    }
    let split = decomposition.split().clone();
    let ids = idempotents(&endo, &split);
    let data = match recover_coordinate_target(&endo, &ids, limits)? {
        CoordinateTargetOutcome::Presented(data) => data,
        CoordinateTargetOutcome::Cut(reason) => return Ok(wrap_cut(reason)),
    };
    let verified = VerifiedTargetPresentation {
        source: module.clone(),
        tilting_limits: tilting.limits(),
        limits: limits.clone(),
        completion: data.completion,
        target: data.target,
        endo,
        split,
        idempotent_images: data.idempotent_images,
        arrow_images: data.arrow_images,
        normal_word_images: data.normal_word_images,
        normal_word_preimages: data.normal_word_preimages,
        radical_nilpotency_index: data.radical_nilpotency_index,
        work: data.work,
    };
    if !verified.verify() {
        return Err(TargetError::Defect {
            reason: "the independent target verifier rejected the recovered presentation"
                .to_string(),
        });
    }
    Ok(TargetPresentationOutcome::Presented(verified))
}

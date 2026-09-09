use std::sync::Arc;

use crate::algebra::{Algebra, AlgebraBuildError};
use crate::completion::CompletionLimits;
use crate::field::{Fp, PrimeField};
use crate::linalg::DenseMat;
use crate::quiver::Quiver;
use crate::relation::{Presentation, Relation};

use super::coordinate::{
    CoordinateAlgebra, PathBuild, ProductCounter, QuiverBuild, TargetErrorOrCut, radical_chain,
    target_paths, target_quiver, target_relations,
};
use super::{TargetCutReason, TargetError, TargetLimits};

pub(super) fn target_defect(reason: &str) -> TargetError {
    TargetError::Defect {
        reason: reason.to_string(),
    }
}

pub(super) fn build_radical_chain<A: CoordinateAlgebra>(
    endo: &A,
    limit: usize,
) -> Result<(Vec<DenseMat>, ProductCounter), TargetErrorOrCut> {
    let mut products = ProductCounter { used: 0, limit };
    let powers = radical_chain(endo, &mut products)?;
    if powers.last().is_none_or(|power| power.rows() != 0) {
        return Err(
            target_defect("the endomorphism radical power chain did not reach zero").into(),
        );
    }
    Ok((powers, products))
}

pub(super) fn checked_target_paths<A: CoordinateAlgebra>(
    endo: &A,
    ids: &[Vec<Fp>],
    powers: &[DenseMat],
    products: &mut ProductCounter,
    limits: &TargetLimits,
) -> Result<(QuiverBuild, PathBuild), TargetErrorOrCut> {
    let quiver_build = target_quiver(endo, ids, powers, products)?;
    let paths = target_paths(
        &quiver_build.quiver,
        &quiver_build.arrow_images,
        endo,
        powers.len(),
        limits.max_paths,
    )?;
    let square_dim = powers.get(1).map_or(0, DenseMat::rows);
    if paths.count < square_dim {
        return Err(
            target_defect("the length-at-least-two path images do not span rad(E)^2").into(),
        );
    }
    Ok((quiver_build, paths))
}

pub(super) fn checked_target_relations(
    quiver: &Quiver,
    field: PrimeField,
    endo_dim: usize,
    paths: &PathBuild,
    square_dim: usize,
    limit: usize,
) -> Result<(Vec<Relation>, usize), TargetErrorOrCut> {
    let (relations, relation_terms) = target_relations(quiver, field, endo_dim, paths, limit)?;
    if relations.len() != paths.count - square_dim {
        return Err(target_defect("the relation count disagrees with the rank of rad(E)^2").into());
    }
    Ok((relations, relation_terms))
}

pub(super) fn completed_target(
    quiver: Quiver,
    field: PrimeField,
    relations: Vec<Relation>,
    limits: &CompletionLimits,
) -> Result<Arc<Algebra>, TargetErrorOrCut> {
    let presentation = Presentation::new(quiver, field, relations)?;
    match Algebra::new(presentation, limits) {
        Ok(value) => Ok(value),
        Err(AlgebraBuildError::Truncated(diagnostics)) => {
            Err(TargetCutReason::Completion(diagnostics).into())
        }
        Err(error) => Err(TargetError::Algebra(error).into()),
    }
}

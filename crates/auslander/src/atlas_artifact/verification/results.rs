use crate::atlas::{CatalogAtlas, MultiplicityCut, MultiplicityCutReason, MultiplicityOutcome};

use super::super::errors::CatalogAtlasArtifactError;
use super::super::model::{
    CatalogAtlasArtifact, CatalogAtlasArtifactResultRow, CatalogAtlasArtifactStatus,
    CatalogAtlasArtifactVerifyLimits,
};
use super::check_limit;

pub(super) fn check_multiplicity_results(
    artifact: &CatalogAtlasArtifact,
    atlas: &CatalogAtlas,
    limits: CatalogAtlasArtifactVerifyLimits,
) -> Result<(), CatalogAtlasArtifactError> {
    let outcome = atlas
        .enumerate_multiplicities(&artifact.target_dimensions, artifact.multiplicity_limits)?;
    match (&artifact.status, &outcome) {
        (CatalogAtlasArtifactStatus::Complete, MultiplicityOutcome::Cut(_)) => {
            Err(CatalogAtlasArtifactError::ReplayMismatch {
                field: "status upgraded to complete".to_string(),
            })
        }
        (CatalogAtlasArtifactStatus::Cut { .. }, MultiplicityOutcome::Complete(_)) => {
            Err(CatalogAtlasArtifactError::ReplayMismatch {
                field: "status cut coverage".to_string(),
            })
        }
        (CatalogAtlasArtifactStatus::Complete, MultiplicityOutcome::Complete(rows)) => {
            compare_result_rows(artifact, atlas, rows.solutions(), limits)
        }
        (
            CatalogAtlasArtifactStatus::Cut {
                reason,
                coverage,
                nodes_visited,
            },
            MultiplicityOutcome::Cut(cut),
        ) => check_cut_outcome(
            artifact,
            atlas,
            *reason,
            *coverage,
            *nodes_visited,
            cut,
            limits,
        ),
    }
}

fn check_cut_outcome(
    artifact: &CatalogAtlasArtifact,
    atlas: &CatalogAtlas,
    reason: MultiplicityCutReason,
    coverage: usize,
    nodes_visited: usize,
    cut: &MultiplicityCut,
    limits: CatalogAtlasArtifactVerifyLimits,
) -> Result<(), CatalogAtlasArtifactError> {
    if cut.reason() != reason
        || cut.nodes_visited() != nodes_visited
        || cut.solutions().len() != coverage
    {
        return Err(CatalogAtlasArtifactError::ReplayMismatch {
            field: "cut status".to_string(),
        });
    }
    compare_result_rows(artifact, atlas, cut.solutions(), limits)
}

fn compare_result_rows(
    artifact: &CatalogAtlasArtifact,
    atlas: &CatalogAtlas,
    expected: &[Vec<usize>],
    limits: CatalogAtlasArtifactVerifyLimits,
) -> Result<(), CatalogAtlasArtifactError> {
    if artifact.result_rows.len() != expected.len() {
        return Err(CatalogAtlasArtifactError::ReplayMismatch {
            field: "result row coverage".to_string(),
        });
    }
    for (index, (stored, multiplicities)) in artifact.result_rows.iter().zip(expected).enumerate() {
        check_result_row(artifact, atlas, index, stored, multiplicities, limits)?;
    }
    Ok(())
}

fn check_result_row(
    artifact: &CatalogAtlasArtifact,
    atlas: &CatalogAtlas,
    index: usize,
    stored: &CatalogAtlasArtifactResultRow,
    multiplicities: &[usize],
    limits: CatalogAtlasArtifactVerifyLimits,
) -> Result<(), CatalogAtlasArtifactError> {
    if stored.multiplicities() != multiplicities {
        return Err(CatalogAtlasArtifactError::ReplayMismatch {
            field: "multiplicity rows".to_string(),
        });
    }
    check_vector_dimension(atlas, multiplicities, &artifact.target_dimensions)?;
    let scores = atlas.self_ext_scores(multiplicities, 0, artifact.max_degree())?;
    if stored.self_ext() != scores {
        return Err(CatalogAtlasArtifactError::ReplayMismatch {
            field: "self-Ext result rows".to_string(),
        });
    }
    check_limit("result row", index, limits.max_result_rows)
}

fn check_vector_dimension(
    atlas: &CatalogAtlas,
    multiplicities: &[usize],
    target: &[usize],
) -> Result<(), CatalogAtlasArtifactError> {
    if multiplicities.len() != atlas.catalog().len() {
        return Err(CatalogAtlasArtifactError::CountMismatch {
            field: "multiplicity vector".to_string(),
        });
    }
    let mut dimensions = vec![0usize; target.len()];
    for (&multiplicity, entry) in multiplicities.iter().zip(atlas.catalog().entries()) {
        accumulate_entry_dimension(&mut dimensions, multiplicity, entry.module().dim_vector())?;
    }
    if dimensions != target {
        return Err(CatalogAtlasArtifactError::ReplayMismatch {
            field: "target dimensions".to_string(),
        });
    }
    Ok(())
}

fn accumulate_entry_dimension(
    dimensions: &mut [usize],
    multiplicity: usize,
    entry_dimensions: &[usize],
) -> Result<(), CatalogAtlasArtifactError> {
    for (vertex, &dimension) in entry_dimensions.iter().enumerate() {
        let product =
            multiplicity
                .checked_mul(dimension)
                .ok_or(CatalogAtlasArtifactError::Overflow {
                    field: "multiplicity dimension",
                })?;
        dimensions[vertex] =
            dimensions[vertex]
                .checked_add(product)
                .ok_or(CatalogAtlasArtifactError::Overflow {
                    field: "target dimension",
                })?;
    }
    Ok(())
}

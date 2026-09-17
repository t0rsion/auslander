use std::sync::Arc;

use crate::arquiver::IndecomposableCatalog;
use crate::atlas::{CatalogAtlas, CatalogExtRow};
use crate::ext::ExtSpace;
use crate::indec::IndecomposableModule;

use super::super::errors::CatalogAtlasArtifactError;
use super::super::model::{
    CatalogAtlasArtifact, CatalogAtlasArtifactExtRow, CatalogAtlasArtifactVerifyLimits,
};
use super::check_limit;

pub(super) fn check_catalog(
    artifact: &CatalogAtlasArtifact,
    catalog: &Arc<IndecomposableCatalog>,
    limits: CatalogAtlasArtifactVerifyLimits,
) -> Result<(), CatalogAtlasArtifactError> {
    if catalog.provenance() != artifact.provenance {
        return Err(CatalogAtlasArtifactError::ReplayMismatch {
            field: "provenance".to_string(),
        });
    }
    if catalog.algebra().field().modulus() != artifact.field {
        return Err(CatalogAtlasArtifactError::FieldMismatch {
            certificate: catalog.algebra().field().modulus(),
            artifact: artifact.field,
        });
    }
    if catalog.len() != artifact.catalog_ids.len() {
        return Err(CatalogAtlasArtifactError::CountMismatch {
            field: "catalog_ids".to_string(),
        });
    }
    for (index, &identifier) in artifact.catalog_ids.iter().enumerate() {
        check_catalog_entry(index, identifier, catalog.entries()[index].as_ref(), limits)?;
    }
    if artifact.target_dimensions.len() != catalog.algebra().quiver().num_vertices() as usize {
        return Err(CatalogAtlasArtifactError::CountMismatch {
            field: "target_dimensions".to_string(),
        });
    }
    Ok(())
}

fn check_catalog_entry(
    index: usize,
    identifier: usize,
    entry: &IndecomposableModule,
    limits: CatalogAtlasArtifactVerifyLimits,
) -> Result<(), CatalogAtlasArtifactError> {
    if identifier != index {
        return Err(CatalogAtlasArtifactError::ReplayMismatch {
            field: "catalog_ids".to_string(),
        });
    }
    check_limit("catalog entry", index, limits.max_catalog_entries)?;
    check_limit(
        "catalog entry dimension",
        entry
            .module()
            .dim_vector()
            .iter()
            .copied()
            .max()
            .unwrap_or(0),
        limits.max_dimension,
    )?;
    check_limit(
        "catalog entry total dimension",
        entry.module().total_dim(),
        limits.max_entry_total_dimension,
    )
}

pub(super) fn check_optimized_table(
    artifact: &CatalogAtlasArtifact,
    atlas: &CatalogAtlas,
) -> Result<(), CatalogAtlasArtifactError> {
    if atlas.work() != artifact.work
        || atlas.max_degree() != artifact.max_degree
        || atlas.limits() != artifact.atlas_limits
    {
        return Err(CatalogAtlasArtifactError::ReplayMismatch {
            field: "atlas metadata".to_string(),
        });
    }
    for (index, row) in atlas.ext_table().rows().iter().enumerate() {
        let Some(stored) = artifact.ext_rows.get(index) else {
            return Err(CatalogAtlasArtifactError::CountMismatch {
                field: "ext_rows".to_string(),
            });
        };
        check_optimized_row(row, stored)?;
    }
    Ok(())
}

fn check_optimized_row(
    rebuilt: &CatalogExtRow,
    stored: &CatalogAtlasArtifactExtRow,
) -> Result<(), CatalogAtlasArtifactError> {
    if rebuilt.source() != stored.source()
        || rebuilt.target() != stored.target()
        || rebuilt.dimensions() != stored.dimensions()
    {
        return Err(CatalogAtlasArtifactError::ReplayMismatch {
            field: "ext_rows".to_string(),
        });
    }
    Ok(())
}

pub(super) fn check_generic_table(
    artifact: &CatalogAtlasArtifact,
    catalog: &Arc<IndecomposableCatalog>,
) -> Result<(), CatalogAtlasArtifactError> {
    for (source, source_entry) in catalog.entries().iter().enumerate() {
        for (target, target_entry) in catalog.entries().iter().enumerate() {
            check_generic_row(
                artifact,
                catalog.len(),
                source,
                target,
                source_entry.as_ref(),
                target_entry.as_ref(),
            )?;
        }
    }
    Ok(())
}

fn check_generic_row(
    artifact: &CatalogAtlasArtifact,
    catalog_len: usize,
    source: usize,
    target: usize,
    source_entry: &IndecomposableModule,
    target_entry: &IndecomposableModule,
) -> Result<(), CatalogAtlasArtifactError> {
    let dimensions = generic_row_dimensions(artifact, catalog_len, source, target)?;
    for (degree, &stored) in dimensions.iter().enumerate() {
        let space = ExtSpace::new(source_entry.module(), target_entry.module(), degree)?;
        if space.dim() != stored {
            return Err(CatalogAtlasArtifactError::ReplayMismatch {
                field: "generic Ext cells".to_string(),
            });
        }
    }
    Ok(())
}

fn generic_row_dimensions(
    artifact: &CatalogAtlasArtifact,
    catalog_len: usize,
    source: usize,
    target: usize,
) -> Result<&[usize], CatalogAtlasArtifactError> {
    let row_index = source
        .checked_mul(catalog_len)
        .and_then(|index| index.checked_add(target))
        .ok_or(CatalogAtlasArtifactError::Overflow { field: "Ext row" })?;
    let row = artifact.ext_rows.get(row_index).ok_or_else(|| {
        CatalogAtlasArtifactError::CountMismatch {
            field: "ext_rows".to_string(),
        }
    })?;
    if row.source() != source || row.target() != target {
        return Err(CatalogAtlasArtifactError::ReplayMismatch {
            field: "ext row identifiers".to_string(),
        });
    }
    Ok(row.dimensions())
}

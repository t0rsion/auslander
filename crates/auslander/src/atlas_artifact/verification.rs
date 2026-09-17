use std::sync::Arc;

use crate::algebra::Algebra;
use crate::arquiver::{CatalogProvenance, IndecomposableCatalog};
use crate::atlas::{CatalogAtlas, CatalogAtlasLimits};
use crate::certificate::QuiverData;
use crate::dynkin::dynkin_type;
use crate::field::PrimeField;
use crate::quiver::Quiver;
use crate::verify::verify;

use super::errors::CatalogAtlasArtifactError;
use super::model::{
    CatalogAtlasArtifact, CatalogAtlasArtifactExtRow, CatalogAtlasArtifactResultRow,
    CatalogAtlasArtifactStatus, CatalogAtlasArtifactVerifyLimits, VerifiedCatalogAtlasArtifact,
};

#[path = "verification/catalog.rs"]
mod catalog;
#[path = "verification/results.rs"]
mod results;

use catalog::{check_catalog, check_generic_table, check_optimized_table};
use results::check_multiplicity_results;

/// Parses and verifies one catalog atlas artifact.
pub fn verify_catalog_atlas_artifact(
    text: &str,
    limits: CatalogAtlasArtifactVerifyLimits,
) -> Result<VerifiedCatalogAtlasArtifact, CatalogAtlasArtifactError> {
    let artifact = CatalogAtlasArtifact::from_json(text, limits.parse)?;
    artifact.verify(limits)
}

impl CatalogAtlasArtifact {
    /// Rebuilds the certificate, catalog, Ext table, and full result sequence.
    pub fn verify(
        &self,
        limits: CatalogAtlasArtifactVerifyLimits,
    ) -> Result<VerifiedCatalogAtlasArtifact, CatalogAtlasArtifactError> {
        preflight(self, limits)?;
        let certificate_text = self.certificate.to_canonical_json();
        let verified = verify(&certificate_text)?;
        let algebra = Algebra::from_verified(verified)?;
        let catalog = Arc::new(rebuild_catalog(self.provenance, &algebra)?);
        check_catalog(self, &catalog, limits)?;
        let atlas = CatalogAtlas::compute(catalog.clone(), self.max_degree, self.atlas_limits)?;
        check_optimized_table(self, &atlas)?;
        check_generic_table(self, &catalog)?;
        check_multiplicity_results(self, &atlas, limits)?;
        Ok(VerifiedCatalogAtlasArtifact {
            artifact: self.clone(),
            algebra,
            catalog,
            atlas,
        })
    }
}

fn preflight(
    artifact: &CatalogAtlasArtifact,
    limits: CatalogAtlasArtifactVerifyLimits,
) -> Result<(), CatalogAtlasArtifactError> {
    check_certificate_budget(artifact, limits)?;
    check_field_and_degree(artifact, limits)?;
    check_catalog_budget(artifact, limits)?;
    check_target_budget(artifact, limits)?;
    check_atlas_limits(artifact.atlas_limits, limits)?;
    check_multiplicity_limits(artifact, limits)?;
    let plan = WorkPlan::new(artifact.catalog_ids.len(), artifact.max_degree)?;
    check_work_budget(artifact, &plan, limits)?;
    check_rows_shape(artifact, artifact.catalog_ids.len(), plan.degrees, limits)
}
fn check_field_and_degree(
    artifact: &CatalogAtlasArtifact,
    limits: CatalogAtlasArtifactVerifyLimits,
) -> Result<(), CatalogAtlasArtifactError> {
    if artifact.certificate.field != artifact.field {
        return Err(CatalogAtlasArtifactError::FieldMismatch {
            certificate: artifact.certificate.field,
            artifact: artifact.field,
        });
    }
    PrimeField::new(artifact.field)?;
    check_limit("max_degree", artifact.max_degree, limits.max_degree)
}
fn check_certificate_budget(
    artifact: &CatalogAtlasArtifact,
    limits: CatalogAtlasArtifactVerifyLimits,
) -> Result<(), CatalogAtlasArtifactError> {
    check_limit(
        "certificate_bytes",
        artifact.certificate.to_canonical_json().len(),
        limits.parse.max_certificate_bytes,
    )?;
    check_limit(
        "vertices",
        artifact.certificate.quiver.vertices as usize,
        limits.max_vertices,
    )?;
    check_limit(
        "arrows",
        artifact.certificate.quiver.arrows.len(),
        limits.max_arrows,
    )?;
    check_limit(
        "algebra_dimension",
        artifact.certificate.normal_words.len(),
        limits.max_algebra_dimension,
    )
}
fn check_catalog_budget(
    artifact: &CatalogAtlasArtifact,
    limits: CatalogAtlasArtifactVerifyLimits,
) -> Result<(), CatalogAtlasArtifactError> {
    check_limit(
        "catalog_entries",
        artifact.catalog_ids.len(),
        limits.max_catalog_entries,
    )?;
    let catalog_upper = catalog_upper_bound(
        artifact.provenance,
        &artifact.certificate.quiver,
        artifact.certificate.normal_words.len(),
    )?;
    check_limit(
        "catalog construction",
        catalog_upper,
        limits.max_catalog_entries,
    )
}

fn check_atlas_limits(
    declared: CatalogAtlasLimits,
    limits: CatalogAtlasArtifactVerifyLimits,
) -> Result<(), CatalogAtlasArtifactError> {
    for (field, declared, limit) in [
        ("atlas.max_pairs", declared.max_pairs, limits.max_pairs),
        (
            "atlas.max_ext_cells",
            declared.max_ext_cells,
            limits.max_ext_cells,
        ),
        (
            "atlas.max_resolution_terms",
            declared.max_resolution_terms,
            limits.max_resolution_terms,
        ),
        (
            "atlas.max_materialized_summands",
            declared.max_materialized_summands,
            limits.max_materialized_summands,
        ),
        (
            "atlas.max_materialized_cells",
            declared.max_materialized_cells,
            limits.max_materialized_cells,
        ),
    ] {
        check_limit(field, declared, limit)?;
    }
    Ok(())
}
#[derive(Clone, Copy)]
struct WorkPlan {
    pairs: usize,
    degrees: usize,
    ext_cells: usize,
    resolution_terms: usize,
}

impl WorkPlan {
    fn new(entries: usize, max_degree: usize) -> Result<Self, CatalogAtlasArtifactError> {
        let pairs = entries
            .checked_mul(entries)
            .ok_or(CatalogAtlasArtifactError::Overflow { field: "pairs" })?;
        let degrees = max_degree
            .checked_add(1)
            .ok_or(CatalogAtlasArtifactError::Overflow {
                field: "degree cells",
            })?;
        let ext_cells = pairs
            .checked_mul(degrees)
            .ok_or(CatalogAtlasArtifactError::Overflow { field: "Ext cells" })?;
        let terms_per_source =
            degrees
                .checked_add(1)
                .ok_or(CatalogAtlasArtifactError::Overflow {
                    field: "resolution terms",
                })?;
        let resolution_terms =
            entries
                .checked_mul(terms_per_source)
                .ok_or(CatalogAtlasArtifactError::Overflow {
                    field: "resolution terms",
                })?;
        Ok(Self {
            pairs,
            degrees,
            ext_cells,
            resolution_terms,
        })
    }
}

fn check_work_budget(
    artifact: &CatalogAtlasArtifact,
    plan: &WorkPlan,
    limits: CatalogAtlasArtifactVerifyLimits,
) -> Result<(), CatalogAtlasArtifactError> {
    check_caller_work_limits(artifact, plan, limits)?;
    for (field, planned, declared) in [
        (
            "atlas planned pairs",
            plan.pairs,
            artifact.atlas_limits.max_pairs,
        ),
        (
            "atlas planned Ext cells",
            plan.ext_cells,
            artifact.atlas_limits.max_ext_cells,
        ),
        (
            "atlas planned resolution terms",
            plan.resolution_terms,
            artifact.atlas_limits.max_resolution_terms,
        ),
    ] {
        check_limit(field, planned, declared)?;
    }
    check_work_shape(artifact, plan)
}

fn check_caller_work_limits(
    artifact: &CatalogAtlasArtifact,
    plan: &WorkPlan,
    limits: CatalogAtlasArtifactVerifyLimits,
) -> Result<(), CatalogAtlasArtifactError> {
    check_limit("pairs", plan.pairs, limits.max_pairs)?;
    check_limit("Ext cells", plan.ext_cells, limits.max_ext_cells)?;
    check_limit(
        "generic Ext cells",
        plan.ext_cells,
        limits.max_generic_ext_cells,
    )?;
    check_limit(
        "resolution terms",
        artifact.work.resolution_terms,
        limits.max_resolution_terms,
    )?;
    check_limit(
        "atlas resolution terms",
        plan.resolution_terms,
        limits.max_resolution_terms,
    )
}

fn check_work_shape(
    artifact: &CatalogAtlasArtifact,
    plan: &WorkPlan,
) -> Result<(), CatalogAtlasArtifactError> {
    if artifact.ext_rows.len() != plan.pairs {
        return Err(CatalogAtlasArtifactError::CountMismatch {
            field: "ext_rows".to_string(),
        });
    }
    if artifact.work.pairs != plan.pairs
        || artifact.work.ext_cells != plan.ext_cells
        || artifact.work.resolutions != artifact.catalog_ids.len()
        || artifact.work.ext_tables != plan.pairs
        || artifact.work.resolution_terms > plan.resolution_terms
    {
        return Err(CatalogAtlasArtifactError::CountMismatch {
            field: "work".to_string(),
        });
    }
    Ok(())
}

fn check_multiplicity_limits(
    artifact: &CatalogAtlasArtifact,
    limits: CatalogAtlasArtifactVerifyLimits,
) -> Result<(), CatalogAtlasArtifactError> {
    check_limit(
        "multiplicity.max_solutions",
        artifact.multiplicity_limits.max_solutions,
        limits.max_result_rows,
    )?;
    check_limit(
        "multiplicity.max_nodes",
        artifact.multiplicity_limits.max_nodes,
        limits.max_nodes,
    )?;
    if let CatalogAtlasArtifactStatus::Cut {
        coverage,
        nodes_visited,
        ..
    } = artifact.status
    {
        check_limit("status.coverage", coverage, limits.max_result_rows)?;
        check_limit("status.nodes_visited", nodes_visited, limits.max_nodes)?;
    }
    Ok(())
}

fn check_target_budget(
    artifact: &CatalogAtlasArtifact,
    limits: CatalogAtlasArtifactVerifyLimits,
) -> Result<(), CatalogAtlasArtifactError> {
    check_limit(
        "target_dimensions",
        artifact.target_dimensions.len(),
        limits.max_vertices,
    )?;
    for &dimension in &artifact.target_dimensions {
        check_limit("target dimension", dimension, limits.max_dimension)?;
    }
    Ok(())
}

fn check_rows_shape(
    artifact: &CatalogAtlasArtifact,
    entries: usize,
    degrees: usize,
    limits: CatalogAtlasArtifactVerifyLimits,
) -> Result<(), CatalogAtlasArtifactError> {
    check_ext_rows_shape(&artifact.ext_rows, entries, degrees, limits)?;
    check_result_rows_shape(&artifact.result_rows, entries, degrees, limits)?;
    check_status_shape(artifact)
}

fn check_ext_rows_shape(
    rows: &[CatalogAtlasArtifactExtRow],
    entries: usize,
    degrees: usize,
    limits: CatalogAtlasArtifactVerifyLimits,
) -> Result<(), CatalogAtlasArtifactError> {
    for row in rows {
        if row.source() >= entries || row.target() >= entries {
            return Err(CatalogAtlasArtifactError::ReplayMismatch {
                field: "ext row identifiers".to_string(),
            });
        }
        if row.dimensions().len() != degrees {
            return Err(CatalogAtlasArtifactError::CountMismatch {
                field: "ext_rows[].dimensions".to_string(),
            });
        }
        for &dimension in row.dimensions() {
            check_limit("Ext dimension", dimension, limits.max_dimension)?;
        }
    }
    Ok(())
}

fn check_result_rows_shape(
    rows: &[CatalogAtlasArtifactResultRow],
    entries: usize,
    degrees: usize,
    limits: CatalogAtlasArtifactVerifyLimits,
) -> Result<(), CatalogAtlasArtifactError> {
    for row in rows {
        if row.multiplicities().len() != entries || row.self_ext().len() != degrees {
            return Err(CatalogAtlasArtifactError::CountMismatch {
                field: "result_rows".to_string(),
            });
        }
        for &multiplicity in row.multiplicities() {
            check_limit("multiplicity", multiplicity, limits.max_multiplicity)?;
        }
        for &score in row.self_ext() {
            check_limit("self-Ext score", score, limits.max_dimension)?;
        }
    }
    Ok(())
}

fn check_status_shape(artifact: &CatalogAtlasArtifact) -> Result<(), CatalogAtlasArtifactError> {
    if let CatalogAtlasArtifactStatus::Cut { coverage, .. } = artifact.status
        && coverage != artifact.result_rows.len()
    {
        return Err(CatalogAtlasArtifactError::CountMismatch {
            field: "status.coverage".to_string(),
        });
    }
    Ok(())
}

fn rebuild_catalog(
    provenance: CatalogProvenance,
    algebra: &Arc<Algebra>,
) -> Result<IndecomposableCatalog, CatalogAtlasArtifactError> {
    match provenance {
        CatalogProvenance::Nakayama => IndecomposableCatalog::nakayama(algebra)
            .map_err(|error| catalog_error("nakayama", error.to_string())),
        CatalogProvenance::DynkinZeroIdeal => IndecomposableCatalog::dynkin(algebra)
            .map_err(|error| catalog_error("dynkin", error.to_string())),
        CatalogProvenance::GentleTree => IndecomposableCatalog::gentle_tree(algebra)
            .map_err(|error| catalog_error("gentle tree", error.to_string())),
    }
}

fn catalog_error(route: &str, message: String) -> CatalogAtlasArtifactError {
    CatalogAtlasArtifactError::Catalog {
        message: format!("{route} route: {message}"),
    }
}

fn catalog_upper_bound(
    provenance: CatalogProvenance,
    quiver_data: &QuiverData,
    algebra_dimension: usize,
) -> Result<usize, CatalogAtlasArtifactError> {
    let vertices = quiver_data.vertices as usize;
    match provenance {
        CatalogProvenance::DynkinZeroIdeal => dynkin_catalog_bound(quiver_data, vertices),
        CatalogProvenance::Nakayama => Ok(algebra_dimension),
        CatalogProvenance::GentleTree => gentle_catalog_bound(vertices),
    }
}

fn dynkin_catalog_bound(
    quiver_data: &QuiverData,
    vertices: usize,
) -> Result<usize, CatalogAtlasArtifactError> {
    let quiver = Quiver::new(quiver_data.vertices, &quiver_data.arrows)
        .map_err(|error| catalog_error("quiver", error.to_string()))?;
    let Some(count) = dynkin_type(&quiver).and_then(|kind| kind.indecomposable_count()) else {
        return safe_dynkin_bound(vertices);
    };
    Ok(count)
}

fn gentle_catalog_bound(vertices: usize) -> Result<usize, CatalogAtlasArtifactError> {
    vertices
        .checked_add(1)
        .and_then(|successor| vertices.checked_mul(successor))
        .map(|product| product / 2)
        .ok_or(CatalogAtlasArtifactError::Overflow {
            field: "gentle catalog bound",
        })
}

fn safe_dynkin_bound(vertices: usize) -> Result<usize, CatalogAtlasArtifactError> {
    vertices
        .checked_mul(vertices)
        .and_then(|square| square.checked_mul(2))
        .ok_or(CatalogAtlasArtifactError::Overflow {
            field: "Dynkin catalog bound",
        })
}

fn check_limit(
    field: &'static str,
    declared: usize,
    limit: usize,
) -> Result<(), CatalogAtlasArtifactError> {
    if declared > limit {
        return Err(CatalogAtlasArtifactError::VerificationLimit {
            field,
            declared,
            limit,
        });
    }
    Ok(())
}

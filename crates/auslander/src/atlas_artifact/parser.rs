use crate::atlas::{
    CatalogAtlasLimits, CatalogAtlasWork, MultiplicityCutReason, MultiplicityLimits,
};
use crate::portable::{Cursor, CursorLimits};

use super::errors::CatalogAtlasArtifactError;
use super::model::{
    CatalogAtlasArtifactExtRow, CatalogAtlasArtifactParseLimits, CatalogAtlasArtifactResultRow,
    CatalogAtlasArtifactStatus,
};
use super::{
    CATALOG_ATLAS_ARTIFACT_ENGINE, CATALOG_ATLAS_ARTIFACT_KIND, CATALOG_ATLAS_ARTIFACT_SCHEMA,
};

type AtlasParse<T> = Result<T, CatalogAtlasArtifactError>;

pub(super) struct RawArtifact {
    pub(super) certificate: String,
    pub(super) field: u64,
    pub(super) provenance: String,
    pub(super) catalog_ids: Vec<usize>,
    pub(super) target_dimensions: Vec<usize>,
    pub(super) max_degree: usize,
    pub(super) atlas_limits: CatalogAtlasLimits,
    pub(super) multiplicity_limits: MultiplicityLimits,
    pub(super) work: CatalogAtlasWork,
    pub(super) ext_rows: Vec<CatalogAtlasArtifactExtRow>,
    pub(super) result_rows: Vec<CatalogAtlasArtifactResultRow>,
    pub(super) status: CatalogAtlasArtifactStatus,
    pub(super) fingerprint: String,
}

struct IdentityFields {
    certificate: String,
    field: u64,
    provenance: String,
    catalog_ids: Vec<usize>,
    target_dimensions: Vec<usize>,
}

impl RawArtifact {
    pub(super) fn parse(text: &str, limits: CatalogAtlasArtifactParseLimits) -> AtlasParse<Self> {
        let mut c = Cursor::new(
            text,
            CursorLimits {
                input_bytes: limits.max_input_bytes,
                integer_digits: limits.max_integer_digits,
                string_bytes: limits.max_string_bytes,
                numeric_values: limits.max_numeric_values,
                array_elements: limits.max_array_elements,
            },
        )?;
        c.token(b'{')?;
        let expected = [
            CATALOG_ATLAS_ARTIFACT_SCHEMA,
            CATALOG_ATLAS_ARTIFACT_KIND,
            CATALOG_ATLAS_ARTIFACT_ENGINE,
        ];
        c.header::<CatalogAtlasArtifactError>("", expected)?;
        let identity = identity_fields(&mut c, &limits)?;
        let raw = Self::data_fields(&mut c, &limits, identity)?;
        c.token(b'}')?;
        c.end()?;
        c.fingerprint_shape(&raw.fingerprint)?;
        Ok(raw)
    }

    fn data_fields(
        c: &mut Cursor,
        limits: &CatalogAtlasArtifactParseLimits,
        identity: IdentityFields,
    ) -> AtlasParse<Self> {
        let max_degree = c.next("max_degree", |c| c.usize("max_degree"))?;
        let atlas_limits = c.next("atlas_limits", atlas_limits)?;
        let multiplicity_limits = c.next("multiplicity_limits", multiplicity_limits)?;
        let work = c.next("work", work)?;
        let ext_rows = c.next("ext_rows", |c| {
            c.array("ext_rows", limits.max_ext_rows, |c, _| ext_row(c, limits))
        })?;
        let result_rows = c.next("result_rows", |c| {
            c.array("result_rows", limits.max_result_rows, |c, _| {
                result_row(c, limits)
            })
        })?;
        let status = c.next("status", status)?;
        let fingerprint = c.next("fingerprint", |c| c.string("fingerprint"))?;
        Ok(Self {
            certificate: identity.certificate,
            field: identity.field,
            provenance: identity.provenance,
            catalog_ids: identity.catalog_ids,
            target_dimensions: identity.target_dimensions,
            max_degree,
            atlas_limits,
            multiplicity_limits,
            work,
            ext_rows,
            result_rows,
            status,
            fingerprint,
        })
    }
}

fn identity_fields(
    c: &mut Cursor,
    limits: &CatalogAtlasArtifactParseLimits,
) -> AtlasParse<IdentityFields> {
    let certificate = c.next("certificate", |c| {
        c.escaped_string("certificate", limits.max_certificate_bytes)
    })?;
    let field = c.next("field", |c| c.u64("field"))?;
    let provenance = c.next("provenance", |c| c.string("provenance"))?;
    let catalog_ids = c.next("catalog_ids", |c| {
        bounded_numbers(c, "catalog_ids", limits.max_catalog_entries, usize::MAX)
    })?;
    let target_dimensions = c.next("target_dimensions", |c| {
        let (length, maximum) = (limits.max_dimensions, limits.max_dimension);
        bounded_numbers(c, "target_dimensions", length, maximum)
    })?;
    Ok(IdentityFields {
        certificate,
        field,
        provenance,
        catalog_ids,
        target_dimensions,
    })
}

/// Reads at most `length` integers. An entry above `maximum` is rejected
/// with its indexed path.
fn bounded_numbers(
    c: &mut Cursor,
    path: &str,
    length: usize,
    maximum: usize,
) -> AtlasParse<Vec<usize>> {
    c.array(path, length, |c, index| {
        let path = format!("{path}[{index}]");
        let value = c.usize(&path)?;
        if value > maximum {
            return Err(CatalogAtlasArtifactError::ParseLimit {
                path,
                used: value,
                limit: maximum,
            });
        }
        Ok(value)
    })
}

fn atlas_limits(c: &mut Cursor) -> AtlasParse<CatalogAtlasLimits> {
    let [
        max_pairs,
        max_ext_cells,
        max_resolution_terms,
        max_materialized_summands,
        max_materialized_cells,
    ] = c.uint_object(
        "atlas_limits",
        [
            "max_pairs",
            "max_ext_cells",
            "max_resolution_terms",
            "max_materialized_summands",
            "max_materialized_cells",
        ],
    )?;
    Ok(CatalogAtlasLimits {
        max_pairs,
        max_ext_cells,
        max_resolution_terms,
        max_materialized_summands,
        max_materialized_cells,
    })
}

fn multiplicity_limits(c: &mut Cursor) -> AtlasParse<MultiplicityLimits> {
    let [max_solutions, max_nodes] =
        c.uint_object("multiplicity_limits", ["max_solutions", "max_nodes"])?;
    Ok(MultiplicityLimits {
        max_solutions,
        max_nodes,
    })
}

fn work(c: &mut Cursor) -> AtlasParse<CatalogAtlasWork> {
    let [pairs, ext_cells, resolutions, resolution_terms, ext_tables] = c.uint_object(
        "work",
        [
            "pairs",
            "ext_cells",
            "resolutions",
            "resolution_terms",
            "ext_tables",
        ],
    )?;
    Ok(CatalogAtlasWork {
        pairs,
        ext_cells,
        resolutions,
        resolution_terms,
        ext_tables,
    })
}

fn ext_row(
    c: &mut Cursor,
    limits: &CatalogAtlasArtifactParseLimits,
) -> AtlasParse<CatalogAtlasArtifactExtRow> {
    c.token(b'{')?;
    c.key("source")?;
    let source = c.usize("ext_rows[].source")?;
    let target = c.next("target", |c| c.usize("ext_rows[].target"))?;
    let dimensions = c.next("dimensions", |c| {
        bounded_numbers(
            c,
            "ext_rows[].dimensions",
            limits.max_ext_degrees,
            usize::MAX,
        )
    })?;
    c.token(b'}')?;
    Ok(CatalogAtlasArtifactExtRow::new(source, target, dimensions))
}

fn result_row(
    c: &mut Cursor,
    limits: &CatalogAtlasArtifactParseLimits,
) -> AtlasParse<CatalogAtlasArtifactResultRow> {
    c.token(b'{')?;
    c.key("multiplicities")?;
    let path = "result_rows[].multiplicities";
    let multiplicities = bounded_numbers(c, path, limits.max_multiplicity_values, usize::MAX)?;
    let self_ext = c.next("self_ext", |c| {
        bounded_numbers(
            c,
            "result_rows[].self_ext",
            limits.max_ext_degrees,
            usize::MAX,
        )
    })?;
    c.token(b'}')?;
    Ok(CatalogAtlasArtifactResultRow::new(multiplicities, self_ext))
}

fn status(c: &mut Cursor) -> AtlasParse<CatalogAtlasArtifactStatus> {
    c.token(b'{')?;
    c.key("kind")?;
    let status = match c.string("status.kind")?.as_str() {
        "complete" => CatalogAtlasArtifactStatus::Complete,
        "cut" => cut_status(c)?,
        _ => return Err(c.syntax("status kind must be complete or cut").into()),
    };
    c.token(b'}')?;
    Ok(status)
}

fn cut_status(c: &mut Cursor) -> AtlasParse<CatalogAtlasArtifactStatus> {
    let reason = c.next("reason", cut_reason)?;
    let coverage = c.next("coverage", |c| c.usize("status.coverage"))?;
    let nodes_visited = c.next("nodes_visited", |c| c.u64("status.nodes_visited"))?;
    Ok(CatalogAtlasArtifactStatus::Cut {
        reason,
        coverage,
        nodes_visited,
    })
}

fn cut_reason(c: &mut Cursor) -> AtlasParse<MultiplicityCutReason> {
    c.token(b'{')?;
    c.key("kind")?;
    let kind = c.string("status.reason.kind")?;
    let limit = c.next("limit", |c| c.u64("status.reason.limit"))?;
    c.token(b'}')?;
    match kind.as_str() {
        "solution_limit" => Ok(MultiplicityCutReason::SolutionLimit { limit }),
        "node_limit" => Ok(MultiplicityCutReason::NodeLimit { limit }),
        _ => Err(c.syntax("unknown multiplicity cut reason").into()),
    }
}

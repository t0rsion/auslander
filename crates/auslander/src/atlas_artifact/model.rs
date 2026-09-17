use std::sync::Arc;

use crate::algebra::Algebra;
use crate::arquiver::{CatalogProvenance, IndecomposableCatalog};
use crate::atlas::{
    CatalogAtlas, CatalogAtlasLimits, CatalogAtlasWork, MultiplicityCutReason, MultiplicityLimits,
    MultiplicityOutcome,
};
use crate::certificate::Certificate;

use super::errors::CatalogAtlasArtifactError;
use super::parser::RawArtifact;
use super::serialization::{fingerprint, push_usizes};
use super::{
    CATALOG_ATLAS_ARTIFACT_ENGINE, CATALOG_ATLAS_ARTIFACT_KIND, CATALOG_ATLAS_ARTIFACT_SCHEMA,
};

/// Limits applied before the artifact parser allocates declared containers.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CatalogAtlasArtifactParseLimits {
    /// The greatest accepted input byte count.
    pub max_input_bytes: usize,
    /// The greatest decoded certificate byte count.
    pub max_certificate_bytes: usize,
    /// The greatest number of catalog entries.
    pub max_catalog_entries: usize,
    /// The greatest number of target-dimension entries.
    pub max_dimensions: usize,
    /// The greatest target or entry dimension at one vertex.
    pub max_dimension: usize,
    /// The greatest number of Ext rows.
    pub max_ext_rows: usize,
    /// The greatest number of Ext dimensions in one row.
    pub max_ext_degrees: usize,
    /// The greatest number of multiplicity result rows.
    pub max_result_rows: usize,
    /// The greatest number of multiplicity values in one row.
    pub max_multiplicity_values: usize,
    /// The greatest number of numeric values in the document.
    pub max_numeric_values: usize,
    /// The greatest number of array elements in the document.
    pub max_array_elements: usize,
    /// The greatest digit count in one unsigned integer.
    pub max_integer_digits: usize,
    /// The greatest byte count of an ordinary string.
    pub max_string_bytes: usize,
}

impl Default for CatalogAtlasArtifactParseLimits {
    fn default() -> Self {
        Self {
            max_input_bytes: 16_777_216,
            max_certificate_bytes: 4_194_304,
            max_catalog_entries: 100_000,
            max_dimensions: 4_096,
            max_dimension: 1_000_000,
            max_ext_rows: 10_000_000,
            max_ext_degrees: 4_096,
            max_result_rows: 1_000_000,
            max_multiplicity_values: 100_000,
            max_numeric_values: 50_000_000,
            max_array_elements: 50_000_000,
            max_integer_digits: 39,
            max_string_bytes: 4_096,
        }
    }
}

/// Resource ceilings for one atlas artifact replay.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CatalogAtlasArtifactVerifyLimits {
    /// Limits applied by the portable parser.
    pub parse: CatalogAtlasArtifactParseLimits,
    /// The greatest number of algebra vertices to reconstruct.
    pub max_vertices: usize,
    /// The greatest number of quiver arrows to reconstruct.
    pub max_arrows: usize,
    /// The greatest algebra basis dimension to reconstruct.
    pub max_algebra_dimension: usize,
    /// The greatest catalog entry count to reconstruct.
    pub max_catalog_entries: usize,
    /// The greatest target or catalog-entry vertex dimension.
    pub max_dimension: usize,
    /// The greatest inclusive Ext degree bound.
    pub max_degree: usize,
    /// The greatest ordered-pair count for the atlas.
    pub max_pairs: usize,
    /// The greatest number of stored Ext cells.
    pub max_ext_cells: usize,
    /// The greatest number of retained resolution terms.
    pub max_resolution_terms: usize,
    /// The greatest number of retained multiplicity rows.
    pub max_result_rows: usize,
    /// The greatest number of multiplicity values in one row.
    pub max_multiplicity: usize,
    /// The greatest number of multiplicity search states.
    pub max_nodes: usize,
    /// The greatest number of direct-sum copies permitted by the atlas.
    pub max_materialized_summands: usize,
    /// The greatest total materialized matrix cell count.
    pub max_materialized_cells: usize,
    /// The greatest total dimension of one catalog entry.
    pub max_entry_total_dimension: usize,
    /// The greatest number of generic Ext cells replayed.
    pub max_generic_ext_cells: usize,
}

impl Default for CatalogAtlasArtifactVerifyLimits {
    fn default() -> Self {
        Self {
            parse: CatalogAtlasArtifactParseLimits::default(),
            max_vertices: 4_096,
            max_arrows: 16_384,
            max_algebra_dimension: 1_000_000,
            max_catalog_entries: 100_000,
            max_dimension: 1_000_000,
            max_degree: 4_096,
            max_pairs: 10_000_000,
            max_ext_cells: 50_000_000,
            max_resolution_terms: 50_000_000,
            max_result_rows: 1_000_000,
            max_multiplicity: 1_000_000,
            max_nodes: 10_000_000,
            max_materialized_summands: 1_000_000,
            max_materialized_cells: 10_000_000,
            max_entry_total_dimension: 1_000_000,
            max_generic_ext_cells: 50_000_000,
        }
    }
}

/// One ordered source-target Ext row in a portable atlas.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CatalogAtlasArtifactExtRow {
    source: usize,
    target: usize,
    dimensions: Vec<usize>,
}

impl CatalogAtlasArtifactExtRow {
    pub(crate) fn new(source: usize, target: usize, dimensions: Vec<usize>) -> Self {
        Self {
            source,
            target,
            dimensions,
        }
    }

    accessor_methods! {
        /// The source catalog identifier.
        pub source() -> usize = |this| this.source;
        /// The target catalog identifier.
        pub target() -> usize = |this| this.target;
        /// Ext dimensions in degrees zero through the stored bound.
        pub dimensions() -> &[usize] = |this| &this.dimensions;
    }
}

/// One multiplicity vector and its cached self-Ext dimensions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CatalogAtlasArtifactResultRow {
    multiplicities: Vec<usize>,
    self_ext: Vec<usize>,
}

impl CatalogAtlasArtifactResultRow {
    pub(crate) fn new(multiplicities: Vec<usize>, self_ext: Vec<usize>) -> Self {
        Self {
            multiplicities,
            self_ext,
        }
    }

    accessor_methods! {
        /// The multiplicities in deterministic catalog order.
        pub multiplicities() -> &[usize] = |this| &this.multiplicities;
        /// Self-Ext dimensions in degrees zero through the stored bound.
        pub self_ext() -> &[usize] = |this| &this.self_ext;
    }
}

/// Complete enumeration or a cut prefix with explicit coverage data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CatalogAtlasArtifactStatus {
    /// The full finite multiplicity enumeration was retained.
    Complete,
    /// The exact prefix stopped at a typed enumeration budget.
    Cut {
        reason: MultiplicityCutReason,
        coverage: usize,
        nodes_visited: usize,
    },
}

impl CatalogAtlasArtifactStatus {
    accessor_methods! {
        /// Whether the stored enumeration claims completeness.
        pub is_complete() -> bool = |this| matches!(this, Self::Complete);
        /// Whether the stored enumeration is a cut prefix.
        pub is_cut() -> bool = |this| matches!(this, Self::Cut { .. });
        /// The retained prefix length.
        pub coverage() -> Option<usize> = |this| match this {
            Self::Complete => None,
            Self::Cut { coverage, .. } => Some(*coverage),
        };
        /// The typed reason for a cut prefix.
        pub cut_reason() -> Option<MultiplicityCutReason> = |this| match this {
            Self::Complete => None,
            Self::Cut { reason, .. } => Some(*reason),
        };
        /// Iterative search states visited before a cut.
        pub nodes_visited() -> Option<usize> = |this| match this {
            Self::Complete => None,
            Self::Cut { nodes_visited, .. } => Some(*nodes_visited),
        };
    }
}

/// A canonical portable catalog atlas claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CatalogAtlasArtifact {
    pub(super) certificate: Certificate,
    pub(super) field: u64,
    pub(super) provenance: CatalogProvenance,
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

/// A verified artifact and its rebuilt algebra, catalog, and atlas.
#[derive(Clone, Debug)]
pub struct VerifiedCatalogAtlasArtifact {
    pub(super) artifact: CatalogAtlasArtifact,
    pub(super) algebra: Arc<Algebra>,
    pub(super) catalog: Arc<IndecomposableCatalog>,
    pub(super) atlas: CatalogAtlas,
}

impl VerifiedCatalogAtlasArtifact {
    accessor_methods! {
        /// The canonical artifact that passed replay.
        pub artifact() -> &CatalogAtlasArtifact = |this| &this.artifact;
        /// The freshly rebuilt algebra.
        pub algebra() -> &Arc<Algebra> = |this| &this.algebra;
        /// The freshly rebuilt complete catalog.
        pub catalog() -> &Arc<IndecomposableCatalog> = |this| &this.catalog;
        /// The freshly rebuilt optimized atlas.
        pub atlas() -> &CatalogAtlas = |this| &this.atlas;
    }
}

impl CatalogAtlasArtifact {
    /// Builds a portable claim from a verified catalog atlas.
    pub fn from_verified(
        atlas: &CatalogAtlas,
        target_dimensions: &[usize],
        multiplicity_limits: MultiplicityLimits,
    ) -> Result<Self, CatalogAtlasArtifactError> {
        if !atlas.verify() {
            return Err(CatalogAtlasArtifactError::ReplayMismatch {
                field: "atlas".to_string(),
            });
        }
        let outcome = atlas.enumerate_multiplicities(target_dimensions, multiplicity_limits)?;
        let result_rows = build_result_rows(atlas, outcome.solutions())?;
        let status = status_from_outcome(&outcome);
        let mut artifact = Self {
            certificate: atlas.algebra().certificate().clone(),
            field: atlas.algebra().field().modulus(),
            provenance: atlas.provenance(),
            catalog_ids: (0..atlas.catalog().len()).collect(),
            target_dimensions: target_dimensions.to_vec(),
            max_degree: atlas.max_degree(),
            atlas_limits: atlas.limits(),
            multiplicity_limits,
            work: atlas.work(),
            ext_rows: atlas
                .ext_table()
                .rows()
                .iter()
                .map(|row| {
                    CatalogAtlasArtifactExtRow::new(
                        row.source(),
                        row.target(),
                        row.dimensions().to_vec(),
                    )
                })
                .collect(),
            result_rows,
            status,
            fingerprint: String::new(),
        };
        artifact.fingerprint = fingerprint(&artifact.canonical_without_fingerprint());
        Ok(artifact)
    }

    accessor_methods! {
        /// The embedded checked completion certificate.
        pub certificate() -> &Certificate = |this| &this.certificate;
        /// The explicitly stored prime modulus.
        pub field() -> u64 = |this| this.field;
        /// The classification theorem behind the catalog.
        pub provenance() -> CatalogProvenance = |this| this.provenance;
        /// Stable catalog identifiers in enumerator order.
        pub catalog_ids() -> &[usize] = |this| &this.catalog_ids;
        /// The target dimension vector for multiplicity enumeration.
        pub target_dimensions() -> &[usize] = |this| &this.target_dimensions;
        /// The inclusive largest stored Ext degree.
        pub max_degree() -> usize = |this| this.max_degree;
        /// Limits used to build the cached Ext atlas.
        pub atlas_limits() -> CatalogAtlasLimits = |this| this.atlas_limits;
        /// Limits used to enumerate multiplicity rows.
        pub multiplicity_limits() -> MultiplicityLimits = |this| this.multiplicity_limits;
        /// Exact operation counts of the cached atlas.
        pub work() -> CatalogAtlasWork = |this| this.work;
        /// Ordered Ext rows in source-major, target-major order.
        pub ext_rows() -> &[CatalogAtlasArtifactExtRow] = |this| &this.ext_rows;
        /// Multiplicity and self-Ext result rows in lexicographic order.
        pub result_rows() -> &[CatalogAtlasArtifactResultRow] = |this| &this.result_rows;
        /// Complete or cut enumeration status.
        pub status() -> &CatalogAtlasArtifactStatus = |this| &this.status;
        /// The canonical non-authenticating corruption fingerprint.
        pub fingerprint() -> &str = |this| &this.fingerprint;
    }

    /// Parses one canonical portable artifact under explicit parser limits.
    pub fn from_json(
        text: &str,
        limits: CatalogAtlasArtifactParseLimits,
    ) -> Result<Self, CatalogAtlasArtifactError> {
        if text.len() > limits.max_input_bytes {
            return Err(CatalogAtlasArtifactError::ParseLimit {
                path: "$".to_string(),
                used: text.len(),
                limit: limits.max_input_bytes,
            });
        }
        let artifact = Self::from_raw(RawArtifact::parse(text, limits)?)?;
        artifact.validate_serialized(text)
    }

    fn from_raw(raw: RawArtifact) -> Result<Self, CatalogAtlasArtifactError> {
        let certificate_text =
            String::from_utf8(raw.certificate).map_err(|_| CatalogAtlasArtifactError::Syntax {
                byte: 0,
                message: "embedded certificate bytes are not UTF-8".to_string(),
            })?;
        let certificate = Certificate::from_json(&certificate_text)?;
        let provenance = provenance_from_str(&raw.provenance).ok_or_else(|| {
            CatalogAtlasArtifactError::Provenance {
                found: raw.provenance.clone(),
            }
        })?;
        let status = raw.status.into_status()?;
        let artifact = Self {
            certificate,
            field: raw.field,
            provenance,
            catalog_ids: raw.catalog_ids,
            target_dimensions: raw.target_dimensions,
            max_degree: raw.max_degree,
            atlas_limits: raw.atlas_limits,
            multiplicity_limits: raw.multiplicity_limits,
            work: raw.work,
            ext_rows: raw
                .ext_rows
                .into_iter()
                .map(|row| CatalogAtlasArtifactExtRow::new(row.source, row.target, row.dimensions))
                .collect(),
            result_rows: raw
                .result_rows
                .into_iter()
                .map(|row| CatalogAtlasArtifactResultRow::new(row.multiplicities, row.self_ext))
                .collect(),
            status,
            fingerprint: raw.fingerprint,
        };
        Ok(artifact)
    }

    fn validate_serialized(self, text: &str) -> Result<Self, CatalogAtlasArtifactError> {
        if self.to_canonical_json() != text {
            return Err(CatalogAtlasArtifactError::NonCanonical);
        }
        if !self.has_valid_fingerprint() {
            return Err(CatalogAtlasArtifactError::ReplayMismatch {
                field: "fingerprint".to_string(),
            });
        }
        Ok(self)
    }

    /// Serializes this artifact to byte-exact canonical JSON.
    pub fn to_canonical_json(&self) -> String {
        let mut output = self.canonical_without_fingerprint();
        output.push_str(",\"fingerprint\":\"");
        output.push_str(&self.fingerprint);
        output.push_str("\"}");
        output
    }

    /// Whether the non-authenticating fingerprint covers the preceding fields.
    pub fn has_valid_fingerprint(&self) -> bool {
        self.fingerprint == fingerprint(&self.canonical_without_fingerprint())
    }

    pub(crate) fn canonical_without_fingerprint(&self) -> String {
        let mut output = String::new();
        output.push_str("{\"schema\":\"");
        output.push_str(CATALOG_ATLAS_ARTIFACT_SCHEMA);
        output.push_str("\",\"kind\":\"");
        output.push_str(CATALOG_ATLAS_ARTIFACT_KIND);
        output.push_str("\",\"engine\":\"");
        output.push_str(CATALOG_ATLAS_ARTIFACT_ENGINE);
        output.push_str("\",\"certificate\":\"");
        super::serialization::push_escaped_string(
            &mut output,
            self.certificate.to_canonical_json().as_bytes(),
        );
        output.push_str("\",\"field\":");
        output.push_str(&self.field.to_string());
        output.push_str(",\"provenance\":\"");
        output.push_str(provenance_str(self.provenance));
        output.push_str("\",\"catalog_ids\":");
        push_usizes(&mut output, &self.catalog_ids);
        output.push_str(",\"target_dimensions\":");
        push_usizes(&mut output, &self.target_dimensions);
        output.push_str(",\"max_degree\":");
        output.push_str(&self.max_degree.to_string());
        output.push_str(",\"atlas_limits\":");
        super::serialization::push_atlas_limits(&mut output, self.atlas_limits);
        output.push_str(",\"multiplicity_limits\":");
        super::serialization::push_multiplicity_limits(&mut output, self.multiplicity_limits);
        output.push_str(",\"work\":");
        super::serialization::push_work(&mut output, self.work);
        output.push_str(",\"ext_rows\":[");
        for (index, row) in self.ext_rows.iter().enumerate() {
            if index != 0 {
                output.push(',');
            }
            output.push_str("{\"source\":");
            output.push_str(&row.source.to_string());
            output.push_str(",\"target\":");
            output.push_str(&row.target.to_string());
            output.push_str(",\"dimensions\":");
            push_usizes(&mut output, &row.dimensions);
            output.push('}');
        }
        output.push_str("],\"result_rows\":[");
        for (index, row) in self.result_rows.iter().enumerate() {
            if index != 0 {
                output.push(',');
            }
            output.push_str("{\"multiplicities\":");
            push_usizes(&mut output, &row.multiplicities);
            output.push_str(",\"self_ext\":");
            push_usizes(&mut output, &row.self_ext);
            output.push('}');
        }
        output.push_str("],\"status\":");
        super::serialization::push_status(&mut output, &self.status);
        output
    }
}

fn build_result_rows(
    atlas: &CatalogAtlas,
    solutions: &[Vec<usize>],
) -> Result<Vec<CatalogAtlasArtifactResultRow>, CatalogAtlasArtifactError> {
    let mut rows = Vec::with_capacity(solutions.len());
    for multiplicities in solutions {
        let self_ext = atlas.self_ext_scores(multiplicities, 0, atlas.max_degree())?;
        rows.push(CatalogAtlasArtifactResultRow::new(
            multiplicities.clone(),
            self_ext,
        ));
    }
    Ok(rows)
}

fn status_from_outcome(outcome: &MultiplicityOutcome) -> CatalogAtlasArtifactStatus {
    match outcome {
        MultiplicityOutcome::Complete(_) => CatalogAtlasArtifactStatus::Complete,
        MultiplicityOutcome::Cut(cut) => CatalogAtlasArtifactStatus::Cut {
            coverage: cut.solutions().len(),
            nodes_visited: cut.nodes_visited(),
            reason: cut.reason(),
        },
    }
}

fn provenance_str(value: CatalogProvenance) -> &'static str {
    match value {
        CatalogProvenance::Nakayama => "nakayama",
        CatalogProvenance::DynkinZeroIdeal => "dynkin_zero_ideal",
        CatalogProvenance::GentleTree => "gentle_tree",
    }
}

pub(super) fn provenance_from_str(value: &str) -> Option<CatalogProvenance> {
    match value {
        "nakayama" => Some(CatalogProvenance::Nakayama),
        "dynkin_zero_ideal" => Some(CatalogProvenance::DynkinZeroIdeal),
        "gentle_tree" => Some(CatalogProvenance::GentleTree),
        _ => None,
    }
}

impl super::parser::RawStatus {
    fn into_status(self) -> Result<CatalogAtlasArtifactStatus, CatalogAtlasArtifactError> {
        if self.kind == "complete" {
            if self.coverage.is_some() || self.nodes_visited.is_some() || self.reason.is_some() {
                return Err(CatalogAtlasArtifactError::CountMismatch {
                    field: "status.complete".to_string(),
                });
            }
            return Ok(CatalogAtlasArtifactStatus::Complete);
        }
        if self.kind != "cut" {
            return Err(CatalogAtlasArtifactError::Syntax {
                byte: 0,
                message: "status kind must be complete or cut".to_string(),
            });
        }
        let reason = self
            .reason
            .ok_or_else(|| CatalogAtlasArtifactError::CountMismatch {
                field: "status.reason".to_string(),
            })?;
        let coverage = self
            .coverage
            .ok_or_else(|| CatalogAtlasArtifactError::CountMismatch {
                field: "status.coverage".to_string(),
            })?;
        let nodes_visited =
            self.nodes_visited
                .ok_or_else(|| CatalogAtlasArtifactError::CountMismatch {
                    field: "status.nodes_visited".to_string(),
                })?;
        Ok(CatalogAtlasArtifactStatus::Cut {
            reason,
            coverage,
            nodes_visited,
        })
    }
}

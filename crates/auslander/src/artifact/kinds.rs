//! The registered portable kinds. A new kind adds one [`ArtifactKind`]
//! variant, its limits field, and one arm in each match of this file.

use crate::atlas_artifact::{
    CATALOG_ATLAS_ARTIFACT_KIND, CATALOG_ATLAS_ARTIFACT_SCHEMA, CatalogAtlasArtifact,
    CatalogAtlasArtifactStatus, CatalogAtlasArtifactVerifyLimits, VerifiedCatalogAtlasArtifact,
    verify_catalog_atlas_artifact,
};
use crate::batch_stream::{
    HOMOLOGICAL_STREAM_PORTABLE_KIND, HOMOLOGICAL_STREAM_PORTABLE_SCHEMA,
    HomologicalStreamPortable, HomologicalStreamPortableStatus, HomologicalStreamVerifyLimits,
    VerifiedHomologicalStream,
};
use crate::census::{
    CENSUS_PORTABLE_KIND, CENSUS_PORTABLE_SCHEMA, CensusPortable, CensusPortableStatus,
    CensusVerifyLimits, VerifiedCensus, verify_census_portable,
};
use crate::control::ComputationControl;
use crate::derived_artifact::{
    ArtifactVerificationOutcome, ArtifactVerifyLimits, DERIVED_ARTIFACT_SCHEMA, DerivedArtifact,
    VerifiedDerivedArtifact, verify_derived_artifact,
};
use crate::derived_classification::{
    ClassificationStatus, DERIVED_ATLAS_ARTIFACT_KIND, DERIVED_ATLAS_ARTIFACT_SCHEMA,
    DerivedAtlasArtifact, DerivedAtlasVerification, DerivedAtlasVerifyLimits, VerifiedDerivedAtlas,
    verify_derived_atlas_artifact,
};
use crate::theorem_artifact::{
    SELF_EXT_LOCUS_ARTIFACT_KIND, SELF_EXT_LOCUS_ARTIFACT_SCHEMA, SelfExtLocusArtifact,
    SelfExtLocusVerifyLimits, VerifiedSelfExtLocusArtifact, verify_self_ext_locus_artifact,
};

use super::{ArtifactReport, ArtifactVerification, PortableArtifactError, VerifiedArtifact};

/// One registered portable format, named by its header.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ArtifactKind {
    /// Schema `auslander-derived-v2`: one derived-equivalence edge.
    DerivedEquivalence,
    /// Kind `census-v1`: a module census result or checkpoint.
    Census,
    /// Kind `homological-self-pair-stream-v2`: a homological stream checkpoint.
    HomologicalStream,
    /// Kind `catalog-atlas-v1`: catalog Ext tables and multiplicity rows.
    CatalogAtlas,
    /// Kind `fixed-dimension-self-ext-locus-v1`: a self-Ext vanishing locus.
    SelfExtLocus,
    /// Kind `derived-atlas-v1`: a certified derived classification.
    DerivedAtlas,
}

impl ArtifactKind {
    /// Every registered kind, in header-matching order.
    pub const ALL: [ArtifactKind; 6] = [
        Self::DerivedEquivalence,
        Self::Census,
        Self::HomologicalStream,
        Self::CatalogAtlas,
        Self::SelfExtLocus,
        Self::DerivedAtlas,
    ];

    /// The `schema` header value.
    pub fn schema(self) -> &'static str {
        self.header().0
    }

    /// The `kind` header value. `None` for a schema without payload kinds.
    pub fn payload_kind(self) -> Option<&'static str> {
        self.header().1
    }

    /// The payload kind, or the schema when the schema has no payload kinds.
    pub fn name(self) -> &'static str {
        self.payload_kind().unwrap_or(self.schema())
    }

    fn header(self) -> (&'static str, Option<&'static str>) {
        match self {
            Self::DerivedEquivalence => (DERIVED_ARTIFACT_SCHEMA, None),
            Self::Census => (CENSUS_PORTABLE_SCHEMA, Some(CENSUS_PORTABLE_KIND)),
            Self::HomologicalStream => (
                HOMOLOGICAL_STREAM_PORTABLE_SCHEMA,
                Some(HOMOLOGICAL_STREAM_PORTABLE_KIND),
            ),
            Self::CatalogAtlas => (
                CATALOG_ATLAS_ARTIFACT_SCHEMA,
                Some(CATALOG_ATLAS_ARTIFACT_KIND),
            ),
            Self::SelfExtLocus => (
                SELF_EXT_LOCUS_ARTIFACT_SCHEMA,
                Some(SELF_EXT_LOCUS_ARTIFACT_KIND),
            ),
            Self::DerivedAtlas => (
                DERIVED_ATLAS_ARTIFACT_SCHEMA,
                Some(DERIVED_ATLAS_ARTIFACT_KIND),
            ),
        }
    }
}

/// The parse and verification limits of every registered kind.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct ArtifactLimits {
    /// Limits for `auslander-derived-v2`.
    pub derived_equivalence: ArtifactVerifyLimits,
    /// Limits for `census-v1`.
    pub census: CensusVerifyLimits,
    /// Limits for `homological-self-pair-stream-v2`.
    pub homological_stream: HomologicalStreamVerifyLimits,
    /// Limits for `catalog-atlas-v1`.
    pub catalog_atlas: CatalogAtlasArtifactVerifyLimits,
    /// Limits for `fixed-dimension-self-ext-locus-v1`.
    pub self_ext_locus: SelfExtLocusVerifyLimits,
    /// Limits for `derived-atlas-v1`.
    pub derived_atlas: DerivedAtlasVerifyLimits,
}

/// A verified value of one registered kind, with its rebuilt live data.
#[derive(Clone, Debug)]
pub enum VerifiedArtifactValue {
    /// A replayed derived-equivalence edge.
    DerivedEquivalence(Box<VerifiedDerivedArtifact>),
    /// A replayed census.
    Census(Box<VerifiedCensus>),
    /// A replayed homological stream checkpoint.
    HomologicalStream(Box<VerifiedHomologicalStream>),
    /// A replayed catalog atlas.
    CatalogAtlas(Box<VerifiedCatalogAtlasArtifact>),
    /// A replayed self-Ext locus claim.
    SelfExtLocus(Box<VerifiedSelfExtLocusArtifact>),
    /// A replayed derived classification.
    DerivedAtlas(Box<VerifiedDerivedAtlas>),
}

from_variants!(PortableArtifactError {
    crate::derived_artifact::ArtifactError => DerivedEquivalence,
    crate::census::CensusPortableError => Census,
    crate::batch_stream::HomologicalStreamPortableError => HomologicalStream,
    crate::atlas_artifact::CatalogAtlasArtifactError => CatalogAtlas,
    crate::theorem_artifact::SelfExtLocusArtifactError => SelfExtLocus,
    crate::derived_classification::DerivedAtlasError => DerivedAtlas,
});

pub(super) fn inspect(
    kind: ArtifactKind,
    text: &str,
    limits: &ArtifactLimits,
) -> Result<ArtifactReport, PortableArtifactError> {
    match kind {
        ArtifactKind::DerivedEquivalence => parsed(
            DerivedArtifact::from_json(text, limits.derived_equivalence.parse),
            derived_report,
        ),
        ArtifactKind::Census => parsed(
            CensusPortable::from_json(text, limits.census.parse),
            census_report,
        ),
        ArtifactKind::HomologicalStream => parsed(
            HomologicalStreamPortable::from_json(text, limits.homological_stream.parse),
            homological_report,
        ),
        ArtifactKind::CatalogAtlas => parsed(
            CatalogAtlasArtifact::from_json(text, limits.catalog_atlas.parse),
            atlas_report,
        ),
        ArtifactKind::SelfExtLocus => parsed(
            SelfExtLocusArtifact::from_json(text, limits.self_ext_locus.parse),
            theorem_report,
        ),
        ArtifactKind::DerivedAtlas => parsed(
            DerivedAtlasArtifact::from_json(text, limits.derived_atlas.parse),
            derived_atlas_report,
        ),
    }
}

fn parsed<T, E>(
    value: Result<T, E>,
    report: fn(&T) -> ArtifactReport,
) -> Result<ArtifactReport, PortableArtifactError>
where
    PortableArtifactError: From<E>,
{
    Ok(report(&value?))
}

pub(super) fn verify(
    kind: ArtifactKind,
    text: &str,
    limits: &ArtifactLimits,
    control: &ComputationControl,
) -> Result<ArtifactVerification, PortableArtifactError> {
    match kind {
        ArtifactKind::DerivedEquivalence => {
            verify_derived(text, limits.derived_equivalence, control)
        }
        ArtifactKind::Census => accepted(
            verify_census_portable(text, limits.census),
            |value| census_report(value.portable()),
            VerifiedArtifactValue::Census,
        ),
        ArtifactKind::HomologicalStream => accepted(
            HomologicalStreamPortable::from_json(text, limits.homological_stream.parse)
                .and_then(|value| value.verify(limits.homological_stream)),
            |value| homological_report(value.portable()),
            VerifiedArtifactValue::HomologicalStream,
        ),
        ArtifactKind::CatalogAtlas => accepted(
            verify_catalog_atlas_artifact(text, limits.catalog_atlas),
            |value| atlas_report(value.artifact()),
            VerifiedArtifactValue::CatalogAtlas,
        ),
        ArtifactKind::SelfExtLocus => accepted(
            verify_self_ext_locus_artifact(text, limits.self_ext_locus),
            |value| theorem_report(value.artifact()),
            VerifiedArtifactValue::SelfExtLocus,
        ),
        ArtifactKind::DerivedAtlas => verify_derived_atlas(text, limits.derived_atlas, control),
    }
}

fn verify_derived_atlas(
    text: &str,
    limits: DerivedAtlasVerifyLimits,
    control: &ComputationControl,
) -> Result<ArtifactVerification, PortableArtifactError> {
    match verify_derived_atlas_artifact(text, limits, control)? {
        DerivedAtlasVerification::Verified(value) => accepted(
            Ok::<_, PortableArtifactError>(*value),
            |value| derived_atlas_report(value.artifact()),
            VerifiedArtifactValue::DerivedAtlas,
        ),
        DerivedAtlasVerification::Stopped(cut) => Ok(ArtifactVerification::Stopped {
            kind: ArtifactKind::DerivedAtlas,
            cut,
        }),
    }
}

fn verify_derived(
    text: &str,
    limits: ArtifactVerifyLimits,
    control: &ComputationControl,
) -> Result<ArtifactVerification, PortableArtifactError> {
    match verify_derived_artifact(text, limits, control)? {
        ArtifactVerificationOutcome::Verified(value) => accepted(
            Ok::<_, PortableArtifactError>(*value),
            |value| derived_report(value.artifact()),
            VerifiedArtifactValue::DerivedEquivalence,
        ),
        ArtifactVerificationOutcome::Stopped(cut) => Ok(ArtifactVerification::Stopped {
            kind: ArtifactKind::DerivedEquivalence,
            cut,
        }),
    }
}

fn accepted<V, E>(
    value: Result<V, E>,
    report: fn(&V) -> ArtifactReport,
    wrap: fn(Box<V>) -> VerifiedArtifactValue,
) -> Result<ArtifactVerification, PortableArtifactError>
where
    PortableArtifactError: From<E>,
{
    let value = value?;
    let report = report(&value);
    let value = wrap(Box::new(value));
    Ok(ArtifactVerification::Verified(Box::new(VerifiedArtifact {
        report,
        value,
    })))
}

fn report(
    kind: ArtifactKind,
    fingerprint: &str,
    canonical_json: String,
    complete: bool,
    summary: Vec<(&'static str, String)>,
) -> ArtifactReport {
    ArtifactReport {
        kind,
        fingerprint: fingerprint.to_string(),
        canonical_json,
        summary,
        complete,
    }
}

fn join(values: &[usize]) -> String {
    let parts: Vec<String> = values.iter().map(usize::to_string).collect();
    parts.join(",")
}

fn derived_report(artifact: &DerivedArtifact) -> ArtifactReport {
    let source = artifact.source_certificate();
    let target = artifact.target_certificate();
    let summary = vec![
        ("source_field", source.field.to_string()),
        ("source_vertices", source.quiver.vertices.to_string()),
        ("mutations", artifact.mutations().len().to_string()),
        ("target_field", target.field.to_string()),
        ("target_vertices", target.quiver.vertices.to_string()),
        (
            "target_dimension",
            artifact.work().endo_dimension.to_string(),
        ),
    ];
    let canonical = artifact.to_canonical_json();
    report(
        ArtifactKind::DerivedEquivalence,
        artifact.fingerprint(),
        canonical,
        true,
        summary,
    )
}

fn census_report(census: &CensusPortable) -> ArtifactReport {
    let status = match census.status() {
        CensusPortableStatus::Complete => "complete".to_string(),
        CensusPortableStatus::Cut(reason) => format!("cut: {reason}"),
    };
    let complete = matches!(census.status(), CensusPortableStatus::Complete);
    let summary = vec![
        ("field", census.certificate().field.to_string()),
        ("dimensions", join(census.dimensions())),
        ("raw_space_size", census.raw_space_size().to_string()),
        ("cursor", census.cursor().to_string()),
        (
            "representatives",
            census.representatives().len().to_string(),
        ),
        ("assignments", census.assignments().len().to_string()),
        ("status", status),
    ];
    let canonical = census.to_canonical_json();
    report(
        ArtifactKind::Census,
        census.fingerprint(),
        canonical,
        complete,
        summary,
    )
}

fn homological_report(stream: &HomologicalStreamPortable) -> ArtifactReport {
    let status = match stream.status() {
        HomologicalStreamPortableStatus::Active => "active".to_string(),
        HomologicalStreamPortableStatus::Complete => "complete".to_string(),
        HomologicalStreamPortableStatus::Cut(reason) => format!("cut: {reason}"),
    };
    let complete = matches!(stream.status(), HomologicalStreamPortableStatus::Complete);
    let summary = vec![
        (
            "census_fingerprint",
            stream.census_fingerprint().to_string(),
        ),
        ("max_degree", stream.max_degree().to_string()),
        ("next_source", stream.next_source().to_string()),
        ("rows", stream.rows().len().to_string()),
        ("chunks", stream.chunk_sizes().len().to_string()),
        ("status", status),
    ];
    let canonical = stream.to_canonical_json();
    report(
        ArtifactKind::HomologicalStream,
        stream.fingerprint(),
        canonical,
        complete,
        summary,
    )
}

fn atlas_report(atlas: &CatalogAtlasArtifact) -> ArtifactReport {
    let status = match atlas.status() {
        CatalogAtlasArtifactStatus::Complete => "complete".to_string(),
        CatalogAtlasArtifactStatus::Cut { reason, .. } => format!("cut: {reason}"),
    };
    let summary = vec![
        ("field", atlas.field().to_string()),
        (
            "provenance",
            crate::atlas_artifact::provenance_str(atlas.provenance()).to_string(),
        ),
        ("catalog_entries", atlas.catalog_ids().len().to_string()),
        ("target_dimensions", join(atlas.target_dimensions())),
        ("max_degree", atlas.max_degree().to_string()),
        ("ext_rows", atlas.ext_rows().len().to_string()),
        ("result_rows", atlas.result_rows().len().to_string()),
        ("status", status),
    ];
    let canonical = atlas.to_canonical_json();
    let complete = atlas.status().is_complete();
    report(
        ArtifactKind::CatalogAtlas,
        atlas.fingerprint(),
        canonical,
        complete,
        summary,
    )
}

fn theorem_report(artifact: &SelfExtLocusArtifact) -> ArtifactReport {
    let checkpoint = artifact.checkpoint();
    let summary = vec![
        (
            "checkpoint_fingerprint",
            checkpoint.fingerprint().to_string(),
        ),
        (
            "census_fingerprint",
            checkpoint.census_fingerprint().to_string(),
        ),
        ("representatives", checkpoint.rows().len().to_string()),
        ("first_degree", artifact.first_degree().to_string()),
        ("last_degree", artifact.last_degree().to_string()),
        ("vanishing", artifact.vanishing_indices().len().to_string()),
    ];
    let canonical = artifact.to_canonical_json();
    report(
        ArtifactKind::SelfExtLocus,
        artifact.fingerprint(),
        canonical,
        true,
        summary,
    )
}

fn derived_atlas_report(atlas: &DerivedAtlasArtifact) -> ArtifactReport {
    let merges: usize = atlas.classes().iter().map(|c| c.merges().len()).sum();
    let complete = atlas.status() == ClassificationStatus::Complete;
    let summary = vec![
        ("field", atlas.field().to_string()),
        ("members", atlas.members().len().to_string()),
        ("classes", atlas.classes().len().to_string()),
        ("merges", merges.to_string()),
        ("separations", atlas.separations().len().to_string()),
        ("unresolved", atlas.unresolved().len().to_string()),
        ("status", atlas.status().as_str().to_string()),
    ];
    let canonical = atlas.to_canonical_json();
    report(
        ArtifactKind::DerivedAtlas,
        atlas.fingerprint(),
        canonical,
        complete,
        summary,
    )
}

use super::super::*;
use super::artifact_error as atlas_artifact_error;
use super::{
    PyCatalogAtlasArtifactExtRow, PyCatalogAtlasArtifactResultRow, PyCatalogAtlasArtifactStatus,
    PyCatalogAtlasLimits, PyCatalogAtlasWork, PyMultiplicityCutReason, PyMultiplicityLimits,
};
use auslander::atlas_artifact::{
    CATALOG_ATLAS_ARTIFACT_ENGINE, CATALOG_ATLAS_ARTIFACT_KIND, CATALOG_ATLAS_ARTIFACT_SCHEMA,
    CatalogAtlasArtifact, CatalogAtlasArtifactParseLimits, CatalogAtlasArtifactVerifyLimits,
    VerifiedCatalogAtlasArtifact, verify_catalog_atlas_artifact as verify_artifact,
};

fn artifact_ext_rows(value: &CatalogAtlasArtifact) -> Vec<PyCatalogAtlasArtifactExtRow> {
    value
        .ext_rows()
        .iter()
        .cloned()
        .map(|inner| PyCatalogAtlasArtifactExtRow { inner })
        .collect()
}

fn artifact_result_rows(value: &CatalogAtlasArtifact) -> Vec<PyCatalogAtlasArtifactResultRow> {
    value
        .result_rows()
        .iter()
        .cloned()
        .map(|inner| PyCatalogAtlasArtifactResultRow { inner })
        .collect()
}

/// A canonical portable catalog atlas claim without replay verification.
#[pyclass(name = "CatalogAtlasArtifact", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyCatalogAtlasArtifact {
    pub(crate) inner: CatalogAtlasArtifact,
}

#[pymethods]
impl PyCatalogAtlasArtifact {
    /// Parses canonical artifact JSON without rebuilding its claim.
    #[new]
    #[pyo3(signature = (text, limits=None))]
    fn new(text: &str, limits: Option<&PyCatalogAtlasArtifactVerifyLimits>) -> PyResult<Self> {
        let limits = limits.map_or_else(CatalogAtlasArtifactParseLimits::default, |value| {
            value.inner.parse
        });
        CatalogAtlasArtifact::from_json(text, limits)
            .map(|inner| Self { inner })
            .map_err(atlas_artifact_error)
    }

    /// The fixed artifact schema identifier.
    #[getter]
    fn schema(&self) -> &'static str {
        CATALOG_ATLAS_ARTIFACT_SCHEMA
    }

    /// The fixed artifact kind identifier.
    #[getter]
    fn kind(&self) -> &'static str {
        CATALOG_ATLAS_ARTIFACT_KIND
    }

    /// The fixed computation engine identifier.
    #[getter]
    fn engine(&self) -> &'static str {
        CATALOG_ATLAS_ARTIFACT_ENGINE
    }

    /// The embedded completion certificate as canonical JSON.
    #[getter]
    fn certificate_json(&self) -> String {
        self.inner.certificate().to_canonical_json()
    }

    /// The explicitly recorded prime modulus.
    #[getter]
    fn field(&self) -> u64 {
        self.inner.field()
    }

    /// The classification theorem behind the catalog.
    #[getter]
    fn provenance(&self) -> &'static str {
        provenance_name(self.inner.provenance())
    }

    /// Stable catalog identifiers in enumerator order.
    #[getter]
    fn catalog_ids(&self) -> Vec<usize> {
        self.inner.catalog_ids().to_vec()
    }

    /// The target dimension vector used for multiplicity enumeration.
    #[getter]
    fn target_dimensions(&self) -> Vec<usize> {
        self.inner.target_dimensions().to_vec()
    }

    /// The number of catalog entries named by the artifact.
    #[getter]
    fn catalog_len(&self) -> usize {
        self.inner.catalog_ids().len()
    }

    /// The inclusive largest Ext degree stored in the artifact.
    #[getter]
    fn max_degree(&self) -> usize {
        self.inner.max_degree()
    }

    /// The atlas limits recorded in the artifact.
    #[getter]
    fn atlas_limits(&self) -> PyCatalogAtlasLimits {
        PyCatalogAtlasLimits {
            inner: self.inner.atlas_limits(),
        }
    }

    /// The multiplicity limits recorded in the artifact.
    #[getter]
    fn multiplicity_limits(&self) -> PyMultiplicityLimits {
        PyMultiplicityLimits {
            inner: self.inner.multiplicity_limits(),
        }
    }

    /// The exact atlas operation counts recorded in the artifact.
    #[getter]
    fn work(&self) -> PyCatalogAtlasWork {
        PyCatalogAtlasWork {
            inner: self.inner.work(),
        }
    }

    /// Ordered Ext rows in source-major, target-major order.
    #[getter]
    fn ext_rows(&self) -> Vec<PyCatalogAtlasArtifactExtRow> {
        artifact_ext_rows(&self.inner)
    }

    /// Multiplicity and self-Ext result rows in deterministic order.
    #[getter]
    fn result_rows(&self) -> Vec<PyCatalogAtlasArtifactResultRow> {
        artifact_result_rows(&self.inner)
    }

    /// `complete` or `cut`.
    #[getter]
    fn status(&self) -> &'static str {
        if self.inner.status().is_complete() {
            "complete"
        } else {
            "cut"
        }
    }

    /// The typed complete or cut status.
    #[getter]
    fn enumeration_status(&self) -> PyCatalogAtlasArtifactStatus {
        PyCatalogAtlasArtifactStatus {
            inner: self.inner.status().clone(),
        }
    }

    /// The typed budget that stopped a cut, or `None` for a complete result.
    #[getter]
    fn cut_reason(&self) -> Option<PyMultiplicityCutReason> {
        self.inner
            .status()
            .cut_reason()
            .map(|inner| PyMultiplicityCutReason { inner })
    }

    /// The parsed value has not passed replay.
    #[getter]
    fn verification(&self) -> &'static str {
        "unverified"
    }

    /// The canonical non-authenticating fingerprint.
    #[getter]
    fn fingerprint(&self) -> &str {
        self.inner.fingerprint()
    }

    /// Whether the fingerprint covers the preceding canonical fields.
    #[getter]
    fn has_valid_fingerprint(&self) -> bool {
        self.inner.has_valid_fingerprint()
    }

    /// Rebuilds and verifies the embedded atlas claim.
    #[pyo3(signature = (limits=None))]
    fn verify(
        &self,
        py: Python<'_>,
        limits: Option<&PyCatalogAtlasArtifactVerifyLimits>,
    ) -> PyResult<PyVerifiedCatalogAtlasArtifact> {
        let limits = limits.map_or_else(CatalogAtlasArtifactVerifyLimits::default, |value| {
            value.inner
        });
        py.allow_threads(|| self.inner.verify(limits))
            .map(|inner| PyVerifiedCatalogAtlasArtifact { inner })
            .map_err(atlas_artifact_error)
    }

    /// The byte-exact canonical artifact JSON.
    #[getter]
    fn canonical_json(&self) -> String {
        self.inner.to_canonical_json()
    }

    fn __len__(&self) -> usize {
        self.catalog_len()
    }

    fn __repr__(&self) -> String {
        format!(
            "CatalogAtlasArtifact(status={:?}, catalog_len={}, max_degree={}, fingerprint={:?})",
            self.status(),
            self.catalog_len(),
            self.max_degree(),
            self.fingerprint()
        )
    }
}

/// A catalog atlas artifact accepted by certificate and table replay.
#[pyclass(name = "VerifiedCatalogAtlasArtifact", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyVerifiedCatalogAtlasArtifact {
    pub(crate) inner: VerifiedCatalogAtlasArtifact,
}

#[pymethods]
impl PyVerifiedCatalogAtlasArtifact {
    /// The canonical artifact that passed replay.
    #[getter]
    fn artifact(&self) -> PyCatalogAtlasArtifact {
        PyCatalogAtlasArtifact {
            inner: self.inner.artifact().clone(),
        }
    }

    /// The freshly rebuilt runtime algebra.
    #[getter]
    fn algebra(&self) -> PyAlgebra {
        PyAlgebra::pinned(self.inner.algebra().clone())
    }

    /// The freshly rebuilt complete catalog.
    #[getter]
    fn catalog(&self) -> PyIndecomposableCatalog {
        PyIndecomposableCatalog {
            inner: self.inner.catalog().clone(),
        }
    }

    /// The freshly rebuilt cached atlas.
    #[getter]
    fn atlas(&self) -> PyCatalogAtlas {
        PyCatalogAtlas::new(self.inner.atlas().clone())
    }

    /// The embedded certificate as canonical JSON.
    #[getter]
    fn certificate_json(&self) -> String {
        self.inner.artifact().certificate().to_canonical_json()
    }

    /// The explicitly recorded prime modulus.
    #[getter]
    fn field(&self) -> u64 {
        self.inner.artifact().field()
    }

    /// The classification theorem behind the catalog.
    #[getter]
    fn provenance(&self) -> &'static str {
        provenance_name(self.inner.artifact().provenance())
    }

    /// The target dimension vector used for multiplicity enumeration.
    #[getter]
    fn target_dimensions(&self) -> Vec<usize> {
        self.inner.artifact().target_dimensions().to_vec()
    }

    /// The inclusive largest Ext degree stored in the artifact.
    #[getter]
    fn max_degree(&self) -> usize {
        self.inner.artifact().max_degree()
    }

    /// `complete` or `cut`.
    #[getter]
    fn status(&self) -> &'static str {
        if self.inner.artifact().status().is_complete() {
            "complete"
        } else {
            "cut"
        }
    }

    /// The typed complete or cut status.
    #[getter]
    fn enumeration_status(&self) -> PyCatalogAtlasArtifactStatus {
        PyCatalogAtlasArtifactStatus {
            inner: self.inner.artifact().status().clone(),
        }
    }

    /// The typed budget that stopped a cut, or `None` for a complete result.
    #[getter]
    fn cut_reason(&self) -> Option<PyMultiplicityCutReason> {
        self.inner
            .artifact()
            .status()
            .cut_reason()
            .map(|inner| PyMultiplicityCutReason { inner })
    }

    /// Stable catalog identifiers in enumerator order.
    #[getter]
    fn catalog_ids(&self) -> Vec<usize> {
        self.inner.artifact().catalog_ids().to_vec()
    }

    /// The number of catalog entries named by the artifact.
    #[getter]
    fn catalog_len(&self) -> usize {
        self.inner.artifact().catalog_ids().len()
    }

    /// The atlas limits recorded in the artifact.
    #[getter]
    fn atlas_limits(&self) -> PyCatalogAtlasLimits {
        PyCatalogAtlasLimits {
            inner: self.inner.artifact().atlas_limits(),
        }
    }

    /// The multiplicity limits recorded in the artifact.
    #[getter]
    fn multiplicity_limits(&self) -> PyMultiplicityLimits {
        PyMultiplicityLimits {
            inner: self.inner.artifact().multiplicity_limits(),
        }
    }

    /// The exact atlas operation counts recorded in the artifact.
    #[getter]
    fn work(&self) -> PyCatalogAtlasWork {
        PyCatalogAtlasWork {
            inner: self.inner.artifact().work(),
        }
    }

    /// Ordered Ext rows in source-major, target-major order.
    #[getter]
    fn ext_rows(&self) -> Vec<PyCatalogAtlasArtifactExtRow> {
        artifact_ext_rows(self.inner.artifact())
    }

    /// Multiplicity and self-Ext result rows in deterministic order.
    #[getter]
    fn result_rows(&self) -> Vec<PyCatalogAtlasArtifactResultRow> {
        artifact_result_rows(self.inner.artifact())
    }

    /// The artifact passed replay.
    #[getter]
    fn verification(&self) -> &'static str {
        "replayed"
    }

    /// The byte-exact canonical artifact JSON.
    #[getter]
    fn canonical_json(&self) -> String {
        self.inner.artifact().to_canonical_json()
    }

    /// The canonical non-authenticating fingerprint.
    #[getter]
    fn fingerprint(&self) -> &str {
        self.inner.artifact().fingerprint()
    }

    /// Repeats replay with default verifier limits.
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| {
            verify_artifact(
                &self.canonical_json(),
                CatalogAtlasArtifactVerifyLimits::default(),
            )
            .is_ok()
        })
    }

    fn __repr__(&self) -> String {
        format!(
            "VerifiedCatalogAtlasArtifact(status={:?}, max_degree={}, fingerprint={:?})",
            self.status(),
            self.max_degree(),
            self.fingerprint()
        )
    }
}

/// Parses and verifies one untrusted catalog atlas artifact.
#[pyfunction]
#[pyo3(signature = (text, limits=None))]
pub(crate) fn verify_catalog_atlas_artifact(
    py: Python<'_>,
    text: &str,
    limits: Option<&PyCatalogAtlasArtifactVerifyLimits>,
) -> PyResult<PyVerifiedCatalogAtlasArtifact> {
    let limits = limits.map_or_else(CatalogAtlasArtifactVerifyLimits::default, |value| {
        value.inner
    });
    py.allow_threads(|| verify_artifact(text, limits))
        .map(|inner| PyVerifiedCatalogAtlasArtifact { inner })
        .map_err(atlas_artifact_error)
}

use auslander::derived_classification::{
    DERIVED_ATLAS_ARTIFACT_ENGINE, DERIVED_ATLAS_ARTIFACT_KIND, DERIVED_ATLAS_ARTIFACT_SCHEMA,
    DerivedAtlasArtifact, DerivedAtlasError, DerivedAtlasParseLimits, DerivedAtlasVerification,
    DerivedAtlasVerifyLimits, verify_derived_atlas_artifact,
};

use super::*;

fn atlas_error(error: DerivedAtlasError) -> PyErr {
    match error {
        DerivedAtlasError::Invariant { .. } => DefectError::new_err(error.to_string()),
        other => value_error(other),
    }
}

fn verification_value(py: Python<'_>, outcome: DerivedAtlasVerification) -> PyResult<Py<PyAny>> {
    match outcome {
        DerivedAtlasVerification::Verified(verified) => Py::new(
            py,
            PyDerivedClassification {
                inner: Arc::new(verified.classification().clone()),
                atlas: Some(Arc::new(verified.artifact().clone())),
            },
        )
        .map(Py::into_any),
        DerivedAtlasVerification::Stopped(inner) => {
            Py::new(py, PyIncompleteArtifactVerification { inner }).map(Py::into_any)
        }
    }
}

/// A canonical `derived-atlas-v1` artifact, parsed without replay.
///
/// `verify()` checks the fingerprint and replays every claim. See
/// `verify_derived_atlas` and `DerivedClassification.to_artifact`.
#[pyclass(name = "DerivedAtlasArtifact", module = "auslander", frozen)]
pub(crate) struct PyDerivedAtlasArtifact {
    inner: Arc<DerivedAtlasArtifact>,
}

#[pymethods]
impl PyDerivedAtlasArtifact {
    /// Parses canonical atlas JSON under the default parser limits.
    ///
    /// Raises ValueError for text that is malformed, not canonical, or over
    /// a parser limit.
    #[new]
    fn new(py: Python<'_>, text: &str) -> PyResult<Self> {
        py.allow_threads(|| {
            DerivedAtlasArtifact::from_json(text, DerivedAtlasParseLimits::default())
        })
        .map(|inner| Self {
            inner: Arc::new(inner),
        })
        .map_err(atlas_error)
    }

    /// The default parser ceiling on input bytes.
    #[classattr]
    fn max_input_bytes() -> usize {
        DerivedAtlasParseLimits::default().max_input_bytes
    }

    #[getter]
    fn schema(&self) -> &'static str {
        DERIVED_ATLAS_ARTIFACT_SCHEMA
    }

    #[getter]
    fn kind(&self) -> &'static str {
        DERIVED_ATLAS_ARTIFACT_KIND
    }

    #[getter]
    fn engine(&self) -> &'static str {
        DERIVED_ATLAS_ARTIFACT_ENGINE
    }

    /// The prime `p` of the field `GF(p)`.
    #[getter]
    fn field(&self) -> u64 {
        self.inner.field()
    }

    #[getter]
    fn member_count(&self) -> usize {
        self.inner.members().len()
    }

    #[getter]
    fn class_count(&self) -> usize {
        self.inner.classes().len()
    }

    #[getter]
    fn unresolved_count(&self) -> usize {
        self.inner.unresolved().len()
    }

    /// `complete` or `incomplete`, as stored.
    #[getter]
    fn status(&self) -> &'static str {
        self.inner.status().as_str()
    }

    /// `unverified`: the value has not been replayed.
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

    /// The byte-exact canonical atlas JSON.
    #[getter]
    fn canonical_json(&self) -> String {
        self.inner.to_canonical_json()
    }

    /// Replays the atlas under the default verifier limits.
    ///
    /// Returns the rebuilt `DerivedClassification`, or an
    /// `IncompleteArtifactVerification` when cancellation through `control`
    /// or a verifier ceiling stopped the replay. Raises ValueError when a
    /// claim does not replay.
    #[pyo3(signature = (control=None))]
    fn verify(
        &self,
        py: Python<'_>,
        control: Option<&PyComputationControl>,
    ) -> PyResult<Py<PyAny>> {
        let control = control_of(control);
        let outcome = py
            .allow_threads(|| {
                self.inner
                    .verify(DerivedAtlasVerifyLimits::default(), &control)
            })
            .map_err(atlas_error)?;
        verification_value(py, outcome)
    }

    fn __repr__(&self) -> String {
        format!(
            "DerivedAtlasArtifact(members={}, classes={}, status={:?}, fingerprint={:?})",
            self.member_count(),
            self.class_count(),
            self.status(),
            self.fingerprint()
        )
    }
}

#[pymethods]
impl PyDerivedClassification {
    /// The `derived-atlas-v1` artifact of this result.
    ///
    /// A replayed result returns the atlas it was replayed from. Raises
    /// ValueError when cancellation stopped a reading, since no replay can
    /// reproduce it.
    fn to_artifact(&self, py: Python<'_>) -> PyResult<PyDerivedAtlasArtifact> {
        if let Some(atlas) = &self.atlas {
            return Ok(PyDerivedAtlasArtifact {
                inner: atlas.clone(),
            });
        }
        py.allow_threads(|| self.inner.to_artifact())
            .map(|inner| PyDerivedAtlasArtifact {
                inner: Arc::new(inner),
            })
            .map_err(atlas_error)
    }

    /// Writes the canonical atlas JSON to `path` with an atomic replace.
    ///
    /// Returns the path as a `pathlib.Path`. Raises as `to_artifact()` does.
    fn export<'py>(&self, py: Python<'py>, path: Bound<'py, PyAny>) -> PyResult<Bound<'py, PyAny>> {
        let text = self.to_artifact(py)?.canonical_json();
        py.import("auslander.checkpoint")?
            .getattr("_write_canonical_json")?
            .call1((path, text))
    }

    /// The fingerprint of the atlas this result was replayed from, or None
    /// for a computed result.
    #[getter]
    fn fingerprint(&self) -> Option<&str> {
        self.atlas.as_deref().map(DerivedAtlasArtifact::fingerprint)
    }
}

/// Parses and replays one untrusted derived atlas.
///
/// `auslander.verify_derived_atlas` reads a path first; this binding takes
/// the text.
#[pyfunction(name = "_verify_derived_atlas")]
#[pyo3(signature = (text, control=None))]
pub(crate) fn py_verify_derived_atlas(
    py: Python<'_>,
    text: &str,
    control: Option<&PyComputationControl>,
) -> PyResult<Py<PyAny>> {
    let control = control_of(control);
    let limits = DerivedAtlasVerifyLimits::default();
    let outcome = py
        .allow_threads(|| verify_derived_atlas_artifact(text, limits, &control))
        .map_err(atlas_error)?;
    verification_value(py, outcome)
}

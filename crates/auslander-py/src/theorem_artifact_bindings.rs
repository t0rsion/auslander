use auslander::theorem_artifact::{
    SELF_EXT_LOCUS_ARTIFACT_KIND, SELF_EXT_LOCUS_ARTIFACT_SCHEMA, SelfExtLocusArtifact,
    SelfExtLocusArtifactError, SelfExtLocusVerifyLimits, VerifiedSelfExtLocusArtifact,
    verify_self_ext_locus_artifact as verify_artifact,
};

use super::*;

fn theorem_artifact_error(error: SelfExtLocusArtifactError) -> PyErr {
    match error {
        SelfExtLocusArtifactError::Checkpoint(error) => checkpoint_error(error),
        SelfExtLocusArtifactError::CounterOverflow { .. } => {
            PyOverflowError::new_err(error.to_string())
        }
        SelfExtLocusArtifactError::Ext(error) => ext_error(error),
        other => value_error(other),
    }
}

/// Parser and independent-verification ceilings for one self-Ext locus.
#[pyclass(name = "SelfExtLocusVerifyLimits", module = "auslander", frozen)]
#[derive(Clone, Copy)]
pub(crate) struct PySelfExtLocusVerifyLimits {
    inner: SelfExtLocusVerifyLimits,
}

#[pymethods]
impl PySelfExtLocusVerifyLimits {
    #[new]
    #[pyo3(signature = (
        checkpoint=None,
        max_input_bytes=None,
        max_vanishing_indices=None,
        max_integer_digits=None,
        max_string_bytes=None,
        max_representatives=None,
        max_degree_span=None,
        max_ext_spaces=None,
    ))]
    #[allow(clippy::too_many_arguments)]
    fn new(
        checkpoint: Option<&PyHomologicalStreamVerifyLimits>,
        max_input_bytes: Option<usize>,
        max_vanishing_indices: Option<usize>,
        max_integer_digits: Option<usize>,
        max_string_bytes: Option<usize>,
        max_representatives: Option<usize>,
        max_degree_span: Option<usize>,
        max_ext_spaces: Option<usize>,
    ) -> Self {
        let defaults = SelfExtLocusVerifyLimits::default();
        let checkpoint = checkpoint.map_or(defaults.checkpoint, |value| value.inner);
        let mut parse = defaults.parse;
        parse.checkpoint = checkpoint.parse;
        parse.max_input_bytes = max_input_bytes.unwrap_or(parse.max_input_bytes);
        parse.max_vanishing_indices = max_vanishing_indices.unwrap_or(parse.max_vanishing_indices);
        parse.max_integer_digits = max_integer_digits.unwrap_or(parse.max_integer_digits);
        parse.max_string_bytes = max_string_bytes.unwrap_or(parse.max_string_bytes);
        Self {
            inner: SelfExtLocusVerifyLimits {
                parse,
                checkpoint,
                max_representatives: max_representatives.unwrap_or(defaults.max_representatives),
                max_degree_span: max_degree_span.unwrap_or(defaults.max_degree_span),
                max_ext_spaces: max_ext_spaces.unwrap_or(defaults.max_ext_spaces),
            },
        }
    }

    #[getter]
    fn checkpoint(&self) -> PyHomologicalStreamVerifyLimits {
        PyHomologicalStreamVerifyLimits {
            inner: self.inner.checkpoint,
        }
    }

    #[getter]
    fn max_input_bytes(&self) -> usize {
        self.inner.parse.max_input_bytes
    }

    #[getter]
    fn max_vanishing_indices(&self) -> usize {
        self.inner.parse.max_vanishing_indices
    }

    #[getter]
    fn max_integer_digits(&self) -> usize {
        self.inner.parse.max_integer_digits
    }

    #[getter]
    fn max_string_bytes(&self) -> usize {
        self.inner.parse.max_string_bytes
    }

    #[getter]
    fn max_representatives(&self) -> usize {
        self.inner.max_representatives
    }

    #[getter]
    fn max_degree_span(&self) -> usize {
        self.inner.max_degree_span
    }

    #[getter]
    fn max_ext_spaces(&self) -> usize {
        self.inner.max_ext_spaces
    }

    fn __repr__(&self) -> String {
        format!(
            "SelfExtLocusVerifyLimits(max_input_bytes={}, max_representatives={}, max_degree_span={}, max_ext_spaces={})",
            self.max_input_bytes(),
            self.max_representatives(),
            self.max_degree_span(),
            self.max_ext_spaces()
        )
    }
}

/// A canonical finite-census claim about positive self-Ext vanishing.
#[pyclass(name = "SelfExtLocusArtifact", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PySelfExtLocusArtifact {
    inner: SelfExtLocusArtifact,
}

#[pymethods]
impl PySelfExtLocusArtifact {
    /// Parse canonical artifact JSON without independent verification.
    #[new]
    #[pyo3(signature = (text, limits=None))]
    fn new(text: &str, limits: Option<&PySelfExtLocusVerifyLimits>) -> PyResult<Self> {
        let limits = limits.map_or_else(SelfExtLocusVerifyLimits::default, |value| value.inner);
        SelfExtLocusArtifact::from_json(text, limits.parse)
            .map(|inner| Self { inner })
            .map_err(theorem_artifact_error)
    }

    #[staticmethod]
    #[pyo3(signature = (text, limits=None))]
    fn from_json(text: &str, limits: Option<&PySelfExtLocusVerifyLimits>) -> PyResult<Self> {
        Self::new(text, limits)
    }

    #[getter]
    fn schema(&self) -> &'static str {
        SELF_EXT_LOCUS_ARTIFACT_SCHEMA
    }

    #[getter]
    fn kind(&self) -> &'static str {
        SELF_EXT_LOCUS_ARTIFACT_KIND
    }

    #[getter]
    fn checkpoint(&self) -> PyHomologicalCheckpoint {
        PyHomologicalCheckpoint {
            inner: self.inner.checkpoint().clone(),
        }
    }

    #[getter]
    fn first_degree(&self) -> usize {
        self.inner.first_degree()
    }

    #[getter]
    fn last_degree(&self) -> usize {
        self.inner.last_degree()
    }

    #[getter]
    fn vanishing_indices(&self) -> Vec<usize> {
        self.inner.vanishing_indices().to_vec()
    }

    #[getter]
    fn vanishing_count(&self) -> usize {
        self.inner.vanishing_indices().len()
    }

    #[getter]
    fn canonical_json(&self) -> String {
        self.inner.to_canonical_json()
    }

    #[getter]
    fn fingerprint(&self) -> &str {
        self.inner.fingerprint()
    }

    #[pyo3(signature = (limits=None))]
    fn verify(
        &self,
        py: Python<'_>,
        limits: Option<&PySelfExtLocusVerifyLimits>,
    ) -> PyResult<PyVerifiedSelfExtLocusArtifact> {
        let limits = limits.map_or_else(SelfExtLocusVerifyLimits::default, |value| value.inner);
        py.allow_threads(|| self.inner.verify(limits))
            .map(|inner| PyVerifiedSelfExtLocusArtifact { inner })
            .map_err(theorem_artifact_error)
    }

    fn __repr__(&self) -> String {
        format!(
            "SelfExtLocusArtifact(degrees={}..={}, vanishing_count={}, fingerprint={:?})",
            self.first_degree(),
            self.last_degree(),
            self.vanishing_count(),
            self.fingerprint()
        )
    }
}

/// A self-Ext locus accepted by checkpoint replay and generic Ext calculation.
#[pyclass(name = "VerifiedSelfExtLocusArtifact", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyVerifiedSelfExtLocusArtifact {
    inner: VerifiedSelfExtLocusArtifact,
}

#[pymethods]
impl PyVerifiedSelfExtLocusArtifact {
    #[getter]
    fn artifact(&self) -> PySelfExtLocusArtifact {
        PySelfExtLocusArtifact {
            inner: self.inner.artifact().clone(),
        }
    }

    #[getter]
    fn checkpoint(&self) -> PyVerifiedHomologicalCheckpoint {
        PyVerifiedHomologicalCheckpoint {
            inner: self.inner.checkpoint().clone(),
        }
    }

    #[getter]
    fn canonical_json(&self) -> String {
        self.inner.artifact().to_canonical_json()
    }

    #[getter]
    fn fingerprint(&self) -> &str {
        self.inner.artifact().fingerprint()
    }

    #[getter]
    fn first_degree(&self) -> usize {
        self.inner.artifact().first_degree()
    }

    #[getter]
    fn last_degree(&self) -> usize {
        self.inner.artifact().last_degree()
    }

    #[getter]
    fn vanishing_indices(&self) -> Vec<usize> {
        self.inner.artifact().vanishing_indices().to_vec()
    }

    #[getter]
    fn vanishing_count(&self) -> usize {
        self.inner.artifact().vanishing_indices().len()
    }

    fn __repr__(&self) -> String {
        format!(
            "VerifiedSelfExtLocusArtifact(degrees={}..={}, vanishing_count={}, fingerprint={:?})",
            self.first_degree(),
            self.last_degree(),
            self.vanishing_count(),
            self.fingerprint()
        )
    }
}

/// Build one canonical self-Ext locus from a replay-verified complete checkpoint.
#[pyfunction]
pub(crate) fn build_self_ext_locus_artifact(
    checkpoint: &PyVerifiedHomologicalCheckpoint,
    first_degree: usize,
    last_degree: usize,
) -> PyResult<PySelfExtLocusArtifact> {
    SelfExtLocusArtifact::from_verified_checkpoint(&checkpoint.inner, first_degree, last_degree)
        .map(|inner| PySelfExtLocusArtifact { inner })
        .map_err(theorem_artifact_error)
}

/// Parse and independently verify one untrusted self-Ext locus artifact.
#[pyfunction]
#[pyo3(signature = (text, limits=None))]
pub(crate) fn verify_self_ext_locus_artifact(
    py: Python<'_>,
    text: &str,
    limits: Option<&PySelfExtLocusVerifyLimits>,
) -> PyResult<PyVerifiedSelfExtLocusArtifact> {
    let limits = limits.map_or_else(SelfExtLocusVerifyLimits::default, |value| value.inner);
    py.allow_threads(|| verify_artifact(text, limits))
        .map(|inner| PyVerifiedSelfExtLocusArtifact { inner })
        .map_err(theorem_artifact_error)
}

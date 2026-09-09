use super::super::*;
use super::execute::{checkpoint_from_outcome, verify_census_inner};
use super::limits::{PyCensusLimits, PyCensusVerifyLimits};
use super::records::{
    PyCensusAssignment, PyCensusCutReason, PyCensusRepresentative, census_counts, census_reason,
    census_status,
};

/// A canonical census result or replayable prefix checkpoint.
#[pyclass(name = "CensusCheckpoint", module = "auslander", frozen)]
pub(crate) struct PyCensusCheckpoint {
    pub(crate) inner: CensusPortable,
}

#[pymethods]
impl PyCensusCheckpoint {
    /// Parse one canonical census JSON value without replaying it.
    #[new]
    #[pyo3(signature = (text, limits=None))]
    fn new(text: &str, limits: Option<&PyCensusVerifyLimits>) -> PyResult<Self> {
        let parse_limits =
            limits.map_or_else(CensusParseLimits::default, |value| value.inner.parse);
        CensusPortable::from_json(text, parse_limits)
            .map(|inner| Self { inner })
            .map_err(super::execute::census_portable_error)
    }

    /// Parse one canonical census JSON value without replaying it.
    #[staticmethod]
    #[pyo3(signature = (text, limits=None))]
    fn from_json(text: &str, limits: Option<&PyCensusVerifyLimits>) -> PyResult<Self> {
        Self::new(text, limits)
    }

    /// Run a checked finite census from an algebra and dimension vector.
    #[staticmethod]
    #[pyo3(signature = (algebra, dimensions, field=None, limits=None, control=None))]
    fn run(
        py: Python<'_>,
        algebra: &PyAlgebra,
        dimensions: Vec<usize>,
        field: Option<&PyPrimeField>,
        limits: Option<&PyCensusLimits>,
        control: Option<&PyComputationControl>,
    ) -> PyResult<Self> {
        super::execute::run_census_inner(py, algebra, dimensions, field, limits, control)
    }

    /// The embedded completion certificate as canonical JSON.
    #[getter]
    fn certificate_json(&self) -> String {
        self.inner.certificate().to_canonical_json()
    }

    /// The prime field named by the embedded completion certificate.
    #[getter]
    fn field(&self) -> u64 {
        self.inner.certificate().field
    }

    /// The dimension vector indexed by quiver vertex.
    #[getter]
    fn dimensions(&self) -> Vec<usize> {
        self.inner.dimensions().to_vec()
    }

    /// The checked number of raw matrix tuples.
    #[getter]
    fn raw_space_size(&self) -> u128 {
        self.inner.raw_space_size()
    }

    /// The number of scalar matrix entries in one candidate.
    #[getter]
    fn coordinate_count(&self) -> usize {
        self.inner.coordinate_count()
    }

    /// The first raw candidate not processed by this checkpoint.
    #[getter]
    fn cursor(&self) -> u128 {
        self.inner.cursor()
    }

    /// The exact resource limits recorded in this checkpoint.
    #[getter]
    fn limits(&self) -> PyCensusLimits {
        PyCensusLimits {
            inner: self.inner.limits(),
        }
    }

    /// The number of fully processed raw candidates.
    #[getter]
    fn candidates(&self) -> usize {
        self.inner.candidates()
    }

    /// The number of relation-valid candidates classified into classes.
    #[getter]
    fn accepted_modules(&self) -> usize {
        self.inner.accepted_modules()
    }

    /// The number of relation-invalid candidates.
    #[getter]
    fn rejected_candidates(&self) -> usize {
        self.inner.rejected_candidates()
    }

    /// The number of completed isomorphism checks.
    #[getter]
    fn isomorphism_checks(&self) -> usize {
        self.inner.isomorphism_checks()
    }

    /// The candidate and comparison work units used by this checkpoint.
    #[getter]
    fn work_units(&self) -> usize {
        self.inner.work_units()
    }

    /// The exact counters as a mapping.
    #[getter]
    fn counts(&self) -> BTreeMap<&'static str, usize> {
        census_counts(&self.inner)
    }

    /// The retained representatives in first-seen order.
    #[getter]
    fn representatives(&self) -> Vec<PyCensusRepresentative> {
        self.inner
            .representatives()
            .iter()
            .cloned()
            .map(|inner| PyCensusRepresentative { inner })
            .collect()
    }

    /// The retained duplicate assignments in candidate order.
    #[getter]
    fn assignments(&self) -> Vec<PyCensusAssignment> {
        self.inner
            .assignments()
            .iter()
            .cloned()
            .map(|inner| PyCensusAssignment { inner })
            .collect()
    }

    /// The number of retained representatives without copying their records.
    #[getter]
    fn representative_count(&self) -> usize {
        self.inner.representatives().len()
    }

    /// The number of retained assignments without copying their witnesses.
    #[getter]
    fn assignment_count(&self) -> usize {
        self.inner.assignments().len()
    }

    /// `complete` or `cut`.
    #[getter]
    fn status(&self) -> &'static str {
        census_status(self.inner.status())
    }

    /// The exact cut reason, or `None` for a complete result.
    #[getter]
    fn cut_reason(&self) -> Option<PyCensusCutReason> {
        census_reason(self.inner.status())
    }

    /// The byte-exact canonical census JSON.
    #[getter]
    fn canonical_json(&self) -> String {
        self.inner.to_canonical_json()
    }

    /// The canonical census fingerprint.
    #[getter]
    fn fingerprint(&self) -> &str {
        self.inner.fingerprint()
    }

    /// Replay this checkpoint against a freshly rebuilt algebra.
    #[pyo3(signature = (limits=None))]
    fn verify(
        &self,
        py: Python<'_>,
        limits: Option<&PyCensusVerifyLimits>,
    ) -> PyResult<PyVerifiedCensusCheckpoint> {
        let limits = limits.map_or_else(CensusVerifyLimits::default, |value| value.inner);
        verify_census_inner(py, &self.inner, limits)
    }

    fn __repr__(&self) -> String {
        format!(
            "CensusCheckpoint(status={:?}, cursor={}, fingerprint={:?})",
            self.status(),
            self.cursor(),
            self.fingerprint()
        )
    }
}

/// A census checkpoint that passed certificate and prefix replay checks.
#[pyclass(name = "VerifiedCensusCheckpoint", module = "auslander", frozen)]
pub(crate) struct PyVerifiedCensusCheckpoint {
    pub(crate) inner: VerifiedCensus,
}

#[pymethods]
impl PyVerifiedCensusCheckpoint {
    /// The embedded completion certificate as canonical JSON.
    #[getter]
    fn certificate_json(&self) -> String {
        self.inner.portable().certificate().to_canonical_json()
    }

    /// The prime field named by the embedded completion certificate.
    #[getter]
    fn field(&self) -> u64 {
        self.inner.portable().certificate().field
    }

    /// The dimension vector indexed by quiver vertex.
    #[getter]
    fn dimensions(&self) -> Vec<usize> {
        self.inner.portable().dimensions().to_vec()
    }

    /// The checked number of raw matrix tuples.
    #[getter]
    fn raw_space_size(&self) -> u128 {
        self.inner.portable().raw_space_size()
    }

    /// The number of scalar matrix entries in one candidate.
    #[getter]
    fn coordinate_count(&self) -> usize {
        self.inner.portable().coordinate_count()
    }

    /// The first raw candidate not processed by this checkpoint.
    #[getter]
    fn cursor(&self) -> u128 {
        self.inner.portable().cursor()
    }

    /// The exact resource limits recorded in this checkpoint.
    #[getter]
    fn limits(&self) -> PyCensusLimits {
        PyCensusLimits {
            inner: self.inner.portable().limits(),
        }
    }

    /// The number of fully processed raw candidates.
    #[getter]
    fn candidates(&self) -> usize {
        self.inner.portable().candidates()
    }

    /// The number of relation-valid candidates classified into classes.
    #[getter]
    fn accepted_modules(&self) -> usize {
        self.inner.portable().accepted_modules()
    }

    /// The number of relation-invalid candidates.
    #[getter]
    fn rejected_candidates(&self) -> usize {
        self.inner.portable().rejected_candidates()
    }

    /// The number of completed isomorphism checks.
    #[getter]
    fn isomorphism_checks(&self) -> usize {
        self.inner.portable().isomorphism_checks()
    }

    /// The candidate and comparison work units used by this checkpoint.
    #[getter]
    fn work_units(&self) -> usize {
        self.inner.portable().work_units()
    }

    /// The exact counters as a mapping.
    #[getter]
    fn counts(&self) -> BTreeMap<&'static str, usize> {
        census_counts(self.inner.portable())
    }

    /// The retained representatives in first-seen order.
    #[getter]
    fn representatives(&self) -> Vec<PyCensusRepresentative> {
        self.inner
            .portable()
            .representatives()
            .iter()
            .cloned()
            .map(|inner| PyCensusRepresentative { inner })
            .collect()
    }

    /// The retained duplicate assignments in candidate order.
    #[getter]
    fn assignments(&self) -> Vec<PyCensusAssignment> {
        self.inner
            .portable()
            .assignments()
            .iter()
            .cloned()
            .map(|inner| PyCensusAssignment { inner })
            .collect()
    }

    /// The number of retained representatives without copying their records.
    #[getter]
    fn representative_count(&self) -> usize {
        self.inner.portable().representatives().len()
    }

    /// The number of retained assignments without copying their witnesses.
    #[getter]
    fn assignment_count(&self) -> usize {
        self.inner.portable().assignments().len()
    }

    /// `complete` or `cut`.
    #[getter]
    fn status(&self) -> &'static str {
        census_status(self.inner.portable().status())
    }

    /// The exact cut reason, or `None` for a complete result.
    #[getter]
    fn cut_reason(&self) -> Option<PyCensusCutReason> {
        census_reason(self.inner.portable().status())
    }

    /// The byte-exact canonical census JSON.
    #[getter]
    fn canonical_json(&self) -> String {
        self.inner.portable().to_canonical_json()
    }

    /// The canonical census fingerprint.
    #[getter]
    fn fingerprint(&self) -> &str {
        self.inner.portable().fingerprint()
    }

    /// Continue this verified cut with new absolute limits.
    #[pyo3(signature = (limits=None, control=None))]
    fn resume(
        &self,
        py: Python<'_>,
        limits: Option<&PyCensusLimits>,
        control: Option<&PyComputationControl>,
    ) -> PyResult<PyCensusCheckpoint> {
        let limits = limits.map_or_else(
            || CensusLimits {
                retention: self.inner.portable().limits().retention,
                ..CensusLimits::default()
            },
            |value| value.inner,
        );
        let control = control.map_or_else(ComputationControl::new, |value| value.inner.clone());
        let outcome = py
            .allow_threads(|| self.inner.resume(limits, Some(&control)))
            .map_err(super::execute::census_resume_error)?;
        checkpoint_from_outcome(outcome)
    }

    fn __repr__(&self) -> String {
        format!(
            "VerifiedCensusCheckpoint(status={:?}, cursor={}, fingerprint={:?})",
            self.status(),
            self.cursor(),
            self.fingerprint()
        )
    }
}

use auslander::catalog_coordinates::{
    self as catalog_coordinates, CatalogCoordinateCutReason, CatalogCoordinateError,
    CatalogCoordinateLimits, CatalogCoordinateMatch, CatalogCoordinateOutcome,
    CatalogCoordinateProgress, CatalogCoordinateUnknown,
    CatalogCoordinates as RustCatalogCoordinates,
};

use super::*;

fn coordinate_error(error: CatalogCoordinateError) -> PyErr {
    let message = error.to_string();
    match error {
        CatalogCoordinateError::FieldMismatch { .. } | CatalogCoordinateError::DifferentAlgebra => {
            PyValueError::new_err(message)
        }
        CatalogCoordinateError::Isomorphism { .. }
        | CatalogCoordinateError::CatalogInvariantViolation { .. } => DefectError::new_err(message),
        CatalogCoordinateError::MultiplicityOverflow { .. }
        | CatalogCoordinateError::WorkOverflow => PyOverflowError::new_err(message),
    }
}

fn wrapped_progress(inner: CatalogCoordinateProgress) -> PyCatalogCoordinateProgress {
    PyCatalogCoordinateProgress { inner }
}

fn wrapped_match(inner: &CatalogCoordinateMatch) -> PyCatalogCoordinateMatch {
    PyCatalogCoordinateMatch {
        inner: inner.clone(),
    }
}

/// Resource limits for matching one module against a complete catalog.
#[pyclass(name = "CatalogCoordinateLimits", module = "auslander", frozen)]
#[derive(Clone, Copy)]
pub(crate) struct PyCatalogCoordinateLimits {
    pub(crate) inner: CatalogCoordinateLimits,
}

#[pymethods]
impl PyCatalogCoordinateLimits {
    /// `CatalogCoordinateLimits(max_work_units=None)` keeps the Rust default when omitted.
    #[new]
    #[pyo3(signature = (max_work_units = None))]
    fn new(max_work_units: Option<usize>) -> Self {
        let defaults = CatalogCoordinateLimits::default();
        Self {
            inner: CatalogCoordinateLimits {
                max_work_units: max_work_units.unwrap_or(defaults.max_work_units),
            },
        }
    }

    /// Maximum number of completed catalog isomorphism checks.
    #[getter]
    fn max_work_units(&self) -> usize {
        self.inner.max_work_units
    }

    fn __repr__(&self) -> String {
        format!(
            "CatalogCoordinateLimits(max_work_units={})",
            self.max_work_units()
        )
    }
}

/// One checked isomorphism from a decomposed summand to a catalog entry.
#[pyclass(name = "CatalogCoordinateMatch", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyCatalogCoordinateMatch {
    pub(crate) inner: CatalogCoordinateMatch,
}

#[pymethods]
impl PyCatalogCoordinateMatch {
    /// The summand position in the decomposition.
    #[getter]
    fn summand(&self) -> usize {
        self.inner.summand()
    }

    /// The matched catalog entry.
    #[getter]
    fn catalog_entry(&self) -> usize {
        self.inner.catalog_entry()
    }

    /// The checked isomorphism from the summand to the catalog entry.
    #[getter]
    fn witness(&self) -> PyMorphism {
        self.inner.witness().into()
    }

    fn __repr__(&self) -> String {
        format!(
            "CatalogCoordinateMatch(summand={}, catalog_entry={})",
            self.summand(),
            self.catalog_entry()
        )
    }
}

/// Checked prefix data for an exact, unknown, or cut coordinate result.
#[pyclass(name = "CatalogCoordinateProgress", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyCatalogCoordinateProgress {
    pub(crate) inner: CatalogCoordinateProgress,
}

#[pymethods]
impl PyCatalogCoordinateProgress {
    /// The verified direct-sum decomposition used by coordinate matching.
    #[getter]
    fn decomposition(&self) -> PyDecomposition {
        PyDecomposition {
            inner: self.inner.decomposition().clone(),
        }
    }

    /// Multiplicities certified so far, in catalog order.
    #[getter]
    fn multiplicities(&self) -> Vec<usize> {
        self.inner.multiplicities().to_vec()
    }

    /// Checked summand matches certified so far.
    #[getter]
    fn matches(&self) -> Vec<PyCatalogCoordinateMatch> {
        self.inner.matches().iter().map(wrapped_match).collect()
    }

    /// The number of completed catalog isomorphism checks.
    #[getter]
    fn work_units(&self) -> usize {
        self.inner.work_units()
    }

    /// Rechecks only the decomposition and witnesses stored in this prefix.
    /// It does not certify a complete coordinate vector.
    #[pyo3(text_signature = "($self, catalog, module)")]
    fn verify(
        &self,
        py: Python<'_>,
        catalog: &PyIndecomposableCatalog,
        module: &PyRightModule,
    ) -> bool {
        py.allow_threads(|| self.inner.verify(&catalog.inner, &module.inner))
    }

    /// The evidence was produced by the coordinate computation.
    #[getter]
    fn verification(&self) -> &'static str {
        "computed"
    }

    fn __len__(&self) -> usize {
        self.inner.matches().len()
    }

    fn __repr__(&self) -> String {
        format!(
            "CatalogCoordinateProgress(summands={}, matches={}, work_units={})",
            self.inner.decomposition().summands().len(),
            self.inner.matches().len(),
            self.inner.work_units()
        )
    }
}

/// Complete catalog coordinates with a verified multiplicity vector.
#[pyclass(name = "CatalogCoordinates", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyCatalogCoordinates {
    pub(crate) inner: RustCatalogCoordinates,
    pub(crate) progress: CatalogCoordinateProgress,
}

#[pymethods]
impl PyCatalogCoordinates {
    /// The verified runtime algebra named by the coordinate result.
    #[getter]
    fn algebra(&self) -> PyAlgebra {
        PyAlgebra::pinned(self.inner.algebra().clone())
    }

    /// The prime field of the coordinate result.
    #[getter]
    fn field(&self) -> PyPrimeField {
        PyPrimeField {
            inner: self.inner.algebra().field(),
        }
    }

    /// The classification theorem carried by the catalog.
    #[getter]
    fn provenance(&self) -> &'static str {
        provenance_name(self.inner.provenance())
    }

    /// The exact multiplicity vector in catalog order.
    #[getter]
    fn multiplicities(&self) -> Vec<usize> {
        self.inner.multiplicities().to_vec()
    }

    /// The verified decomposition of the input module.
    #[getter]
    fn decomposition(&self) -> PyDecomposition {
        PyDecomposition {
            inner: self.inner.decomposition().clone(),
        }
    }

    /// One checked isomorphism per decomposed summand, in summand order.
    #[getter]
    fn matches(&self) -> Vec<PyCatalogCoordinateMatch> {
        self.inner.matches().iter().map(wrapped_match).collect()
    }

    /// The completed catalog isomorphism checks.
    #[getter]
    fn work_units(&self) -> usize {
        self.inner.work_units()
    }

    /// The exact matching prefix, exposed with the same shape as cut results.
    #[getter]
    fn progress(&self) -> PyCatalogCoordinateProgress {
        wrapped_progress(self.progress.clone())
    }

    /// `exact` for this result.
    #[getter]
    fn status(&self) -> &'static str {
        "exact"
    }

    /// Whether every decomposed summand matched a catalog entry.
    #[getter]
    fn is_exact(&self) -> bool {
        true
    }

    /// The evidence was produced by the coordinate computation.
    #[getter]
    fn verification(&self) -> &'static str {
        "computed"
    }

    /// Rechecks the decomposition, multiplicities, and every witness.
    #[pyo3(text_signature = "($self, catalog, module)")]
    fn verify(
        &self,
        py: Python<'_>,
        catalog: &PyIndecomposableCatalog,
        module: &PyRightModule,
    ) -> bool {
        py.allow_threads(|| self.inner.verify(&catalog.inner, &module.inner))
    }

    fn __len__(&self) -> usize {
        self.inner.matches().len()
    }

    fn __repr__(&self) -> String {
        format!(
            "CatalogCoordinates(multiplicities={:?}, work_units={})",
            self.inner.multiplicities(),
            self.inner.work_units()
        )
    }
}

/// Why an exact coordinate decision stayed unknown.
#[pyclass(name = "CatalogCoordinateUnknownReason", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyCatalogCoordinateUnknownReason {
    pub(crate) inner: CatalogCoordinateUnknown,
}

#[pymethods]
impl PyCatalogCoordinateUnknownReason {
    /// `undetermined_summand` or `isomorphism`.
    #[getter]
    fn kind(&self) -> &'static str {
        match &self.inner {
            CatalogCoordinateUnknown::UndeterminedSummand { .. } => "undetermined_summand",
            CatalogCoordinateUnknown::Isomorphism { .. } => "isomorphism",
        }
    }

    /// The undecided summand position.
    #[getter]
    fn summand(&self) -> usize {
        match &self.inner {
            CatalogCoordinateUnknown::UndeterminedSummand { summand, .. }
            | CatalogCoordinateUnknown::Isomorphism { summand, .. } => *summand,
        }
    }

    /// The catalog entry involved in an undecided isomorphism, if present.
    #[getter]
    fn catalog_entry(&self) -> Option<usize> {
        match &self.inner {
            CatalogCoordinateUnknown::UndeterminedSummand { .. } => None,
            CatalogCoordinateUnknown::Isomorphism { catalog_entry, .. } => Some(*catalog_entry),
        }
    }

    /// The exhausted decomposition attempts, if the summand stayed undecided.
    #[getter]
    fn attempts(&self) -> Option<u32> {
        match &self.inner {
            CatalogCoordinateUnknown::UndeterminedSummand { attempts, .. } => Some(*attempts),
            CatalogCoordinateUnknown::Isomorphism { .. } => None,
        }
    }

    /// The generic isomorphism reason, if present.
    #[getter]
    fn detail(&self) -> Option<String> {
        match &self.inner {
            CatalogCoordinateUnknown::UndeterminedSummand { .. } => None,
            CatalogCoordinateUnknown::Isomorphism { reason, .. } => Some(reason.clone()),
        }
    }

    fn __str__(&self) -> String {
        self.inner.to_string()
    }

    fn __repr__(&self) -> String {
        format!(
            "CatalogCoordinateUnknownReason(kind={:?}, summand={})",
            self.kind(),
            self.summand()
        )
    }
}

/// A coordinate request whose decomposition or isomorphism matching stayed unknown.
#[pyclass(name = "CatalogCoordinateUnknown", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyCatalogCoordinateUnknown {
    pub(crate) progress: CatalogCoordinateProgress,
    pub(crate) reason: CatalogCoordinateUnknown,
}

#[pymethods]
impl PyCatalogCoordinateUnknown {
    /// The checked prefix available before the undecided operation.
    #[getter]
    fn progress(&self) -> PyCatalogCoordinateProgress {
        wrapped_progress(self.progress.clone())
    }

    /// The typed undecided operation.
    #[getter]
    fn reason(&self) -> PyCatalogCoordinateUnknownReason {
        PyCatalogCoordinateUnknownReason {
            inner: self.reason.clone(),
        }
    }

    /// `undetermined_summand` or `isomorphism`.
    #[getter]
    fn kind(&self) -> &'static str {
        self.reason().kind()
    }

    /// The undecided summand position.
    #[getter]
    fn summand(&self) -> usize {
        self.reason().summand()
    }

    /// The catalog entry involved in an undecided isomorphism, if present.
    #[getter]
    fn catalog_entry(&self) -> Option<usize> {
        self.reason().catalog_entry()
    }

    /// The exhausted decomposition attempts, if present.
    #[getter]
    fn attempts(&self) -> Option<u32> {
        self.reason().attempts()
    }

    /// The generic isomorphism reason, if present.
    #[getter]
    fn detail(&self) -> Option<String> {
        self.reason().detail()
    }

    /// The decomposition retained in the checked prefix.
    #[getter]
    fn decomposition(&self) -> PyDecomposition {
        self.progress().decomposition()
    }

    /// Multiplicities certified before the undecided operation.
    #[getter]
    fn multiplicities(&self) -> Vec<usize> {
        self.progress.multiplicities().to_vec()
    }

    /// Checked summand matches certified before the undecided operation.
    #[getter]
    fn matches(&self) -> Vec<PyCatalogCoordinateMatch> {
        self.progress.matches().iter().map(wrapped_match).collect()
    }

    /// The completed catalog isomorphism checks.
    #[getter]
    fn work_units(&self) -> usize {
        self.progress.work_units()
    }

    /// `unknown` for this result.
    #[getter]
    fn status(&self) -> &'static str {
        "unknown"
    }

    /// Whether every summand matched a catalog entry.
    #[getter]
    fn is_exact(&self) -> bool {
        false
    }

    /// Rechecks only the retained decomposition and stored witnesses.
    /// It does not certify completeness or recheck the unknown reason.
    #[pyo3(text_signature = "($self, catalog, module)")]
    fn verify(
        &self,
        py: Python<'_>,
        catalog: &PyIndecomposableCatalog,
        module: &PyRightModule,
    ) -> bool {
        py.allow_threads(|| self.progress.verify(&catalog.inner, &module.inner))
    }

    /// The evidence was produced by the coordinate computation.
    #[getter]
    fn verification(&self) -> &'static str {
        "computed"
    }

    fn __repr__(&self) -> String {
        format!(
            "CatalogCoordinateUnknown(summand={}, kind={:?})",
            self.summand(),
            self.kind()
        )
    }
}

/// Why matching stopped before the next catalog entry could be checked.
#[pyclass(name = "CatalogCoordinateCutReason", module = "auslander", frozen)]
#[derive(Clone, Copy)]
pub(crate) struct PyCatalogCoordinateCutReason {
    pub(crate) inner: CatalogCoordinateCutReason,
}

#[pymethods]
impl PyCatalogCoordinateCutReason {
    /// `work_limit` for the matching limit.
    #[getter]
    fn kind(&self) -> &'static str {
        "work_limit"
    }

    /// The maximum number of catalog isomorphism checks.
    #[getter]
    fn limit(&self) -> usize {
        match self.inner {
            CatalogCoordinateCutReason::WorkLimit { limit } => limit,
        }
    }

    fn __str__(&self) -> String {
        self.inner.to_string()
    }

    fn __repr__(&self) -> String {
        format!(
            "CatalogCoordinateCutReason(kind={:?}, limit={})",
            self.kind(),
            self.limit()
        )
    }
}

/// A coordinate request stopped at its checked matching limit.
#[pyclass(name = "CatalogCoordinateCut", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyCatalogCoordinateCut {
    pub(crate) progress: CatalogCoordinateProgress,
    pub(crate) reason: CatalogCoordinateCutReason,
}

#[pymethods]
impl PyCatalogCoordinateCut {
    /// The checked prefix available at the matching limit.
    #[getter]
    fn progress(&self) -> PyCatalogCoordinateProgress {
        wrapped_progress(self.progress.clone())
    }

    /// The typed limit that stopped matching.
    #[getter]
    fn reason(&self) -> PyCatalogCoordinateCutReason {
        PyCatalogCoordinateCutReason { inner: self.reason }
    }

    /// `work_limit` for this result.
    #[getter]
    fn kind(&self) -> &'static str {
        self.reason().kind()
    }

    /// The maximum number of catalog isomorphism checks.
    #[getter]
    fn limit(&self) -> usize {
        self.reason().limit()
    }

    /// The decomposition retained in the checked prefix.
    #[getter]
    fn decomposition(&self) -> PyDecomposition {
        self.progress().decomposition()
    }

    /// Multiplicities certified before the cut.
    #[getter]
    fn multiplicities(&self) -> Vec<usize> {
        self.progress.multiplicities().to_vec()
    }

    /// Checked summand matches certified before the cut.
    #[getter]
    fn matches(&self) -> Vec<PyCatalogCoordinateMatch> {
        self.progress.matches().iter().map(wrapped_match).collect()
    }

    /// The completed catalog isomorphism checks.
    #[getter]
    fn work_units(&self) -> usize {
        self.progress.work_units()
    }

    /// `cut` for this result.
    #[getter]
    fn status(&self) -> &'static str {
        "cut"
    }

    /// Whether every summand matched a catalog entry.
    #[getter]
    fn is_exact(&self) -> bool {
        false
    }

    /// Rechecks only the retained decomposition and stored witnesses.
    /// It does not certify completeness or recheck the cut reason.
    #[pyo3(text_signature = "($self, catalog, module)")]
    fn verify(
        &self,
        py: Python<'_>,
        catalog: &PyIndecomposableCatalog,
        module: &PyRightModule,
    ) -> bool {
        py.allow_threads(|| self.progress.verify(&catalog.inner, &module.inner))
    }

    /// The evidence was produced by the coordinate computation.
    #[getter]
    fn verification(&self) -> &'static str {
        "computed"
    }

    fn __repr__(&self) -> String {
        format!(
            "CatalogCoordinateCut(limit={}, work_units={})",
            self.limit(),
            self.work_units()
        )
    }
}

fn wrap_coordinate_outcome<'py>(
    py: Python<'py>,
    outcome: CatalogCoordinateOutcome,
) -> PyResult<Bound<'py, PyAny>> {
    let progress = outcome.progress().clone();
    match outcome {
        CatalogCoordinateOutcome::Exact(inner) => {
            Ok(Bound::new(py, PyCatalogCoordinates { inner, progress })?.into_any())
        }
        CatalogCoordinateOutcome::Unknown { reason, .. } => {
            Ok(Bound::new(py, PyCatalogCoordinateUnknown { progress, reason })?.into_any())
        }
        CatalogCoordinateOutcome::Cut { reason, .. } => {
            Ok(Bound::new(py, PyCatalogCoordinateCut { progress, reason })?.into_any())
        }
    }
}

#[pymethods]
impl PyIndecomposableCatalog {
    /// Coordinates a module against this complete catalog.
    #[pyo3(signature = (module, limits = None))]
    fn coordinates<'py>(
        &self,
        py: Python<'py>,
        module: &PyRightModule,
        limits: Option<&PyCatalogCoordinateLimits>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let limits = limits.map_or_else(CatalogCoordinateLimits::default, |value| value.inner);
        let outcome = py
            .allow_threads(|| {
                catalog_coordinates::coordinates_with_limits(&self.inner, &module.inner, limits)
            })
            .map_err(coordinate_error)?;
        wrap_coordinate_outcome(py, outcome)
    }
}

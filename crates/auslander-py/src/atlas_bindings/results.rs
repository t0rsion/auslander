use super::super::*;
use super::{
    CatalogAtlas, MultiplicityComplete, MultiplicityCut, MultiplicityCutReason, MultiplicityLimits,
    MultiplicityOutcome,
};

fn catalog_value(catalog: &std::sync::Arc<IndecomposableCatalog>) -> PyIndecomposableCatalog {
    PyIndecomposableCatalog {
        inner: catalog.clone(),
    }
}

fn solution_at(solutions: &[Vec<usize>], index: usize, kind: &str) -> PyResult<Vec<usize>> {
    solutions.get(index).cloned().ok_or_else(|| {
        pyo3::exceptions::PyIndexError::new_err(format!(
            "{kind} solution index {index} out of range for {} solutions",
            solutions.len()
        ))
    })
}

/// The checked budget that stopped a multiplicity enumeration.
#[pyclass(name = "MultiplicityCutReason", module = "auslander", frozen)]
#[derive(Clone, Copy)]
pub(crate) struct PyMultiplicityCutReason {
    pub(crate) inner: MultiplicityCutReason,
}

#[pymethods]
impl PyMultiplicityCutReason {
    /// `solution_limit` or `node_limit`.
    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner {
            MultiplicityCutReason::SolutionLimit { .. } => "solution_limit",
            MultiplicityCutReason::NodeLimit { .. } => "node_limit",
        }
    }

    /// The ceiling that stopped the search.
    #[getter]
    fn limit(&self) -> usize {
        match self.inner {
            MultiplicityCutReason::SolutionLimit { limit }
            | MultiplicityCutReason::NodeLimit { limit } => limit,
        }
    }

    fn __repr__(&self) -> String {
        format!(
            "MultiplicityCutReason(kind={:?}, limit={})",
            self.kind(),
            self.limit()
        )
    }
}

/// Every multiplicity vector in a complete enumeration.
#[pyclass(name = "MultiplicityComplete", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyMultiplicityComplete {
    pub(crate) inner: MultiplicityComplete,
}

#[pymethods]
impl PyMultiplicityComplete {
    /// The complete catalog scope of the result.
    #[getter]
    fn catalog(&self) -> PyIndecomposableCatalog {
        catalog_value(self.inner.catalog())
    }

    /// The prime modulus of the catalog algebra.
    #[getter]
    fn field(&self) -> u64 {
        self.inner.catalog().algebra().field().modulus()
    }

    /// The classification theorem behind the catalog.
    #[getter]
    fn provenance(&self) -> &'static str {
        provenance_name(self.inner.catalog().provenance())
    }

    /// The requested total dimension vector.
    #[getter]
    fn target_dimensions(&self) -> Vec<usize> {
        self.inner.target_dimensions().to_vec()
    }

    /// Every multiplicity vector in deterministic catalog order.
    #[getter]
    fn solutions(&self) -> Vec<Vec<usize>> {
        self.inner.solutions().to_vec()
    }

    /// The limits used by the complete computation.
    #[getter]
    fn limits(&self) -> PyMultiplicityLimits {
        PyMultiplicityLimits {
            inner: self.inner.limits(),
        }
    }

    /// The number of search states visited.
    #[getter]
    fn nodes_visited(&self) -> usize {
        self.inner.nodes_visited()
    }

    /// `complete` for this result.
    #[getter]
    fn status(&self) -> &'static str {
        "complete"
    }

    /// The computation has not been replayed.
    #[getter]
    fn verification(&self) -> &'static str {
        "computed"
    }

    fn __len__(&self) -> usize {
        self.inner.len()
    }

    fn __getitem__(&self, index: usize) -> PyResult<Vec<usize>> {
        solution_at(self.inner.solutions(), index, "complete")
    }

    fn __repr__(&self) -> String {
        format!(
            "MultiplicityComplete(solutions={}, target_dimensions={:?})",
            self.inner.len(),
            self.inner.target_dimensions()
        )
    }
}

/// The exact multiplicity prefix retained when a checked budget stopped search.
#[pyclass(name = "MultiplicityCut", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyMultiplicityCut {
    pub(crate) inner: MultiplicityCut,
}

#[pymethods]
impl PyMultiplicityCut {
    /// The complete catalog scope of the result.
    #[getter]
    fn catalog(&self) -> PyIndecomposableCatalog {
        catalog_value(self.inner.catalog())
    }

    /// The prime modulus of the catalog algebra.
    #[getter]
    fn field(&self) -> u64 {
        self.inner.catalog().algebra().field().modulus()
    }

    /// The classification theorem behind the catalog.
    #[getter]
    fn provenance(&self) -> &'static str {
        provenance_name(self.inner.catalog().provenance())
    }

    /// The requested total dimension vector.
    #[getter]
    fn target_dimensions(&self) -> Vec<usize> {
        self.inner.target_dimensions().to_vec()
    }

    /// The exact prefix found before the cut.
    #[getter]
    fn solutions(&self) -> Vec<Vec<usize>> {
        self.inner.solutions().to_vec()
    }

    /// The limits used by the cut computation.
    #[getter]
    fn limits(&self) -> PyMultiplicityLimits {
        PyMultiplicityLimits {
            inner: self.inner.limits(),
        }
    }

    /// The budget that stopped the search.
    #[getter]
    fn reason(&self) -> PyMultiplicityCutReason {
        PyMultiplicityCutReason {
            inner: self.inner.reason(),
        }
    }

    /// The number of retained solutions.
    #[getter]
    fn coverage(&self) -> usize {
        self.inner.len()
    }

    /// The number of search states visited before the cut.
    #[getter]
    fn nodes_visited(&self) -> usize {
        self.inner.nodes_visited()
    }

    /// The retained-solution ceiling.
    #[getter]
    fn limit(&self) -> usize {
        self.inner.limit()
    }

    /// `cut` for this result.
    #[getter]
    fn status(&self) -> &'static str {
        "cut"
    }

    /// The computation has not been replayed.
    #[getter]
    fn verification(&self) -> &'static str {
        "computed"
    }

    fn __len__(&self) -> usize {
        self.inner.len()
    }

    fn __getitem__(&self, index: usize) -> PyResult<Vec<usize>> {
        solution_at(self.inner.solutions(), index, "cut")
    }

    fn __repr__(&self) -> String {
        format!(
            "MultiplicityCut(solutions={}, reason={:?})",
            self.inner.len(),
            self.reason().kind()
        )
    }
}

/// A complete multiplicity result or an exact prefix cut.
#[pyclass(name = "MultiplicityResult", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyMultiplicityResult {
    pub(crate) atlas: std::sync::Arc<CatalogAtlas>,
    pub(crate) inner: MultiplicityOutcome,
}

impl PyMultiplicityResult {
    pub(crate) fn new(
        atlas: std::sync::Arc<CatalogAtlas>,
        _dimensions: Vec<usize>,
        outcome: MultiplicityOutcome,
        _limits: MultiplicityLimits,
    ) -> Self {
        Self {
            atlas,
            inner: outcome,
        }
    }
}

#[pymethods]
impl PyMultiplicityResult {
    /// The complete catalog scope of the result.
    #[getter]
    fn catalog(&self) -> PyIndecomposableCatalog {
        catalog_value(self.inner.catalog())
    }

    /// The prime modulus of the catalog algebra.
    #[getter]
    fn field(&self) -> u64 {
        self.atlas.algebra().field().modulus()
    }

    /// The classification theorem behind the catalog.
    #[getter]
    fn provenance(&self) -> &'static str {
        provenance_name(self.atlas.provenance())
    }

    /// The inclusive Ext degree bound of the atlas used for this result.
    #[getter]
    fn max_degree(&self) -> usize {
        self.atlas.max_degree()
    }

    /// The requested total dimension vector.
    #[getter]
    fn target_dimensions(&self) -> Vec<usize> {
        self.inner.target_dimensions().to_vec()
    }

    /// Retained multiplicity vectors in deterministic order.
    #[getter]
    fn solutions(&self) -> Vec<Vec<usize>> {
        self.inner.solutions().to_vec()
    }

    /// `complete` or `cut`.
    #[getter]
    fn status(&self) -> &'static str {
        if self.inner.is_complete() {
            "complete"
        } else {
            "cut"
        }
    }

    /// The computation has not been replayed.
    #[getter]
    fn verification(&self) -> &'static str {
        "computed"
    }

    /// Whether every multiplicity solution was retained.
    #[getter]
    fn is_complete(&self) -> bool {
        self.inner.is_complete()
    }

    /// Whether search stopped at a checked limit.
    #[getter]
    fn is_cut(&self) -> bool {
        self.inner.cut().is_some()
    }

    /// The complete typed result, or `None` after a cut.
    #[getter]
    fn complete(&self) -> Option<PyMultiplicityComplete> {
        self.inner
            .complete()
            .cloned()
            .map(|inner| PyMultiplicityComplete { inner })
    }

    /// The cut typed result, or `None` for a complete result.
    #[getter]
    fn cut(&self) -> Option<PyMultiplicityCut> {
        self.inner
            .cut()
            .cloned()
            .map(|inner| PyMultiplicityCut { inner })
    }

    /// The typed cut reason, or `None` for a complete result.
    #[getter]
    fn cut_reason(&self) -> Option<PyMultiplicityCutReason> {
        self.inner.cut().map(|cut| PyMultiplicityCutReason {
            inner: cut.reason(),
        })
    }

    /// The number of search states visited.
    #[getter]
    fn nodes_visited(&self) -> usize {
        match &self.inner {
            MultiplicityOutcome::Complete(result) => result.nodes_visited(),
            MultiplicityOutcome::Cut(cut) => cut.nodes_visited(),
        }
    }

    /// The number of retained solutions.
    #[getter]
    fn coverage(&self) -> usize {
        self.inner.len()
    }

    fn __len__(&self) -> usize {
        self.inner.len()
    }

    fn __getitem__(&self, index: usize) -> PyResult<Vec<usize>> {
        solution_at(self.inner.solutions(), index, "multiplicity")
    }

    fn __repr__(&self) -> String {
        format!(
            "MultiplicityResult(status={:?}, solutions={}, target_dimensions={:?})",
            self.status(),
            self.inner.len(),
            self.inner.target_dimensions()
        )
    }
}

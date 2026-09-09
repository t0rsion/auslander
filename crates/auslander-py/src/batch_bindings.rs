use super::*;

/// Preflight limits for selected-pair homological analysis.

#[pyclass(name = "HomologicalBatchLimits", module = "auslander", frozen)]
#[derive(Clone, Copy)]
pub(crate) struct PyHomologicalBatchLimits {
    pub(crate) inner: HomologicalBatchLimits,
}

#[pymethods]
impl PyHomologicalBatchLimits {
    /// `HomologicalBatchLimits(max_pairs=None, max_ext_cells=None)`.
    #[new]
    #[pyo3(signature = (max_pairs=None, max_ext_cells=None))]
    fn new(max_pairs: Option<usize>, max_ext_cells: Option<usize>) -> Self {
        let defaults = HomologicalBatchLimits::default();
        Self {
            inner: HomologicalBatchLimits {
                max_pairs: max_pairs.unwrap_or(defaults.max_pairs),
                max_ext_cells: max_ext_cells.unwrap_or(defaults.max_ext_cells),
            },
        }
    }

    /// Maximum number of selected ordered pairs.
    #[getter]
    fn max_pairs(&self) -> usize {
        self.inner.max_pairs
    }

    /// Maximum number of stored Ext dimension cells.
    #[getter]
    fn max_ext_cells(&self) -> usize {
        self.inner.max_ext_cells
    }
}

/// Exact dimensions for one selected pair in a homological batch.
#[pyclass(name = "HomologicalPair", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyHomologicalPair {
    pub(crate) inner: HomologicalPair,
}

#[pymethods]
impl PyHomologicalPair {
    /// The source module index.
    #[getter]
    fn source(&self) -> usize {
        self.inner.source()
    }

    /// The target module index.
    #[getter]
    fn target(&self) -> usize {
        self.inner.target()
    }

    /// `dim_k Hom(source, target)`.
    #[getter]
    fn hom_dim(&self) -> usize {
        self.inner.hom_dim()
    }

    /// `dim_k stable Hom(source, target)`.
    #[getter]
    fn stable_hom_dim(&self) -> usize {
        self.inner.stable_hom_dim()
    }

    /// Ext dimensions from degree zero through the batch bound.
    #[getter]
    fn ext_dimensions(&self) -> Vec<usize> {
        self.inner.ext_dimensions().to_vec()
    }

    fn __repr__(&self) -> String {
        format!(
            "HomologicalPair(source={}, target={}, ext_dimensions={:?})",
            self.inner.source(),
            self.inner.target(),
            self.inner.ext_dimensions()
        )
    }
}

/// Exact shared-work counts for a homological batch.
#[pyclass(name = "HomologicalBatchWork", module = "auslander", frozen)]
#[derive(Clone, Copy)]
pub(crate) struct PyHomologicalBatchWork {
    pub(crate) inner: HomologicalBatchWork,
}

#[pymethods]
impl PyHomologicalBatchWork {
    #[getter]
    fn resolutions(&self) -> usize {
        self.inner.resolutions
    }

    #[getter]
    fn target_covers(&self) -> usize {
        self.inner.target_covers
    }

    #[getter]
    fn hom_spaces(&self) -> usize {
        self.inner.hom_spaces
    }

    #[getter]
    fn projective_factor_spaces(&self) -> usize {
        self.inner.projective_factor_spaces
    }

    #[getter]
    fn ext_tables(&self) -> usize {
        self.inner.ext_tables
    }
}

/// Selected Hom, stable-Hom, and Ext tables with shared source work.
///
/// With `pairs=None`, the constructor computes only self-pairs. Use
/// `all_pairs` for the full ordered square.
#[pyclass(name = "HomologicalBatch", module = "auslander")]
pub(crate) struct PyHomologicalBatch {
    pub(crate) inner: HomologicalBatch,
}

#[pymethods]
impl PyHomologicalBatch {
    /// `HomologicalBatch(modules, max_degree, pairs=None, limits=None)`.
    #[new]
    #[pyo3(signature = (modules, max_degree, pairs=None, limits=None))]
    fn new(
        py: Python<'_>,
        modules: Vec<PyRef<'_, PyRightModule>>,
        max_degree: usize,
        pairs: Option<Vec<(usize, usize)>>,
        limits: Option<&PyHomologicalBatchLimits>,
    ) -> PyResult<Self> {
        let modules: Vec<Module> = modules.iter().map(|module| module.inner.clone()).collect();
        let limits = limits.map_or_else(HomologicalBatchLimits::default, |value| value.inner);
        let result = py.allow_threads(|| match pairs {
            Some(pairs) => HomologicalBatch::compute(modules, pairs, max_degree, limits),
            None => HomologicalBatch::self_pairs(modules, max_degree, limits),
        });
        Ok(Self {
            inner: result.map_err(homological_batch_error)?,
        })
    }

    /// Compute every ordered pair in source-major order.
    #[staticmethod]
    #[pyo3(signature = (modules, max_degree, limits=None))]
    fn all_pairs(
        py: Python<'_>,
        modules: Vec<PyRef<'_, PyRightModule>>,
        max_degree: usize,
        limits: Option<&PyHomologicalBatchLimits>,
    ) -> PyResult<Self> {
        let modules: Vec<Module> = modules.iter().map(|module| module.inner.clone()).collect();
        let limits = limits.map_or_else(HomologicalBatchLimits::default, |value| value.inner);
        Ok(Self {
            inner: py
                .allow_threads(|| HomologicalBatch::all_pairs(modules, max_degree, limits))
                .map_err(homological_batch_error)?,
        })
    }

    /// The modules indexed by selected pairs.
    #[getter]
    fn modules(&self) -> Vec<PyRightModule> {
        wrap_all(self.inner.modules())
    }

    /// The largest stored Ext degree.
    #[getter]
    fn max_degree(&self) -> usize {
        self.inner.max_degree()
    }

    /// Selected `(source, target)` indices in result order.
    #[getter]
    fn selected_pairs(&self) -> Vec<(usize, usize)> {
        self.inner.selected_pairs().to_vec()
    }

    /// Exact results in selected-pair order.
    #[getter]
    fn pairs(&self) -> Vec<PyHomologicalPair> {
        self.inner
            .pairs()
            .iter()
            .cloned()
            .map(|inner| PyHomologicalPair { inner })
            .collect()
    }

    /// Exact counts of shared computations.
    #[getter]
    fn work(&self) -> PyHomologicalBatchWork {
        PyHomologicalBatchWork {
            inner: self.inner.work(),
        }
    }

    /// The stored minimal resolution for one selected source, if present.
    #[pyo3(text_signature = "($self, source)")]
    fn resolution(&self, source: usize) -> Option<PyResolution> {
        self.inner
            .resolution(source)
            .map(|resolution| wrapped_resolution(&self.inner.modules()[source], resolution))
    }

    /// Recompute the full stable-Hom quotient for one selected result.
    #[pyo3(text_signature = "($self, pair)")]
    fn stable_hom(&self, py: Python<'_>, pair: usize) -> PyResult<PyStableHomSpace> {
        Ok(PyStableHomSpace {
            inner: py
                .allow_threads(|| self.inner.stable_hom(pair))
                .map_err(homological_batch_error)?,
        })
    }

    /// Recompute every result and exact work count.
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "HomologicalBatch(modules={}, pairs={}, max_degree={})",
            self.inner.modules().len(),
            self.inner.pairs().len(),
            self.inner.max_degree()
        )
    }
}

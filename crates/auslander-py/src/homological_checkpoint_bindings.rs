use super::*;

pub(crate) fn checkpoint_error(error: HomologicalStreamPortableError) -> PyErr {
    match error {
        HomologicalStreamPortableError::CounterOverflow { .. } => {
            PyOverflowError::new_err(error.to_string())
        }
        HomologicalStreamPortableError::Batch(error) => homological_batch_error(error),
        HomologicalStreamPortableError::Stream(error) => engine_error(error),
        other => value_error(other),
    }
}

#[pyclass(name = "HomologicalStreamBudget", module = "auslander", frozen)]
#[derive(Clone, Copy)]
pub(crate) struct PyHomologicalStreamBudget {
    inner: HomologicalStreamBudget,
}

#[pymethods]
impl PyHomologicalStreamBudget {
    /// `HomologicalStreamBudget(max_sources=None, max_work_units=None)`.
    #[new]
    #[pyo3(signature = (max_sources=None, max_work_units=None))]
    fn new(max_sources: Option<usize>, max_work_units: Option<usize>) -> Self {
        let defaults = HomologicalStreamBudget::default();
        Self {
            inner: HomologicalStreamBudget {
                max_sources: max_sources.unwrap_or(defaults.max_sources),
                max_work_units: max_work_units.unwrap_or(defaults.max_work_units),
            },
        }
    }

    #[getter]
    fn max_sources(&self) -> usize {
        self.inner.max_sources
    }

    #[getter]
    fn max_work_units(&self) -> usize {
        self.inner.max_work_units
    }

    fn __repr__(&self) -> String {
        format!(
            "HomologicalStreamBudget(max_sources={}, max_work_units={})",
            self.max_sources(),
            self.max_work_units()
        )
    }
}

#[pyclass(name = "HomologicalStreamConfig", module = "auslander", frozen)]
#[derive(Clone, Copy)]
pub(crate) struct PyHomologicalStreamConfig {
    inner: HomologicalStreamConfig,
}

#[pymethods]
impl PyHomologicalStreamConfig {
    /// Fixed chunk sizes and absolute work ceilings.
    #[new]
    #[pyo3(signature = (
        max_live_sources=None,
        max_pairs=None,
        max_ext_cells=None,
        max_sources=None,
        max_work_units=None,
    ))]
    fn new(
        max_live_sources: Option<usize>,
        max_pairs: Option<usize>,
        max_ext_cells: Option<usize>,
        max_sources: Option<usize>,
        max_work_units: Option<usize>,
    ) -> Self {
        let chunk = HomologicalBatchStreamLimits::default();
        let budget = HomologicalStreamBudget::default();
        Self {
            inner: HomologicalStreamConfig {
                chunk_limits: HomologicalBatchStreamLimits {
                    max_live_sources: max_live_sources.unwrap_or(chunk.max_live_sources),
                    max_pairs: max_pairs.unwrap_or(chunk.max_pairs),
                    max_ext_cells: max_ext_cells.unwrap_or(chunk.max_ext_cells),
                },
                budget: HomologicalStreamBudget {
                    max_sources: max_sources.unwrap_or(budget.max_sources),
                    max_work_units: max_work_units.unwrap_or(budget.max_work_units),
                },
            },
        }
    }

    #[getter]
    fn max_live_sources(&self) -> usize {
        self.inner.chunk_limits.max_live_sources
    }

    #[getter]
    fn max_pairs(&self) -> usize {
        self.inner.chunk_limits.max_pairs
    }

    #[getter]
    fn max_ext_cells(&self) -> usize {
        self.inner.chunk_limits.max_ext_cells
    }

    #[getter]
    fn max_sources(&self) -> usize {
        self.inner.budget.max_sources
    }

    #[getter]
    fn max_work_units(&self) -> usize {
        self.inner.budget.max_work_units
    }

    fn __repr__(&self) -> String {
        format!(
            "HomologicalStreamConfig(max_live_sources={}, max_pairs={}, max_ext_cells={}, max_sources={}, max_work_units={})",
            self.max_live_sources(),
            self.max_pairs(),
            self.max_ext_cells(),
            self.max_sources(),
            self.max_work_units()
        )
    }
}

#[pyclass(name = "HomologicalStreamVerifyLimits", module = "auslander", frozen)]
#[derive(Clone, Copy)]
pub(crate) struct PyHomologicalStreamVerifyLimits {
    pub(crate) inner: HomologicalStreamVerifyLimits,
}

#[pymethods]
impl PyHomologicalStreamVerifyLimits {
    /// Parser and exact replay ceilings for one homological checkpoint.
    #[new]
    #[pyo3(signature = (
        census=None,
        max_input_bytes=None,
        max_census_bytes=None,
        max_rows=None,
        max_ext_dimensions=None,
        max_numeric_values=None,
        max_array_elements=None,
        max_integer_digits=None,
        max_string_bytes=None,
        max_representatives=None,
        max_degree=None,
        max_work_units=None,
    ))]
    #[allow(clippy::too_many_arguments)]
    fn new(
        census: Option<&PyCensusVerifyLimits>,
        max_input_bytes: Option<usize>,
        max_census_bytes: Option<usize>,
        max_rows: Option<usize>,
        max_ext_dimensions: Option<usize>,
        max_numeric_values: Option<usize>,
        max_array_elements: Option<usize>,
        max_integer_digits: Option<usize>,
        max_string_bytes: Option<usize>,
        max_representatives: Option<usize>,
        max_degree: Option<usize>,
        max_work_units: Option<usize>,
    ) -> Self {
        let defaults = HomologicalStreamVerifyLimits::default();
        Self {
            inner: HomologicalStreamVerifyLimits {
                parse: HomologicalStreamParseLimits {
                    max_input_bytes: max_input_bytes.unwrap_or(defaults.parse.max_input_bytes),
                    max_census_bytes: max_census_bytes.unwrap_or(defaults.parse.max_census_bytes),
                    max_rows: max_rows.unwrap_or(defaults.parse.max_rows),
                    max_ext_dimensions: max_ext_dimensions
                        .unwrap_or(defaults.parse.max_ext_dimensions),
                    max_numeric_values: max_numeric_values
                        .unwrap_or(defaults.parse.max_numeric_values),
                    max_array_elements: max_array_elements
                        .unwrap_or(defaults.parse.max_array_elements),
                    max_integer_digits: max_integer_digits
                        .unwrap_or(defaults.parse.max_integer_digits),
                    max_string_bytes: max_string_bytes.unwrap_or(defaults.parse.max_string_bytes),
                },
                census: census.map_or(defaults.census, |value| value.inner),
                max_representatives: max_representatives.unwrap_or(defaults.max_representatives),
                max_degree: max_degree.unwrap_or(defaults.max_degree),
                max_work_units: max_work_units.unwrap_or(defaults.max_work_units),
            },
        }
    }

    #[getter]
    fn max_input_bytes(&self) -> usize {
        self.inner.parse.max_input_bytes
    }

    #[getter]
    fn max_census_bytes(&self) -> usize {
        self.inner.parse.max_census_bytes
    }

    #[getter]
    fn max_rows(&self) -> usize {
        self.inner.parse.max_rows
    }

    #[getter]
    fn max_ext_dimensions(&self) -> usize {
        self.inner.parse.max_ext_dimensions
    }

    #[getter]
    fn max_numeric_values(&self) -> usize {
        self.inner.parse.max_numeric_values
    }

    #[getter]
    fn max_array_elements(&self) -> usize {
        self.inner.parse.max_array_elements
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
    fn census(&self) -> PyCensusVerifyLimits {
        PyCensusVerifyLimits {
            inner: self.inner.census,
        }
    }

    #[getter]
    fn max_representatives(&self) -> usize {
        self.inner.max_representatives
    }

    #[getter]
    fn max_degree(&self) -> usize {
        self.inner.max_degree
    }

    #[getter]
    fn max_work_units(&self) -> usize {
        self.inner.max_work_units
    }

    fn __repr__(&self) -> String {
        format!(
            "HomologicalStreamVerifyLimits(max_input_bytes={}, max_rows={}, max_representatives={}, max_degree={}, max_work_units={})",
            self.max_input_bytes(),
            self.max_rows(),
            self.max_representatives(),
            self.max_degree(),
            self.max_work_units()
        )
    }
}

#[pyclass(name = "HomologicalStreamCutReason", module = "auslander", frozen)]
#[derive(Clone, Copy)]
pub(crate) struct PyHomologicalStreamCutReason {
    inner: HomologicalStreamCutReason,
}

#[pymethods]
impl PyHomologicalStreamCutReason {
    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner {
            HomologicalStreamCutReason::Cancelled => "cancelled",
            HomologicalStreamCutReason::SourceLimit { .. } => "source_limit",
            HomologicalStreamCutReason::WorkLimit { .. } => "work_limit",
        }
    }

    #[getter]
    fn limit(&self) -> Option<usize> {
        match self.inner {
            HomologicalStreamCutReason::Cancelled => None,
            HomologicalStreamCutReason::SourceLimit { limit }
            | HomologicalStreamCutReason::WorkLimit { limit } => Some(limit),
        }
    }
}

#[pyclass(name = "HomologicalStreamRow", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyHomologicalStreamRow {
    inner: HomologicalBatchStreamRow,
}

#[pymethods]
impl PyHomologicalStreamRow {
    #[getter]
    fn source(&self) -> usize {
        self.inner.source()
    }

    #[getter]
    fn target(&self) -> usize {
        self.inner.target()
    }

    #[getter]
    fn hom_dim(&self) -> usize {
        self.inner.hom_dim()
    }

    #[getter]
    fn stable_hom_dim(&self) -> usize {
        self.inner.stable_hom_dim()
    }

    #[getter]
    fn ext_dimensions(&self) -> Vec<usize> {
        self.inner.ext_dimensions().to_vec()
    }

    #[getter]
    fn resolution_status(&self) -> &'static str {
        match self.inner.resolution_end() {
            ResolutionEnd::Finite => "finite",
            ResolutionEnd::Cut { .. } => "cut",
        }
    }

    #[getter]
    fn resolution_cut_at(&self) -> Option<usize> {
        match self.inner.resolution_end() {
            ResolutionEnd::Finite => None,
            ResolutionEnd::Cut { at } => Some(at),
        }
    }
}

#[pyclass(name = "HomologicalStreamWork", module = "auslander", frozen)]
#[derive(Clone, Copy)]
pub(crate) struct PyHomologicalStreamWork {
    inner: HomologicalBatchStreamWork,
}

#[pymethods]
impl PyHomologicalStreamWork {
    #[getter]
    fn chunks(&self) -> usize {
        self.inner.chunks
    }

    #[getter]
    fn sources(&self) -> usize {
        self.inner.sources
    }

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

    #[getter]
    fn peak_live_sources(&self) -> usize {
        self.inner.peak_live_sources
    }
}

fn stream_status(status: &HomologicalStreamPortableStatus) -> &'static str {
    match status {
        HomologicalStreamPortableStatus::Active => "active",
        HomologicalStreamPortableStatus::Complete => "complete",
        HomologicalStreamPortableStatus::Cut(_) => "cut",
    }
}

fn cut_reason(status: &HomologicalStreamPortableStatus) -> Option<PyHomologicalStreamCutReason> {
    match status {
        HomologicalStreamPortableStatus::Cut(reason) => {
            Some(PyHomologicalStreamCutReason { inner: *reason })
        }
        HomologicalStreamPortableStatus::Active | HomologicalStreamPortableStatus::Complete => None,
    }
}

#[pyclass(name = "HomologicalCheckpoint", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyHomologicalCheckpoint {
    pub(crate) inner: HomologicalStreamPortable,
}

#[pymethods]
impl PyHomologicalCheckpoint {
    /// Parse canonical checkpoint JSON without replaying it.
    #[new]
    #[pyo3(signature = (text, limits=None))]
    fn new(text: &str, limits: Option<&PyHomologicalStreamVerifyLimits>) -> PyResult<Self> {
        let limits = limits.map_or_else(HomologicalStreamParseLimits::default, |value| {
            value.inner.parse
        });
        HomologicalStreamPortable::from_json(text, limits)
            .map(|inner| Self { inner })
            .map_err(checkpoint_error)
    }

    #[staticmethod]
    #[pyo3(signature = (text, limits=None))]
    fn from_json(text: &str, limits: Option<&PyHomologicalStreamVerifyLimits>) -> PyResult<Self> {
        Self::new(text, limits)
    }

    #[getter]
    fn census_json(&self) -> &str {
        self.inner.census()
    }

    #[getter]
    fn census_fingerprint(&self) -> &str {
        self.inner.census_fingerprint()
    }

    #[getter]
    fn max_degree(&self) -> usize {
        self.inner.max_degree()
    }

    #[getter]
    fn config(&self) -> PyHomologicalStreamConfig {
        PyHomologicalStreamConfig {
            inner: self.inner.config(),
        }
    }

    #[getter]
    fn next_source(&self) -> usize {
        self.inner.next_source()
    }

    #[getter]
    fn rows(&self) -> Vec<PyHomologicalStreamRow> {
        self.inner
            .rows()
            .iter()
            .cloned()
            .map(|inner| PyHomologicalStreamRow { inner })
            .collect()
    }

    #[getter]
    fn row_count(&self) -> usize {
        self.inner.rows().len()
    }

    #[getter]
    fn chunk_sizes(&self) -> Vec<usize> {
        self.inner.chunk_sizes().to_vec()
    }

    #[getter]
    fn work(&self) -> PyHomologicalStreamWork {
        PyHomologicalStreamWork {
            inner: self.inner.work(),
        }
    }

    #[getter]
    fn status(&self) -> &'static str {
        stream_status(self.inner.status())
    }

    #[getter]
    fn cut_reason(&self) -> Option<PyHomologicalStreamCutReason> {
        cut_reason(self.inner.status())
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
        limits: Option<&PyHomologicalStreamVerifyLimits>,
    ) -> PyResult<PyVerifiedHomologicalCheckpoint> {
        let limits =
            limits.map_or_else(HomologicalStreamVerifyLimits::default, |value| value.inner);
        py.allow_threads(|| self.inner.verify(limits))
            .map(|inner| PyVerifiedHomologicalCheckpoint { inner })
            .map_err(checkpoint_error)
    }

    fn __repr__(&self) -> String {
        format!(
            "HomologicalCheckpoint(status={:?}, next_source={}, fingerprint={:?})",
            self.status(),
            self.next_source(),
            self.fingerprint()
        )
    }
}

#[pyclass(name = "VerifiedHomologicalCheckpoint", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyVerifiedHomologicalCheckpoint {
    pub(crate) inner: VerifiedHomologicalStream,
}

#[pymethods]
impl PyVerifiedHomologicalCheckpoint {
    #[getter]
    fn checkpoint(&self) -> PyHomologicalCheckpoint {
        PyHomologicalCheckpoint {
            inner: self.inner.portable().clone(),
        }
    }

    #[getter]
    fn status(&self) -> &'static str {
        stream_status(self.inner.portable().status())
    }

    #[getter]
    fn next_source(&self) -> usize {
        self.inner.portable().next_source()
    }

    #[getter]
    fn chunk_sizes(&self) -> Vec<usize> {
        self.inner.portable().chunk_sizes().to_vec()
    }

    #[getter]
    fn canonical_json(&self) -> String {
        self.inner.portable().to_canonical_json()
    }

    #[getter]
    fn fingerprint(&self) -> &str {
        self.inner.portable().fingerprint()
    }

    /// Resume after the last replay-verified source row.
    #[pyo3(signature = (budget=None, control=None))]
    fn resume(
        &self,
        budget: Option<&PyHomologicalStreamBudget>,
        control: Option<&PyComputationControl>,
    ) -> PyResult<PyHomologicalCheckpointStream> {
        let budget = budget.map_or_else(HomologicalStreamBudget::default, |value| value.inner);
        self.inner
            .resume(budget, control.map(|value| &value.inner))
            .map(|inner| PyHomologicalCheckpointStream { inner })
            .map_err(checkpoint_error)
    }

    fn __repr__(&self) -> String {
        format!(
            "VerifiedHomologicalCheckpoint(status={:?}, next_source={}, fingerprint={:?})",
            self.status(),
            self.next_source(),
            self.fingerprint()
        )
    }
}

#[pyclass(name = "HomologicalCheckpointStream", module = "auslander")]
pub(crate) struct PyHomologicalCheckpointStream {
    inner: HomologicalSelfPairCheckpointStream,
}

#[pymethods]
impl PyHomologicalCheckpointStream {
    /// The last fully committed checkpoint.
    #[getter]
    fn checkpoint(&self) -> PyHomologicalCheckpoint {
        PyHomologicalCheckpoint {
            inner: self.inner.checkpoint(),
        }
    }

    /// Compute one source chunk and return the new committed checkpoint.
    fn advance(&mut self, py: Python<'_>) -> PyResult<PyHomologicalCheckpoint> {
        let step = py.allow_threads(|| self.inner.next_chunk());
        if let HomologicalStreamStep::Failed { error, .. } = step {
            return Err(checkpoint_error(error));
        }
        Ok(self.checkpoint())
    }

    fn __repr__(&self) -> String {
        let checkpoint = self.inner.checkpoint();
        format!(
            "HomologicalCheckpointStream(status={:?}, next_source={})",
            stream_status(checkpoint.status()),
            checkpoint.next_source()
        )
    }
}

/// Start a bounded homological stream over a replay-verified complete census.
#[pyfunction]
#[pyo3(signature = (census, max_degree, config=None, control=None))]
pub(crate) fn start_homological_stream(
    census: &PyVerifiedCensusCheckpoint,
    max_degree: usize,
    config: Option<&PyHomologicalStreamConfig>,
    control: Option<&PyComputationControl>,
) -> PyResult<PyHomologicalCheckpointStream> {
    let config = config.map_or_else(HomologicalStreamConfig::default, |value| value.inner);
    homological_stream_from_census(
        &census.inner,
        max_degree,
        config,
        control.map(|value| &value.inner),
    )
    .map(|inner| PyHomologicalCheckpointStream { inner })
    .map_err(checkpoint_error)
}

/// Parse and replay-verify canonical homological checkpoint JSON.
#[pyfunction]
#[pyo3(signature = (text, limits=None))]
pub(crate) fn verify_homological_checkpoint(
    py: Python<'_>,
    text: &str,
    limits: Option<&PyHomologicalStreamVerifyLimits>,
) -> PyResult<PyVerifiedHomologicalCheckpoint> {
    let limits = limits.map_or_else(HomologicalStreamVerifyLimits::default, |value| value.inner);
    let portable =
        HomologicalStreamPortable::from_json(text, limits.parse).map_err(checkpoint_error)?;
    py.allow_threads(|| portable.verify(limits))
        .map(|inner| PyVerifiedHomologicalCheckpoint { inner })
        .map_err(checkpoint_error)
}

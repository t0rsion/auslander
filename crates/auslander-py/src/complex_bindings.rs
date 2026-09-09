use super::*;

/// A nonempty finite complex whose consecutive maps compose to zero.
///
/// Terms and maps use display order: `maps[i]` goes from `terms[i]` to
/// `terms[i + 1]`. Construction checks every endpoint and composite.

#[pyclass(name = "CheckedComplex", module = "auslander", frozen)]
pub(crate) struct PyCheckedComplex {
    pub(crate) inner: CheckedComplex,
}

impl From<&CheckedComplex> for PyCheckedComplex {
    fn from(inner: &CheckedComplex) -> Self {
        Self {
            inner: inner.clone(),
        }
    }
}

#[pymethods]
impl PyCheckedComplex {
    /// CheckedComplex(terms, maps); raises ValueError for an empty term list,
    /// a wrong map count, a mismatched endpoint, or a nonzero composite.
    #[new]
    #[pyo3(text_signature = "(terms, maps)")]
    fn new(
        terms: Vec<PyRef<'_, PyRightModule>>,
        maps: Vec<PyRef<'_, PyMorphism>>,
    ) -> PyResult<Self> {
        let terms = terms.iter().map(|term| term.inner.clone()).collect();
        let maps = maps.iter().map(|map| map.inner.clone()).collect();
        Ok(Self {
            inner: CheckedComplex::new(terms, maps).map_err(value_error)?,
        })
    }

    /// The terms in display order.
    #[getter]
    fn terms(&self) -> Vec<PyRightModule> {
        wrap_all(self.inner.terms())
    }

    /// The maps in display order.
    #[getter]
    fn maps(&self) -> Vec<PyMorphism> {
        wrap_all(self.inner.maps())
    }

    /// Rechecks every endpoint and zero composite.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    /// Converts display order to increasing homological degrees.
    #[pyo3(text_signature = "($self, lower)")]
    fn bounded(&self, lower: i32) -> PyResult<PyBoundedComplex> {
        Ok(PyBoundedComplex {
            inner: self.inner.bounded(lower).map_err(value_error)?,
        })
    }

    /// The exact homology dimension vector at one term.
    #[pyo3(text_signature = "($self, index)")]
    fn homology_dimensions(&self, index: usize) -> PyResult<PyHomologyDimensions> {
        Ok(PyHomologyDimensions {
            inner: self.inner.homology_dimensions(index).map_err(value_error)?,
        })
    }

    /// An ExactComplex, or a NonExactWitness at the first nonexact term.
    #[pyo3(text_signature = "($self)")]
    fn exactness<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        match self.inner.exactness() {
            ExactnessOutcome::Exact(inner) => {
                Ok(Bound::new(py, PyExactComplex { inner })?.into_any())
            }
            ExactnessOutcome::NotExact(inner) => {
                Ok(Bound::new(py, PyNonExactWitness { inner })?.into_any())
            }
        }
    }

    fn __len__(&self) -> usize {
        self.inner.len()
    }

    fn __repr__(&self) -> String {
        format!(
            "CheckedComplex(terms={}, maps={})",
            self.inner.terms().len(),
            self.inner.maps().len()
        )
    }
}

/// Exact homology dimensions at one term of a CheckedComplex.
#[pyclass(name = "HomologyDimensions", module = "auslander", frozen)]
pub(crate) struct PyHomologyDimensions {
    pub(crate) inner: HomologyDimensions,
}

#[pymethods]
impl PyHomologyDimensions {
    /// The term index in display order.
    #[getter]
    fn index(&self) -> usize {
        self.inner.index()
    }

    /// The homology dimension at each quiver vertex.
    #[getter]
    fn dimension_vector(&self) -> Vec<usize> {
        self.inner.dimension_vector().to_vec()
    }

    /// Whether every entry of the dimension vector is zero.
    #[getter]
    fn is_zero(&self) -> bool {
        self.inner.is_zero()
    }

    /// Rechecks the complex and the stored dimensions.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "HomologyDimensions(index={}, dimension_vector={:?})",
            self.inner.index(),
            self.inner.dimension_vector()
        )
    }
}

/// The first term of a CheckedComplex with nonzero homology.
#[pyclass(name = "NonExactWitness", module = "auslander", frozen)]
pub(crate) struct PyNonExactWitness {
    pub(crate) inner: NonExactWitness,
}

#[pymethods]
impl PyNonExactWitness {
    /// The first nonexact term index.
    #[getter]
    fn index(&self) -> usize {
        self.inner.homology().index()
    }

    /// The first nonzero homology dimension vector.
    #[getter]
    fn dimension_vector(&self) -> Vec<usize> {
        self.inner.homology().dimension_vector().to_vec()
    }

    /// The full checked homology record.
    #[getter]
    fn homology(&self) -> PyHomologyDimensions {
        PyHomologyDimensions {
            inner: self.inner.homology().clone(),
        }
    }

    /// Rechecks that this is the first nonexact term.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "NonExactWitness(index={}, dimension_vector={:?})",
            self.inner.homology().index(),
            self.inner.homology().dimension_vector()
        )
    }
}

/// A finite CheckedComplex proved exact at every term.
#[pyclass(name = "ExactComplex", module = "auslander", frozen)]
pub(crate) struct PyExactComplex {
    pub(crate) inner: ExactComplex,
}

#[pymethods]
impl PyExactComplex {
    /// The checked complex whose homology vanishes.
    #[getter]
    fn complex(&self) -> PyCheckedComplex {
        self.inner.complex().into()
    }

    /// Rechecks every endpoint, composite, and homology dimension.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __len__(&self) -> usize {
        self.inner.complex().len()
    }

    fn __repr__(&self) -> String {
        format!("ExactComplex(terms={})", self.inner.complex().len())
    }
}

#[pyclass(name = "ComputationControl", module = "auslander", frozen)]
pub(crate) struct PyComputationControl {
    pub(crate) inner: ComputationControl,
}

pub(crate) fn early_progress_stage_name(stage: ProgressStage) -> Option<&'static str> {
    match stage {
        ProgressStage::Idle => Some("idle"),
        ProgressStage::ReplacementCover => Some("replacement_cover"),
        ProgressStage::ReplacementTotalize => Some("replacement_totalize"),
        ProgressStage::ReplacementVerify => Some("replacement_verify"),
        ProgressStage::DerivedHom => Some("derived_hom"),
        _ => None,
    }
}

pub(crate) fn progress_stage_name(stage: ProgressStage) -> &'static str {
    if let Some(name) = early_progress_stage_name(stage) {
        return name;
    }
    match stage {
        ProgressStage::HomologicalBatch => "homological_batch",
        ProgressStage::Census => "census",
        ProgressStage::Tilting => "tilting",
        ProgressStage::Mutation => "mutation",
        ProgressStage::ArtifactVerify => "artifact_verify",
        ProgressStage::Complete => "complete",
        _ => unreachable!("early progress stage was handled"),
    }
}

#[pymethods]
impl PyComputationControl {
    #[new]
    fn new() -> PyComputationControl {
        PyComputationControl {
            inner: ComputationControl::new(),
        }
    }

    /// Requests cancellation at the next checked boundary.
    fn cancel(&self) {
        self.inner.cancel();
    }

    /// Whether cancellation has been requested.
    #[getter]
    fn is_cancelled(&self) -> bool {
        self.inner.is_cancelled()
    }

    /// The current deterministic computation stage.
    #[getter]
    fn stage(&self) -> &'static str {
        progress_stage_name(self.inner.progress().stage())
    }

    /// Completed deterministic work units.
    #[getter]
    fn completed_work(&self) -> usize {
        self.inner.progress().completed_work()
    }

    /// Accepted deterministic work units.
    #[getter]
    fn reserved_work(&self) -> usize {
        self.inner.progress().reserved_work()
    }
}

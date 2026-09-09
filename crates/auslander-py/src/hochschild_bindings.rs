use super::*;

/// Four resource ceilings for one relative bar cohomology request.

#[pyclass(name = "BarLimits", module = "auslander", frozen)]
#[derive(Clone, Copy)]
pub(crate) struct PyBarLimits {
    pub(crate) inner: BarLimits,
}

#[pymethods]
impl PyBarLimits {
    /// BarLimits(max_tensor_tuples, max_cochain_dim, max_matrix_entries,
    /// max_work_units). Every ceiling is required and independent.
    #[new]
    #[pyo3(
        text_signature = "(max_tensor_tuples, max_cochain_dim, max_matrix_entries, max_work_units)"
    )]
    fn new(
        max_tensor_tuples: usize,
        max_cochain_dim: usize,
        max_matrix_entries: usize,
        max_work_units: u64,
    ) -> Self {
        Self {
            inner: BarLimits {
                max_tensor_tuples,
                max_cochain_dim,
                max_matrix_entries,
                max_work_units,
            },
        }
    }

    #[getter]
    fn max_tensor_tuples(&self) -> usize {
        self.inner.max_tensor_tuples
    }

    #[getter]
    fn max_cochain_dim(&self) -> usize {
        self.inner.max_cochain_dim
    }

    #[getter]
    fn max_matrix_entries(&self) -> usize {
        self.inner.max_matrix_entries
    }

    #[getter]
    fn max_work_units(&self) -> u64 {
        self.inner.max_work_units
    }

    fn __repr__(&self) -> String {
        format!(
            "BarLimits(max_tensor_tuples={}, max_cochain_dim={}, max_matrix_entries={}, max_work_units={})",
            self.inner.max_tensor_tuples,
            self.inner.max_cochain_dim,
            self.inner.max_matrix_entries,
            self.inner.max_work_units
        )
    }
}

/// The first rejected reservation of an incomplete bar request.
#[pyclass(name = "BarBudgetDiagnostics", module = "auslander", frozen)]
pub(crate) struct PyBarBudgetDiagnostics {
    pub(crate) inner: BarBudgetDiagnostics,
}

#[pymethods]
impl PyBarBudgetDiagnostics {
    /// The caller ceiling name, or `size_overflow`.
    #[getter]
    fn reason(&self) -> &'static str {
        bar_reason_name(self.inner.reason)
    }

    /// The operation whose reservation stopped the request.
    #[getter]
    fn stage(&self) -> &'static str {
        bar_stage_name(self.inner.stage)
    }

    #[getter]
    fn completed_degree_count(&self) -> usize {
        self.inner.completed_degree_count
    }

    #[getter]
    fn first_uncomputed_differential(&self) -> usize {
        self.inner.first_uncomputed_differential
    }

    #[getter]
    fn work_units(&self) -> u64 {
        self.inner.work_units
    }

    #[getter]
    fn matrix_entries(&self) -> usize {
        self.inner.matrix_entries
    }

    #[getter]
    fn used(&self) -> u128 {
        self.inner.used
    }

    #[getter]
    fn proposed(&self) -> u128 {
        self.inner.proposed
    }

    #[getter]
    fn ceiling(&self) -> Option<u128> {
        self.inner.ceiling
    }

    fn __repr__(&self) -> String {
        format!(
            "BarBudgetDiagnostics(reason={:?}, stage={:?}, used={}, proposed={}, ceiling={:?})",
            self.reason(),
            self.stage(),
            self.inner.used,
            self.inner.proposed,
            self.inner.ceiling
        )
    }
}

/// Final work and retained-matrix counters of a complete bar request.
#[pyclass(name = "BarRunDiagnostics", module = "auslander", frozen)]
pub(crate) struct PyBarRunDiagnostics {
    pub(crate) inner: BarRunDiagnostics,
}

#[pymethods]
impl PyBarRunDiagnostics {
    #[getter]
    fn work_units(&self) -> u64 {
        self.inner.work_units
    }

    #[getter]
    fn matrix_entries(&self) -> usize {
        self.inner.matrix_entries
    }

    fn __repr__(&self) -> String {
        format!(
            "BarRunDiagnostics(work_units={}, matrix_entries={})",
            self.inner.work_units, self.inner.matrix_entries
        )
    }
}

/// Exact Hochschild cohomology through one requested degree.
#[pyclass(name = "HochschildCohomology", module = "auslander", frozen)]
pub(crate) struct PyHochschildCohomology {
    pub(crate) inner: HochschildCohomology,
}

#[pymethods]
impl PyHochschildCohomology {
    /// The requested last cohomological degree.
    #[getter]
    fn requested_degree(&self) -> usize {
        self.inner.requested_degree()
    }

    /// The effective resource ceilings.
    #[getter]
    fn limits(&self) -> PyBarLimits {
        PyBarLimits {
            inner: self.inner.limits(),
        }
    }

    /// The exact dimensions from H^0 through the requested degree.
    #[getter]
    fn dimensions(&self) -> Vec<usize> {
        self.inner
            .degrees()
            .iter()
            .map(HochschildDegree::dim)
            .collect()
    }

    /// The exact space at a completed degree.
    #[pyo3(text_signature = "($self, degree)")]
    fn degree(&self, degree: usize) -> PyResult<PyHochschildDegree> {
        let inner = self.inner.degree(degree).ok_or_else(|| {
            PyValueError::new_err(format!(
                "Hochschild degree {degree} is outside 0..={}",
                self.inner.requested_degree()
            ))
        })?;
        Ok(PyHochschildDegree {
            inner: inner.clone(),
            field: self.inner.algebra().field(),
        })
    }

    /// The final work and retained-matrix counters.
    #[getter]
    fn diagnostics(&self) -> PyBarRunDiagnostics {
        PyBarRunDiagnostics {
            inner: self.inner.diagnostics(),
        }
    }

    /// Rebuilds the request and compares every stored coordinate and matrix.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "HochschildCohomology(requested_degree={}, dimensions={:?})",
            self.inner.requested_degree(),
            self.dimensions()
        )
    }
}

/// The exact leading degrees retained when a bar request reaches a resource cut.
///
/// This class has no requested-degree accessor. `completed_degrees` contains
/// only spaces whose outgoing differential, square check, and quotient bases
/// all finished.
#[pyclass(name = "IncompleteHochschildCohomology", module = "auslander", frozen)]
pub(crate) struct PyIncompleteHochschildCohomology {
    pub(crate) inner: IncompleteHochschildCohomology,
}

#[pymethods]
impl PyIncompleteHochschildCohomology {
    /// The effective resource ceilings.
    #[getter]
    fn limits(&self) -> PyBarLimits {
        PyBarLimits {
            inner: self.inner.limits(),
        }
    }

    /// The completed exact prefix. No later degree is present.
    #[getter]
    fn completed_degrees(&self) -> Vec<PyHochschildDegree> {
        let field = self.inner.algebra().field();
        self.inner
            .completed_degrees()
            .iter()
            .cloned()
            .map(|inner| PyHochschildDegree { inner, field })
            .collect()
    }

    /// The caller ceiling name, or `size_overflow`.
    #[getter]
    fn reason(&self) -> &'static str {
        bar_reason_name(self.inner.diagnostics().reason)
    }

    /// The first rejected reservation and its exact counters.
    #[getter]
    fn diagnostics(&self) -> PyBarBudgetDiagnostics {
        PyBarBudgetDiagnostics {
            inner: self.inner.diagnostics().clone(),
        }
    }

    /// Rebuilds the request and compares the prefix and first cut.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "IncompleteHochschildCohomology(completed_degrees={}, reason={:?})",
            self.inner.completed_degrees().len(),
            self.reason()
        )
    }
}

/// One exact Hochschild cohomology space with deterministic bases.
#[pyclass(name = "HochschildDegree", module = "auslander", frozen)]
pub(crate) struct PyHochschildDegree {
    pub(crate) inner: HochschildDegree,
    pub(crate) field: PrimeField,
}

#[pymethods]
impl PyHochschildDegree {
    #[getter]
    fn degree(&self) -> usize {
        self.inner.degree()
    }

    #[getter]
    fn dim(&self) -> usize {
        self.inner.dim()
    }

    /// The relative cochain basis as `(tuple_rank, output_basis_index)` pairs.
    #[getter]
    fn cochain_basis(&self) -> Vec<(usize, usize)> {
        self.inner
            .cochain_basis()
            .iter()
            .map(|coordinate| (coordinate.tuple_rank, coordinate.output))
            .collect()
    }

    /// Decodes a relative input tuple rank.
    ///
    /// Degree zero returns a vertex integer. Positive degree returns the list
    /// of nontrivial normal-word basis indices. An out-of-range rank raises
    /// ValueError.
    #[pyo3(text_signature = "($self, tuple_rank)")]
    fn input_for_rank(&self, py: Python<'_>, tuple_rank: usize) -> PyResult<Py<PyAny>> {
        match self.inner.input_for_rank(tuple_rank).ok_or_else(|| {
            PyValueError::new_err(format!("tuple rank {tuple_rank} is outside this degree"))
        })? {
            BarInput::Vertex(vertex) => vertex.into_py_any(py),
            BarInput::Tuple(indices) => indices.into_py_any(py),
        }
    }

    /// Resolves one algebra basis index as `(source, target, arrow_ids)`.
    #[pyo3(text_signature = "($self, basis_index)")]
    fn basis_word(&self, basis_index: usize) -> PyResult<(u32, u32, Vec<u32>)> {
        let word = self
            .inner
            .algebra()
            .basis()
            .get(basis_index)
            .ok_or_else(|| {
                PyValueError::new_err(format!("basis index {basis_index} is out of range"))
            })?;
        Ok((
            word.source(),
            word.target(),
            word.arrows().iter().map(|arrow| arrow.0).collect(),
        ))
    }

    #[getter]
    fn differential(&self) -> Vec<Vec<u64>> {
        self.inner.differential().entries_u64()
    }

    #[getter]
    fn cocycle_basis(&self) -> Vec<Vec<u64>> {
        self.inner.cocycle_basis().entries_u64()
    }

    #[getter]
    fn coboundary_basis(&self) -> Vec<Vec<u64>> {
        self.inner.coboundary_basis().entries_u64()
    }

    #[getter]
    fn complement_basis(&self) -> Vec<Vec<u64>> {
        self.inner.complement_basis().entries_u64()
    }

    /// The zero class in deterministic complement coordinates.
    #[pyo3(text_signature = "($self)")]
    fn zero_class(&self) -> PyHochschildClass {
        PyHochschildClass {
            inner: self.inner.zero_class(),
            field: self.field,
        }
    }

    /// A class from complement coordinates, reduced modulo the prime.
    #[pyo3(text_signature = "($self, coordinates)")]
    fn class_from_coordinates(&self, coordinates: Vec<i64>) -> PyResult<PyHochschildClass> {
        let coordinates = coordinates
            .into_iter()
            .map(|value| self.field.elem(value))
            .collect();
        Ok(PyHochschildClass {
            inner: self
                .inner
                .class_from_coordinates(coordinates)
                .map_err(hochschild_error)?,
            field: self.field,
        })
    }

    /// Rebuilds through this degree and compares every stored basis and matrix.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "HochschildDegree(degree={}, dim={})",
            self.inner.degree(),
            self.inner.dim()
        )
    }
}

/// A Hochschild class in deterministic complement coordinates.
#[pyclass(name = "HochschildClass", module = "auslander", frozen)]
pub(crate) struct PyHochschildClass {
    pub(crate) inner: HochschildClass,
    pub(crate) field: PrimeField,
}

#[pymethods]
impl PyHochschildClass {
    /// The exact Hochschild space this class belongs to.
    #[getter]
    fn degree(&self) -> PyHochschildDegree {
        PyHochschildDegree {
            inner: self.inner.degree().clone(),
            field: self.field,
        }
    }

    /// The deterministic complement coordinates in `0..p`.
    #[getter]
    fn coordinates(&self) -> Vec<u64> {
        row_u64(self.inner.coordinates())
    }

    #[getter]
    fn is_zero(&self) -> bool {
        self.inner.is_zero()
    }

    /// The representative cochain in the full relative coordinate basis.
    #[getter]
    fn representative(&self) -> Vec<u64> {
        row_u64(&self.inner.representative())
    }

    /// Evaluates the representative on one normalized input.
    ///
    /// Degree zero takes a vertex integer. Positive degree takes a list of
    /// nontrivial normal-word basis indices. Bad degree, basis, or composability
    /// raises ValueError.
    #[pyo3(text_signature = "($self, input)")]
    fn evaluate(&self, input: &Bound<'_, PyAny>) -> PyResult<Vec<(usize, u64)>> {
        let input = if self.inner.degree().degree() == 0 {
            BarInput::Vertex(input.extract::<u32>()?)
        } else {
            BarInput::Tuple(input.extract::<Vec<usize>>()?)
        };
        let evaluated = self.inner.evaluate(&input).map_err(hochschild_error)?;
        let (indices, values): (Vec<_>, Vec<_>) = evaluated.into_iter().unzip();
        Ok(indices.into_iter().zip(row_u64(&values)).collect())
    }

    /// Rechecks the coordinate length and reconstructs the degree.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "HochschildClass(degree={}, coordinates={:?})",
            self.inner.degree().degree(),
            self.coordinates()
        )
    }
}

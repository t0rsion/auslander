use super::*;

/// Degree-`q` chain maps between two bounded complexes.

#[pyclass(name = "HomotopyHom", module = "auslander", frozen)]
pub(crate) struct PyHomotopyHom {
    pub(crate) inner: HomotopyHom,
}

#[pymethods]
impl PyHomotopyHom {
    #[new]
    #[pyo3(signature = (source, target, degree = 0), text_signature = "(source, target, degree=0)")]
    fn new(
        py: Python<'_>,
        source: &PyBoundedComplex,
        target: &PyBoundedComplex,
        degree: i32,
    ) -> PyResult<PyHomotopyHom> {
        Ok(PyHomotopyHom {
            inner: py
                .allow_threads(|| HomotopyHom::new(&source.inner, &target.inner, degree))
                .map_err(homotopy_error)?,
        })
    }

    #[getter]
    fn degree(&self) -> i32 {
        self.inner.degree()
    }

    #[getter]
    fn dim(&self) -> usize {
        self.inner.dim()
    }

    #[getter]
    fn source(&self) -> PyBoundedComplex {
        PyBoundedComplex {
            inner: self.inner.source().clone(),
        }
    }

    #[getter]
    fn target(&self) -> PyBoundedComplex {
        PyBoundedComplex {
            inner: self.inner.target().clone(),
        }
    }

    #[getter]
    fn shifted_target(&self) -> PyBoundedComplex {
        PyBoundedComplex {
            inner: self.inner.shifted_target().clone(),
        }
    }

    #[getter]
    fn basis_rows(&self) -> Vec<Vec<u64>> {
        self.inner.basis_rows().entries_u64()
    }

    #[pyo3(text_signature = "($self, index)")]
    fn basis_morphism(&self, index: usize) -> PyResult<PyChainMap> {
        if index >= self.inner.dim() {
            return Err(PyValueError::new_err(format!(
                "chain Hom basis index {index} is outside 0..{}",
                self.inner.dim()
            )));
        }
        Ok(PyChainMap {
            inner: self.inner.basis_morphism(index),
        })
    }

    #[pyo3(text_signature = "($self, coordinates)")]
    fn morphism(&self, coordinates: Vec<i64>) -> PyResult<PyChainMap> {
        if coordinates.len() != self.inner.dim() {
            return Err(PyValueError::new_err(format!(
                "chain Hom coordinate count is {}, expected {}",
                coordinates.len(),
                self.inner.dim()
            )));
        }
        let field = self.inner.source().terms()[0].field();
        let coordinates: Vec<Fp> = coordinates
            .into_iter()
            .map(|value| field.elem(value))
            .collect();
        Ok(PyChainMap {
            inner: self.inner.morphism(&coordinates),
        })
    }

    #[pyo3(text_signature = "($self, map)")]
    fn coordinates(&self, map: &PyChainMap) -> PyResult<Vec<u64>> {
        Ok(row_u64(
            &self.inner.coords(&map.inner).map_err(value_error)?,
        ))
    }

    #[pyo3(text_signature = "($self)")]
    fn quotient(&self, py: Python<'_>) -> PyResult<PyHomotopyHomQuotient> {
        Ok(PyHomotopyHomQuotient {
            inner: py
                .allow_threads(|| self.inner.quotient())
                .map_err(homotopy_error)?,
        })
    }

    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "HomotopyHom(degree={}, chain_dim={})",
            self.inner.degree(),
            self.inner.dim()
        )
    }
}

/// Degree-`q` chain maps modulo null-homotopic maps.
#[pyclass(name = "HomotopyHomQuotient", module = "auslander", frozen)]
pub(crate) struct PyHomotopyHomQuotient {
    pub(crate) inner: HomotopyHomQuotient,
}

#[pymethods]
impl PyHomotopyHomQuotient {
    #[getter]
    fn degree(&self) -> i32 {
        self.inner.degree()
    }

    #[getter]
    fn dim(&self) -> usize {
        self.inner.dim()
    }

    #[getter]
    fn source(&self) -> PyBoundedComplex {
        PyBoundedComplex {
            inner: self.inner.source().clone(),
        }
    }

    #[getter]
    fn target(&self) -> PyBoundedComplex {
        PyBoundedComplex {
            inner: self.inner.target().clone(),
        }
    }

    #[getter]
    fn shifted_target(&self) -> PyBoundedComplex {
        PyBoundedComplex {
            inner: self.inner.shifted_target().clone(),
        }
    }

    #[getter]
    fn null_homotopic_basis(&self) -> Vec<Vec<u64>> {
        self.inner.null_homotopic_basis().entries_u64()
    }

    #[getter]
    fn complement_basis(&self) -> Vec<Vec<u64>> {
        self.inner.complement_basis().entries_u64()
    }

    #[pyo3(text_signature = "($self, coordinates)")]
    fn representative(&self, coordinates: Vec<i64>) -> PyResult<PyChainMap> {
        if coordinates.len() != self.inner.dim() {
            return Err(PyValueError::new_err(format!(
                "homotopy class coordinate count is {}, expected {}",
                coordinates.len(),
                self.inner.dim()
            )));
        }
        let field = self.inner.source().terms()[0].field();
        let coordinates: Vec<Fp> = coordinates
            .into_iter()
            .map(|value| field.elem(value))
            .collect();
        Ok(PyChainMap {
            inner: self.inner.representative(&coordinates),
        })
    }

    /// Returns class coordinates and the null-homotopic remainder.
    #[pyo3(text_signature = "($self, map)")]
    fn reduce(&self, py: Python<'_>, map: &PyChainMap) -> PyResult<(Vec<u64>, PyChainMap)> {
        let quotient = self.inner.clone();
        let map = map.inner.clone();
        let (coordinates, remainder) = py
            .allow_threads(|| quotient.reduce(&map))
            .map_err(homotopy_error)?;
        Ok((row_u64(&coordinates), PyChainMap { inner: remainder }))
    }

    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "HomotopyHomQuotient(degree={}, dim={})",
            self.inner.degree(),
            self.inner.dim()
        )
    }
}

/// Degree-zero chain maps modulo null-homotopic maps.
#[pyclass(name = "ChainHomQuotient", module = "auslander", frozen)]
pub(crate) struct PyChainHomQuotient {
    pub(crate) inner: ChainHomQuotient,
}

#[pymethods]
impl PyChainHomQuotient {
    /// The dimension of the quotient.
    #[getter]
    fn dim(&self) -> usize {
        self.inner.dim()
    }

    /// The source complex.
    #[getter]
    fn source(&self) -> PyBoundedComplex {
        PyBoundedComplex {
            inner: self.inner.source().clone(),
        }
    }

    /// The target complex.
    #[getter]
    fn target(&self) -> PyBoundedComplex {
        PyBoundedComplex {
            inner: self.inner.target().clone(),
        }
    }

    /// The deterministic null-homotopic basis in component coordinates.
    #[getter]
    fn null_homotopic_basis(&self) -> Vec<Vec<u64>> {
        self.inner.null_homotopic_basis().entries_u64()
    }

    /// The deterministic quotient complement in component coordinates.
    #[getter]
    fn complement_basis(&self) -> Vec<Vec<u64>> {
        self.inner.complement_basis().entries_u64()
    }

    /// Returns one representative from quotient-basis coordinates.
    #[pyo3(text_signature = "($self, coordinates)")]
    fn representative(&self, coordinates: Vec<i64>) -> PyResult<PyChainMap> {
        if coordinates.len() != self.inner.dim() {
            return Err(PyValueError::new_err(format!(
                "chain homotopy quotient coordinate count is {}, expected {}",
                coordinates.len(),
                self.inner.dim()
            )));
        }
        let field = self.inner.source().terms()[0].field();
        let coordinates: Vec<Fp> = coordinates
            .into_iter()
            .map(|value| field.elem(value))
            .collect();
        Ok(PyChainMap {
            inner: self.inner.representative(&coordinates),
        })
    }

    /// Returns quotient coordinates and the null-homotopic remainder.
    #[pyo3(text_signature = "($self, map)")]
    fn reduce(&self, py: Python<'_>, map: &PyChainMap) -> PyResult<(Vec<u64>, PyChainMap)> {
        let quotient = self.inner.clone();
        let map = map.inner.clone();
        let (coordinates, remainder) = py
            .allow_threads(|| quotient.reduce(&map))
            .map_err(homotopy_error)?;
        Ok((row_u64(&coordinates), PyChainMap { inner: remainder }))
    }

    /// Recomputes the chain Hom, null-homotopic subspace, and complement.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!("ChainHomQuotient(dim={})", self.inner.dim())
    }
}

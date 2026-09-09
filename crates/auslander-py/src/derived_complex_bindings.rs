use super::*;

/// A bounded complex whose terms carry verified membership in `add(T)`.

#[pyclass(name = "AddTComplex", module = "auslander", frozen)]
pub(crate) struct PyAddTComplex {
    pub(crate) inner: RustAddTComplex,
}

#[pymethods]
impl PyAddTComplex {
    /// Builds a bounded `add(T)` complex from one witness per term.
    #[new]
    #[pyo3(text_signature = "(complex, witnesses)")]
    fn new(
        py: Python<'_>,
        complex: &PyBoundedComplex,
        witnesses: Vec<PyRef<'_, PyAddClosureWitness>>,
    ) -> PyResult<PyAddTComplex> {
        let complex = complex.inner.clone();
        let witnesses = witnesses
            .iter()
            .map(|witness| witness.inner.clone())
            .collect();
        Ok(PyAddTComplex {
            inner: py
                .allow_threads(|| RustAddTComplex::new(complex, witnesses))
                .map_err(transport_error)?,
        })
    }

    /// The bounded source complex.
    #[getter]
    fn complex(&self) -> PyBoundedComplex {
        PyBoundedComplex {
            inner: self.inner.complex().clone(),
        }
    }

    /// One add(T) witness per source term.
    #[getter]
    fn witnesses(&self) -> Vec<PyAddClosureWitness> {
        self.inner
            .witnesses()
            .iter()
            .cloned()
            .map(|inner| PyAddClosureWitness { inner })
            .collect()
    }

    /// Rechecks the bounded complex and every term witness.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "AddTComplex(degree_range={:?})",
            self.complex().degree_range()
        )
    }
}

/// A bounded target complex with checked canonical-projective term models.
#[pyclass(name = "ProjectiveTargetComplex", module = "auslander", frozen)]
pub(crate) struct PyProjectiveTargetComplex {
    pub(crate) inner: RustProjectiveTargetComplex,
}

#[pymethods]
impl PyProjectiveTargetComplex {
    /// The bounded complex over the recovered target algebra.
    #[getter]
    fn complex(&self) -> PyBoundedComplex {
        PyBoundedComplex {
            inner: self.inner.complex().clone(),
        }
    }

    /// Rechecks every projective term model and differential.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "ProjectiveTargetComplex(degree_range={:?})",
            self.complex().degree_range()
        )
    }
}

/// Two mutually inverse checked chain maps.
#[pyclass(name = "ChainIsomorphism", module = "auslander", frozen)]
pub(crate) struct PyChainIsomorphism {
    pub(crate) inner: RustChainIsomorphism,
}

#[pymethods]
impl PyChainIsomorphism {
    /// Builds a chain isomorphism after checking both inverse identities.
    #[new]
    #[pyo3(text_signature = "(forward, backward)")]
    fn new(forward: &PyChainMap, backward: &PyChainMap) -> PyResult<PyChainIsomorphism> {
        Ok(PyChainIsomorphism {
            inner: RustChainIsomorphism::new(forward.inner.clone(), backward.inner.clone())
                .map_err(transport_error)?,
        })
    }

    /// The forward chain map.
    #[getter]
    fn forward(&self) -> PyChainMap {
        PyChainMap {
            inner: self.inner.forward().clone(),
        }
    }

    /// The inverse chain map.
    #[getter]
    fn backward(&self) -> PyChainMap {
        PyChainMap {
            inner: self.inner.backward().clone(),
        }
    }

    /// Rechecks both maps and both inverse identities.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "ChainIsomorphism(degree_range={:?})",
            (
                self.inner.forward().range().lower(),
                self.inner.forward().range().upper()
            )
        )
    }
}

/// Strict bounded transport fixed by one verified target presentation.
#[pyclass(name = "StrictTransport", module = "auslander", frozen)]
pub(crate) struct PyStrictTransport {
    pub(crate) inner: RustStrictTransport,
}

#[pymethods]
impl PyStrictTransport {
    /// Builds strict transport from one verified target presentation.
    #[new]
    #[pyo3(text_signature = "(target)")]
    fn new(py: Python<'_>, target: &PyTargetPresentation) -> PyResult<PyStrictTransport> {
        let target = target.inner.clone();
        Ok(PyStrictTransport {
            inner: py
                .allow_threads(|| RustStrictTransport::new(target))
                .map_err(transport_error)?,
        })
    }

    /// The target presentation that fixes this transport.
    #[getter]
    fn target(&self) -> PyTargetPresentation {
        PyTargetPresentation {
            inner: self.inner.target().clone(),
        }
    }

    /// Stores verified canonical-projective models for every target term.
    #[pyo3(text_signature = "($self, complex)")]
    fn target_complex(
        &self,
        py: Python<'_>,
        complex: &PyBoundedComplex,
    ) -> PyResult<PyProjectiveTargetComplex> {
        let complex = complex.inner.clone();
        Ok(PyProjectiveTargetComplex {
            inner: py
                .allow_threads(|| self.inner.target_complex(complex))
                .map_err(transport_error)?,
        })
    }

    /// Transports a bounded `add(T)` complex to target projectives.
    #[pyo3(text_signature = "($self, source)")]
    fn forward(
        &self,
        py: Python<'_>,
        source: &PyAddTComplex,
    ) -> PyResult<PyProjectiveTargetComplex> {
        Ok(PyProjectiveTargetComplex {
            inner: py
                .allow_threads(|| self.inner.forward(&source.inner))
                .map_err(transport_error)?,
        })
    }

    /// Transports a bounded projective target complex back to `add(T)`.
    #[pyo3(text_signature = "($self, target)")]
    fn reverse(
        &self,
        py: Python<'_>,
        target: &PyProjectiveTargetComplex,
    ) -> PyResult<PyAddTComplex> {
        Ok(PyAddTComplex {
            inner: py
                .allow_threads(|| self.inner.reverse(&target.inner))
                .map_err(transport_error)?,
        })
    }

    /// Transports a checked chain map between bounded `add(T)` complexes.
    #[pyo3(text_signature = "($self, source, target, map)")]
    fn forward_chain_map(
        &self,
        py: Python<'_>,
        source: &PyAddTComplex,
        target: &PyAddTComplex,
        map: &PyChainMap,
    ) -> PyResult<PyChainMap> {
        Ok(PyChainMap {
            inner: py
                .allow_threads(|| {
                    self.inner
                        .forward_chain_map(&source.inner, &target.inner, &map.inner)
                })
                .map_err(transport_error)?,
        })
    }

    /// Transports a checked chain map between target projective complexes.
    #[pyo3(text_signature = "($self, source, target, map)")]
    fn reverse_chain_map(
        &self,
        py: Python<'_>,
        source: &PyProjectiveTargetComplex,
        target: &PyProjectiveTargetComplex,
        map: &PyChainMap,
    ) -> PyResult<PyChainMap> {
        Ok(PyChainMap {
            inner: py
                .allow_threads(|| {
                    self.inner
                        .reverse_chain_map(&source.inner, &target.inner, &map.inner)
                })
                .map_err(transport_error)?,
        })
    }

    /// Transports a chain homotopy between bounded `add(T)` complexes.
    #[pyo3(text_signature = "($self, source, target, homotopy)")]
    fn forward_homotopy(
        &self,
        py: Python<'_>,
        source: &PyAddTComplex,
        target: &PyAddTComplex,
        homotopy: &PyChainHomotopy,
    ) -> PyResult<PyChainHomotopy> {
        Ok(PyChainHomotopy {
            inner: py
                .allow_threads(|| {
                    self.inner
                        .forward_homotopy(&source.inner, &target.inner, &homotopy.inner)
                })
                .map_err(transport_error)?,
        })
    }

    /// Transports a chain homotopy between target projective complexes.
    #[pyo3(text_signature = "($self, source, target, homotopy)")]
    fn reverse_homotopy(
        &self,
        py: Python<'_>,
        source: &PyProjectiveTargetComplex,
        target: &PyProjectiveTargetComplex,
        homotopy: &PyChainHomotopy,
    ) -> PyResult<PyChainHomotopy> {
        Ok(PyChainHomotopy {
            inner: py
                .allow_threads(|| {
                    self.inner
                        .reverse_homotopy(&source.inner, &target.inner, &homotopy.inner)
                })
                .map_err(transport_error)?,
        })
    }

    /// Transports the mapping cone of a checked source chain map.
    #[pyo3(text_signature = "($self, source, target, map)")]
    fn forward_cone(
        &self,
        py: Python<'_>,
        source: &PyAddTComplex,
        target: &PyAddTComplex,
        map: &PyChainMap,
    ) -> PyResult<PyBoundedComplex> {
        Ok(PyBoundedComplex {
            inner: py
                .allow_threads(|| {
                    self.inner
                        .forward_cone(&source.inner, &target.inner, &map.inner)
                })
                .map_err(transport_error)?,
        })
    }

    /// Transports the mapping cone of a checked target chain map.
    #[pyo3(text_signature = "($self, source, target, map)")]
    fn reverse_cone(
        &self,
        py: Python<'_>,
        source: &PyProjectiveTargetComplex,
        target: &PyProjectiveTargetComplex,
        map: &PyChainMap,
    ) -> PyResult<PyBoundedComplex> {
        Ok(PyBoundedComplex {
            inner: py
                .allow_threads(|| {
                    self.inner
                        .reverse_cone(&source.inner, &target.inner, &map.inner)
                })
                .map_err(transport_error)?,
        })
    }

    /// Transports an explicit homological shift of a bounded `add(T)` complex.
    #[pyo3(text_signature = "($self, source, amount)")]
    fn forward_shift(
        &self,
        py: Python<'_>,
        source: &PyAddTComplex,
        amount: i32,
    ) -> PyResult<PyProjectiveTargetComplex> {
        Ok(PyProjectiveTargetComplex {
            inner: py
                .allow_threads(|| self.inner.forward_shift(&source.inner, amount))
                .map_err(transport_error)?,
        })
    }

    /// Transports an explicit homological shift of a target projective complex.
    #[pyo3(text_signature = "($self, target, amount)")]
    fn reverse_shift(
        &self,
        py: Python<'_>,
        target: &PyProjectiveTargetComplex,
        amount: i32,
    ) -> PyResult<PyAddTComplex> {
        Ok(PyAddTComplex {
            inner: py
                .allow_threads(|| self.inner.reverse_shift(&target.inner, amount))
                .map_err(transport_error)?,
        })
    }

    /// Transports the direct sum of bounded `add(T)` complexes.
    #[pyo3(text_signature = "($self, sources)")]
    fn forward_direct_sum(
        &self,
        py: Python<'_>,
        sources: Vec<PyRef<'_, PyAddTComplex>>,
    ) -> PyResult<PyProjectiveTargetComplex> {
        let sources: Vec<RustAddTComplex> =
            sources.iter().map(|source| source.inner.clone()).collect();
        Ok(PyProjectiveTargetComplex {
            inner: py
                .allow_threads(|| {
                    self.inner
                        .forward_direct_sum(&sources.iter().collect::<Vec<_>>())
                })
                .map_err(transport_error)?,
        })
    }

    /// Transports the direct sum of target projective complexes.
    #[pyo3(text_signature = "($self, targets)")]
    fn reverse_direct_sum(
        &self,
        py: Python<'_>,
        targets: Vec<PyRef<'_, PyProjectiveTargetComplex>>,
    ) -> PyResult<PyAddTComplex> {
        let targets: Vec<RustProjectiveTargetComplex> =
            targets.iter().map(|target| target.inner.clone()).collect();
        Ok(PyAddTComplex {
            inner: py
                .allow_threads(|| {
                    self.inner
                        .reverse_direct_sum(&targets.iter().collect::<Vec<_>>())
                })
                .map_err(transport_error)?,
        })
    }

    /// Returns the source unit after forward then reverse transport.
    #[pyo3(text_signature = "($self, source)")]
    fn source_round_trip(
        &self,
        py: Python<'_>,
        source: &PyAddTComplex,
    ) -> PyResult<PyChainIsomorphism> {
        Ok(PyChainIsomorphism {
            inner: py
                .allow_threads(|| self.inner.source_round_trip(&source.inner))
                .map_err(transport_error)?,
        })
    }

    /// Returns the target counit after reverse then forward transport.
    #[pyo3(text_signature = "($self, target)")]
    fn target_round_trip(
        &self,
        py: Python<'_>,
        target: &PyProjectiveTargetComplex,
    ) -> PyResult<PyChainIsomorphism> {
        Ok(PyChainIsomorphism {
            inner: py
                .allow_threads(|| self.inner.target_round_trip(&target.inner))
                .map_err(transport_error)?,
        })
    }

    /// Rechecks the target and canonical-projective models.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "StrictTransport(source_dims={:?}, target_dim={})",
            self.inner.target().source().dim_vector(),
            self.inner.target().target().dim()
        )
    }
}

/// One graded homotopy endomorphism quotient of the tilting resolution.
#[pyclass(name = "GradedHomotopyEndomorphisms", module = "auslander", frozen)]
pub(crate) struct PyGradedHomotopyEndomorphisms {
    pub(crate) inner: GradedHomotopyEndomorphisms,
}

#[pymethods]
impl PyGradedHomotopyEndomorphisms {
    /// The target shift degree.
    #[getter]
    fn degree(&self) -> i32 {
        self.inner.degree()
    }

    /// The deterministic quotient in this degree.
    #[getter]
    fn quotient(&self) -> PyChainHomQuotient {
        PyChainHomQuotient {
            inner: self.inner.quotient().clone(),
        }
    }

    /// Rechecks the stored quotient basis and null-homotopic subspace.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "GradedHomotopyEndomorphisms(degree={}, dim={})",
            self.inner.degree(),
            self.inner.quotient().dim()
        )
    }
}

/// The checked degree-zero map from homotopy endomorphisms to `End_A(T)`.
#[pyclass(name = "DegreeZeroEndIdentification", module = "auslander", frozen)]
pub(crate) struct PyDegreeZeroEndIdentification {
    pub(crate) inner: DegreeZeroEndIdentification,
}

#[pymethods]
impl PyDegreeZeroEndIdentification {
    /// The degree-zero homotopy endomorphism quotient.
    #[getter]
    fn quotient(&self) -> PyChainHomQuotient {
        PyChainHomQuotient {
            inner: self.inner.quotient().clone(),
        }
    }

    /// Rows map quotient-basis coordinates to `End_A(T)` coordinates.
    #[getter]
    fn coordinates(&self) -> Vec<Vec<u64>> {
        self.inner.coordinates().entries_u64()
    }

    fn __repr__(&self) -> String {
        format!(
            "DegreeZeroEndIdentification(dim={})",
            self.inner.quotient().dim()
        )
    }
}

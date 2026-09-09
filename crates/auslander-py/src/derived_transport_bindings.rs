use super::*;

/// Automatic replacement and transport through a classical tilting equivalence.
#[pyclass(name = "DerivedTransport", module = "auslander", frozen)]

pub(crate) struct PyDerivedTransport {
    pub(crate) inner: RustDerivedTransport,
}

pub(crate) enum AutomaticTransportResult {
    Forward(Box<DerivedForwardTransport>),
    Reverse(Box<DerivedReverseTransport>),
}

/// One complete automatic forward or inverse transport.
#[pyclass(name = "DerivedTransportResult", module = "auslander", frozen)]
pub(crate) struct PyDerivedTransportResult {
    pub(crate) inner: AutomaticTransportResult,
}

#[pymethods]
impl PyDerivedTransportResult {
    #[getter]
    fn direction(&self) -> &'static str {
        match self.inner {
            AutomaticTransportResult::Forward(_) => "forward",
            AutomaticTransportResult::Reverse(_) => "reverse",
        }
    }

    #[getter]
    fn input(&self) -> PyBoundedComplex {
        let inner = match &self.inner {
            AutomaticTransportResult::Forward(value) => value.input(),
            AutomaticTransportResult::Reverse(value) => value.input(),
        };
        PyBoundedComplex {
            inner: inner.clone(),
        }
    }

    #[getter]
    fn replacement(&self) -> PyPerfectReplacement {
        let inner = match &self.inner {
            AutomaticTransportResult::Forward(value) => value.replacement(),
            AutomaticTransportResult::Reverse(value) => value.replacement(),
        };
        PyPerfectReplacement {
            inner: inner.clone(),
        }
    }

    #[getter]
    fn output(&self) -> PyBoundedComplex {
        let inner = match &self.inner {
            AutomaticTransportResult::Forward(value) => value.output().complex(),
            AutomaticTransportResult::Reverse(value) => value.output().complex(),
        };
        PyBoundedComplex {
            inner: inner.clone(),
        }
    }

    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| match &self.inner {
            AutomaticTransportResult::Forward(value) => value.verify(),
            AutomaticTransportResult::Reverse(value) => value.verify(),
        })
    }
}

#[pymethods]
impl PyDerivedTransport {
    #[new]
    fn new(certificate: &PyDerivedEquivalenceCertificate) -> PyResult<PyDerivedTransport> {
        Ok(PyDerivedTransport {
            inner: RustDerivedTransport::new(certificate.inner.clone()).map_err(engine_error)?,
        })
    }

    #[pyo3(signature = (input, limits=None, control=None))]
    fn forward(
        &self,
        py: Python<'_>,
        input: &PyBoundedComplex,
        limits: Option<&PyReplacementLimits>,
        control: Option<&PyComputationControl>,
    ) -> PyResult<Py<PyAny>> {
        let limits = limits.map_or_else(ReplacementLimits::default, |value| value.inner);
        let control = control.map(|value| value.inner.clone());
        match py
            .allow_threads(|| self.inner.forward(&input.inner, limits, control.as_ref()))
            .map_err(engine_error)?
        {
            DerivedForwardOutcome::Transported(value) => Py::new(
                py,
                PyDerivedTransportResult {
                    inner: AutomaticTransportResult::Forward(value),
                },
            )
            .map(Py::into_any),
            DerivedForwardOutcome::ReplacementCut(value) => Py::new(
                py,
                PyIncompletePerfectReplacement {
                    inner: ReplacementBoundary::Cut(value),
                },
            )
            .map(Py::into_any),
            DerivedForwardOutcome::ReplacementCancelled(value) => Py::new(
                py,
                PyIncompletePerfectReplacement {
                    inner: ReplacementBoundary::Cancelled(value),
                },
            )
            .map(Py::into_any),
        }
    }

    #[pyo3(signature = (input, limits=None, control=None))]
    fn reverse(
        &self,
        py: Python<'_>,
        input: &PyBoundedComplex,
        limits: Option<&PyReplacementLimits>,
        control: Option<&PyComputationControl>,
    ) -> PyResult<Py<PyAny>> {
        let limits = limits.map_or_else(ReplacementLimits::default, |value| value.inner);
        let control = control.map(|value| value.inner.clone());
        match py
            .allow_threads(|| self.inner.reverse(&input.inner, limits, control.as_ref()))
            .map_err(engine_error)?
        {
            DerivedReverseOutcome::Transported(value) => Py::new(
                py,
                PyDerivedTransportResult {
                    inner: AutomaticTransportResult::Reverse(value),
                },
            )
            .map(Py::into_any),
            DerivedReverseOutcome::ReplacementCut(value) => Py::new(
                py,
                PyIncompletePerfectReplacement {
                    inner: ReplacementBoundary::Cut(value),
                },
            )
            .map(Py::into_any),
            DerivedReverseOutcome::ReplacementCancelled(value) => Py::new(
                py,
                PyIncompletePerfectReplacement {
                    inner: ReplacementBoundary::Cancelled(value),
                },
            )
            .map(Py::into_any),
        }
    }
}

/// A checked bounded derived equivalence from a classical tilting module.
#[pyclass(name = "DerivedEquivalenceCertificate", module = "auslander", frozen)]
pub(crate) struct PyDerivedEquivalenceCertificate {
    pub(crate) inner: RustDerivedEquivalenceCertificate,
}

#[pymethods]
impl PyDerivedEquivalenceCertificate {
    /// Builds the complete certificate from checked tilting and target data.
    #[new]
    #[pyo3(text_signature = "(tilting, target)")]
    fn new(
        py: Python<'_>,
        tilting: &PyClassicalTiltingModule,
        target: &PyTargetPresentation,
    ) -> PyResult<PyDerivedEquivalenceCertificate> {
        let tilting = tilting.inner().clone();
        let target = target.inner.clone();
        Ok(PyDerivedEquivalenceCertificate {
            inner: py
                .allow_threads(|| RustDerivedEquivalenceCertificate::new(tilting, target))
                .map_err(derived_certificate_error)?,
        })
    }

    /// The tilting certificate used by this derived-equivalence certificate.
    #[getter]
    fn tilting(&self) -> PyClassicalTiltingModule {
        PyClassicalTiltingModule {
            home: Arc::new(RustClassicalTiltingResult::Tilting(
                self.inner.tilting().clone(),
            )),
        }
    }

    /// The verified split target presentation.
    #[getter]
    fn target(&self) -> PyTargetPresentation {
        PyTargetPresentation {
            inner: self.inner.target().clone(),
        }
    }

    /// The tilting resolution as a bounded homological complex.
    #[getter]
    fn resolution_complex(&self) -> PyBoundedComplex {
        PyBoundedComplex {
            inner: self.inner.resolution_complex().clone(),
        }
    }

    /// The deterministic graded homotopy endomorphism quotients.
    #[getter]
    fn graded_homotopy(&self) -> Vec<PyGradedHomotopyEndomorphisms> {
        self.inner
            .graded_homotopy()
            .iter()
            .cloned()
            .map(|inner| PyGradedHomotopyEndomorphisms { inner })
            .collect()
    }

    /// The checked degree-zero `End_A(T)` coordinate map.
    #[getter]
    fn degree_zero_identification(&self) -> PyDegreeZeroEndIdentification {
        PyDegreeZeroEndIdentification {
            inner: self.inner.degree_zero_identification().clone(),
        }
    }

    /// The strict transport fixed by the stored target presentation.
    #[getter]
    fn transport(&self) -> PyStrictTransport {
        PyStrictTransport {
            inner: self.inner.transport().clone(),
        }
    }

    /// Automatic transport for ordinary bounded complexes.
    #[getter]
    fn automatic_transport(&self) -> PyResult<PyDerivedTransport> {
        PyDerivedTransport::new(self)
    }

    /// Rechecks tilting, generation, target recovery, Hom vanishing, and transport.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "DerivedEquivalenceCertificate(resolution_width={}, graded_spaces={})",
            self.inner.tilting().projective_dimension(),
            self.inner.graded_homotopy().len()
        )
    }
}

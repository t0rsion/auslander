use super::*;

/// A nonempty bounded complex in increasing homological degree order.
///
/// `differentials[i]` maps `terms[i + 1]` to `terms[i]`. Construction checks
/// the endpoints and every consecutive composite.

#[pyclass(name = "BoundedComplex", module = "auslander", frozen)]
pub(crate) struct PyBoundedComplex {
    pub(crate) inner: BoundedComplex,
}

#[pymethods]
impl PyBoundedComplex {
    /// BoundedComplex(lower, terms, differentials).
    #[new]
    #[pyo3(text_signature = "(lower, terms, differentials)")]
    fn new(
        lower: i32,
        terms: Vec<PyRef<'_, PyRightModule>>,
        differentials: Vec<PyRef<'_, PyMorphism>>,
    ) -> PyResult<PyBoundedComplex> {
        Ok(PyBoundedComplex {
            inner: BoundedComplex::new(
                lower,
                terms.iter().map(|term| term.inner.clone()).collect(),
                differentials
                    .iter()
                    .map(|differential| differential.inner.clone())
                    .collect(),
            )
            .map_err(bounded_complex_error)?,
        })
    }

    /// The inclusive stored degree interval.
    #[getter]
    pub(crate) fn degree_range(&self) -> (i32, i32) {
        (self.inner.lower(), self.inner.upper())
    }

    /// Terms in increasing homological degree order.
    #[getter]
    fn terms(&self) -> Vec<PyRightModule> {
        wrap_all(self.inner.terms())
    }

    /// Differentials in increasing source-degree order.
    #[getter]
    fn differentials(&self) -> Vec<PyMorphism> {
        wrap_all(self.inner.differentials())
    }

    /// The term at one stored degree.
    #[pyo3(text_signature = "($self, degree)")]
    fn term(&self, degree: i32) -> PyResult<PyRightModule> {
        Ok(self.inner.term(degree).map_err(value_error)?.into())
    }

    /// The differential with the named source degree, or None at the lower end.
    #[pyo3(text_signature = "($self, degree)")]
    fn differential(&self, degree: i32) -> Option<PyMorphism> {
        self.inner
            .differential(degree)
            .cloned()
            .map(PyMorphism::from)
    }

    /// The shifted complex `(C[s])_n = C_(n-s)`.
    #[pyo3(text_signature = "($self, amount)")]
    fn shift(&self, amount: i32) -> PyResult<PyBoundedComplex> {
        Ok(PyBoundedComplex {
            inner: self.inner.shift(amount).map_err(bounded_complex_error)?,
        })
    }

    /// The direct sum, with explicit zero padding to the common degree range.
    #[staticmethod]
    #[pyo3(text_signature = "(complexes)")]
    fn direct_sum(complexes: Vec<PyRef<'_, PyBoundedComplex>>) -> PyResult<PyBoundedComplex> {
        let refs: Vec<&BoundedComplex> = complexes.iter().map(|complex| &complex.inner).collect();
        Ok(PyBoundedComplex {
            inner: BoundedComplex::direct_sum(&refs).map_err(bounded_complex_error)?,
        })
    }

    /// The identity chain map.
    #[pyo3(text_signature = "($self)")]
    fn identity(&self) -> PyChainMap {
        PyChainMap {
            inner: ChainMap::identity(&self.inner),
        }
    }

    /// The zero chain map to `target`, with zero padding when ranges differ.
    #[pyo3(text_signature = "($self, target)")]
    fn zero_map(&self, target: &PyBoundedComplex) -> PyResult<PyChainMap> {
        Ok(PyChainMap {
            inner: ChainMap::zero(&self.inner, &target.inner).map_err(homotopy_error)?,
        })
    }

    /// Degree-`q` chain maps to `target` before quotienting by homotopy.
    #[pyo3(text_signature = "($self, target, degree=0)", signature = (target, degree = 0))]
    fn hom(
        &self,
        py: Python<'_>,
        target: &PyBoundedComplex,
        degree: i32,
    ) -> PyResult<PyHomotopyHom> {
        Ok(PyHomotopyHom {
            inner: py
                .allow_threads(|| HomotopyHom::new(&self.inner, &target.inner, degree))
                .map_err(homotopy_error)?,
        })
    }

    /// Build a checked bounded projective model or return its typed checked prefix.
    #[pyo3(
        text_signature = "($self, limits=None, control=None)",
        signature = (limits=None, control=None)
    )]
    fn perfect_replacement(
        &self,
        py: Python<'_>,
        limits: Option<&PyReplacementLimits>,
        control: Option<&PyComputationControl>,
    ) -> PyResult<Py<PyAny>> {
        let limits = limits.map_or_else(ReplacementLimits::default, |value| value.inner);
        let control = control.map(|value| value.inner.clone());
        let outcome = py
            .allow_threads(|| replace_perfect(&self.inner, limits, control.as_ref()))
            .map_err(engine_error)?;
        match outcome {
            ReplacementOutcome::Replaced(inner) => {
                Py::new(py, PyPerfectReplacement { inner }).map(Py::into_any)
            }
            ReplacementOutcome::Cut(inner) => Py::new(
                py,
                PyIncompletePerfectReplacement {
                    inner: ReplacementBoundary::Cut(inner),
                },
            )
            .map(Py::into_any),
            ReplacementOutcome::Cancelled(inner) => Py::new(
                py,
                PyIncompletePerfectReplacement {
                    inner: ReplacementBoundary::Cancelled(inner),
                },
            )
            .map(Py::into_any),
        }
    }

    /// Compute every finite-support derived Hom space to `target`.
    #[pyo3(
        text_signature = "($self, target, limits=None, control=None)",
        signature = (target, limits=None, control=None)
    )]
    fn derived_hom(
        &self,
        py: Python<'_>,
        target: &PyBoundedComplex,
        limits: Option<&PyDerivedHomLimits>,
        control: Option<&PyComputationControl>,
    ) -> PyResult<Py<PyAny>> {
        let limits = limits.map_or_else(DerivedHomLimits::default, |value| value.inner);
        let control = control.map(|value| value.inner.clone());
        let outcome = py
            .allow_threads(|| derived_hom(&self.inner, &target.inner, limits, control.as_ref()))
            .map_err(engine_error)?;
        match outcome {
            DerivedHomOutcome::Complete(inner) => {
                Py::new(py, PyDerivedHom { inner }).map(Py::into_any)
            }
            DerivedHomOutcome::ReplacementCut(inner) => Py::new(
                py,
                PyIncompleteDerivedHom {
                    inner: DerivedHomBoundary::ReplacementCut(inner),
                },
            )
            .map(Py::into_any),
            DerivedHomOutcome::ReplacementCancelled(inner) => Py::new(
                py,
                PyIncompleteDerivedHom {
                    inner: DerivedHomBoundary::ReplacementCancelled(inner),
                },
            )
            .map(Py::into_any),
            DerivedHomOutcome::WorkCut(inner) => Py::new(
                py,
                PyIncompleteDerivedHom {
                    inner: DerivedHomBoundary::WorkCut(inner),
                },
            )
            .map(Py::into_any),
            DerivedHomOutcome::Cancelled(inner) => Py::new(
                py,
                PyIncompleteDerivedHom {
                    inner: DerivedHomBoundary::Cancelled(inner),
                },
            )
            .map(Py::into_any),
        }
    }

    /// Rechecks endpoints and zero composites.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    #[getter]
    fn is_zero(&self) -> bool {
        self.inner.is_zero()
    }

    #[pyo3(text_signature = "($self, other)")]
    fn agrees_with(&self, other: &PyBoundedComplex) -> bool {
        self.inner.agrees_with(&other.inner)
    }

    fn __len__(&self) -> usize {
        self.inner.len()
    }

    fn __repr__(&self) -> String {
        format!(
            "BoundedComplex(degree_range={:?}, term_dims={:?})",
            self.degree_range(),
            self.inner
                .terms()
                .iter()
                .map(|term| term.dim_vector())
                .collect::<Vec<_>>()
        )
    }
}

/// A degree-zero chain map between bounded complexes.
#[pyclass(name = "ChainMap", module = "auslander", frozen)]
pub(crate) struct PyChainMap {
    pub(crate) inner: ChainMap,
}

#[pymethods]
impl PyChainMap {
    /// ChainMap(source, target, components), with one component per common degree.
    #[new]
    #[pyo3(text_signature = "(source, target, components)")]
    fn new(
        source: &PyBoundedComplex,
        target: &PyBoundedComplex,
        components: Vec<PyRef<'_, PyMorphism>>,
    ) -> PyResult<PyChainMap> {
        Ok(PyChainMap {
            inner: ChainMap::new(
                &source.inner,
                &target.inner,
                components
                    .iter()
                    .map(|component| component.inner.clone())
                    .collect(),
            )
            .map_err(homotopy_error)?,
        })
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
    fn components(&self) -> Vec<PyMorphism> {
        wrap_all(self.inner.components())
    }

    #[getter]
    fn degree_range(&self) -> (i32, i32) {
        (self.inner.range().lower(), self.inner.range().upper())
    }

    #[pyo3(text_signature = "($self, degree)")]
    fn component(&self, degree: i32) -> PyResult<PyMorphism> {
        Ok(self.inner.component(degree).map_err(homotopy_error)?.into())
    }

    /// Composes this map first, then `other`.
    #[pyo3(text_signature = "($self, other)")]
    fn then(&self, other: &PyChainMap) -> PyResult<PyChainMap> {
        Ok(PyChainMap {
            inner: self.inner.then(&other.inner).map_err(homotopy_error)?,
        })
    }

    #[pyo3(text_signature = "($self, other)")]
    fn add(&self, other: &PyChainMap) -> PyResult<PyChainMap> {
        Ok(PyChainMap {
            inner: self.inner.add(&other.inner).map_err(homotopy_error)?,
        })
    }

    #[pyo3(text_signature = "($self, scalar)")]
    fn scale(&self, scalar: i64) -> PyChainMap {
        let field = self.inner.source().terms()[0].field();
        PyChainMap {
            inner: self.inner.scale(field.elem(scalar)),
        }
    }

    #[pyo3(text_signature = "($self, amount)")]
    fn shift(&self, amount: i32) -> PyResult<PyChainMap> {
        Ok(PyChainMap {
            inner: self.inner.shift(amount).map_err(homotopy_error)?,
        })
    }

    #[pyo3(text_signature = "($self)")]
    fn mapping_cone(&self) -> PyResult<PyBoundedComplex> {
        Ok(PyBoundedComplex {
            inner: self.inner.mapping_cone().map_err(bounded_complex_error)?,
        })
    }

    #[pyo3(text_signature = "($self)")]
    fn is_null_homotopic(&self, py: Python<'_>) -> PyResult<bool> {
        py.allow_threads(|| self.inner.is_null_homotopic())
            .map_err(engine_error)
    }

    #[pyo3(text_signature = "($self, other, homotopy)")]
    fn homotopic_to(
        &self,
        py: Python<'_>,
        other: &PyChainMap,
        homotopy: &PyChainHomotopy,
    ) -> PyResult<bool> {
        py.allow_threads(|| self.inner.homotopic_to(&other.inner, &homotopy.inner))
            .map_err(homotopy_error)
    }

    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    #[pyo3(text_signature = "($self, other)")]
    fn agrees_with(&self, other: &PyChainMap) -> bool {
        self.inner.agrees_with(&other.inner)
    }

    fn __repr__(&self) -> String {
        format!(
            "ChainMap(degree_range={:?}, components={})",
            self.degree_range(),
            self.inner.components().len()
        )
    }
}

/// A degree-one component family `h_n: X_n -> Y_(n+1)`.
#[pyclass(name = "ChainHomotopy", module = "auslander", frozen)]
pub(crate) struct PyChainHomotopy {
    pub(crate) inner: ChainHomotopy,
}

#[pymethods]
impl PyChainHomotopy {
    #[new]
    #[pyo3(text_signature = "(source, target, components)")]
    fn new(
        source: &PyBoundedComplex,
        target: &PyBoundedComplex,
        components: Vec<PyRef<'_, PyMorphism>>,
    ) -> PyResult<PyChainHomotopy> {
        Ok(PyChainHomotopy {
            inner: ChainHomotopy::new(
                &source.inner,
                &target.inner,
                components
                    .iter()
                    .map(|component| component.inner.clone())
                    .collect(),
            )
            .map_err(homotopy_error)?,
        })
    }

    /// Builds and checks a homotopy from `left` to `right`.
    #[staticmethod]
    #[pyo3(text_signature = "(left, right, components)")]
    fn between(
        left: &PyChainMap,
        right: &PyChainMap,
        components: Vec<PyRef<'_, PyMorphism>>,
    ) -> PyResult<PyChainHomotopy> {
        Ok(PyChainHomotopy {
            inner: ChainHomotopy::between(
                &left.inner,
                &right.inner,
                components
                    .iter()
                    .map(|component| component.inner.clone())
                    .collect(),
            )
            .map_err(homotopy_error)?,
        })
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
    fn components(&self) -> Vec<PyMorphism> {
        wrap_all(self.inner.components())
    }

    #[pyo3(text_signature = "($self)")]
    fn boundary(&self) -> PyResult<PyChainMap> {
        Ok(PyChainMap {
            inner: self.inner.boundary().map_err(homotopy_error)?,
        })
    }

    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "ChainHomotopy(components={})",
            self.inner.components().len()
        )
    }
}

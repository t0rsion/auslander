use super::*;

/// Resource ceilings for automatic bounded projective replacement.

#[pyclass(name = "ReplacementLimits", module = "auslander", frozen)]
pub(crate) struct PyReplacementLimits {
    pub(crate) inner: ReplacementLimits,
}

#[pymethods]
impl PyReplacementLimits {
    #[new]
    #[pyo3(signature = (
        max_resolution_steps=16,
        max_complex_terms=4096,
        max_total_dimension=1_000_000,
        max_matrix_entries=16_000_000,
        max_work_units=20_000_000
    ))]
    fn new(
        max_resolution_steps: usize,
        max_complex_terms: usize,
        max_total_dimension: usize,
        max_matrix_entries: usize,
        max_work_units: usize,
    ) -> PyReplacementLimits {
        PyReplacementLimits {
            inner: ReplacementLimits {
                max_resolution_steps,
                max_complex_terms,
                max_total_dimension,
                max_matrix_entries,
                max_work_units,
            },
        }
    }
}

/// A bounded projective model with a checked quasi-isomorphism to its input.
#[pyclass(name = "PerfectReplacement", module = "auslander", frozen)]
pub(crate) struct PyPerfectReplacement {
    pub(crate) inner: RustPerfectReplacement,
}

#[pymethods]
impl PyPerfectReplacement {
    #[getter]
    fn original(&self) -> PyBoundedComplex {
        PyBoundedComplex {
            inner: self.inner.original().clone(),
        }
    }

    #[getter]
    fn projective(&self) -> PyBoundedComplex {
        PyBoundedComplex {
            inner: self.inner.projective().complex().clone(),
        }
    }

    #[getter]
    fn quasi_isomorphism(&self) -> PyChainMap {
        PyChainMap {
            inner: self.inner.quasi_isomorphism().map().clone(),
        }
    }

    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }
}

pub(crate) enum ReplacementBoundary {
    Cut(ReplacementCut),
    Cancelled(ReplacementCancellation),
}

/// A checked replacement prefix that did not unlock a projective model.
#[pyclass(name = "IncompletePerfectReplacement", module = "auslander", frozen)]
pub(crate) struct PyIncompletePerfectReplacement {
    pub(crate) inner: ReplacementBoundary,
}

#[pymethods]
impl PyIncompletePerfectReplacement {
    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner {
            ReplacementBoundary::Cut(_) => "cut",
            ReplacementBoundary::Cancelled(_) => "cancelled",
        }
    }

    #[getter]
    fn prefix_length(&self) -> usize {
        match &self.inner {
            ReplacementBoundary::Cut(value) => value.prefix().len(),
            ReplacementBoundary::Cancelled(value) => value.prefix().len(),
        }
    }

    #[getter]
    fn next_kernel(&self) -> Option<PyBoundedComplex> {
        match &self.inner {
            ReplacementBoundary::Cut(value) => value.next_kernel(),
            ReplacementBoundary::Cancelled(value) => value.next_kernel(),
        }
        .cloned()
        .map(|inner| PyBoundedComplex { inner })
    }

    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| match &self.inner {
            ReplacementBoundary::Cut(value) => value.verify(),
            ReplacementBoundary::Cancelled(value) => value.verify(),
        })
    }
}

/// Resource ceilings for finite graded derived Hom.
#[pyclass(name = "DerivedHomLimits", module = "auslander", frozen)]
pub(crate) struct PyDerivedHomLimits {
    pub(crate) inner: DerivedHomLimits,
}

#[pymethods]
impl PyDerivedHomLimits {
    #[new]
    #[pyo3(signature = (replacement=None, max_degrees=256, max_work_units=16_000_000))]
    fn new(
        replacement: Option<&PyReplacementLimits>,
        max_degrees: usize,
        max_work_units: usize,
    ) -> PyDerivedHomLimits {
        PyDerivedHomLimits {
            inner: DerivedHomLimits {
                replacement: replacement.map_or_else(ReplacementLimits::default, |v| v.inner),
                max_degrees,
                max_work_units,
            },
        }
    }
}

/// A complete finite graded derived Hom value.
#[pyclass(name = "DerivedHom", module = "auslander", frozen)]
pub(crate) struct PyDerivedHom {
    pub(crate) inner: RustDerivedHom,
}

#[pymethods]
impl PyDerivedHom {
    #[getter]
    fn support(&self) -> (i32, i32) {
        (self.inner.support().lower(), self.inner.support().upper())
    }

    #[getter]
    fn dimensions(&self) -> Vec<usize> {
        (self.inner.support().lower()..=self.inner.support().upper())
            .map(|degree| self.inner.dimension(degree))
            .collect()
    }

    fn dimension(&self, degree: i32) -> usize {
        self.inner.dimension(degree)
    }

    fn space(&self, degree: i32) -> Option<PyHomotopyHomQuotient> {
        self.inner
            .space(degree)
            .cloned()
            .map(|inner| PyHomotopyHomQuotient { inner })
    }

    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }
}

pub(crate) enum DerivedHomBoundary {
    ReplacementCut(ReplacementCut),
    ReplacementCancelled(ReplacementCancellation),
    WorkCut(DerivedHomCut),
    Cancelled(DerivedHomCancellation),
}

/// A typed checked prefix of an unfinished derived Hom computation.
#[pyclass(name = "IncompleteDerivedHom", module = "auslander", frozen)]
pub(crate) struct PyIncompleteDerivedHom {
    pub(crate) inner: DerivedHomBoundary,
}

#[pymethods]
impl PyIncompleteDerivedHom {
    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner {
            DerivedHomBoundary::ReplacementCut(_) => "replacement_cut",
            DerivedHomBoundary::ReplacementCancelled(_) => "replacement_cancelled",
            DerivedHomBoundary::WorkCut(_) => "work_cut",
            DerivedHomBoundary::Cancelled(_) => "cancelled",
        }
    }

    #[getter]
    fn next_degree(&self) -> Option<i32> {
        match &self.inner {
            DerivedHomBoundary::WorkCut(value) => Some(value.next_degree()),
            DerivedHomBoundary::Cancelled(value) => Some(value.next_degree()),
            _ => None,
        }
    }

    #[getter]
    fn dimensions(&self) -> Vec<usize> {
        match &self.inner {
            DerivedHomBoundary::WorkCut(value) => value
                .spaces()
                .iter()
                .map(HomotopyHomQuotient::dim)
                .collect(),
            DerivedHomBoundary::Cancelled(value) => value
                .spaces()
                .iter()
                .map(HomotopyHomQuotient::dim)
                .collect(),
            _ => Vec::new(),
        }
    }

    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| match &self.inner {
            DerivedHomBoundary::ReplacementCut(value) => value.verify(),
            DerivedHomBoundary::ReplacementCancelled(value) => value.verify(),
            DerivedHomBoundary::WorkCut(value) => value.verify(),
            DerivedHomBoundary::Cancelled(value) => value.verify(),
        })
    }
}

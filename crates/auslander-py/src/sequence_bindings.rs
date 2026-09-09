use super::*;

/// A retraction and a section proving a sequence split.
///
/// `retraction` is r: E -> N with inclusion followed by r the identity of N,
/// and `section` is s: M -> E with s followed by the projection the identity
/// of M. Both are Morphisms, so A-linearity holds by construction. Instances
/// are immutable and come only from `ShortExactSequence.split_status`.

#[pyclass(name = "SplitWitness", module = "auslander", frozen)]
pub(crate) struct PySplitWitness {
    pub(crate) inner: sequence::SplitWitness,
}

#[pymethods]
impl PySplitWitness {
    /// The retraction r: E -> N.
    #[getter]
    fn retraction(&self) -> PyMorphism {
        self.inner.retraction().into()
    }

    /// The section s: M -> E.
    #[getter]
    fn section(&self) -> PyMorphism {
        self.inner.section().into()
    }

    fn __repr__(&self) -> String {
        format!(
            "SplitWitness(middle_dims={:?}, sub_dims={:?})",
            self.inner.retraction().source().dim_vector(),
            self.inner.retraction().target().dim_vector()
        )
    }
}

/// A dual vector proving a sequence non-split.
///
/// The retraction system is a linear system in the entries of a candidate
/// retraction, built in a fixed equation order. `dual` is a vector y with
/// y A = 0 and y b = 1; the second identity pins its scale. Its existence
/// proves the system unsolvable by multiplication alone, so no retraction
/// exists. Instances are immutable and come only from
/// `ShortExactSequence.split_status`.
#[pyclass(name = "NonSplitWitness", module = "auslander", frozen)]
pub(crate) struct PyNonSplitWitness {
    pub(crate) inner: sequence::NonSplitWitness,
}

#[pymethods]
impl PyNonSplitWitness {
    /// The dual vector as canonical integers in 0..p, one entry per equation
    /// of the retraction system.
    #[getter]
    fn dual(&self) -> Vec<u64> {
        row_u64(self.inner.dual())
    }

    fn __repr__(&self) -> String {
        format!("NonSplitWitness(equations={})", self.inner.dual().len())
    }
}

/// A short exact sequence 0 -> sub -> middle -> quotient -> 0.
///
/// Exactness was checked at construction, per vertex: the inclusion is mono,
/// the projection is epi, the composite is zero, and the middle dimension is
/// the sum of the other two. Together these force image equals kernel, so
/// holding a ShortExactSequence is proof of exactness. Instances are
/// immutable and come from `ExtClass.extension`.
#[pyclass(name = "ShortExactSequence", module = "auslander", frozen)]
pub(crate) struct PyShortExactSequence {
    pub(crate) inner: sequence::ShortExactSequence,
}

#[pymethods]
impl PyShortExactSequence {
    /// The sub module N.
    #[getter]
    fn sub(&self) -> PyRightModule {
        self.inner.sub().into()
    }

    /// The middle module E.
    #[getter]
    fn middle(&self) -> PyRightModule {
        self.inner.middle().into()
    }

    /// The quotient module M.
    #[getter]
    fn quotient(&self) -> PyRightModule {
        self.inner.quotient().into()
    }

    /// The inclusion N -> E.
    #[getter]
    fn inclusion(&self) -> PyMorphism {
        self.inner.inclusion().into()
    }

    /// The projection E -> M.
    #[getter]
    fn projection(&self) -> PyMorphism {
        self.inner.projection().into()
    }

    /// The class of this extension in Ext^1(quotient, sub). The space is
    /// rebuilt for this call, so the class of an extension built from a class
    /// carries the same coordinates as the original.
    #[pyo3(text_signature = "($self)")]
    fn ext1_class(&self, py: Python<'_>) -> PyResult<PyExtClass> {
        let space = py
            .allow_threads(|| ext::ExtSpace::new(self.inner.quotient(), self.inner.sub(), 1))
            .map_err(value_error)?;
        Ok(PyExtClass {
            inner: py
                .allow_threads(|| self.inner.ext1_class(&space))
                .map_err(sequence_error)?,
        })
    }

    /// Whether the sequence splits, decided by solving the retraction system.
    /// Both answers carry a proof; see `split_status`.
    #[getter]
    fn is_split(&self) -> bool {
        matches!(self.inner.split_status(), SplitStatus::Split(_))
    }

    /// The proof behind `is_split`: a SplitWitness with a retraction and a
    /// section, or a NonSplitWitness with the dual vector of the unsolvable
    /// retraction system.
    #[getter]
    fn split_status<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        match self.inner.split_status() {
            SplitStatus::Split(inner) => Ok(Bound::new(py, PySplitWitness { inner })?.into_any()),
            SplitStatus::NonSplit(inner) => {
                Ok(Bound::new(py, PyNonSplitWitness { inner })?.into_any())
            }
        }
    }

    /// Rechecks the sequence: rebuilds it through the exactness checks and
    /// rechecks the split-status witness by multiplication.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| {
            if sequence::ShortExactSequence::new(
                self.inner.inclusion().clone(),
                self.inner.projection().clone(),
            )
            .is_err()
            {
                return false;
            }
            match self.inner.split_status() {
                SplitStatus::Split(w) => w.verify(&self.inner),
                SplitStatus::NonSplit(w) => w.verify(&self.inner),
            }
        })
    }

    fn __repr__(&self) -> String {
        format!(
            "ShortExactSequence(sub_dims={:?}, middle_dims={:?}, quotient_dims={:?})",
            self.inner.sub().dim_vector(),
            self.inner.middle().dim_vector(),
            self.inner.quotient().dim_vector()
        )
    }
}

use super::*;

/// An iterated syzygy with the minimal resolution prefix that proves it.

#[pyclass(name = "Syzygy", module = "auslander")]
pub(crate) struct PySyzygy {
    pub(crate) inner: Syzygy,
}

#[pymethods]
impl PySyzygy {
    /// The module whose syzygy was computed.
    #[getter]
    fn source(&self) -> PyRightModule {
        self.inner.source().into()
    }

    /// The exponent `n` in `Ω^n(source)`.
    #[getter]
    fn degree(&self) -> usize {
        self.inner.degree()
    }

    /// The module `Ω^n(source)`.
    #[getter]
    fn module(&self) -> PyRightModule {
        self.inner.module().into()
    }

    /// The minimal resolution prefix, or `None` for the zeroth syzygy.
    #[getter]
    fn resolution(&self) -> Option<PyResolution> {
        match self.inner.witness() {
            SyzygyWitness::Identity => None,
            SyzygyWitness::Resolution(resolution) => {
                Some(wrapped_resolution(self.inner.source(), resolution))
            }
        }
    }

    /// Recompute the syzygy and its witness.
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "Syzygy(degree={}, dims={:?})",
            self.inner.degree(),
            self.inner.module().dim_vector()
        )
    }
}

/// An iterated cosyzygy with the minimal coresolution prefix that proves it.
#[pyclass(name = "Cosyzygy", module = "auslander")]
pub(crate) struct PyCosyzygy {
    pub(crate) inner: Cosyzygy,
}

#[pymethods]
impl PyCosyzygy {
    /// The module whose cosyzygy was computed.
    #[getter]
    fn source(&self) -> PyRightModule {
        self.inner.source().into()
    }

    /// The exponent `n` in `Ω^(-n)(source)`.
    #[getter]
    fn degree(&self) -> usize {
        self.inner.degree()
    }

    /// The module `Ω^(-n)(source)`.
    #[getter]
    fn module(&self) -> PyRightModule {
        self.inner.module().into()
    }

    /// The minimal coresolution prefix, or `None` for the zeroth cosyzygy.
    #[getter]
    fn coresolution(&self) -> Option<PyInjectiveCoresolution> {
        match self.inner.witness() {
            CosyzygyWitness::Identity => None,
            CosyzygyWitness::Coresolution(coresolution) => Some(PyInjectiveCoresolution {
                inner: coresolution.clone(),
            }),
        }
    }

    /// Recompute the cosyzygy and its witness.
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "Cosyzygy(degree={}, dims={:?})",
            self.inner.degree(),
            self.inner.module().dim_vector()
        )
    }
}

/// How a computed resolution prefix ended: FINITE (reached zero) or CUT (step
/// budget ran out with the next syzygy nonzero).
#[pyclass(name = "ResolutionKind", module = "auslander", frozen, eq, hash)]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum PyResolutionKind {
    #[pyo3(name = "FINITE")]
    Finite,
    #[pyo3(name = "CUT")]
    Cut,
}

/// How a resolution prefix ended: kind FINITE with at = None means the
/// resolution reached zero; kind CUT with at = n means exactly n differentials
/// were computed and the (n+1)-st syzygy is nonzero, with nothing claimed
/// beyond it. The invariant kind == FINITE iff at is None is enforced at
/// construction, and instances are immutable.
#[pyclass(name = "ResolutionStatus", module = "auslander", frozen, eq, hash)]
#[derive(PartialEq, Eq, Hash)]
pub(crate) struct PyResolutionStatus {
    pub(crate) end: ResolutionEnd,
}

#[pymethods]
impl PyResolutionStatus {
    /// ResolutionStatus(kind, at=None); raises ValueError unless FINITE comes
    /// with at=None and CUT with an integer at.
    #[new]
    #[pyo3(signature = (kind, at = None), text_signature = "(kind, at=None)")]
    fn new(kind: PyResolutionKind, at: Option<usize>) -> PyResult<Self> {
        let end = match (kind, at) {
            (PyResolutionKind::Finite, None) => ResolutionEnd::Finite,
            (PyResolutionKind::Cut, Some(at)) => ResolutionEnd::Cut { at },
            (PyResolutionKind::Finite, Some(_)) => {
                return Err(PyValueError::new_err(
                    "ResolutionStatus: FINITE takes at=None",
                ));
            }
            (PyResolutionKind::Cut, None) => {
                return Err(PyValueError::new_err(
                    "ResolutionStatus: CUT needs an integer at",
                ));
            }
        };
        Ok(PyResolutionStatus { end })
    }

    /// ResolutionKind.FINITE or ResolutionKind.CUT.
    #[getter]
    fn kind(&self) -> PyResolutionKind {
        match self.end {
            ResolutionEnd::Finite => PyResolutionKind::Finite,
            ResolutionEnd::Cut { .. } => PyResolutionKind::Cut,
        }
    }

    /// The number of computed differentials for CUT; None for FINITE.
    #[getter]
    fn at(&self) -> Option<usize> {
        match self.end {
            ResolutionEnd::Finite => None,
            ResolutionEnd::Cut { at } => Some(at),
        }
    }

    fn __repr__(&self) -> String {
        match self.end {
            ResolutionEnd::Finite => "ResolutionStatus(ResolutionKind.FINITE)".to_string(),
            ResolutionEnd::Cut { at } => {
                format!("ResolutionStatus(ResolutionKind.CUT, at={at})")
            }
        }
    }
}

/// A minimal projective resolution prefix ... -> P_1 -> P_0 -> M -> 0.
///
/// `terms[k]` is P_k and `maps[k]` the differential from terms[k + 1] to
/// terms[k], so there is one map fewer than there are terms; `augmentation` is
/// the projective cover P_0 -> M. `status` says how the computed prefix ended;
/// see ResolutionStatus. Minimality: every differential lands in the radical
/// of its target. InjectiveCoresolution states the dual condition.
#[pyclass(name = "Resolution", module = "auslander")]
pub(crate) struct PyResolution {
    pub(crate) module: Module,
    pub(crate) inner: ProjectiveResolution,
}

#[pymethods]
impl PyResolution {
    /// The terms P_0, P_1, ... as Modules over the same algebra object as the
    /// resolved module.
    #[getter]
    fn terms(&self) -> Vec<PyRightModule> {
        wrap_all(&self.inner.terms)
    }

    /// Dimension vectors of the terms: terms_dims[k] is the dim vector of P_k.
    #[getter]
    fn terms_dims(&self) -> Vec<Vec<usize>> {
        dim_vectors(&self.inner.terms)
    }

    /// The differentials, maps[k] going from terms[k + 1] to terms[k].
    #[getter]
    fn maps(&self) -> Vec<PyMorphism> {
        wrap_all(&self.inner.maps)
    }

    /// The augmentation P_0 -> M, the projective cover of the resolved module.
    #[getter]
    fn augmentation(&self) -> PyMorphism {
        (&self.inner.augmentation).into()
    }

    /// How the prefix ended, as an immutable ResolutionStatus: kind FINITE (the
    /// resolution reached zero, so pd M = len(terms_dims) - 1 for nonzero M) or
    /// kind CUT with at = n (exactly n differentials computed, the (n+1)-st
    /// syzygy nonzero).
    #[getter]
    fn status(&self) -> PyResolutionStatus {
        PyResolutionStatus {
            end: self.inner.end,
        }
    }

    /// The projective dimension proved by this stored resolution prefix.
    #[getter]
    fn projective_dimension(&self) -> PyBounded {
        let inner = match self.inner.end {
            ResolutionEnd::Finite => Bounded::Exact(self.inner.terms.len() - 1),
            ResolutionEnd::Cut { at } => Bounded::AtLeast(at.saturating_add(1)),
        };
        PyBounded { inner }
    }

    /// The projective dimension of the resolved module, decided up to `bound`
    /// differentials: Exact(n) with n <= bound, or AtLeast(bound + 1): the
    /// resolution is minimal, so the lower bound is genuine.
    #[pyo3(text_signature = "($self, bound)")]
    fn pd(&self, py: Python<'_>, bound: usize) -> PyBounded {
        PyBounded {
            inner: py.allow_threads(|| projective_dimension(&self.module, bound)),
        }
    }

    fn __repr__(&self) -> String {
        format!(
            "Resolution(terms={}, status={})",
            self.inner.terms.len(),
            end_repr(self.inner.end)
        )
    }
}

/// A minimal injective coresolution prefix 0 -> M -> I^0 -> I^1 -> ...
///
/// `terms[k]` is I^k and `maps[k]` the differential d^k from I^k to I^{k+1}, so
/// there is one map fewer than there are terms; `coaugmentation` is the
/// injective envelope M -> I^0. `status` says how the computed prefix ended, in
/// the same ResolutionStatus shape a projective resolution reports. Minimality
/// is the dual of "differentials land in the radical": soc I^k lies in the
/// kernel of d^k at every step.
#[pyclass(name = "InjectiveCoresolution", module = "auslander")]
pub(crate) struct PyInjectiveCoresolution {
    pub(crate) inner: InjectiveCoresolution,
}

#[pymethods]
impl PyInjectiveCoresolution {
    /// The terms I^0, I^1, ... as Modules over the same algebra object as the
    /// coresolved module.
    #[getter]
    fn terms(&self) -> Vec<PyRightModule> {
        wrap_all(&self.inner.terms)
    }

    /// Dimension vectors of the terms: terms_dims[k] is the dim vector of I^k.
    #[getter]
    fn terms_dims(&self) -> Vec<Vec<usize>> {
        dim_vectors(&self.inner.terms)
    }

    /// The differentials, maps[k] going from terms[k] to terms[k + 1].
    #[getter]
    fn maps(&self) -> Vec<PyMorphism> {
        wrap_all(&self.inner.maps)
    }

    /// The coaugmentation M -> I^0, the injective envelope of the coresolved
    /// module.
    #[getter]
    fn coaugmentation(&self) -> PyMorphism {
        (&self.inner.coaugmentation).into()
    }

    /// How the prefix ended, as an immutable ResolutionStatus: kind FINITE (the
    /// coresolution reached zero, so id M = len(terms_dims) - 1 for nonzero M)
    /// or kind CUT with at = n (exactly n differentials computed, the (n+1)-st
    /// cosyzygy nonzero).
    #[getter]
    fn status(&self) -> PyResolutionStatus {
        PyResolutionStatus {
            end: self.inner.end,
        }
    }

    fn __repr__(&self) -> String {
        format!(
            "InjectiveCoresolution(terms={}, status={})",
            self.inner.terms.len(),
            end_repr(self.inner.end)
        )
    }
}

/// A homological invariant known exactly or bounded from below.
///
/// Exactly one of `exact` and `at_least` is set. AtLeast(n) asserts only that the
/// true value is >= n; it does not claim the value finite or infinite. There is no
/// "None means infinite" convention anywhere in this package.
///
/// Instances are immutable and hash by value, so a Bounded is a dict key or
/// set element.
#[pyclass(name = "Bounded", module = "auslander", frozen)]
pub(crate) struct PyBounded {
    pub(crate) inner: Bounded<usize>,
}

#[pymethods]
impl PyBounded {
    /// The exact value, or None when only a lower bound is known.
    #[getter]
    fn exact(&self) -> Option<usize> {
        match self.inner {
            Bounded::Exact(n) => Some(n),
            Bounded::AtLeast(_) => None,
        }
    }

    /// The genuine lower bound, or None when the value is known exactly.
    #[getter]
    fn at_least(&self) -> Option<usize> {
        match self.inner {
            Bounded::Exact(_) => None,
            Bounded::AtLeast(n) => Some(n),
        }
    }

    fn __repr__(&self) -> String {
        match self.inner {
            Bounded::Exact(n) => format!("Exact({n})"),
            Bounded::AtLeast(n) => format!("AtLeast({n})"),
        }
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        other
            .extract::<PyRef<'_, PyBounded>>()
            .is_ok_and(|o| o.inner == self.inner)
    }

    /// Hashes the variant and the value, matching `__eq__`. `Bounded` is not a
    /// Rust `Hash` type, so the tag is written here: Exact(n) and AtLeast(n)
    /// must not collide.
    fn __hash__(&self) -> u64 {
        let mut hasher = DefaultHasher::new();
        match self.inner {
            Bounded::Exact(n) => (0u8, n).hash(&mut hasher),
            Bounded::AtLeast(n) => (1u8, n).hash(&mut hasher),
        }
        hasher.finish()
    }
}

/// The global dimension of the algebra, decided up to `bound` differentials:
/// gldim A = max_v pd S_v. Returns Exact when every simple resolves within the
/// bound, AtLeast(bound + 1) otherwise.
#[pyfunction]
#[pyo3(text_signature = "(algebra, field, bound)")]
pub(crate) fn global_dimension(
    py: Python<'_>,
    algebra: &PyAlgebra,
    field: &PyPrimeField,
    bound: usize,
) -> PyResult<PyBounded> {
    let algebra = algebra.over(py, field.inner)?;
    Ok(PyBounded {
        inner: py.allow_threads(|| ext::global_dimension(&algebra, bound)),
    })
}

/// Every indecomposable right module of a Nakayama algebra, as
/// (Module, Certificate) pairs: the uniserial quotients P_i / rad^l P_i for
/// 1 <= l <= dim P_i, ordered by vertex then by length l, so the count is
/// dim_k A (the sum of the Kupisch series). Every certificate has kind
/// "indecomposable": it comes from the exact decomposition machinery, which
/// must certify a uniserial module. Raises ValueError when a vertex has more
/// than one incoming or outgoing arrow, i.e. the algebra is not Nakayama and
/// the list would not be exhaustive.
#[pyfunction]
#[pyo3(text_signature = "(algebra, field)")]
pub(crate) fn nakayama_indecomposables(
    py: Python<'_>,
    algebra: &PyAlgebra,
    field: &PyPrimeField,
) -> PyResult<Vec<(PyRightModule, PyCertificate)>> {
    let algebra = algebra.over(py, field.inner)?;
    Ok(py
        .allow_threads(|| enumerate::nakayama_indecomposables(&algebra))
        .map_err(value_error)?
        .into_iter()
        .map(|(m, c)| (m.into(), PyCertificate { inner: c }))
        .collect())
}

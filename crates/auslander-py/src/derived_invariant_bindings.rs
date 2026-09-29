use super::*;

use auslander::derived_classification::ClassificationLimits;
use auslander::derived_invariant::{
    DerivedInequivalenceWitness, DerivedInvariantKind, DerivedInvariants, InvariantLimits,
    InvariantReading, InvariantStop, InvariantValue, WitnessError, first_difference,
};

/// `InvariantLimits()`: the limits of the committed `F_2` study record.
fn default_limits() -> InvariantLimits {
    ClassificationLimits::with_walk_vertices(8).invariants
}

/// The Python name of every invariant kind, in table order.
pub(crate) fn invariant_kind_names() -> Vec<String> {
    DerivedInvariantKind::ALL.iter().map(variant_name).collect()
}

/// The kind with Python name `name`. Raises ValueError listing the names.
pub(crate) fn invariant_kind(name: &str) -> PyResult<DerivedInvariantKind> {
    DerivedInvariantKind::ALL
        .into_iter()
        .find(|kind| variant_name(kind) == name)
        .ok_or_else(|| {
            PyValueError::new_err(format!(
                "unknown invariant kind {name:?}; the kinds are {}",
                invariant_kind_names().join(", ")
            ))
        })
}

/// The Python form of one finished value: an `int`, a list of `int`, the
/// Avella-Alaminos-Geiss pairs as a list of `(n, m)` tuples, or the winding
/// class as a string such as `planar` or `gcd 2`.
pub(crate) fn invariant_value_object(py: Python<'_>, value: &InvariantValue) -> PyResult<PyObject> {
    match value {
        InvariantValue::Count(count) => count.into_py_any(py),
        InvariantValue::Integer(integer) => integer.into_py_any(py),
        InvariantValue::Factors(values) | InvariantValue::Polynomial(values) => {
            values.clone().into_py_any(py)
        }
        InvariantValue::AagFunction(function) => function.pairs().to_vec().into_py_any(py),
        InvariantValue::Dimensions(dimensions) => dimensions.clone().into_py_any(py),
        InvariantValue::WindingClass(class) => class.to_string().into_py_any(py),
        other => Err(DefectError::new_err(format!(
            "this binding has no Python form for {other:?}"
        ))),
    }
}

fn stop_reason(stop: &InvariantStop) -> String {
    match stop {
        InvariantStop::Overflow => "an intermediate integer left the i128 range".to_string(),
        InvariantStop::BarCut(diagnostics) => format!(
            "the bar computation hit {} during {}",
            bar_reason_name(diagnostics.reason),
            bar_stage_name(diagnostics.stage)
        ),
        InvariantStop::Cancelled => {
            "cancellation was requested before the bar computation started".to_string()
        }
        other => variant_name(other),
    }
}

/// Resource ceilings for the derived invariants of one algebra.
///
/// `hochschild_degree` is the last degree `d` of `dim HH^0, ..., dim HH^d`,
/// default 2. `bar` bounds that computation. The defaults are the limits of
/// the committed `F_2` study: `BarLimits(10000, 100000, 10000000,
/// 1000000000)`.
#[pyclass(name = "InvariantLimits", module = "auslander", frozen)]
#[derive(Clone, Copy)]
pub(crate) struct PyInvariantLimits {
    pub(crate) inner: InvariantLimits,
}

#[pymethods]
impl PyInvariantLimits {
    #[new]
    #[pyo3(signature = (hochschild_degree = None, bar = None))]
    fn new(hochschild_degree: Option<usize>, bar: Option<&PyBarLimits>) -> PyInvariantLimits {
        PyInvariantLimits {
            inner: InvariantLimits {
                hochschild_degree: hochschild_degree.unwrap_or(default_limits().hochschild_degree),
                bar: bar.map_or(default_limits().bar, |limits| limits.inner),
            },
        }
    }

    #[getter]
    fn hochschild_degree(&self) -> usize {
        self.inner.hochschild_degree
    }

    #[getter]
    fn bar(&self) -> PyBarLimits {
        PyBarLimits {
            inner: self.inner.bar,
        }
    }

    pub(crate) fn __repr__(&self) -> String {
        format!(
            "InvariantLimits(hochschild_degree={}, bar={})",
            self.inner.hochschild_degree,
            self.bar().__repr__()
        )
    }
}

/// The outcome of one derived invariant.
///
/// `status` is `finished`, `stopped`, or `not_applicable`. A finished
/// reading has a `value`. A stopped reading names its `stop`: `overflow`,
/// `bar_cut`, or `cancelled`. A `not_applicable` reading belongs to
/// `aag_function` and `winding_class` on a presentation that is not gentle;
/// more resources give the same reading. Only two finished values can
/// separate two algebras.
#[pyclass(name = "InvariantReading", module = "auslander", frozen)]
pub(crate) struct PyInvariantReading {
    kind: DerivedInvariantKind,
    inner: InvariantReading,
}

#[pymethods]
impl PyInvariantReading {
    /// The invariant kind, one of `DERIVED_INVARIANT_KINDS`.
    #[getter]
    fn kind(&self) -> String {
        variant_name(&self.kind)
    }

    #[getter]
    fn status(&self) -> &'static str {
        match self.inner {
            InvariantReading::Finished(_) => "finished",
            InvariantReading::Stopped(_) => "stopped",
            InvariantReading::NotApplicable(_) => "not_applicable",
        }
    }

    /// The finished value, or None when the reading did not finish.
    #[getter]
    fn value(&self, py: Python<'_>) -> PyResult<Option<PyObject>> {
        match &self.inner {
            InvariantReading::Finished(value) => invariant_value_object(py, value).map(Some),
            _ => Ok(None),
        }
    }

    /// The stop of a stopped reading, or None.
    #[getter]
    fn stop(&self) -> Option<String> {
        match &self.inner {
            InvariantReading::Stopped(stop) => Some(variant_name(stop)),
            _ => None,
        }
    }

    /// Why the reading has no value, or None for a finished reading.
    #[getter]
    fn reason(&self) -> Option<String> {
        match &self.inner {
            InvariantReading::Finished(_) => None,
            InvariantReading::Stopped(stop) => Some(stop_reason(stop)),
            InvariantReading::NotApplicable(error) => Some(error.to_string()),
        }
    }

    /// The bar diagnostics of a `bar_cut` stop, or None.
    #[getter]
    fn bar_diagnostics(&self) -> Option<PyBarBudgetDiagnostics> {
        match &self.inner {
            InvariantReading::Stopped(InvariantStop::BarCut(diagnostics)) => {
                Some(PyBarBudgetDiagnostics {
                    inner: (**diagnostics).clone(),
                })
            }
            _ => None,
        }
    }

    /// Whether both readings finished and their values differ. Raises
    /// ValueError when the kinds differ.
    fn separates(&self, other: &PyInvariantReading) -> PyResult<bool> {
        if self.kind != other.kind {
            return Err(PyValueError::new_err(format!(
                "cannot compare a {} reading with a {} reading",
                self.kind(),
                other.kind()
            )));
        }
        Ok(self.inner.separates(&other.inner))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        let detail = match (self.value(py)?, self.stop()) {
            (Some(value), _) => format!("value={}", value.bind(py).repr()?),
            (None, Some(stop)) => format!("stop={stop:?}"),
            (None, None) => format!("reason={:?}", self.reason().unwrap_or_default()),
        };
        Ok(format!(
            "InvariantReading(kind={:?}, status={:?}, {detail})",
            self.kind(),
            self.status()
        ))
    }
}

/// Every derived invariant of one algebra, in `DERIVED_INVARIANT_KINDS`
/// order.
///
/// Each invariant is a necessary condition for derived equivalence. Equal
/// values never merge two algebras. `first_difference` names the first kind
/// whose two finished values differ, which proves that two algebras are not
/// derived equivalent. See `DerivedInequivalenceWitness`.
#[pyclass(name = "DerivedInvariants", module = "auslander", frozen)]
pub(crate) struct PyDerivedInvariants {
    pub(crate) inner: DerivedInvariants,
}

#[pymethods]
impl PyDerivedInvariants {
    /// The algebra these invariants describe.
    #[getter]
    fn algebra(&self) -> PyAlgebra {
        PyAlgebra::pinned(self.inner.algebra().clone())
    }

    #[getter]
    fn limits(&self) -> PyInvariantLimits {
        PyInvariantLimits {
            inner: self.inner.limits(),
        }
    }

    /// One reading per kind, in table order.
    #[getter]
    fn readings(&self) -> Vec<PyInvariantReading> {
        DerivedInvariantKind::ALL
            .into_iter()
            .map(|kind| self.reading_of(kind))
            .collect()
    }

    /// The reading of the kind named `kind`.
    fn reading(&self, kind: &str) -> PyResult<PyInvariantReading> {
        Ok(self.reading_of(invariant_kind(kind)?))
    }

    fn __getitem__(&self, kind: &str) -> PyResult<PyInvariantReading> {
        self.reading(kind)
    }

    fn __len__(&self) -> usize {
        DerivedInvariantKind::ALL.len()
    }

    /// The first kind in table order whose readings both finished and
    /// differ, or None when every pair of finished readings agrees.
    ///
    /// None does not certify a derived equivalence. The fields are not
    /// compared here; `DerivedInequivalenceWitness` compares them.
    fn first_difference(&self, other: &PyDerivedInvariants) -> Option<String> {
        first_difference(&self.inner, &other.inner).map(|kind| variant_name(&kind))
    }

    fn __repr__(slf: &Bound<'_, Self>) -> PyResult<String> {
        python_helper(slf.as_any(), "display", "show")?
            .getattr("text")?
            .extract()
    }

    fn _repr_html_(slf: &Bound<'_, Self>) -> PyResult<String> {
        python_helper(slf.as_any(), "display", "show")?
            .getattr("html")?
            .extract()
    }
}

impl PyDerivedInvariants {
    fn reading_of(&self, kind: DerivedInvariantKind) -> PyInvariantReading {
        PyInvariantReading {
            kind,
            inner: self.inner.reading(kind).clone(),
        }
    }
}

/// Two algebras over one field and one derived invariant whose finished
/// values differ. The difference proves that the algebras are not derived
/// equivalent.
///
/// `DerivedInequivalenceWitness(left, right, kind=None)` takes two
/// `DerivedInvariants` records computed under equal limits. With
/// `kind=None` it uses `left.first_difference(right)`. Raises ValueError when
/// the fields or limits differ, or when the kind does not separate the
/// records. `verify()` recomputes both values from scratch.
#[pyclass(name = "DerivedInequivalenceWitness", module = "auslander", frozen)]
pub(crate) struct PyDerivedInequivalenceWitness {
    pub(crate) inner: DerivedInequivalenceWitness,
}

#[pymethods]
impl PyDerivedInequivalenceWitness {
    #[new]
    #[pyo3(signature = (left, right, kind = None))]
    fn new(
        left: &PyDerivedInvariants,
        right: &PyDerivedInvariants,
        kind: Option<&str>,
    ) -> PyResult<PyDerivedInequivalenceWitness> {
        let kind = match kind {
            Some(name) => invariant_kind(name)?,
            None => first_difference(&left.inner, &right.inner).ok_or_else(|| {
                PyValueError::new_err("no finished invariant separates the two records")
            })?,
        };
        DerivedInequivalenceWitness::new(&left.inner, &right.inner, kind)
            .map(|inner| PyDerivedInequivalenceWitness { inner })
            .map_err(witness_error)
    }

    #[getter]
    fn left(&self) -> PyAlgebra {
        PyAlgebra::pinned(self.inner.left().clone())
    }

    #[getter]
    fn right(&self) -> PyAlgebra {
        PyAlgebra::pinned(self.inner.right().clone())
    }

    /// The separating invariant kind.
    #[getter]
    fn kind(&self) -> String {
        variant_name(&self.inner.kind())
    }

    #[getter]
    fn left_value(&self, py: Python<'_>) -> PyResult<PyObject> {
        invariant_value_object(py, self.inner.left_value())
    }

    #[getter]
    fn right_value(&self, py: Python<'_>) -> PyResult<PyObject> {
        invariant_value_object(py, self.inner.right_value())
    }

    /// The limits under which both values finished.
    #[getter]
    fn limits(&self) -> PyInvariantLimits {
        PyInvariantLimits {
            inner: self.inner.limits(),
        }
    }

    /// Recomputes the invariant of both algebras. True only when both values
    /// finish, equal the stored values, and differ.
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!(
            "DerivedInequivalenceWitness(kind={:?}, left_value={}, right_value={})",
            self.kind(),
            self.left_value(py)?.bind(py).repr()?,
            self.right_value(py)?.bind(py).repr()?
        ))
    }
}

/// A rejected witness as ValueError, with the kind in its Python spelling.
fn witness_error(error: WitnessError) -> PyErr {
    match error {
        WitnessError::NoDifference(kind) => PyValueError::new_err(format!(
            "the invariant {} does not separate the two records",
            variant_name(&kind)
        )),
        other => value_error(other),
    }
}

pub(crate) fn invariant_limits(limits: Option<&PyInvariantLimits>) -> InvariantLimits {
    limits.map_or_else(default_limits, |limits| limits.inner)
}

pub(crate) fn control_of(control: Option<&PyComputationControl>) -> ComputationControl {
    control.map_or_else(ComputationControl::new, |value| value.inner.clone())
}

#[pymethods]
impl PyAlgebra {
    /// Computes every derived invariant of this algebra.
    ///
    /// `limits` defaults to `InvariantLimits()`. Cancellation through
    /// `control` is checked once, before the bar computation. The Cartan
    /// invariants always finish or stop on `overflow`. Field-free
    /// presentations need `field`.
    #[pyo3(signature = (limits = None, control = None, field = None))]
    fn derived_invariants(
        &self,
        py: Python<'_>,
        limits: Option<&PyInvariantLimits>,
        control: Option<&PyComputationControl>,
        field: Option<&PyPrimeField>,
    ) -> PyResult<PyDerivedInvariants> {
        let algebra = self.algebra_for(py, field, "derived invariants")?;
        let (limits, control) = (invariant_limits(limits), control_of(control));
        py.allow_threads(|| DerivedInvariants::compute(&algebra, limits, &control))
            .map(|inner| PyDerivedInvariants { inner })
            .map_err(hochschild_error)
    }
}

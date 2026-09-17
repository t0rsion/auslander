use std::sync::Arc;

use auslander::arquiver::CatalogError;
use auslander::higher::{
    HigherExtPair, HigherOrthogonality, HigherOrthogonalityError, HigherOrthogonalityLimits,
    HigherOrthogonalityWork,
};

use super::*;

/// The classification name used by a complete catalog.
pub(crate) fn provenance_name(provenance: CatalogProvenance) -> &'static str {
    match provenance {
        CatalogProvenance::Nakayama => "nakayama",
        CatalogProvenance::DynkinZeroIdeal => "dynkin_zero_ideal",
        CatalogProvenance::GentleTree => "gentle_tree",
    }
}

fn wrapped_catalog(inner: IndecomposableCatalog) -> PyIndecomposableCatalog {
    PyIndecomposableCatalog {
        inner: Arc::new(inner),
    }
}

fn build_catalog(
    py: Python<'_>,
    algebra: &PyAlgebra,
    field: Option<&PyPrimeField>,
    route: &str,
) -> PyResult<Arc<Algebra>> {
    algebra.algebra_for(py, field, route)
}

fn catalog_error(error: CatalogError) -> PyErr {
    match error {
        CatalogError::UnsupportedDomain { .. } => {
            UnsupportedDomainError::new_err(error.to_string())
        }
    }
}

#[pymethods]
impl PyAlgebra {
    /// Builds a complete indecomposable catalog through the first supported route.
    #[pyo3(signature = (field = None), text_signature = "($self, field=None)")]
    fn catalog(
        &self,
        py: Python<'_>,
        field: Option<&PyPrimeField>,
    ) -> PyResult<PyIndecomposableCatalog> {
        auto_catalog(py, self, field)
    }
}

/// A complete list of the indecomposable modules of one verified algebra.
///
/// Entries are immutable certified modules in catalog order. The index of an
/// entry is its stable identifier. Construction needs an exhaustive
/// classification route, so unsupported algebras raise `UnsupportedDomainError`
/// from `auto` and the module-level `catalog` function.
#[pyclass(name = "IndecomposableCatalog", module = "auslander", frozen)]
pub(crate) struct PyIndecomposableCatalog {
    pub(crate) inner: Arc<IndecomposableCatalog>,
}

impl PyIndecomposableCatalog {
    fn dynkin_impl(
        py: Python<'_>,
        algebra: &PyAlgebra,
        field: Option<&PyPrimeField>,
    ) -> PyResult<Self> {
        let algebra = build_catalog(py, algebra, field, "a Dynkin catalog")?;
        py.allow_threads(|| IndecomposableCatalog::dynkin(&algebra))
            .map(wrapped_catalog)
            .map_err(dynkin_error)
    }

    fn nakayama_impl(
        py: Python<'_>,
        algebra: &PyAlgebra,
        field: Option<&PyPrimeField>,
    ) -> PyResult<Self> {
        let algebra = build_catalog(py, algebra, field, "a Nakayama catalog")?;
        py.allow_threads(|| IndecomposableCatalog::nakayama(&algebra))
            .map(wrapped_catalog)
            .map_err(value_error)
    }

    fn auto_impl(
        py: Python<'_>,
        algebra: &PyAlgebra,
        field: Option<&PyPrimeField>,
    ) -> PyResult<Self> {
        let algebra = build_catalog(py, algebra, field, "a catalog")?;
        py.allow_threads(|| IndecomposableCatalog::complete(&algebra))
            .map(wrapped_catalog)
            .map_err(catalog_error)
    }

    fn gentle_tree_impl(
        py: Python<'_>,
        algebra: &PyAlgebra,
        field: Option<&PyPrimeField>,
    ) -> PyResult<Self> {
        let algebra = build_catalog(py, algebra, field, "a gentle-tree catalog")?;
        py.allow_threads(|| IndecomposableCatalog::gentle_tree(&algebra))
            .map(wrapped_catalog)
            .map_err(value_error)
    }
}

/// Builds an automatic catalog for an `Algebra` binding method.
pub(crate) fn auto_catalog(
    py: Python<'_>,
    algebra: &PyAlgebra,
    field: Option<&PyPrimeField>,
) -> PyResult<PyIndecomposableCatalog> {
    PyIndecomposableCatalog::auto_impl(py, algebra, field)
}

#[pymethods]
impl PyIndecomposableCatalog {
    /// Builds a catalog through the first supported complete route.
    #[staticmethod]
    #[pyo3(signature = (algebra, field = None))]
    fn auto(py: Python<'_>, algebra: &PyAlgebra, field: Option<&PyPrimeField>) -> PyResult<Self> {
        Self::auto_impl(py, algebra, field)
    }

    /// Builds a catalog through Gabriel's Dynkin classification.
    #[staticmethod]
    #[pyo3(signature = (algebra, field = None))]
    fn dynkin(py: Python<'_>, algebra: &PyAlgebra, field: Option<&PyPrimeField>) -> PyResult<Self> {
        Self::dynkin_impl(py, algebra, field)
    }

    /// Builds a catalog through the Nakayama classification.
    #[staticmethod]
    #[pyo3(signature = (algebra, field = None))]
    fn nakayama(
        py: Python<'_>,
        algebra: &PyAlgebra,
        field: Option<&PyPrimeField>,
    ) -> PyResult<Self> {
        Self::nakayama_impl(py, algebra, field)
    }

    /// Builds a catalog through the gentle-tree string classification.
    #[staticmethod]
    #[pyo3(signature = (algebra, field = None))]
    fn gentle_tree(
        py: Python<'_>,
        algebra: &PyAlgebra,
        field: Option<&PyPrimeField>,
    ) -> PyResult<Self> {
        Self::gentle_tree_impl(py, algebra, field)
    }

    /// Computes higher Ext orthogonals over this catalog.
    #[pyo3(signature = (chosen, max_degree, limits = None))]
    fn higher_orthogonality(
        &self,
        py: Python<'_>,
        chosen: Vec<usize>,
        max_degree: usize,
        limits: Option<&PyHigherOrthogonalityLimits>,
    ) -> PyResult<PyHigherOrthogonality> {
        compute_higher(py, self, chosen, max_degree, limits)
    }

    /// Builds the valued Auslander-Reiten quiver from this catalog.
    #[pyo3(text_signature = "($self)")]
    fn ar_quiver(&self, py: Python<'_>) -> PyResult<PyArQuiver> {
        py.allow_threads(|| auslander::arquiver::ar_quiver_from_catalog(&self.inner))
            .map(|inner| PyArQuiver {
                inner: Arc::new(inner),
            })
            .map_err(ar_quiver_error)
    }

    /// The certified modules in catalog order.
    #[getter]
    fn entries(&self) -> Vec<PyRightModule> {
        self.inner
            .entries()
            .iter()
            .map(|entry| entry.module().into())
            .collect()
    }

    /// The classification theorem that makes the entries complete.
    #[getter]
    fn provenance(&self) -> &'static str {
        provenance_name(self.inner.provenance())
    }

    /// The prime field of the runtime algebra represented by this catalog.
    #[getter]
    fn field(&self) -> PyPrimeField {
        PyPrimeField {
            inner: self.inner.algebra().field(),
        }
    }

    /// The number of indecomposable entries.
    fn __len__(&self) -> usize {
        self.inner.len()
    }

    /// Returns one certified module by catalog index.
    fn __getitem__(&self, index: usize) -> PyResult<PyRightModule> {
        self.inner
            .entries()
            .get(index)
            .map(|entry| entry.module().into())
            .ok_or_else(|| {
                pyo3::exceptions::PyIndexError::new_err(format!(
                    "catalog index {index} out of range for {} entries",
                    self.inner.len()
                ))
            })
    }

    fn __repr__(&self) -> String {
        format!(
            "IndecomposableCatalog(len={}, provenance={:?}, field=F_{})",
            self.inner.len(),
            self.provenance(),
            self.inner.algebra().field().modulus()
        )
    }
}

/// Builds a complete indecomposable catalog through the first supported route.
///
/// A field is required for a field-free monomial presentation. A
/// general-relation algebra carries its field, so `field` may be omitted.
#[pyfunction]
#[pyo3(signature = (algebra, field = None))]
pub(crate) fn catalog(
    py: Python<'_>,
    algebra: &PyAlgebra,
    field: Option<&PyPrimeField>,
) -> PyResult<PyIndecomposableCatalog> {
    auto_catalog(py, algebra, field)
}

/// Resource limits for one higher-orthogonality table.
#[pyclass(name = "HigherOrthogonalityLimits", module = "auslander", frozen)]
#[derive(Clone, Copy)]
pub(crate) struct PyHigherOrthogonalityLimits {
    pub(crate) inner: HigherOrthogonalityLimits,
}

#[pymethods]
impl PyHigherOrthogonalityLimits {
    /// `HigherOrthogonalityLimits(max_pairs=None, max_ext_cells=None)`.
    #[new]
    #[pyo3(signature = (max_pairs = None, max_ext_cells = None))]
    fn new(max_pairs: Option<usize>, max_ext_cells: Option<usize>) -> Self {
        let defaults = HigherOrthogonalityLimits::default();
        Self {
            inner: HigherOrthogonalityLimits {
                max_pairs: max_pairs.unwrap_or(defaults.max_pairs),
                max_ext_cells: max_ext_cells.unwrap_or(defaults.max_ext_cells),
            },
        }
    }

    /// Maximum number of distinct ordered source and target pairs.
    #[getter]
    fn max_pairs(&self) -> usize {
        self.inner.max_pairs
    }

    /// Maximum number of stored positive-degree Ext dimensions.
    #[getter]
    fn max_ext_cells(&self) -> usize {
        self.inner.max_ext_cells
    }

    fn __repr__(&self) -> String {
        format!(
            "HigherOrthogonalityLimits(max_pairs={}, max_ext_cells={})",
            self.inner.max_pairs, self.inner.max_ext_cells
        )
    }
}

/// Positive-degree Ext dimensions for one ordered pair of catalog entries.
#[pyclass(name = "HigherExtPair", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyHigherExtPair {
    pub(crate) inner: HigherExtPair,
}

#[pymethods]
impl PyHigherExtPair {
    /// The source catalog index.
    #[getter]
    fn source(&self) -> usize {
        self.inner.source()
    }

    /// The target catalog index.
    #[getter]
    fn target(&self) -> usize {
        self.inner.target()
    }

    /// Dimensions in degrees one through the inclusive orthogonality bound.
    #[getter]
    fn dimensions(&self) -> Vec<usize> {
        self.inner.dimensions().to_vec()
    }

    /// Alias for `dimensions`, named like `HomologicalPair.ext_dimensions`.
    #[getter]
    fn ext_dimensions(&self) -> Vec<usize> {
        self.dimensions()
    }

    /// Whether every stored positive-degree Ext group vanishes.
    #[getter]
    fn vanishes(&self) -> bool {
        self.inner.vanishes()
    }

    fn __repr__(&self) -> String {
        format!(
            "HigherExtPair(source={}, target={}, dimensions={:?})",
            self.inner.source(),
            self.inner.target(),
            self.inner.dimensions()
        )
    }
}

/// Exact operation counts for one higher-orthogonality computation.
#[pyclass(name = "HigherOrthogonalityWork", module = "auslander", frozen)]
#[derive(Clone, Copy)]
pub(crate) struct PyHigherOrthogonalityWork {
    pub(crate) inner: HigherOrthogonalityWork,
}

#[pymethods]
impl PyHigherOrthogonalityWork {
    /// Number of distinct source resolutions.
    #[getter]
    fn resolutions(&self) -> usize {
        self.inner.resolutions
    }

    /// Number of Ext tables computed from those resolutions.
    #[getter]
    fn ext_tables(&self) -> usize {
        self.inner.ext_tables
    }

    fn __repr__(&self) -> String {
        format!(
            "HigherOrthogonalityWork(resolutions={}, ext_tables={})",
            self.inner.resolutions, self.inner.ext_tables
        )
    }
}

fn higher_error(error: HigherOrthogonalityError) -> PyErr {
    let message = error.to_string();
    match error {
        HigherOrthogonalityError::DegreeOverflow { degree } => {
            attach(PyOverflowError::new_err(message), |value| {
                value.setattr("degree", degree)
            })
        }
        HigherOrthogonalityError::PairLimit { requested, limit }
        | HigherOrthogonalityError::ExtCellLimit { requested, limit } => {
            attach(BudgetExhaustedError::new_err(message), |value| {
                value.setattr("requested", requested)?;
                value.setattr("limit", limit)
            })
        }
        HigherOrthogonalityError::IndexOutOfRange {
            position,
            index,
            catalog,
        } => attach(PyValueError::new_err(message), |value| {
            value.setattr("position", position)?;
            value.setattr("index", index)?;
            value.setattr("catalog", catalog)
        }),
        HigherOrthogonalityError::DuplicateIndex {
            index,
            first,
            second,
        } => attach(PyValueError::new_err(message), |value| {
            value.setattr("index", index)?;
            value.setattr("first", first)?;
            value.setattr("second", second)
        }),
        HigherOrthogonalityError::ZeroDegree => PyValueError::new_err(message),
    }
}

fn compute_higher(
    py: Python<'_>,
    catalog: &PyIndecomposableCatalog,
    chosen: Vec<usize>,
    max_degree: usize,
    limits: Option<&PyHigherOrthogonalityLimits>,
) -> PyResult<PyHigherOrthogonality> {
    let limits = limits.map_or_else(HigherOrthogonalityLimits::default, |value| value.inner);
    let inner = py
        .allow_threads(|| HigherOrthogonality::compute(&catalog.inner, &chosen, max_degree, limits))
        .map_err(higher_error)?;
    Ok(PyHigherOrthogonality { inner })
}

/// Higher Ext orthogonality over a complete indecomposable catalog.
#[pyclass(name = "HigherOrthogonality", module = "auslander", frozen)]
pub(crate) struct PyHigherOrthogonality {
    pub(crate) inner: HigherOrthogonality,
}

#[pymethods]
impl PyHigherOrthogonality {
    /// Computes both orthogonals through the inclusive positive degree bound.
    #[staticmethod]
    #[pyo3(signature = (catalog, chosen, max_degree, limits = None))]
    fn compute(
        py: Python<'_>,
        catalog: &PyIndecomposableCatalog,
        chosen: Vec<usize>,
        max_degree: usize,
        limits: Option<&PyHigherOrthogonalityLimits>,
    ) -> PyResult<Self> {
        compute_higher(py, catalog, chosen, max_degree, limits)
    }

    /// The catalog provenance that supports the completeness claim.
    #[getter]
    fn provenance(&self) -> &'static str {
        provenance_name(self.inner.provenance())
    }

    /// The selected catalog indices, sorted increasingly.
    #[getter]
    fn chosen(&self) -> Vec<usize> {
        self.inner.chosen().to_vec()
    }

    /// The inclusive positive Ext degree bound.
    #[getter]
    fn max_degree(&self) -> usize {
        self.inner.max_degree()
    }

    /// Stored Ext rows in source-major order.
    #[getter]
    fn pairs(&self) -> Vec<PyHigherExtPair> {
        self.inner
            .pairs()
            .iter()
            .cloned()
            .map(|inner| PyHigherExtPair { inner })
            .collect()
    }

    /// Catalog indices orthogonal on the left to every selected entry.
    #[getter]
    fn left(&self) -> Vec<usize> {
        self.inner.left().to_vec()
    }

    /// Catalog indices orthogonal on the right to every selected entry.
    #[getter]
    fn right(&self) -> Vec<usize> {
        self.inner.right().to_vec()
    }

    /// Whether all positive-degree Ext groups between selected entries vanish.
    #[getter]
    fn is_rigid(&self) -> bool {
        self.inner.is_rigid()
    }

    /// Whether both orthogonals equal the selected index set.
    #[getter]
    fn is_two_sided_maximal(&self) -> bool {
        self.inner.is_two_sided_maximal()
    }

    /// Exact operation counts for this table.
    #[getter]
    fn work(&self) -> PyHigherOrthogonalityWork {
        PyHigherOrthogonalityWork {
            inner: self.inner.work(),
        }
    }

    /// Recomputes this result over the supplied catalog.
    #[pyo3(text_signature = "($self, catalog)")]
    fn verify(&self, py: Python<'_>, catalog: &PyIndecomposableCatalog) -> bool {
        py.allow_threads(|| self.inner.verify(&catalog.inner))
    }

    fn __repr__(&self) -> String {
        format!(
            "HigherOrthogonality(chosen={:?}, max_degree={}, left={}, right={}, is_rigid={})",
            self.inner.chosen(),
            self.inner.max_degree(),
            self.inner.left().len(),
            self.inner.right().len(),
            self.inner.is_rigid()
        )
    }
}

/// Computes higher Ext orthogonals over a supplied complete catalog.
#[pyfunction]
#[pyo3(signature = (catalog, chosen, max_degree, limits = None))]
pub(crate) fn higher_orthogonality(
    py: Python<'_>,
    catalog: &PyIndecomposableCatalog,
    chosen: Vec<usize>,
    max_degree: usize,
    limits: Option<&PyHigherOrthogonalityLimits>,
) -> PyResult<PyHigherOrthogonality> {
    compute_higher(py, catalog, chosen, max_degree, limits)
}

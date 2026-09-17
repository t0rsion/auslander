use std::sync::Arc;

use auslander::atlas::{
    AtlasMaterializeError, AtlasScoreError, CatalogAtlas, CatalogAtlasError, CatalogAtlasLimits,
    CatalogAtlasWork, CatalogExtRow, CatalogExtTable, MultiplicityComplete, MultiplicityCut,
    MultiplicityCutReason, MultiplicityError, MultiplicityLimits, MultiplicityOutcome,
};
use auslander::atlas_artifact::{CatalogAtlasArtifact, CatalogAtlasArtifactError};

use super::*;

mod artifact;
mod limits;
mod results;
mod rows;

pub(crate) use artifact::*;
pub(crate) use limits::*;
pub(crate) use results::*;
pub(crate) use rows::*;

/// A cached ordered Ext table for one complete indecomposable catalog.
#[pyclass(name = "CatalogAtlas", module = "auslander", frozen)]
pub(crate) struct PyCatalogAtlas {
    pub(crate) inner: Arc<CatalogAtlas>,
}

impl PyCatalogAtlas {
    pub(crate) fn new(inner: CatalogAtlas) -> Self {
        Self {
            inner: Arc::new(inner),
        }
    }

    pub(crate) fn result(
        &self,
        dimensions: Vec<usize>,
        outcome: MultiplicityOutcome,
        limits: MultiplicityLimits,
    ) -> PyMultiplicityResult {
        PyMultiplicityResult::new(self.inner.clone(), dimensions, outcome, limits)
    }
}

fn atlas_error(error: CatalogAtlasError) -> PyErr {
    let message = error.to_string();
    match error {
        CatalogAtlasError::DegreeOverflow { degree } => {
            attach(PyOverflowError::new_err(message), |value| {
                value.setattr("degree", degree)
            })
        }
        CatalogAtlasError::PairCountOverflow { catalog_len }
        | CatalogAtlasError::ExtCellCountOverflow {
            pairs: catalog_len,
            degrees: _,
        }
        | CatalogAtlasError::ResolutionCountOverflow {
            sources: catalog_len,
            terms_per_source: _,
        } => attach(PyOverflowError::new_err(message), |value| {
            value.setattr("catalog_len", catalog_len)
        }),
        CatalogAtlasError::ResolutionTermOverflow { terms_per_source } => {
            attach(PyOverflowError::new_err(message), |value| {
                value.setattr("terms_per_source", terms_per_source)
            })
        }
        CatalogAtlasError::PairLimit { requested, limit }
        | CatalogAtlasError::ExtCellLimit { requested, limit }
        | CatalogAtlasError::ResolutionTermLimit { requested, limit } => {
            attach(BudgetExhaustedError::new_err(message), |value| {
                value.setattr("requested", requested)?;
                value.setattr("limit", limit)
            })
        }
    }
}

fn multiplicity_error(error: MultiplicityError) -> PyErr {
    match error {
        MultiplicityError::DimensionVectorLength { .. } => value_error(error),
        MultiplicityError::NodeCountOverflow => PyOverflowError::new_err(error.to_string()),
        MultiplicityError::NodeStackAllocationFailed { .. } => {
            DefectError::new_err(error.to_string())
        }
    }
}

fn score_error(error: AtlasScoreError) -> PyErr {
    match error {
        AtlasScoreError::ProductOverflow { .. } | AtlasScoreError::SumOverflow { .. } => {
            PyOverflowError::new_err(error.to_string())
        }
        AtlasScoreError::MultiplicityLength { .. }
        | AtlasScoreError::DegreeRange { .. }
        | AtlasScoreError::DegreeOutsideAtlas { .. } => value_error(error),
    }
}

fn materialize_error(error: AtlasMaterializeError) -> PyErr {
    let message = error.to_string();
    match error {
        AtlasMaterializeError::MultiplicityLength { .. } => PyValueError::new_err(message),
        AtlasMaterializeError::SummandLimit { requested, limit } => {
            attach(BudgetExhaustedError::new_err(message), |value| {
                value.setattr("requested", requested)?;
                value.setattr("limit", limit)
            })
        }
        AtlasMaterializeError::SummandCountOverflow
        | AtlasMaterializeError::DimensionProductOverflow { .. }
        | AtlasMaterializeError::DimensionSumOverflow { .. }
        | AtlasMaterializeError::TotalDimensionOverflow
        | AtlasMaterializeError::CellProductOverflow { .. }
        | AtlasMaterializeError::CellCountOverflow => PyOverflowError::new_err(message),
        AtlasMaterializeError::CellLimit { requested, limit } => {
            attach(BudgetExhaustedError::new_err(message), |value| {
                value.setattr("requested", requested)?;
                value.setattr("limit", limit)
            })
        }
        AtlasMaterializeError::AllocationFailed { .. } => DefectError::new_err(message),
    }
}

fn artifact_error(error: CatalogAtlasArtifactError) -> PyErr {
    let message = error.to_string();
    match error {
        CatalogAtlasArtifactError::ParseLimit { path, used, limit } => {
            attach(BudgetExhaustedError::new_err(message.clone()), |value| {
                value.setattr("path", path)?;
                value.setattr("used", used)?;
                value.setattr("limit", limit)
            })
        }
        CatalogAtlasArtifactError::Overflow { field } => {
            attach(PyOverflowError::new_err(message.clone()), |value| {
                value.setattr("field", field)
            })
        }
        CatalogAtlasArtifactError::VerificationLimit {
            field,
            declared,
            limit,
        } => attach(BudgetExhaustedError::new_err(message), |value| {
            value.setattr("field", field)?;
            value.setattr("declared", declared)?;
            value.setattr("limit", limit)
        }),
        CatalogAtlasArtifactError::Atlas(error) => atlas_error(error),
        CatalogAtlasArtifactError::Multiplicity(error) => multiplicity_error(error),
        CatalogAtlasArtifactError::Score(error) => score_error(error),
        CatalogAtlasArtifactError::Ext(error) => ext_error(error),
        error => value_error(error),
    }
}

#[pymethods]
impl PyIndecomposableCatalog {
    /// Builds a cached Ext atlas through the inclusive degree bound.
    #[pyo3(signature = (max_degree, limits = None))]
    fn atlas(
        &self,
        py: Python<'_>,
        max_degree: usize,
        limits: Option<&PyCatalogAtlasLimits>,
    ) -> PyResult<PyCatalogAtlas> {
        let limits = limits.map_or_else(CatalogAtlasLimits::default, |value| value.inner);
        py.allow_threads(|| CatalogAtlas::compute(self.inner.clone(), max_degree, limits))
            .map(PyCatalogAtlas::new)
            .map_err(atlas_error)
    }
}

#[pymethods]
impl PyCatalogAtlas {
    /// The catalog shared by this atlas.
    #[getter]
    fn catalog(&self) -> PyIndecomposableCatalog {
        PyIndecomposableCatalog {
            inner: self.inner.catalog().clone(),
        }
    }

    /// The prime modulus of the atlas algebra.
    #[getter]
    fn field(&self) -> u64 {
        self.inner.algebra().field().modulus()
    }

    /// The classification theorem carried by the catalog.
    #[getter]
    fn provenance(&self) -> String {
        provenance_name(self.inner.provenance()).to_string()
    }

    /// The atlas was computed from the complete catalog.
    #[getter]
    fn verification(&self) -> &'static str {
        "computed"
    }

    /// The ordered Ext table is complete through the stored degree bound.
    #[getter]
    fn status(&self) -> &'static str {
        "complete"
    }

    /// The inclusive largest stored Ext degree.
    #[getter]
    fn max_degree(&self) -> usize {
        self.inner.max_degree()
    }

    /// The checked resource ceilings used by this atlas.
    #[getter]
    fn limits(&self) -> PyCatalogAtlasLimits {
        PyCatalogAtlasLimits {
            inner: self.inner.limits(),
        }
    }

    /// The exact operation counts for this atlas.
    #[getter]
    fn work(&self) -> PyCatalogAtlasWork {
        PyCatalogAtlasWork {
            inner: self.inner.work(),
        }
    }

    /// The ordered Ext table in source-major, target-major order.
    #[getter]
    fn ext_table(&self) -> PyCatalogExtTable {
        PyCatalogExtTable {
            inner: self.inner.ext_table().clone(),
        }
    }

    /// The ordered Ext rows in source-major, target-major order.
    #[getter]
    fn pairs(&self) -> Vec<PyCatalogExtRow> {
        self.inner
            .pairs()
            .iter()
            .cloned()
            .map(|inner| PyCatalogExtRow { inner })
            .collect()
    }

    /// Returns the Ext dimensions of one ordered catalog pair.
    #[pyo3(signature = (source, target))]
    fn ext_dimensions(&self, source: usize, target: usize) -> Option<Vec<usize>> {
        self.inner
            .ext_dimensions(source, target)
            .map(<[usize]>::to_vec)
    }

    /// Returns one stored Ext dimension.
    #[pyo3(signature = (source, target, degree))]
    fn ext_dim(&self, source: usize, target: usize, degree: usize) -> Option<usize> {
        self.inner.ext_dim(source, target, degree)
    }

    /// Recomputes every source resolution and Ext row.
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    /// Enumerates catalog multiplicities with the requested dimension vector.
    #[pyo3(signature = (dimensions, limits = None))]
    fn enumerate(
        &self,
        py: Python<'_>,
        dimensions: Vec<usize>,
        limits: Option<&PyMultiplicityLimits>,
    ) -> PyResult<PyMultiplicityResult> {
        let limits = limits.map_or_else(MultiplicityLimits::default, |value| value.inner);
        let outcome = py
            .allow_threads(|| self.inner.enumerate_multiplicities(&dimensions, limits))
            .map_err(multiplicity_error)?;
        Ok(self.result(dimensions, outcome, limits))
    }

    /// Computes `mᵀ E_k n` for every degree in `first..=last`.
    #[pyo3(signature = (left, right, first = 0, last = None))]
    fn ext_scores(
        &self,
        py: Python<'_>,
        left: Vec<usize>,
        right: Vec<usize>,
        first: usize,
        last: Option<usize>,
    ) -> PyResult<Vec<usize>> {
        let last = last.unwrap_or(self.inner.max_degree());
        py.allow_threads(|| self.inner.ext_scores(&left, &right, first, last))
            .map_err(score_error)
    }

    /// Computes `mᵀ E_k m` for every degree in `first..=last`.
    #[pyo3(signature = (multiplicities, first = 0, last = None))]
    fn self_ext_scores(
        &self,
        py: Python<'_>,
        multiplicities: Vec<usize>,
        first: usize,
        last: Option<usize>,
    ) -> PyResult<Vec<usize>> {
        let last = last.unwrap_or(self.inner.max_degree());
        py.allow_threads(|| self.inner.self_ext_scores(&multiplicities, first, last))
            .map_err(score_error)
    }

    /// Checks whether every stored Ext contribution vanishes in the range.
    #[pyo3(signature = (left, right, first = 0, last = None))]
    fn ext_vanishes(
        &self,
        py: Python<'_>,
        left: Vec<usize>,
        right: Vec<usize>,
        first: usize,
        last: Option<usize>,
    ) -> PyResult<bool> {
        let last = last.unwrap_or(self.inner.max_degree());
        py.allow_threads(|| self.inner.ext_vanishes(&left, &right, first, last))
            .map_err(score_error)
    }

    /// Checks whether every stored self-Ext contribution vanishes in the range.
    #[pyo3(signature = (multiplicities, first = 0, last = None))]
    fn self_ext_vanishes(
        &self,
        py: Python<'_>,
        multiplicities: Vec<usize>,
        first: usize,
        last: Option<usize>,
    ) -> PyResult<bool> {
        let last = last.unwrap_or(self.inner.max_degree());
        py.allow_threads(|| self.inner.self_ext_vanishes(&multiplicities, first, last))
            .map_err(score_error)
    }

    /// Materializes a direct sum in catalog order from its multiplicity vector.
    #[pyo3(signature = (multiplicities))]
    fn materialize(&self, py: Python<'_>, multiplicities: Vec<usize>) -> PyResult<PyRightModule> {
        py.allow_threads(|| self.inner.materialize(&multiplicities))
            .map(PyRightModule::from)
            .map_err(materialize_error)
    }

    /// Exports this atlas and one multiplicity enumeration as canonical JSON.
    #[pyo3(signature = (dimensions, limits = None))]
    fn export(
        &self,
        py: Python<'_>,
        dimensions: Vec<usize>,
        limits: Option<&PyMultiplicityLimits>,
    ) -> PyResult<PyCatalogAtlasArtifact> {
        let limits = limits.map_or_else(MultiplicityLimits::default, |value| value.inner);
        py.allow_threads(|| CatalogAtlasArtifact::from_verified(&self.inner, &dimensions, limits))
            .map(|inner| PyCatalogAtlasArtifact { inner })
            .map_err(artifact_error)
    }

    fn __len__(&self) -> usize {
        self.inner.catalog().len()
    }

    fn __repr__(&self) -> String {
        format!(
            "CatalogAtlas(catalog_len={}, max_degree={}, provenance={:?})",
            self.inner.catalog().len(),
            self.inner.max_degree(),
            self.provenance()
        )
    }
}

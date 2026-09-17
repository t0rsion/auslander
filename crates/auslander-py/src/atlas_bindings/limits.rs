use super::super::*;
use super::{CatalogAtlasLimits, CatalogAtlasWork, MultiplicityLimits};
use auslander::atlas_artifact::{
    CatalogAtlasArtifactParseLimits, CatalogAtlasArtifactVerifyLimits,
};

/// Resource ceilings for one cached catalog atlas.
#[pyclass(name = "CatalogAtlasLimits", module = "auslander", frozen)]
#[derive(Clone, Copy)]
pub(crate) struct PyCatalogAtlasLimits {
    pub(crate) inner: CatalogAtlasLimits,
}

#[pymethods]
impl PyCatalogAtlasLimits {
    /// `CatalogAtlasLimits` accepts optional ceilings for atlas storage.
    #[new]
    #[pyo3(signature = (max_pairs=None, max_ext_cells=None, max_resolution_terms=None, max_materialized_summands=None, max_materialized_cells=None))]
    fn new(
        max_pairs: Option<usize>,
        max_ext_cells: Option<usize>,
        max_resolution_terms: Option<usize>,
        max_materialized_summands: Option<usize>,
        max_materialized_cells: Option<usize>,
    ) -> Self {
        let defaults = CatalogAtlasLimits::default();
        Self {
            inner: CatalogAtlasLimits {
                max_pairs: max_pairs.unwrap_or(defaults.max_pairs),
                max_ext_cells: max_ext_cells.unwrap_or(defaults.max_ext_cells),
                max_resolution_terms: max_resolution_terms.unwrap_or(defaults.max_resolution_terms),
                max_materialized_summands: max_materialized_summands
                    .unwrap_or(defaults.max_materialized_summands),
                max_materialized_cells: max_materialized_cells
                    .unwrap_or(defaults.max_materialized_cells),
            },
        }
    }

    #[getter]
    fn max_pairs(&self) -> usize {
        self.inner.max_pairs
    }

    #[getter]
    fn max_ext_cells(&self) -> usize {
        self.inner.max_ext_cells
    }

    #[getter]
    fn max_resolution_terms(&self) -> usize {
        self.inner.max_resolution_terms
    }

    #[getter]
    fn max_materialized_summands(&self) -> usize {
        self.inner.max_materialized_summands
    }

    #[getter]
    fn max_materialized_cells(&self) -> usize {
        self.inner.max_materialized_cells
    }

    fn __repr__(&self) -> String {
        format!(
            "CatalogAtlasLimits(max_pairs={}, max_ext_cells={}, max_resolution_terms={}, max_materialized_summands={}, max_materialized_cells={})",
            self.max_pairs(),
            self.max_ext_cells(),
            self.max_resolution_terms(),
            self.max_materialized_summands(),
            self.max_materialized_cells()
        )
    }
}

/// Resource ceilings for one catalog multiplicity enumeration.
#[pyclass(name = "MultiplicityLimits", module = "auslander", frozen)]
#[derive(Clone, Copy)]
pub(crate) struct PyMultiplicityLimits {
    pub(crate) inner: MultiplicityLimits,
}

#[pymethods]
impl PyMultiplicityLimits {
    /// `MultiplicityLimits` accepts optional solution and search-node ceilings.
    #[new]
    #[pyo3(signature = (max_solutions=None, max_nodes=None))]
    fn new(max_solutions: Option<usize>, max_nodes: Option<usize>) -> Self {
        let defaults = MultiplicityLimits::default();
        Self {
            inner: MultiplicityLimits {
                max_solutions: max_solutions.unwrap_or(defaults.max_solutions),
                max_nodes: max_nodes.unwrap_or(defaults.max_nodes),
            },
        }
    }

    #[getter]
    fn max_solutions(&self) -> usize {
        self.inner.max_solutions
    }

    #[getter]
    fn max_nodes(&self) -> usize {
        self.inner.max_nodes
    }

    fn __repr__(&self) -> String {
        format!(
            "MultiplicityLimits(max_solutions={}, max_nodes={})",
            self.max_solutions(),
            self.max_nodes()
        )
    }
}

/// Exact operation counts for one cached catalog atlas.
#[pyclass(name = "CatalogAtlasWork", module = "auslander", frozen)]
#[derive(Clone, Copy)]
pub(crate) struct PyCatalogAtlasWork {
    pub(crate) inner: CatalogAtlasWork,
}

#[pymethods]
impl PyCatalogAtlasWork {
    #[getter]
    fn pairs(&self) -> usize {
        self.inner.pairs
    }

    #[getter]
    fn ext_cells(&self) -> usize {
        self.inner.ext_cells
    }

    #[getter]
    fn resolutions(&self) -> usize {
        self.inner.resolutions
    }

    #[getter]
    fn resolution_terms(&self) -> usize {
        self.inner.resolution_terms
    }

    #[getter]
    fn ext_tables(&self) -> usize {
        self.inner.ext_tables
    }

    fn __repr__(&self) -> String {
        format!(
            "CatalogAtlasWork(pairs={}, ext_cells={}, resolutions={}, resolution_terms={}, ext_tables={})",
            self.pairs(),
            self.ext_cells(),
            self.resolutions(),
            self.resolution_terms(),
            self.ext_tables()
        )
    }
}

/// Parser ceilings for one portable catalog atlas artifact.
#[pyclass(name = "CatalogAtlasArtifactParseLimits", module = "auslander", frozen)]
#[derive(Clone, Copy)]
pub(crate) struct PyCatalogAtlasArtifactParseLimits {
    pub(crate) inner: CatalogAtlasArtifactParseLimits,
}

#[pymethods]
impl PyCatalogAtlasArtifactParseLimits {
    /// Optional byte, container, and value ceilings for artifact parsing.
    #[new]
    #[pyo3(signature = (
        max_input_bytes=None,
        max_certificate_bytes=None,
        max_catalog_entries=None,
        max_dimensions=None,
        max_dimension=None,
        max_ext_rows=None,
        max_ext_degrees=None,
        max_result_rows=None,
        max_multiplicity_values=None,
        max_numeric_values=None,
        max_array_elements=None,
        max_integer_digits=None,
        max_string_bytes=None,
    ))]
    #[allow(clippy::too_many_arguments)]
    fn new(
        max_input_bytes: Option<usize>,
        max_certificate_bytes: Option<usize>,
        max_catalog_entries: Option<usize>,
        max_dimensions: Option<usize>,
        max_dimension: Option<usize>,
        max_ext_rows: Option<usize>,
        max_ext_degrees: Option<usize>,
        max_result_rows: Option<usize>,
        max_multiplicity_values: Option<usize>,
        max_numeric_values: Option<usize>,
        max_array_elements: Option<usize>,
        max_integer_digits: Option<usize>,
        max_string_bytes: Option<usize>,
    ) -> Self {
        let defaults = CatalogAtlasArtifactParseLimits::default();
        Self {
            inner: CatalogAtlasArtifactParseLimits {
                max_input_bytes: max_input_bytes.unwrap_or(defaults.max_input_bytes),
                max_certificate_bytes: max_certificate_bytes
                    .unwrap_or(defaults.max_certificate_bytes),
                max_catalog_entries: max_catalog_entries.unwrap_or(defaults.max_catalog_entries),
                max_dimensions: max_dimensions.unwrap_or(defaults.max_dimensions),
                max_dimension: max_dimension.unwrap_or(defaults.max_dimension),
                max_ext_rows: max_ext_rows.unwrap_or(defaults.max_ext_rows),
                max_ext_degrees: max_ext_degrees.unwrap_or(defaults.max_ext_degrees),
                max_result_rows: max_result_rows.unwrap_or(defaults.max_result_rows),
                max_multiplicity_values: max_multiplicity_values
                    .unwrap_or(defaults.max_multiplicity_values),
                max_numeric_values: max_numeric_values.unwrap_or(defaults.max_numeric_values),
                max_array_elements: max_array_elements.unwrap_or(defaults.max_array_elements),
                max_integer_digits: max_integer_digits.unwrap_or(defaults.max_integer_digits),
                max_string_bytes: max_string_bytes.unwrap_or(defaults.max_string_bytes),
            },
        }
    }

    #[getter]
    fn max_input_bytes(&self) -> usize {
        self.inner.max_input_bytes
    }

    #[getter]
    fn max_certificate_bytes(&self) -> usize {
        self.inner.max_certificate_bytes
    }

    #[getter]
    fn max_catalog_entries(&self) -> usize {
        self.inner.max_catalog_entries
    }

    #[getter]
    fn max_dimensions(&self) -> usize {
        self.inner.max_dimensions
    }

    #[getter]
    fn max_dimension(&self) -> usize {
        self.inner.max_dimension
    }

    #[getter]
    fn max_ext_rows(&self) -> usize {
        self.inner.max_ext_rows
    }

    #[getter]
    fn max_ext_degrees(&self) -> usize {
        self.inner.max_ext_degrees
    }

    #[getter]
    fn max_result_rows(&self) -> usize {
        self.inner.max_result_rows
    }

    #[getter]
    fn max_multiplicity_values(&self) -> usize {
        self.inner.max_multiplicity_values
    }

    #[getter]
    fn max_numeric_values(&self) -> usize {
        self.inner.max_numeric_values
    }

    #[getter]
    fn max_array_elements(&self) -> usize {
        self.inner.max_array_elements
    }

    #[getter]
    fn max_integer_digits(&self) -> usize {
        self.inner.max_integer_digits
    }

    #[getter]
    fn max_string_bytes(&self) -> usize {
        self.inner.max_string_bytes
    }

    fn __repr__(&self) -> String {
        format!(
            "CatalogAtlasArtifactParseLimits(max_input_bytes={}, max_catalog_entries={}, max_ext_rows={}, max_result_rows={})",
            self.max_input_bytes(),
            self.max_catalog_entries(),
            self.max_ext_rows(),
            self.max_result_rows()
        )
    }
}

/// Replay ceilings for one portable catalog atlas artifact.
#[pyclass(
    name = "CatalogAtlasArtifactVerifyLimits",
    module = "auslander",
    frozen
)]
#[derive(Clone, Copy)]
pub(crate) struct PyCatalogAtlasArtifactVerifyLimits {
    pub(crate) inner: CatalogAtlasArtifactVerifyLimits,
}

#[pymethods]
impl PyCatalogAtlasArtifactVerifyLimits {
    /// Optional parser and replay ceilings for artifact verification.
    #[new]
    #[pyo3(signature = (
        parse=None,
        max_vertices=None,
        max_arrows=None,
        max_algebra_dimension=None,
        max_catalog_entries=None,
        max_dimension=None,
        max_degree=None,
        max_pairs=None,
        max_ext_cells=None,
        max_resolution_terms=None,
        max_result_rows=None,
        max_multiplicity=None,
        max_nodes=None,
        max_materialized_summands=None,
        max_materialized_cells=None,
        max_entry_total_dimension=None,
        max_generic_ext_cells=None,
    ))]
    #[allow(clippy::too_many_arguments)]
    fn new(
        parse: Option<&PyCatalogAtlasArtifactParseLimits>,
        max_vertices: Option<usize>,
        max_arrows: Option<usize>,
        max_algebra_dimension: Option<usize>,
        max_catalog_entries: Option<usize>,
        max_dimension: Option<usize>,
        max_degree: Option<usize>,
        max_pairs: Option<usize>,
        max_ext_cells: Option<usize>,
        max_resolution_terms: Option<usize>,
        max_result_rows: Option<usize>,
        max_multiplicity: Option<usize>,
        max_nodes: Option<usize>,
        max_materialized_summands: Option<usize>,
        max_materialized_cells: Option<usize>,
        max_entry_total_dimension: Option<usize>,
        max_generic_ext_cells: Option<usize>,
    ) -> Self {
        let defaults = CatalogAtlasArtifactVerifyLimits::default();
        Self {
            inner: CatalogAtlasArtifactVerifyLimits {
                parse: parse.map_or(defaults.parse, |value| value.inner),
                max_vertices: max_vertices.unwrap_or(defaults.max_vertices),
                max_arrows: max_arrows.unwrap_or(defaults.max_arrows),
                max_algebra_dimension: max_algebra_dimension
                    .unwrap_or(defaults.max_algebra_dimension),
                max_catalog_entries: max_catalog_entries.unwrap_or(defaults.max_catalog_entries),
                max_dimension: max_dimension.unwrap_or(defaults.max_dimension),
                max_degree: max_degree.unwrap_or(defaults.max_degree),
                max_pairs: max_pairs.unwrap_or(defaults.max_pairs),
                max_ext_cells: max_ext_cells.unwrap_or(defaults.max_ext_cells),
                max_resolution_terms: max_resolution_terms.unwrap_or(defaults.max_resolution_terms),
                max_result_rows: max_result_rows.unwrap_or(defaults.max_result_rows),
                max_multiplicity: max_multiplicity.unwrap_or(defaults.max_multiplicity),
                max_nodes: max_nodes.unwrap_or(defaults.max_nodes),
                max_materialized_summands: max_materialized_summands
                    .unwrap_or(defaults.max_materialized_summands),
                max_materialized_cells: max_materialized_cells
                    .unwrap_or(defaults.max_materialized_cells),
                max_entry_total_dimension: max_entry_total_dimension
                    .unwrap_or(defaults.max_entry_total_dimension),
                max_generic_ext_cells: max_generic_ext_cells
                    .unwrap_or(defaults.max_generic_ext_cells),
            },
        }
    }

    #[getter]
    fn parse(&self) -> PyCatalogAtlasArtifactParseLimits {
        PyCatalogAtlasArtifactParseLimits {
            inner: self.inner.parse,
        }
    }

    #[getter]
    fn max_input_bytes(&self) -> usize {
        self.inner.parse.max_input_bytes
    }

    #[getter]
    fn max_certificate_bytes(&self) -> usize {
        self.inner.parse.max_certificate_bytes
    }

    #[getter]
    fn max_dimensions(&self) -> usize {
        self.inner.parse.max_dimensions
    }

    #[getter]
    fn max_ext_rows(&self) -> usize {
        self.inner.parse.max_ext_rows
    }

    #[getter]
    fn max_ext_degrees(&self) -> usize {
        self.inner.parse.max_ext_degrees
    }

    #[getter]
    fn max_multiplicity_values(&self) -> usize {
        self.inner.parse.max_multiplicity_values
    }

    #[getter]
    fn max_numeric_values(&self) -> usize {
        self.inner.parse.max_numeric_values
    }

    #[getter]
    fn max_array_elements(&self) -> usize {
        self.inner.parse.max_array_elements
    }

    #[getter]
    fn max_integer_digits(&self) -> usize {
        self.inner.parse.max_integer_digits
    }

    #[getter]
    fn max_string_bytes(&self) -> usize {
        self.inner.parse.max_string_bytes
    }

    #[getter]
    fn max_vertices(&self) -> usize {
        self.inner.max_vertices
    }

    #[getter]
    fn max_arrows(&self) -> usize {
        self.inner.max_arrows
    }

    #[getter]
    fn max_algebra_dimension(&self) -> usize {
        self.inner.max_algebra_dimension
    }

    #[getter]
    fn max_catalog_entries(&self) -> usize {
        self.inner.max_catalog_entries
    }

    #[getter]
    fn max_dimension(&self) -> usize {
        self.inner.max_dimension
    }

    #[getter]
    fn max_degree(&self) -> usize {
        self.inner.max_degree
    }

    #[getter]
    fn max_pairs(&self) -> usize {
        self.inner.max_pairs
    }

    #[getter]
    fn max_ext_cells(&self) -> usize {
        self.inner.max_ext_cells
    }

    #[getter]
    fn max_resolution_terms(&self) -> usize {
        self.inner.max_resolution_terms
    }

    #[getter]
    fn max_result_rows(&self) -> usize {
        self.inner.max_result_rows
    }

    #[getter]
    fn max_multiplicity(&self) -> usize {
        self.inner.max_multiplicity
    }

    #[getter]
    fn max_nodes(&self) -> usize {
        self.inner.max_nodes
    }

    #[getter]
    fn max_materialized_summands(&self) -> usize {
        self.inner.max_materialized_summands
    }

    #[getter]
    fn max_materialized_cells(&self) -> usize {
        self.inner.max_materialized_cells
    }

    #[getter]
    fn max_entry_total_dimension(&self) -> usize {
        self.inner.max_entry_total_dimension
    }

    #[getter]
    fn max_generic_ext_cells(&self) -> usize {
        self.inner.max_generic_ext_cells
    }

    fn __repr__(&self) -> String {
        format!(
            "CatalogAtlasArtifactVerifyLimits(max_vertices={}, max_catalog_entries={}, max_degree={}, max_result_rows={})",
            self.max_vertices(),
            self.max_catalog_entries(),
            self.max_degree(),
            self.max_result_rows()
        )
    }
}

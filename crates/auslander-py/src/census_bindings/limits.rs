use super::super::*;

/// A checked resource envelope for one finite module census.
#[pyclass(name = "CensusLimits", module = "auslander", frozen)]
#[derive(Clone, Copy)]
pub(crate) struct PyCensusLimits {
    pub(crate) inner: CensusLimits,
}

#[pymethods]
impl PyCensusLimits {
    /// `CensusLimits` bounds one census and selects duplicate-record retention.
    #[new]
    #[pyo3(signature = (max_candidates=None, max_representatives=None, max_assignments=None, max_isomorphism_checks=None, max_work_units=None, *, retention=None))]
    #[allow(clippy::too_many_arguments)]
    fn new(
        max_candidates: Option<usize>,
        max_representatives: Option<usize>,
        max_assignments: Option<usize>,
        max_isomorphism_checks: Option<usize>,
        max_work_units: Option<usize>,
        retention: Option<&str>,
    ) -> PyResult<Self> {
        let defaults = CensusLimits::default();
        let retention = parse_retention(retention, defaults.retention)?;
        Ok(Self {
            inner: CensusLimits {
                retention,
                max_candidates: max_candidates.unwrap_or(defaults.max_candidates),
                max_representatives: max_representatives.unwrap_or(defaults.max_representatives),
                max_assignments: max_assignments.unwrap_or(defaults.max_assignments),
                max_isomorphism_checks: max_isomorphism_checks
                    .unwrap_or(defaults.max_isomorphism_checks),
                max_work_units: max_work_units.unwrap_or(defaults.max_work_units),
            },
        })
    }

    /// The duplicate-record retention mode.
    #[getter]
    fn retention(&self) -> &'static str {
        self.inner.retention.as_str()
    }

    /// Maximum raw candidates fully processed.
    #[getter]
    fn max_candidates(&self) -> usize {
        self.inner.max_candidates
    }

    /// Maximum retained representatives.
    #[getter]
    fn max_representatives(&self) -> usize {
        self.inner.max_representatives
    }

    /// Maximum retained duplicate assignments.
    #[getter]
    fn max_assignments(&self) -> usize {
        self.inner.max_assignments
    }

    /// Maximum completed isomorphism comparisons.
    #[getter]
    fn max_isomorphism_checks(&self) -> usize {
        self.inner.max_isomorphism_checks
    }

    /// Maximum candidate and comparison work units.
    #[getter]
    fn max_work_units(&self) -> usize {
        self.inner.max_work_units
    }

    fn __repr__(&self) -> String {
        format!(
            "CensusLimits(retention={:?}, max_candidates={}, max_representatives={}, max_assignments={}, max_isomorphism_checks={}, max_work_units={})",
            self.retention(),
            self.max_candidates(),
            self.max_representatives(),
            self.max_assignments(),
            self.max_isomorphism_checks(),
            self.max_work_units()
        )
    }
}

fn parse_retention(value: Option<&str>, default: CensusRetention) -> PyResult<CensusRetention> {
    match value {
        None => Ok(default),
        Some("all_assignments") => Ok(CensusRetention::AllAssignments),
        Some("representatives_only") => Ok(CensusRetention::RepresentativesOnly),
        Some(value) => Err(PyValueError::new_err(format!(
            "retention must be 'all_assignments' or 'representatives_only', got {value:?}"
        ))),
    }
}

/// A caller-owned ceiling for parsing and replaying a portable census file.
#[pyclass(name = "CensusVerifyLimits", module = "auslander", frozen)]
#[derive(Clone, Copy)]
pub(crate) struct PyCensusVerifyLimits {
    pub(crate) inner: CensusVerifyLimits,
}

#[pymethods]
impl PyCensusVerifyLimits {
    /// `CensusVerifyLimits` accepts bounded parser and replay ceilings as keyword arguments.
    #[new]
    #[pyo3(signature = (*, max_input_bytes=None, max_certificate_bytes=None, max_dimensions=None, max_dimension=None, max_representatives=None, max_assignments=None, max_coordinate_values=None, max_witness_matrices=None, max_witness_rows=None, max_witness_columns=None, max_witness_entries=None, max_numeric_values=None, max_array_elements=None, max_integer_digits=None, max_string_bytes=None, max_vertices=None, max_coordinates=None, max_candidates=None, max_isomorphism_checks=None, max_work_units=None))]
    #[allow(clippy::too_many_arguments)]
    fn new(
        max_input_bytes: Option<usize>,
        max_certificate_bytes: Option<usize>,
        max_dimensions: Option<usize>,
        max_dimension: Option<usize>,
        max_representatives: Option<usize>,
        max_assignments: Option<usize>,
        max_coordinate_values: Option<usize>,
        max_witness_matrices: Option<usize>,
        max_witness_rows: Option<usize>,
        max_witness_columns: Option<usize>,
        max_witness_entries: Option<usize>,
        max_numeric_values: Option<usize>,
        max_array_elements: Option<usize>,
        max_integer_digits: Option<usize>,
        max_string_bytes: Option<usize>,
        max_vertices: Option<usize>,
        max_coordinates: Option<usize>,
        max_candidates: Option<usize>,
        max_isomorphism_checks: Option<usize>,
        max_work_units: Option<usize>,
    ) -> Self {
        let defaults = CensusVerifyLimits::default();
        let parse = defaults.parse;
        Self {
            inner: CensusVerifyLimits {
                parse: CensusParseLimits {
                    max_input_bytes: max_input_bytes.unwrap_or(parse.max_input_bytes),
                    max_certificate_bytes: max_certificate_bytes
                        .unwrap_or(parse.max_certificate_bytes),
                    max_dimensions: max_dimensions.unwrap_or(parse.max_dimensions),
                    max_dimension: max_dimension.unwrap_or(parse.max_dimension),
                    max_representatives: max_representatives.unwrap_or(parse.max_representatives),
                    max_assignments: max_assignments.unwrap_or(parse.max_assignments),
                    max_coordinate_values: max_coordinate_values
                        .unwrap_or(parse.max_coordinate_values),
                    max_witness_matrices: max_witness_matrices
                        .unwrap_or(parse.max_witness_matrices),
                    max_witness_rows: max_witness_rows.unwrap_or(parse.max_witness_rows),
                    max_witness_columns: max_witness_columns.unwrap_or(parse.max_witness_columns),
                    max_witness_entries: max_witness_entries.unwrap_or(parse.max_witness_entries),
                    max_numeric_values: max_numeric_values.unwrap_or(parse.max_numeric_values),
                    max_array_elements: max_array_elements.unwrap_or(parse.max_array_elements),
                    max_integer_digits: max_integer_digits.unwrap_or(parse.max_integer_digits),
                    max_string_bytes: max_string_bytes.unwrap_or(parse.max_string_bytes),
                },
                max_vertices: max_vertices.unwrap_or(defaults.max_vertices),
                max_coordinates: max_coordinates.unwrap_or(defaults.max_coordinates),
                max_dimension: max_dimension.unwrap_or(defaults.max_dimension),
                max_candidates: max_candidates.unwrap_or(defaults.max_candidates),
                max_representatives: max_representatives.unwrap_or(defaults.max_representatives),
                max_assignments: max_assignments.unwrap_or(defaults.max_assignments),
                max_isomorphism_checks: max_isomorphism_checks
                    .unwrap_or(defaults.max_isomorphism_checks),
                max_work_units: max_work_units.unwrap_or(defaults.max_work_units),
            },
        }
    }

    /// The greatest accepted input byte count.
    #[getter]
    fn max_input_bytes(&self) -> usize {
        self.inner.parse.max_input_bytes
    }

    /// The greatest embedded certificate byte count.
    #[getter]
    fn max_certificate_bytes(&self) -> usize {
        self.inner.parse.max_certificate_bytes
    }

    /// The greatest number of dimension entries.
    #[getter]
    fn max_dimensions(&self) -> usize {
        self.inner.parse.max_dimensions
    }

    /// The greatest dimension at one vertex.
    #[getter]
    fn max_dimension(&self) -> usize {
        self.inner.max_dimension
    }

    /// The greatest number of retained representatives.
    #[getter]
    fn max_representatives(&self) -> usize {
        self.inner.max_representatives
    }

    /// The greatest number of retained assignments.
    #[getter]
    fn max_assignments(&self) -> usize {
        self.inner.max_assignments
    }

    /// The greatest coordinate count in one module.
    #[getter]
    fn max_coordinate_values(&self) -> usize {
        self.inner.parse.max_coordinate_values
    }

    /// The greatest number of witness matrices.
    #[getter]
    fn max_witness_matrices(&self) -> usize {
        self.inner.parse.max_witness_matrices
    }

    /// The greatest number of witness rows.
    #[getter]
    fn max_witness_rows(&self) -> usize {
        self.inner.parse.max_witness_rows
    }

    /// The greatest number of witness columns.
    #[getter]
    fn max_witness_columns(&self) -> usize {
        self.inner.parse.max_witness_columns
    }

    /// The greatest number of witness scalar entries.
    #[getter]
    fn max_witness_entries(&self) -> usize {
        self.inner.parse.max_witness_entries
    }

    /// The greatest number of numeric values in the document.
    #[getter]
    fn max_numeric_values(&self) -> usize {
        self.inner.parse.max_numeric_values
    }

    /// The greatest number of array elements in the document.
    #[getter]
    fn max_array_elements(&self) -> usize {
        self.inner.parse.max_array_elements
    }

    /// The greatest digit count in one unsigned integer.
    #[getter]
    fn max_integer_digits(&self) -> usize {
        self.inner.parse.max_integer_digits
    }

    /// The greatest byte count of one portable string.
    #[getter]
    fn max_string_bytes(&self) -> usize {
        self.inner.parse.max_string_bytes
    }

    /// The greatest number of reconstructed algebra vertices.
    #[getter]
    fn max_vertices(&self) -> usize {
        self.inner.max_vertices
    }

    /// The greatest reconstructed coordinate count.
    #[getter]
    fn max_coordinates(&self) -> usize {
        self.inner.max_coordinates
    }

    /// The greatest replayed candidate count.
    #[getter]
    fn max_candidates(&self) -> usize {
        self.inner.max_candidates
    }

    /// The greatest replayed isomorphism-check count.
    #[getter]
    fn max_isomorphism_checks(&self) -> usize {
        self.inner.max_isomorphism_checks
    }

    /// The greatest replay work count.
    #[getter]
    fn max_work_units(&self) -> usize {
        self.inner.max_work_units
    }

    fn __repr__(&self) -> String {
        format!(
            "CensusVerifyLimits(max_input_bytes={}, max_candidates={}, max_representatives={}, max_assignments={}, max_work_units={})",
            self.max_input_bytes(),
            self.max_candidates(),
            self.max_representatives(),
            self.max_assignments(),
            self.max_work_units()
        )
    }
}

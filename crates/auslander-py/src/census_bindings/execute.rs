use super::super::*;
use super::checkpoint::{PyCensusCheckpoint, PyVerifiedCensusCheckpoint};
use super::limits::{PyCensusLimits, PyCensusVerifyLimits};

pub(super) fn census_portable_error(error: CensusPortableError) -> PyErr {
    value_error(error)
}

pub(super) fn census_resume_error(error: CensusResumeError) -> PyErr {
    value_error(error)
}

pub(super) fn checkpoint_from_outcome(outcome: CensusOutcome) -> PyResult<PyCensusCheckpoint> {
    if let CensusOutcome::Failed(failed) = &outcome {
        return Err(DefectError::new_err(format!(
            "census failed at cursor {}: {}",
            failed.cursor(),
            failed.error()
        )));
    }
    CensusPortable::from_outcome(&outcome)
        .map(|inner| PyCensusCheckpoint { inner })
        .map_err(census_portable_error)
}

pub(super) fn run_census_inner(
    py: Python<'_>,
    algebra: &PyAlgebra,
    dimensions: Vec<usize>,
    field: Option<&PyPrimeField>,
    limits: Option<&PyCensusLimits>,
    control: Option<&PyComputationControl>,
) -> PyResult<PyCensusCheckpoint> {
    let algebra = algebra.algebra_for(py, field, "a census")?;
    let limits = limits.map_or_else(CensusLimits::default, |value| value.inner);
    let control = control.map_or_else(ComputationControl::new, |value| value.inner.clone());
    let census = py
        .allow_threads(|| Census::new(&algebra, dimensions))
        .map_err(value_error)?;
    let outcome = py.allow_threads(|| census.run_with(limits, Some(&control)));
    checkpoint_from_outcome(outcome)
}

pub(super) fn verify_census_inner(
    py: Python<'_>,
    portable: &CensusPortable,
    limits: CensusVerifyLimits,
) -> PyResult<PyVerifiedCensusCheckpoint> {
    let verified = py
        .allow_threads(|| portable.verify(limits))
        .map_err(census_portable_error)?;
    Ok(PyVerifiedCensusCheckpoint { inner: verified })
}

/// Run a checked finite census from an algebra and dimension vector.
#[pyfunction]
#[pyo3(signature = (algebra, dimensions, field=None, limits=None, control=None))]
pub(crate) fn run_census(
    py: Python<'_>,
    algebra: &PyAlgebra,
    dimensions: Vec<usize>,
    field: Option<&PyPrimeField>,
    limits: Option<&PyCensusLimits>,
    control: Option<&PyComputationControl>,
) -> PyResult<PyCensusCheckpoint> {
    run_census_inner(py, algebra, dimensions, field, limits, control)
}

/// Parse and replay-verify one canonical census checkpoint.
#[pyfunction]
#[pyo3(signature = (text, limits=None))]
pub(crate) fn verify_census_checkpoint(
    py: Python<'_>,
    text: &str,
    limits: Option<&PyCensusVerifyLimits>,
) -> PyResult<PyVerifiedCensusCheckpoint> {
    let limits = limits.map_or_else(CensusVerifyLimits::default, |value| value.inner);
    let portable = py
        .allow_threads(|| CensusPortable::from_json(text, limits.parse))
        .map_err(census_portable_error)?;
    verify_census_inner(py, &portable, limits)
}

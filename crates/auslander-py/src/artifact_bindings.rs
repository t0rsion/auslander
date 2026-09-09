use super::*;

/// A portable derived-equivalence artifact accepted by the independent verifier.

#[pyclass(name = "VerifiedDerivedArtifact", module = "auslander", frozen)]
pub(crate) struct PyVerifiedDerivedArtifact {
    pub(crate) inner: VerifiedDerivedArtifact,
}

#[pymethods]
impl PyVerifiedDerivedArtifact {
    /// The byte-exact canonical artifact JSON.
    #[getter]
    fn canonical_json(&self) -> String {
        self.inner.artifact().to_canonical_json()
    }

    /// The canonical artifact fingerprint.
    #[getter]
    fn fingerprint(&self) -> &str {
        self.inner.artifact().fingerprint()
    }

    /// The number of checked mutations from the regular generator.
    #[getter]
    fn mutation_count(&self) -> usize {
        self.inner.artifact().mutations().len()
    }

    /// The source prime.
    #[getter]
    fn source_field(&self) -> u64 {
        self.inner.artifact().source_certificate().field
    }

    /// The target prime.
    #[getter]
    fn target_field(&self) -> u64 {
        self.inner.artifact().target_certificate().field
    }

    /// Repeats independent verification with the default verifier limits.
    fn verify(&self, py: Python<'_>) -> bool {
        let text = self.inner.artifact().to_canonical_json();
        py.allow_threads(|| {
            matches!(
                verify_artifact(
                    &text,
                    ArtifactVerifyLimits::default(),
                    &ComputationControl::new(),
                ),
                Ok(ArtifactVerificationOutcome::Verified(_))
            )
        })
    }

    fn __repr__(&self) -> String {
        format!(
            "VerifiedDerivedArtifact(mutations={}, fingerprint={:?})",
            self.mutation_count(),
            self.fingerprint()
        )
    }
}

/// A portable artifact verification stopped before it could accept the claim.
#[pyclass(name = "IncompleteArtifactVerification", module = "auslander", frozen)]
pub(crate) struct PyIncompleteArtifactVerification {
    pub(crate) inner: ArtifactVerificationCut,
}

#[pymethods]
impl PyIncompleteArtifactVerification {
    /// "cancelled", "declared_limit", or "work_limit".
    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner {
            ArtifactVerificationCut::Cancelled { .. } => "cancelled",
            ArtifactVerificationCut::DeclaredLimit { .. } => "declared_limit",
            ArtifactVerificationCut::WorkLimit { .. } => "work_limit",
        }
    }

    /// Completed mutation work, when the cut records it.
    #[getter]
    fn completed(&self) -> Option<usize> {
        match self.inner {
            ArtifactVerificationCut::Cancelled {
                completed_mutations,
            } => Some(completed_mutations),
            ArtifactVerificationCut::WorkLimit { completed, .. } => Some(completed),
            ArtifactVerificationCut::DeclaredLimit { .. } => None,
        }
    }

    /// The rejected declared-limit field, when present.
    #[getter]
    fn field(&self) -> Option<&'static str> {
        match self.inner {
            ArtifactVerificationCut::DeclaredLimit { field, .. } => Some(field),
            _ => None,
        }
    }

    fn __repr__(&self) -> String {
        format!("IncompleteArtifactVerification(kind={:?})", self.kind())
    }
}

pub(crate) fn artifact_error(error: ArtifactError) -> PyErr {
    match error {
        error @ (ArtifactError::ParseLimit { .. }
        | ArtifactError::Syntax { .. }
        | ArtifactError::Certificate { .. }
        | ArtifactError::Schema { .. }
        | ArtifactError::FingerprintShape
        | ArtifactError::FingerprintMismatch
        | ArtifactError::Mathematical(_)) => value_error(error),
        other => DefectError::new_err(other.to_string()),
    }
}

pub(crate) fn artifact_initial_tilting(
    algebra: &Arc<Algebra>,
) -> PyResult<CertifiedTiltingComplex> {
    match regular_tilting_complex(algebra, TiltingComplexLimits::default())
        .map_err(|error| DefectError::new_err(error.to_string()))?
    {
        TiltingComplexResult::Tilting(value) => Ok(*value),
        outcome => Err(DefectError::new_err(format!(
            "regular tilting classification did not complete: {outcome:?}"
        ))),
    }
}

pub(crate) fn named_tilting_mutation(
    tilting: &CertifiedTiltingComplex,
    direction: &str,
    summand: usize,
    position: usize,
) -> PyResult<TiltingMutationOutcome> {
    let limits = TiltingComplexLimits::default();
    match direction {
        "left" => left_tilting_mutation(tilting, summand, limits),
        "right" => right_tilting_mutation(tilting, summand, limits),
        _ => {
            return Err(PyValueError::new_err(format!(
                "mutation {position} direction must be 'left' or 'right'"
            )));
        }
    }
    .map_err(|error| DefectError::new_err(error.to_string()))
}

pub(crate) fn require_tilting_mutation(
    outcome: TiltingMutationOutcome,
    position: usize,
) -> PyResult<CertifiedTiltingComplex> {
    let TiltingMutationOutcome::Tilting(value) = outcome else {
        return Err(PyValueError::new_err(format!(
            "mutation {position} did not produce a tilting complex: {outcome:?}"
        )));
    };
    Ok(*value)
}

pub(crate) fn apply_named_mutations(
    mut tilting: CertifiedTiltingComplex,
    mutations: &[(String, usize)],
) -> PyResult<CertifiedTiltingComplex> {
    for (position, (direction, summand)) in mutations.iter().enumerate() {
        let outcome = named_tilting_mutation(&tilting, direction, *summand, position)?;
        tilting = require_tilting_mutation(outcome, position)?;
    }
    Ok(tilting)
}

pub(crate) fn artifact_edge(
    tilting: CertifiedTiltingComplex,
) -> PyResult<RustDerivedEquivalenceEdge> {
    match RustDerivedEquivalenceEdge::recover(tilting, &TargetLimits::default())
        .map_err(|error| DefectError::new_err(error.to_string()))?
    {
        DerivedEquivalenceEdgeOutcome::Certified(value) => Ok(*value),
        DerivedEquivalenceEdgeOutcome::Cut(cut) => Err(BudgetExhaustedError::new_err(format!(
            "derived target recovery stopped: {:?}",
            cut.reason()
        ))),
    }
}

pub(crate) fn build_derived_artifact_inner(
    algebra: &Arc<Algebra>,
    mutations: &[(String, usize)],
) -> PyResult<String> {
    let tilting = artifact_initial_tilting(algebra)?;
    let tilting = apply_named_mutations(tilting, mutations)?;
    let edge = artifact_edge(tilting)?;
    RustDerivedArtifact::from_edge(&edge)
        .map(|artifact| artifact.to_canonical_json())
        .map_err(artifact_error)
}

/// Build a canonical derived artifact from a checked left or right mutation recipe.
#[pyfunction]
#[pyo3(signature = (algebra, mutations, field=None))]
pub(crate) fn build_derived_artifact(
    py: Python<'_>,
    algebra: &PyAlgebra,
    mutations: Vec<(String, usize)>,
    field: Option<&PyPrimeField>,
) -> PyResult<String> {
    let algebra = algebra.algebra_for(py, field, "a derived artifact")?;
    py.allow_threads(|| build_derived_artifact_inner(&algebra, &mutations))
}

/// Verify one untrusted `auslander-derived-v1` artifact.
#[pyfunction(name = "verify_derived_artifact")]
#[pyo3(
    text_signature = "(text, control=None)",
    signature = (text, control=None)
)]
pub(crate) fn py_verify_derived_artifact(
    py: Python<'_>,
    text: &str,
    control: Option<&PyComputationControl>,
) -> PyResult<Py<PyAny>> {
    let control = control.map_or_else(ComputationControl::new, |value| value.inner.clone());
    let outcome = py
        .allow_threads(|| verify_artifact(text, ArtifactVerifyLimits::default(), &control))
        .map_err(artifact_error)?;
    match outcome {
        ArtifactVerificationOutcome::Verified(inner) => {
            Py::new(py, PyVerifiedDerivedArtifact { inner: *inner }).map(Py::into_any)
        }
        ArtifactVerificationOutcome::Cut(inner) => {
            Py::new(py, PyIncompleteArtifactVerification { inner }).map(Py::into_any)
        }
    }
}

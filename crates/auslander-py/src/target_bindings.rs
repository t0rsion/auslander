use super::*;

/// Independent bounds for classical tilting classification.

#[pyclass(name = "TiltingLimits", module = "auslander", frozen)]
#[derive(Clone, Copy)]
pub(crate) struct PyTiltingLimits {
    pub(crate) inner: TiltingLimits,
}

#[pymethods]
impl PyTiltingLimits {
    /// TiltingLimits(max_projective_dimension, max_generation_steps).
    #[new]
    #[pyo3(text_signature = "(max_projective_dimension, max_generation_steps)")]
    fn new(max_projective_dimension: usize, max_generation_steps: usize) -> Self {
        Self {
            inner: TiltingLimits {
                max_projective_dimension,
                max_generation_steps,
            },
        }
    }

    /// The projective-resolution differential bound.
    #[getter]
    fn max_projective_dimension(&self) -> usize {
        self.inner.max_projective_dimension
    }

    /// The minimal left-approximation map bound.
    #[getter]
    fn max_generation_steps(&self) -> usize {
        self.inner.max_generation_steps
    }

    fn __repr__(&self) -> String {
        format!(
            "TiltingLimits(max_projective_dimension={}, max_generation_steps={})",
            self.inner.max_projective_dimension, self.inner.max_generation_steps
        )
    }
}

/// Independent ceilings for one split target-presentation run.
#[pyclass(name = "TargetLimits", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyTargetLimits {
    pub(crate) inner: TargetLimits,
}

#[pymethods]
impl PyTargetLimits {
    /// TargetLimits with explicit target and completion ceilings.
    #[new]
    #[pyo3(signature = (
        max_endo_dimension = 4096,
        max_radical_products = 1_000_000,
        max_paths = 1_000_000,
        max_relation_terms = 1_000_000,
        max_basis = 4096,
        max_word_len = 64,
        max_steps = 1_000_000,
        max_origin_terms = 4096,
        max_ambiguities = 65_536,
    ))]
    #[allow(clippy::too_many_arguments)]
    fn new(
        max_endo_dimension: usize,
        max_radical_products: usize,
        max_paths: usize,
        max_relation_terms: usize,
        max_basis: usize,
        max_word_len: usize,
        max_steps: usize,
        max_origin_terms: usize,
        max_ambiguities: usize,
    ) -> PyTargetLimits {
        PyTargetLimits {
            inner: TargetLimits {
                max_endo_dimension,
                max_radical_products,
                max_paths,
                max_relation_terms,
                completion: CompletionLimits {
                    max_basis,
                    max_word_len,
                    max_steps,
                    max_origin_terms,
                    max_ambiguities,
                },
            },
        }
    }

    #[getter]
    fn max_endo_dimension(&self) -> usize {
        self.inner.max_endo_dimension
    }

    #[getter]
    fn max_radical_products(&self) -> usize {
        self.inner.max_radical_products
    }

    #[getter]
    fn max_paths(&self) -> usize {
        self.inner.max_paths
    }

    #[getter]
    fn max_relation_terms(&self) -> usize {
        self.inner.max_relation_terms
    }

    #[getter]
    fn max_basis(&self) -> usize {
        self.inner.completion.max_basis
    }

    #[getter]
    fn max_word_len(&self) -> usize {
        self.inner.completion.max_word_len
    }

    #[getter]
    fn max_steps(&self) -> usize {
        self.inner.completion.max_steps
    }

    #[getter]
    fn max_origin_terms(&self) -> usize {
        self.inner.completion.max_origin_terms
    }

    #[getter]
    fn max_ambiguities(&self) -> usize {
        self.inner.completion.max_ambiguities
    }

    fn __repr__(&self) -> String {
        format!(
            "TargetLimits(max_endo_dimension={}, max_radical_products={}, max_paths={}, \
             max_relation_terms={})",
            self.inner.max_endo_dimension,
            self.inner.max_radical_products,
            self.inner.max_paths,
            self.inner.max_relation_terms
        )
    }
}

/// Exact deterministic work counts from a completed target recovery.
#[pyclass(name = "TargetWork", module = "auslander", frozen)]
#[derive(Clone, Copy)]
pub(crate) struct PyTargetWork {
    pub(crate) inner: TargetWork,
}

#[pymethods]
impl PyTargetWork {
    #[getter]
    fn endo_dimension(&self) -> usize {
        self.inner.endo_dimension
    }

    #[getter]
    fn radical_products(&self) -> usize {
        self.inner.radical_products
    }

    #[getter]
    fn paths(&self) -> usize {
        self.inner.paths
    }

    #[getter]
    fn relation_terms(&self) -> usize {
        self.inner.relation_terms
    }

    fn __repr__(&self) -> String {
        format!(
            "TargetWork(endo_dimension={}, radical_products={}, paths={}, relation_terms={})",
            self.inner.endo_dimension,
            self.inner.radical_products,
            self.inner.paths,
            self.inner.relation_terms
        )
    }
}

/// A verified split presentation of `End_A(T)^op`.
#[pyclass(name = "TargetPresentation", module = "auslander", frozen)]
pub(crate) struct PyTargetPresentation {
    pub(crate) inner: VerifiedTargetPresentation,
}

#[pymethods]
impl PyTargetPresentation {
    /// The source tilting module.
    #[getter]
    fn source(&self) -> PyRightModule {
        self.inner.source().into()
    }

    /// The ordered indecomposable summands that define target vertices.
    #[getter]
    fn summands(&self) -> Vec<PyRightModule> {
        wrap_all(self.inner.split().summands())
    }

    /// The summand inclusions into the source tilting module.
    #[getter]
    fn inclusions(&self) -> Vec<PyMorphism> {
        wrap_all(self.inner.split().inclusions())
    }

    /// The source projections onto the ordered summands.
    #[getter]
    fn projections(&self) -> Vec<PyMorphism> {
        wrap_all(self.inner.split().projections())
    }

    /// The deterministic morphism basis of `End_A(T)`.
    #[getter]
    fn endomorphism_basis(&self) -> Vec<PyMorphism> {
        wrap_all(self.inner.endo().basis())
    }

    /// An endomorphism of `T` from deterministic basis coordinates.
    #[pyo3(text_signature = "($self, coordinates)")]
    fn endomorphism(&self, coordinates: Vec<i64>) -> PyResult<PyMorphism> {
        if coordinates.len() != self.inner.endo().dim() {
            return Err(PyValueError::new_err(format!(
                "endomorphism coordinate count is {}, expected {}",
                coordinates.len(),
                self.inner.endo().dim()
            )));
        }
        let field = self.inner.target().field();
        let coordinates: Vec<Fp> = coordinates
            .into_iter()
            .map(|value| field.elem(value))
            .collect();
        Ok(self.inner.endo().morphism(&coordinates).into())
    }

    /// The checked target bound quiver algebra.
    #[getter]
    fn target(&self) -> PyAlgebra {
        PyAlgebra::pinned(self.inner.target().clone())
    }

    /// The limits used by this recovery.
    #[getter]
    fn limits(&self) -> PyTargetLimits {
        PyTargetLimits {
            inner: self.inner.limits().clone(),
        }
    }

    /// The exact deterministic work counts.
    #[getter]
    fn work(&self) -> PyTargetWork {
        PyTargetWork {
            inner: self.inner.work(),
        }
    }

    /// The first zero radical-power index of `End_A(T)`.
    #[getter]
    fn radical_nilpotency_index(&self) -> usize {
        self.inner.radical_nilpotency_index()
    }

    /// Primitive idempotent images, one row per target vertex.
    #[getter]
    fn idempotent_images(&self) -> Vec<Vec<u64>> {
        self.inner.idempotent_images().entries_u64()
    }

    /// Arrow images, one row per target arrow.
    #[getter]
    fn arrow_images(&self) -> Vec<Vec<u64>> {
        self.inner.arrow_images().entries_u64()
    }

    /// Normal-word images in endomorphism coordinates.
    #[getter]
    fn normal_word_images(&self) -> Vec<Vec<u64>> {
        self.inner.normal_word_images().entries_u64()
    }

    /// The inverse matrix from endomorphism to target coordinates.
    #[getter]
    fn normal_word_preimages(&self) -> Vec<Vec<u64>> {
        self.inner.normal_word_preimages().entries_u64()
    }

    /// The target completion certificate in canonical JSON.
    #[getter]
    fn certificate_json(&self) -> String {
        self.inner.completion_certificate().to_canonical_json()
    }

    /// Maps target coordinates to `End_A(T)` coordinates.
    #[pyo3(text_signature = "($self, coordinates)")]
    fn map_coordinates(&self, coordinates: Vec<i64>) -> PyResult<Vec<u64>> {
        if coordinates.len() != self.inner.target().dim() {
            return Err(PyValueError::new_err(format!(
                "target coordinate count is {}, expected {}",
                coordinates.len(),
                self.inner.target().dim()
            )));
        }
        let field = self.inner.target().field();
        let coordinates: Vec<Fp> = coordinates
            .into_iter()
            .map(|value| field.elem(value))
            .collect();
        Ok(row_u64(&self.inner.map_coordinates(&coordinates)))
    }

    /// Maps `End_A(T)` coordinates back to target coordinates.
    #[pyo3(text_signature = "($self, coordinates)")]
    fn preimage_coordinates(&self, coordinates: Vec<i64>) -> PyResult<Vec<u64>> {
        if coordinates.len() != self.inner.endo().dim() {
            return Err(PyValueError::new_err(format!(
                "endomorphism coordinate count is {}, expected {}",
                coordinates.len(),
                self.inner.endo().dim()
            )));
        }
        let field = self.inner.target().field();
        let coordinates: Vec<Fp> = coordinates
            .into_iter()
            .map(|value| field.elem(value))
            .collect();
        Ok(row_u64(&self.inner.preimage_coordinates(&coordinates)))
    }

    /// Recomputes the source classification, target, and algebra map.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "TargetPresentation(vertices={}, arrows={}, dimension={})",
            self.inner.target().quiver().num_vertices(),
            self.inner.target().quiver().num_arrows(),
            self.inner.target().dim()
        )
    }
}

/// A certified target that is not split over the base prime field.
#[pyclass(name = "UnsupportedTarget", module = "auslander", frozen)]
pub(crate) struct PyUnsupportedTarget {
    pub(crate) inner: NonSplitTarget,
}

#[pymethods]
impl PyUnsupportedTarget {
    #[getter]
    fn module(&self) -> PyRightModule {
        self.inner.module().into()
    }

    #[getter]
    fn summand(&self) -> usize {
        self.inner.summand()
    }

    #[getter]
    fn residue_degree(&self) -> usize {
        self.inner.residue_degree()
    }

    #[getter]
    fn limits(&self) -> PyTargetLimits {
        PyTargetLimits {
            inner: self.inner.limits().clone(),
        }
    }

    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "UnsupportedTarget(summand={}, residue_degree={})",
            self.inner.summand(),
            self.inner.residue_degree()
        )
    }
}

pub(crate) fn target_stage_name(stage: TargetCutStage) -> String {
    match stage {
        TargetCutStage::EndoDimension => "endomorphism_dimension".to_string(),
        TargetCutStage::RadicalPower { power } => format!("radical_power:{power}"),
        TargetCutStage::RadicalCorner {
            source,
            target,
            power,
        } => format!("radical_corner:{source}:{target}:{power}"),
        TargetCutStage::Paths { length } => format!("paths:{length}"),
        TargetCutStage::Relations { source, target } => {
            format!("relations:{source}:{target}")
        }
    }
}

/// A target recovery stopped at its first rejected reservation.
#[pyclass(name = "IncompleteTargetPresentation", module = "auslander", frozen)]
pub(crate) struct PyIncompleteTargetPresentation {
    pub(crate) inner: TargetPresentationCut,
}

#[pymethods]
impl PyIncompleteTargetPresentation {
    #[getter]
    fn source(&self) -> PyRightModule {
        self.inner.source().into()
    }

    #[getter]
    fn limits(&self) -> PyTargetLimits {
        PyTargetLimits {
            inner: self.inner.limits().clone(),
        }
    }

    #[getter]
    fn tilting_limits(&self) -> PyTiltingLimits {
        PyTiltingLimits {
            inner: self.inner.tilting_limits(),
        }
    }

    /// The stopped ceiling: `target_budget` or `completion_budget`.
    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner.reason() {
            TargetCutReason::Budget(_) => "target_budget",
            TargetCutReason::Completion(_) => "completion_budget",
        }
    }

    /// The exact target stage, or the completion budget name.
    #[getter]
    fn stage(&self) -> String {
        match self.inner.reason() {
            TargetCutReason::Budget(cut) => target_stage_name(cut.stage),
            TargetCutReason::Completion(cut) => completion_reason_name(cut.reason).to_string(),
        }
    }

    /// The target stage kind without embedded indices.
    #[getter]
    fn stage_kind(&self) -> &'static str {
        match self.inner.reason() {
            TargetCutReason::Budget(cut) => match cut.stage {
                TargetCutStage::EndoDimension => "endomorphism_dimension",
                TargetCutStage::RadicalPower { .. } => "radical_power",
                TargetCutStage::RadicalCorner { .. } => "radical_corner",
                TargetCutStage::Paths { .. } => "paths",
                TargetCutStage::Relations { .. } => "relations",
            },
            TargetCutReason::Completion(_) => "completion",
        }
    }

    #[getter]
    fn power(&self) -> Option<usize> {
        match self.inner.reason() {
            TargetCutReason::Budget(cut) => match cut.stage {
                TargetCutStage::RadicalPower { power }
                | TargetCutStage::RadicalCorner { power, .. } => Some(power),
                _ => None,
            },
            TargetCutReason::Completion(_) => None,
        }
    }

    #[getter]
    fn source_vertex(&self) -> Option<u32> {
        match self.inner.reason() {
            TargetCutReason::Budget(cut) => match cut.stage {
                TargetCutStage::RadicalCorner { source, .. }
                | TargetCutStage::Relations { source, .. } => Some(source),
                _ => None,
            },
            TargetCutReason::Completion(_) => None,
        }
    }

    #[getter]
    fn target_vertex(&self) -> Option<u32> {
        match self.inner.reason() {
            TargetCutReason::Budget(cut) => match cut.stage {
                TargetCutStage::RadicalCorner { target, .. }
                | TargetCutStage::Relations { target, .. } => Some(target),
                _ => None,
            },
            TargetCutReason::Completion(_) => None,
        }
    }

    #[getter]
    fn path_length(&self) -> Option<usize> {
        match self.inner.reason() {
            TargetCutReason::Budget(cut) => match cut.stage {
                TargetCutStage::Paths { length } => Some(length),
                _ => None,
            },
            TargetCutReason::Completion(_) => None,
        }
    }

    /// Units reserved before a target-budget cut.
    #[getter]
    fn used(&self) -> Option<usize> {
        match self.inner.reason() {
            TargetCutReason::Budget(cut) => Some(cut.used),
            TargetCutReason::Completion(_) => None,
        }
    }

    /// Units requested by a rejected target reservation.
    #[getter]
    fn requested(&self) -> Option<usize> {
        match self.inner.reason() {
            TargetCutReason::Budget(cut) => Some(cut.requested),
            TargetCutReason::Completion(_) => None,
        }
    }

    /// The target budget that rejected the reservation.
    #[getter]
    fn limit(&self) -> Option<usize> {
        match self.inner.reason() {
            TargetCutReason::Budget(cut) => Some(cut.limit),
            TargetCutReason::Completion(_) => None,
        }
    }

    /// Completion basis size at a completion cut.
    #[getter]
    fn completion_basis_len(&self) -> Option<usize> {
        match self.inner.reason() {
            TargetCutReason::Budget(_) => None,
            TargetCutReason::Completion(cut) => Some(cut.basis_len),
        }
    }

    /// Pending completion ambiguities at a completion cut.
    #[getter]
    fn completion_pending_ambiguities(&self) -> Option<usize> {
        match self.inner.reason() {
            TargetCutReason::Budget(_) => None,
            TargetCutReason::Completion(cut) => Some(cut.pending_ambiguities),
        }
    }

    /// Completion work units consumed before a completion cut.
    #[getter]
    fn completion_steps_used(&self) -> Option<usize> {
        match self.inner.reason() {
            TargetCutReason::Budget(_) => None,
            TargetCutReason::Completion(cut) => Some(cut.steps_used),
        }
    }

    /// Repeats target recovery and requires the same first cut.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "IncompleteTargetPresentation(kind={:?}, stage={:?})",
            self.kind(),
            self.stage()
        )
    }
}

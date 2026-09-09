use super::*;

/// A classical tilting classification with one of three mathematical outcomes.
///
/// `is_tilting` is True for a certificate, False only for a positive
/// self-extension, and None when a caller bound or generation step blocks the
/// decision. Exactly one of `tilting`, `rejection`, and `blocker` is set.

#[pyclass(name = "ClassicalTiltingResult", module = "auslander", frozen)]
pub(crate) struct PyClassicalTiltingResult {
    pub(crate) inner: Arc<RustClassicalTiltingResult>,
}

#[pymethods]
impl PyClassicalTiltingResult {
    /// True, False, or None for a certified, rejected, or undetermined result.
    #[getter]
    fn is_tilting(&self) -> Option<bool> {
        match self.inner.as_ref() {
            RustClassicalTiltingResult::Tilting(_) => Some(true),
            RustClassicalTiltingResult::NotTilting(_) => Some(false),
            RustClassicalTiltingResult::Undetermined(_) => None,
        }
    }

    /// The accepted certificate, or None for the other two outcomes.
    #[getter]
    fn tilting(&self) -> Option<PyClassicalTiltingModule> {
        matches!(self.inner.as_ref(), RustClassicalTiltingResult::Tilting(_)).then(|| {
            PyClassicalTiltingModule {
                home: self.inner.clone(),
            }
        })
    }

    /// The first positive self-extension, or None when not rejected.
    #[getter]
    fn rejection(&self) -> Option<PyPositiveSelfExtension> {
        matches!(
            self.inner.as_ref(),
            RustClassicalTiltingResult::NotTilting(_)
        )
        .then(|| PyPositiveSelfExtension {
            home: self.inner.clone(),
        })
    }

    /// The projective-dimension or generation blocker, or None when decided.
    #[getter]
    fn blocker(&self) -> Option<PyTiltingBlocker> {
        matches!(
            self.inner.as_ref(),
            RustClassicalTiltingResult::Undetermined(_)
        )
        .then(|| PyTiltingBlocker {
            home: self.inner.clone(),
        })
    }

    /// Rechecks the proof data carried by the selected outcome.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| match self.inner.as_ref() {
            RustClassicalTiltingResult::Tilting(value) => value.verify(),
            RustClassicalTiltingResult::NotTilting(value) => value.verify(),
            RustClassicalTiltingResult::Undetermined(value) => value.verify(),
        })
    }

    fn __repr__(&self) -> &'static str {
        match self.inner.as_ref() {
            RustClassicalTiltingResult::Tilting(_) => "ClassicalTiltingResult(is_tilting=True)",
            RustClassicalTiltingResult::NotTilting(_) => "ClassicalTiltingResult(is_tilting=False)",
            RustClassicalTiltingResult::Undetermined(_) => {
                "ClassicalTiltingResult(is_tilting=None)"
            }
        }
    }
}

/// A basic module certified against all three classical tilting conditions.
#[pyclass(name = "ClassicalTiltingModule", module = "auslander", frozen)]
pub(crate) struct PyClassicalTiltingModule {
    pub(crate) home: Arc<RustClassicalTiltingResult>,
}

impl PyClassicalTiltingModule {
    pub(crate) fn inner(&self) -> &tilting::ClassicalTiltingModule {
        let RustClassicalTiltingResult::Tilting(inner) = self.home.as_ref() else {
            unreachable!("the wrapper is created only for a tilting outcome")
        };
        inner
    }
}

#[pymethods]
impl PyClassicalTiltingModule {
    /// Classifies a basic module under two independent bounds.
    #[staticmethod]
    #[pyo3(text_signature = "(module, limits)")]
    fn classify(
        py: Python<'_>,
        module: &PyRightModule,
        limits: &PyTiltingLimits,
    ) -> PyResult<PyClassicalTiltingResult> {
        let result = py
            .allow_threads(|| tilting::classify(&module.inner, limits.inner))
            .map_err(tilting_error)?;
        Ok(PyClassicalTiltingResult {
            inner: Arc::new(result),
        })
    }

    /// The certified basic module.
    #[getter]
    fn module(&self) -> PyRightModule {
        self.inner().module().into()
    }

    /// The exact projective dimension.
    #[getter]
    fn projective_dimension(&self) -> usize {
        self.inner().projective_dimension()
    }

    /// The limits used by this successful classification.
    #[getter]
    fn limits(&self) -> PyTiltingLimits {
        PyTiltingLimits {
            inner: self.inner().limits(),
        }
    }

    /// The complete minimal projective resolution.
    #[getter]
    fn resolution(&self) -> PyResolution {
        wrapped_resolution(self.inner().module(), self.inner().resolution())
    }

    /// The zero self-Ext spaces in degrees 1 through pd T.
    #[getter]
    fn ext_spaces(&self) -> Vec<PyExtSpace> {
        self.inner()
            .ext_spaces()
            .iter()
            .cloned()
            .map(|inner| PyExtSpace { inner })
            .collect()
    }

    /// The checked exact generation complex A -> T^0 -> ... -> T^n.
    #[getter]
    fn generation_complex(&self) -> PyExactComplex {
        PyExactComplex {
            inner: self.inner().generation_complex().clone(),
        }
    }

    /// One add(T) witness for each generation term after A.
    #[getter]
    fn add_witnesses(&self) -> Vec<PyAddClosureWitness> {
        self.inner()
            .add_witnesses()
            .iter()
            .cloned()
            .map(|inner| PyAddClosureWitness { inner })
            .collect()
    }

    /// A witness that `module` lies in `add(T)`, or None when it does not.
    ///
    /// A blocked decomposition raises `CertificationBlockedError`. The None
    /// result is exact once both decompositions are certified.
    #[pyo3(text_signature = "($self, module)")]
    fn add_closure_witness(
        &self,
        py: Python<'_>,
        module: &PyRightModule,
    ) -> PyResult<Option<PyAddClosureWitness>> {
        check_same_context(self.inner().module(), &module.inner)?;
        let target = py
            .allow_threads(|| BasicDecomposition::new(self.inner().module()))
            .map_err(basic_error)?;
        Ok(py
            .allow_threads(|| AddClosureWitness::from_module(&module.inner, &target))
            .map_err(basic_error)?
            .map(|inner| PyAddClosureWitness { inner }))
    }

    /// Recovers `End_A(T)^op` as a checked split bound quiver algebra.
    ///
    /// The result is `TargetPresentation` on success, `UnsupportedTarget`
    /// when a summand has residue degree greater than one, or
    /// `IncompleteTargetPresentation` when a caller ceiling stops the run.
    #[pyo3(text_signature = "($self, limits)")]
    fn target_presentation<'py>(
        &self,
        py: Python<'py>,
        limits: &PyTargetLimits,
    ) -> PyResult<Bound<'py, PyAny>> {
        match py
            .allow_threads(|| present_target(self.inner(), &limits.inner))
            .map_err(target_error)?
        {
            TargetPresentationOutcome::Presented(inner) => {
                Ok(Bound::new(py, PyTargetPresentation { inner })?.into_any())
            }
            TargetPresentationOutcome::Unsupported(inner) => {
                Ok(Bound::new(py, PyUnsupportedTarget { inner })?.into_any())
            }
            TargetPresentationOutcome::Cut(inner) => {
                Ok(Bound::new(py, PyIncompleteTargetPresentation { inner })?.into_any())
            }
        }
    }

    /// Recomputes the resolution, Ext spaces, generation route, and witnesses.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner().verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "ClassicalTiltingModule(projective_dimension={}, module_dims={:?})",
            self.inner().projective_dimension(),
            self.inner().module().dim_vector()
        )
    }
}

/// The first positive self-extension of a non-tilting candidate.
#[pyclass(name = "PositiveSelfExtension", module = "auslander", frozen)]
pub(crate) struct PyPositiveSelfExtension {
    pub(crate) home: Arc<RustClassicalTiltingResult>,
}

impl PyPositiveSelfExtension {
    fn inner(&self) -> &tilting::PositiveSelfExtension {
        let RustClassicalTiltingResult::NotTilting(inner) = self.home.as_ref() else {
            unreachable!("the wrapper is created only for a rejection")
        };
        inner
    }
}

#[pymethods]
impl PyPositiveSelfExtension {
    /// The rejected module.
    #[getter]
    fn module(&self) -> PyRightModule {
        self.inner().module().into()
    }

    /// The first positive degree with nonzero self-Ext.
    #[getter]
    fn degree(&self) -> usize {
        self.inner().degree()
    }

    /// The dimension of that Ext space.
    #[getter]
    fn dimension(&self) -> usize {
        self.inner().dimension()
    }

    /// The proved finite projective dimension.
    #[getter]
    fn projective_dimension(&self) -> usize {
        self.inner().projective_dimension()
    }

    /// The positive self-Ext space.
    #[getter]
    fn space(&self) -> PyExtSpace {
        PyExtSpace {
            inner: self.inner().space().clone(),
        }
    }

    /// The complete projective resolution used by the rejection.
    #[getter]
    fn resolution(&self) -> PyResolution {
        wrapped_resolution(self.inner().module(), self.inner().resolution())
    }

    /// Recomputes the finite resolution and every Ext space through the witness.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner().verify())
    }
}

/// A bound or generation step that leaves classical tilting undetermined.
#[pyclass(name = "TiltingBlocker", module = "auslander", frozen)]
pub(crate) struct PyTiltingBlocker {
    pub(crate) home: Arc<RustClassicalTiltingResult>,
}

impl PyTiltingBlocker {
    fn inner(&self) -> &TiltingBlocker {
        let RustClassicalTiltingResult::Undetermined(inner) = self.home.as_ref() else {
            unreachable!("the wrapper is created only for an undetermined outcome")
        };
        inner
    }
}

#[pymethods]
impl PyTiltingBlocker {
    /// `projective_dimension` or `generation`.
    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner() {
            TiltingBlocker::ProjectiveDimension(_) => "projective_dimension",
            TiltingBlocker::Generation(_) => "generation",
        }
    }

    /// The candidate module.
    #[getter]
    fn module(&self) -> PyRightModule {
        match self.inner() {
            TiltingBlocker::ProjectiveDimension(value) => value.module().into(),
            TiltingBlocker::Generation(value) => value.module().into(),
        }
    }

    /// The genuine projective-dimension lower bound, only for that blocker.
    #[getter]
    fn projective_dimension(&self) -> Option<PyBounded> {
        self.inner().projective_dimension().map(|value| PyBounded {
            inner: value.projective_dimension(),
        })
    }

    /// The requested projective-dimension bound, only for that blocker.
    #[getter]
    fn projective_dimension_bound(&self) -> Option<usize> {
        self.inner()
            .projective_dimension()
            .map(|value| value.bound())
    }

    /// The first blocked generation stage, only for a generation blocker.
    #[getter]
    fn stage(&self) -> Option<usize> {
        self.inner().generation().map(GenerationBlocker::stage)
    }

    /// The generation-step bound, only for a generation blocker.
    #[getter]
    fn max_generation_steps(&self) -> Option<usize> {
        self.inner().generation().map(GenerationBlocker::max_steps)
    }

    /// `non_monic` or `step_limit`, only for a generation blocker.
    #[getter]
    fn generation_kind(&self) -> Option<&'static str> {
        self.inner().generation().map(|value| match value {
            GenerationBlocker::NonMonic { .. } => "non_monic",
            GenerationBlocker::StepLimit { .. } => "step_limit",
        })
    }

    /// The checked maps built before the blocked generation stage.
    #[getter]
    fn partial_complex(&self) -> Option<PyCheckedComplex> {
        self.inner()
            .generation()
            .map(|value| value.partial_complex().into())
    }

    /// The nonzero kernel dimensions of a non-monic approximation.
    #[getter]
    fn kernel_dimension_vector(&self) -> Option<Vec<usize>> {
        self.inner()
            .generation()
            .and_then(GenerationBlocker::kernel_dimension_vector)
            .map(<[usize]>::to_vec)
    }

    /// The last nonzero cokernel dimensions of a step-limit blocker.
    #[getter]
    fn cokernel_dimension_vector(&self) -> Option<Vec<usize>> {
        self.inner()
            .generation()
            .and_then(GenerationBlocker::cokernel_dimension_vector)
            .map(<[usize]>::to_vec)
    }

    /// The last nonzero cokernel of a step-limit blocker.
    #[getter]
    fn cokernel(&self) -> Option<PyRightModule> {
        self.inner()
            .generation()
            .and_then(GenerationBlocker::cokernel)
            .map(Into::into)
    }

    /// Recomputes the stored cut or bounded generation route.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner().verify())
    }

    fn __repr__(&self) -> String {
        format!("TiltingBlocker(kind={:?})", self.kind())
    }
}

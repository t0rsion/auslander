use super::*;

#[path = "algebra_ops.rs"]
mod algebra_ops;

/// The field-free analysis of a named monomial family. Every family the
/// static constructors expose is finite dimensional, so the standard-path
/// enumeration cannot fail here.
pub(crate) fn analyzed(ideal: MonomialIdeal) -> MonomialPresentation {
    MonomialPresentation::new(ideal).expect("a named monomial family is finite dimensional")
}

/// How a Python `Algebra` holds its verified runtime algebras.
pub(crate) enum AlgebraKind {
    /// Field-free monomial data with one verified runtime algebra per field.
    Monomial {
        presentation: Box<MonomialPresentation>,
        per_field: Mutex<BTreeMap<u64, Arc<Algebra>>>,
    },
    /// A field-bound runtime algebra.
    General(Arc<Algebra>),
}

/// The bound quiver algebra kQ/I over a checked prime field.
///
/// Two kinds share this class. `Algebra(quiver, forbidden)` and the named
/// constructors build monomial presentations: forbidden words are lists of
/// arrow ids, each of length >= 2 and composable left to right. A constructor
/// can bind one field, or leave the presentation field-free. Each requested
/// field gets one verified runtime algebra, built on first use and cached.
///
/// `Algebra.from_relations` and `Algebra.from_certificate` build a
/// general-relation algebra. Its dimension and structure constants depend on
/// the field, so it is bound to the one field it was verified over and raises
/// ValueError for any other. `field` names that field, or is None for an
/// unbound monomial presentation.
///
/// Every runtime algebra passes completion and independent certificate
/// verification before use, so `dim` and the Cartan matrix are exact. Modules
/// interact (hom, ext) only when built from the same Algebra object over equal
/// fields.
#[pyclass(name = "Algebra", module = "auslander")]
pub(crate) struct PyAlgebra {
    pub(crate) kind: AlgebraKind,
}

impl PyAlgebra {
    fn wrap(presentation: MonomialPresentation) -> PyAlgebra {
        PyAlgebra {
            kind: AlgebraKind::Monomial {
                presentation: Box::new(presentation),
                per_field: Mutex::new(BTreeMap::new()),
            },
        }
    }

    fn from_presentation(
        py: Python<'_>,
        presentation: MonomialPresentation,
        field: Option<PrimeField>,
    ) -> PyResult<PyAlgebra> {
        match field {
            None => Ok(Self::wrap(presentation)),
            Some(field) => py
                .allow_threads(|| algebra::monomial_algebra(presentation.ideal(), field))
                .map_err(build_error)
                .map(Self::pinned),
        }
    }

    pub(crate) fn pinned(algebra: Arc<Algebra>) -> PyAlgebra {
        PyAlgebra {
            kind: AlgebraKind::General(algebra),
        }
    }

    /// The verified runtime algebra over `field`.
    pub(crate) fn over(&self, py: Python<'_>, field: PrimeField) -> PyResult<Arc<Algebra>> {
        match &self.kind {
            AlgebraKind::Monomial {
                presentation,
                per_field,
            } => {
                // A panic inside the crate must not brick this object, so a
                // poisoned lock hands back its data: the cache is a map of
                // verified algebras and no half-written state can reach it.
                let cached = per_field
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner)
                    .get(&field.modulus())
                    .cloned();
                if let Some(found) = cached {
                    return Ok(found);
                }
                // The lock is not held across the build. A second thread would
                // block on it while holding the GIL, and this one needs the GIL
                // back to return, which deadlocks both. Two threads may then
                // build the same field at once; the loser's algebra is dropped,
                // so one field keeps one Arc, which `check_same_context` reads.
                let built = py
                    .allow_threads(|| algebra::monomial_algebra(presentation.ideal(), field))
                    .map_err(build_error)?;
                Ok(per_field
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner)
                    .entry(field.modulus())
                    .or_insert(built)
                    .clone())
            }
            AlgebraKind::General(algebra) => {
                if algebra.field().modulus() == field.modulus() {
                    return Ok(algebra.clone());
                }
                Err(PyValueError::new_err(format!(
                    "this algebra was built over F_{} and cannot be used over F_{}",
                    algebra.field().modulus(),
                    field.modulus()
                )))
            }
        }
    }

    /// Selects the runtime algebra for a field-sensitive construction.
    /// Field-free presentations require `field`; bound algebras may omit it.
    pub(crate) fn algebra_for(
        &self,
        py: Python<'_>,
        field: Option<&PyPrimeField>,
        what: &str,
    ) -> PyResult<Arc<Algebra>> {
        match (&self.kind, field) {
            (AlgebraKind::General(algebra), None) => Ok(algebra.clone()),
            (_, Some(field)) => self.over(py, field.inner),
            (AlgebraKind::Monomial { .. }, None) => Err(PyValueError::new_err(format!(
                "this field-free algebra needs a field; pass a field to build {what}"
            ))),
        }
    }

    fn quiver_ref(&self) -> &Quiver {
        match &self.kind {
            AlgebraKind::Monomial { presentation, .. } => presentation.quiver(),
            AlgebraKind::General(algebra) => algebra.quiver(),
        }
    }

    fn check_vertex(&self, v: u32) -> PyResult<()> {
        let n = self.quiver_ref().num_vertices();
        if v >= n {
            return Err(PyValueError::new_err(format!(
                "vertex {v} out of range: the quiver has vertices 0..{n}"
            )));
        }
        Ok(())
    }
}

#[pymethods]
impl PyAlgebra {
    /// kQ/(forbidden) with a certified finite standard-path basis; raises ValueError
    /// when a forbidden word is too short or not a path, or when the algebra would
    /// be infinite-dimensional.
    #[new]
    #[pyo3(signature = (quiver, forbidden, field = None), text_signature = "(quiver, forbidden, field=None)")]
    fn new(
        py: Python<'_>,
        quiver: &PyQuiver,
        forbidden: Vec<Vec<u32>>,
        field: Option<&PyPrimeField>,
    ) -> PyResult<Self> {
        let forbidden: Vec<Vec<ArrowId>> = forbidden
            .into_iter()
            .map(|word| word.into_iter().map(ArrowId).collect())
            .collect();
        let ideal = MonomialIdeal::new(quiver.inner.clone(), forbidden).map_err(value_error)?;
        PyAlgebra::from_presentation(
            py,
            MonomialPresentation::new(ideal).map_err(value_error)?,
            field.map(|value| value.inner),
        )
    }

    /// kQ/I for a general admissible ideal over one prime field. Each relation
    /// is a list of (coefficient, path) terms; a path is a list of arrow ids
    /// composed left to right, and coefficients are integers reduced mod p.
    /// The terms of one relation must share one source and one target, every
    /// path needs length >= 2, and a coefficient that reduces to zero is
    /// rejected.
    ///
    /// Construction runs completion and verifies the emitted certificate. The
    /// result is bound to `field` and refuses any other. The optional keywords
    /// cap the completion budgets, and an exhausted budget raises
    /// TruncationError. Raises ValueError on a rejected relation and on an
    /// infinite-dimensional quotient, whose message carries a cyclic word
    /// witness.
    #[staticmethod]
    #[pyo3(signature = (quiver, relations, field, *, max_basis = None, max_word_len = None, max_steps = None, max_origin_terms = None, max_ambiguities = None))]
    // The five budgets are keyword-only Python arguments, so grouping them into
    // one struct would change the signature callers write.
    #[allow(clippy::too_many_arguments)]
    fn from_relations(
        py: Python<'_>,
        quiver: &PyQuiver,
        relations: Vec<Vec<(i64, Vec<u32>)>>,
        field: &PyPrimeField,
        max_basis: Option<usize>,
        max_word_len: Option<usize>,
        max_steps: Option<usize>,
        max_origin_terms: Option<usize>,
        max_ambiguities: Option<usize>,
    ) -> PyResult<PyAlgebra> {
        let f = field.inner;
        let mut checked = Vec::with_capacity(relations.len());
        for (i, terms) in relations.into_iter().enumerate() {
            let terms = terms
                .into_iter()
                .map(|(coeff, word)| (f.elem(coeff), word.into_iter().map(ArrowId).collect()))
                .collect();
            checked.push(
                Relation::new(&quiver.inner, f, terms)
                    .map_err(|e| PyValueError::new_err(format!("relation {i} rejected: {e}")))?,
            );
        }
        let presentation = Presentation::new(quiver.inner.clone(), f, checked)
            .map_err(|e| PyValueError::new_err(format!("relation rejected: {e}")))?;
        let limits = limits_from(
            max_basis,
            max_word_len,
            max_steps,
            max_origin_terms,
            max_ambiguities,
        );
        let built = py
            .allow_threads(|| Algebra::new(presentation, &limits))
            .map_err(build_error)?;
        Ok(PyAlgebra::pinned(built))
    }

    /// The algebra rebuilt from certificate bytes. The bytes are verified from
    /// scratch, then the algebra is built from the verified data alone. The
    /// result is bound to the certificate's field. An optional `field` checks
    /// that binding before construction.
    ///
    /// The optional keywords set the rebuilt algebra's completion limits, used
    /// only by later derived completions such as tau and the injective
    /// constructions; omitted keywords keep the defaults. Certificate bytes
    /// never carry budgets, because untrusted input must not choose resource
    /// envelopes. Preserving raised budgets across a reload therefore takes
    /// these explicit keywords. Raises ValueError with the verifier's message
    /// when the bytes fail any check, an infinite-dimensional quotient
    /// included.
    #[staticmethod]
    #[pyo3(signature = (json, *, field = None, max_basis = None, max_word_len = None, max_steps = None, max_origin_terms = None, max_ambiguities = None))]
    #[allow(
        clippy::too_many_arguments,
        reason = "PyO3 adds the GIL token to the explicit Python keyword limits"
    )]
    fn from_certificate(
        py: Python<'_>,
        json: &str,
        field: Option<&PyPrimeField>,
        max_basis: Option<usize>,
        max_word_len: Option<usize>,
        max_steps: Option<usize>,
        max_origin_terms: Option<usize>,
        max_ambiguities: Option<usize>,
    ) -> PyResult<PyAlgebra> {
        let limits = limits_from(
            max_basis,
            max_word_len,
            max_steps,
            max_origin_terms,
            max_ambiguities,
        );
        let verified = py
            .allow_threads(|| verify::verify(json))
            .map_err(value_error)?;
        if let Some(field) = field {
            let expected = verified.field().modulus();
            if expected != field.inner.modulus() {
                return Err(PyValueError::new_err(format!(
                    "the certificate is over F_{expected}, not F_{}",
                    field.inner.modulus()
                )));
            }
        }
        // A certificate can verify and still describe a non-admissible ideal, whose
        // arrow ideal never reaches zero. That is bad input, not a crate defect.
        let algebra = Algebra::from_verified_with_limits(verified, &limits).map_err(build_error)?;
        Ok(PyAlgebra::pinned(algebra))
    }

    /// Path algebra of linearly oriented A_n: vertices 0..n, arrows i -> i+1.
    #[staticmethod]
    #[pyo3(signature = (n, field = None), text_signature = "(n, field=None)")]
    fn linear_an(py: Python<'_>, n: usize, field: Option<&PyPrimeField>) -> PyResult<PyAlgebra> {
        PyAlgebra::from_presentation(
            py,
            analyzed(monomial::linear_an_ideal(n)),
            field.map(|value| value.inner),
        )
    }

    /// Kronecker-type algebra: vertices 0, 1 and m parallel arrows 0 -> 1;
    /// hereditary, dim = m + 2.
    #[staticmethod]
    #[pyo3(signature = (m, field = None), text_signature = "(m, field=None)")]
    fn kronecker(py: Python<'_>, m: usize, field: Option<&PyPrimeField>) -> PyResult<PyAlgebra> {
        PyAlgebra::from_presentation(
            py,
            analyzed(monomial::kronecker_ideal(m)),
            field.map(|value| value.inner),
        )
    }

    /// k[x]/(x^2): one vertex, one loop x, forbidden word xx.
    #[staticmethod]
    #[pyo3(signature = (field = None), text_signature = "(field=None)")]
    fn dual_numbers(py: Python<'_>, field: Option<&PyPrimeField>) -> PyResult<PyAlgebra> {
        PyAlgebra::from_presentation(
            py,
            analyzed(monomial::truncated_poly_ideal(2).expect("x^2 is an admissible relation")),
            field.map(|value| value.inner),
        )
    }

    /// k[x]/(x^n): one vertex, one loop x, forbidden word x^n; raises ValueError
    /// for n < 2 (the ideal would not be admissible).
    #[staticmethod]
    #[pyo3(signature = (n, field = None), text_signature = "(n, field=None)")]
    fn truncated_poly(
        py: Python<'_>,
        n: usize,
        field: Option<&PyPrimeField>,
    ) -> PyResult<PyAlgebra> {
        PyAlgebra::from_presentation(
            py,
            analyzed(monomial::truncated_poly_ideal(n).map_err(value_error)?),
            field.map(|value| value.inner),
        )
    }

    /// Linear Nakayama algebra over linearly oriented A_n with dim P_i = kupisch[i];
    /// raises ValueError on an invalid Kupisch series (needs kupisch[n-1] == 1,
    /// interior entries >= 2, and kupisch[i+1] >= kupisch[i] - 1).
    #[staticmethod]
    #[pyo3(signature = (kupisch, field = None), text_signature = "(kupisch, field=None)")]
    fn linear_nakayama(
        py: Python<'_>,
        kupisch: Vec<usize>,
        field: Option<&PyPrimeField>,
    ) -> PyResult<PyAlgebra> {
        PyAlgebra::from_presentation(
            py,
            analyzed(monomial::linear_nakayama_ideal(&kupisch).map_err(value_error)?),
            field.map(|value| value.inner),
        )
    }

    /// Cyclic Nakayama algebra over the cycle 0 -> 1 -> ... -> n-1 -> 0 with
    /// dim P_i = kupisch[i]; raises ValueError on an invalid series (all entries
    /// >= 2 and cyclically kupisch[i+1] >= kupisch[i] - 1).
    #[staticmethod]
    #[pyo3(signature = (kupisch, field = None), text_signature = "(kupisch, field=None)")]
    fn cyclic_nakayama(
        py: Python<'_>,
        kupisch: Vec<usize>,
        field: Option<&PyPrimeField>,
    ) -> PyResult<PyAlgebra> {
        PyAlgebra::from_presentation(
            py,
            analyzed(monomial::cyclic_nakayama_ideal(&kupisch).map_err(value_error)?),
            field.map(|value| value.inner),
        )
    }

    /// Cyclic quiver on n vertices with rad^2 = 0: every length-2 path forbidden;
    /// dim = 2n.
    #[staticmethod]
    #[pyo3(signature = (n, field = None), text_signature = "(n, field=None)")]
    fn radical_square_zero_cycle(
        py: Python<'_>,
        n: usize,
        field: Option<&PyPrimeField>,
    ) -> PyResult<PyAlgebra> {
        PyAlgebra::from_presentation(
            py,
            analyzed(monomial::radical_square_zero_cycle_ideal(n)),
            field.map(|value| value.inner),
        )
    }

    /// Linearly oriented A_n with zero relations: each (start, length) pair kills
    /// the unique path of that length from vertex start. kA_3/(ab) is
    /// an_with_relations(3, [(0, 2)]). Raises ValueError when a zero path runs past
    /// the last vertex or has length < 2.
    #[staticmethod]
    #[pyo3(signature = (n, zero_paths, field = None), text_signature = "(n, zero_paths, field=None)")]
    fn an_with_relations(
        py: Python<'_>,
        n: usize,
        zero_paths: Vec<(usize, usize)>,
        field: Option<&PyPrimeField>,
    ) -> PyResult<PyAlgebra> {
        PyAlgebra::from_presentation(
            py,
            analyzed(monomial::an_with_relations_ideal(n, &zero_paths).map_err(value_error)?),
            field.map(|value| value.inner),
        )
    }

    /// dim_k of the algebra: the number of basis paths, trivial paths included.
    /// A monomial algebra reports its field-independent standard-path count; a
    /// general-relation algebra reports the normal-word count over its bound
    /// field.
    #[getter]
    fn dim(&self) -> usize {
        match &self.kind {
            AlgebraKind::Monomial { presentation, .. } => presentation.dim(),
            AlgebraKind::General(algebra) => algebra.dim(),
        }
    }

    /// The bound prime field, or None for a field-free monomial presentation.
    #[getter]
    fn field(&self) -> Option<PyPrimeField> {
        match &self.kind {
            AlgebraKind::Monomial { .. } => None,
            AlgebraKind::General(algebra) => Some(PyPrimeField {
                inner: algebra.field(),
            }),
        }
    }

    /// The effective completion limits as a dict with keys "max_basis",
    /// "max_word_len", "max_steps", "max_origin_terms", and "max_ambiguities".
    /// Derived completions (tau, injective
    /// envelopes, coresolutions, injective dimensions) run with them. A
    /// general-relation algebra reports its stored limits; a field-free
    /// monomial algebra reports the limits derived from its presentation.
    #[getter]
    fn completion_limits(&self) -> BTreeMap<&'static str, usize> {
        let limits = match &self.kind {
            AlgebraKind::Monomial { presentation, .. } => {
                algebra::monomial_limits(presentation.ideal())
            }
            AlgebraKind::General(algebra) => algebra.completion_limits().clone(),
        };
        BTreeMap::from([
            ("max_ambiguities", limits.max_ambiguities),
            ("max_basis", limits.max_basis),
            ("max_origin_terms", limits.max_origin_terms),
            ("max_steps", limits.max_steps),
            ("max_word_len", limits.max_word_len),
        ])
    }

    /// Number of vertices of the underlying quiver.
    #[getter]
    fn num_vertices(&self) -> u32 {
        self.quiver_ref().num_vertices()
    }

    /// Number of arrows of the underlying quiver (the length `module` expects of
    /// its maps argument).
    #[getter]
    fn num_arrows(&self) -> usize {
        self.quiver_ref().num_arrows()
    }

    /// The underlying quiver, as a fresh Quiver object; the argument the
    /// diagram-recognition functions take.
    #[getter]
    fn quiver(&self) -> PyQuiver {
        PyQuiver {
            inner: self.quiver_ref().clone(),
        }
    }

    /// The Cartan matrix C with C[i][j] = dim e_i A e_j, the number of basis
    /// paths i -> j; row i is the dimension vector of the projective P_i.
    #[pyo3(text_signature = "($self)")]
    fn cartan_matrix(&self) -> Vec<Vec<usize>> {
        match &self.kind {
            AlgebraKind::Monomial { presentation, .. } => presentation.cartan_matrix(),
            AlgebraKind::General(algebra) => algebra.cartan_matrix(),
        }
    }

    /// The valued Auslander-Reiten quiver of the algebra: one vertex per
    /// indecomposable of a complete enumeration, one arrow per nonzero space
    /// of irreducible maps.
    ///
    /// The enumeration route is fixed: Dynkin, Nakayama, then gentle tree. An
    /// unsupported algebra raises UnsupportedDomainError naming all three
    /// failed routes. The quiver is complete for its domain; no budget cuts it
    /// short. A general-relation algebra and a field-bound monomial algebra
    /// carry their field, so `field` may be omitted. An unbound monomial
    /// presentation requires it.
    #[pyo3(signature = (field = None))]
    fn ar_quiver(&self, py: Python<'_>, field: Option<&PyPrimeField>) -> PyResult<PyArQuiver> {
        let algebra = self.algebra_for(py, field, "an AR quiver")?;
        let quiver = py
            .allow_threads(|| arquiver::ar_quiver(&algebra))
            .map_err(ar_quiver_error)?;
        Ok(PyArQuiver {
            inner: Arc::new(quiver),
        })
    }

    /// Walks the support tau-tilting quiver from (A, 0) under left mutation
    /// and returns one of two classes.
    ///
    /// A walk whose frontier empties returns a
    /// ClosedSupportTauTiltingGraph, but only after the closure certificate
    /// passes its own recheck. Every slot of every vertex is decided, every
    /// left mutation lands inside the vertex set, and the recheck confirms
    /// both from the stored pairs and maps, so the vertex list is every basic
    /// support tau-tilting pair of the algebra up to isomorphism (Adachi,
    /// Iyama, and Reiten, Theorem 2.35(b) applied to a finite left-closed
    /// set). That class has `pairs()`. A recheck that fails raises
    /// GraphError instead, since it contradicts a theorem whose hypotheses
    /// hold.
    ///
    /// A walk that runs out of budget or hits a step it cannot certify returns
    /// an IncompleteSupportTauTiltingGraph, which has `vertices_found` and no
    /// `pairs()` accessor at all. Neither stop raises: both are values on that
    /// class, under `reason` and `diagnostics`. A truncated set is a biased
    /// sample of the quiver, not a nearly complete list.
    ///
    /// `limits` is a MutationGraphLimits; omitting it takes the defaults. A
    /// general-relation algebra carries its field, so `field` may be omitted;
    /// an unbound monomial presentation requires it.
    #[pyo3(signature = (field = None, *, limits = None))]
    fn support_tau_tilting_graph<'py>(
        &self,
        py: Python<'py>,
        field: Option<&PyPrimeField>,
        limits: Option<&PyMutationGraphLimits>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let algebra = self.algebra_for(py, field, "a mutation graph")?;
        let budgets = limits.map_or_else(MutationGraphLimits::default, |l| l.inner);
        let outcome = py
            .allow_threads(|| taugraph::support_tau_tilting_graph(&algebra, &budgets))
            .map_err(graph_error)?;
        match outcome {
            SupportTauTiltingGraphOutcome::Closed(inner) => Ok(Bound::new(
                py,
                PyClosedSupportTauTiltingGraph {
                    inner: Arc::new(inner),
                },
            )?
            .into_any()),
            SupportTauTiltingGraphOutcome::Incomplete(inner) => Ok(Bound::new(
                py,
                PyIncompleteSupportTauTiltingGraph {
                    inner: Arc::new(inner),
                },
            )?
            .into_any()),
        }
    }

    /// Lists every support tau-tilting pair of the algebra from the definition
    /// over an exhaustive catalog of its indecomposables.
    ///
    /// Completeness comes from the catalog's classification theorem and from
    /// nothing else. The module part of a basic pair is a direct sum of
    /// pairwise non-isomorphic indecomposables, so walking the subsets of a
    /// complete catalog reaches every pair. The catalog domains are path
    /// algebras of Dynkin type, Nakayama algebras, and gentle tree algebras.
    /// Any other algebra raises UnsupportedDomainError naming all failed
    /// routes.
    ///
    /// This route is independent of the mutation-graph certificate. It uses no
    /// mutation, no approximation, and no theorem about the support
    /// tau-tilting quiver: only Hom, tau, and the four conditions of a pair.
    /// When both routes produce the same list, that is evidence, not one route
    /// restating the other.
    /// A field-bound algebra omits `field`; an unbound monomial presentation
    /// requires it.
    #[pyo3(signature = (field = None))]
    fn enumerate_over_catalog(
        &self,
        py: Python<'_>,
        field: Option<&PyPrimeField>,
    ) -> PyResult<PyCatalogEnumeration> {
        let algebra = self.algebra_for(py, field, "a catalog enumeration")?;
        let catalog = py
            .allow_threads(|| IndecomposableCatalog::complete(&algebra))
            .map_err(|error| UnsupportedDomainError::new_err(error.to_string()))?;
        Ok(PyCatalogEnumeration {
            inner: Arc::new(
                py.allow_threads(|| supporttau::enumerate_over_catalog(&catalog))
                    .map_err(support_tau_error)?,
            ),
        })
    }

    fn __repr__(&self) -> String {
        match &self.kind {
            AlgebraKind::Monomial { presentation, .. } => format!(
                "Algebra(dim={}, vertices={})",
                presentation.dim(),
                presentation.quiver().num_vertices()
            ),
            AlgebraKind::General(algebra) => format!(
                "Algebra(dim={}, vertices={}, field=F_{})",
                algebra.dim(),
                algebra.quiver().num_vertices(),
                algebra.field().modulus()
            ),
        }
    }
}

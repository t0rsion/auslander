use super::*;

/// The field-free analysis of a named monomial family. Every family the
/// static constructors expose is finite dimensional, so the standard-path
/// enumeration cannot fail here.
pub(crate) fn analyzed(ideal: MonomialIdeal) -> MonomialPresentation {
    MonomialPresentation::new(ideal).expect("a named monomial family is finite dimensional")
}

/// How a Python Algebra holds its verified runtime algebras.
pub(crate) enum AlgebraKind {
    /// Field-free monomial combinatorics. Each field gets one verified
    /// runtime algebra, built on first use and cached.
    Monomial {
        presentation: Box<MonomialPresentation>,
        per_field: Mutex<BTreeMap<u64, Arc<Algebra>>>,
    },
    /// A general-relation algebra, bound to the one field it was verified
    /// over.
    General(Arc<Algebra>),
}

/// The bound quiver algebra kQ/I over a checked prime field.
///
/// Two kinds share this class. `Algebra(quiver, forbidden)` and the named
/// constructors build a monomial algebra: forbidden words are lists of arrow
/// ids, each of length >= 2 (admissibility) and composable left to right. A
/// monomial presentation is field-free, so a field enters only when building
/// modules, and each field gets one verified runtime algebra, built on first
/// use and cached.
///
/// `Algebra.from_relations` and `Algebra.from_certificate` build a
/// general-relation algebra. Its dimension and structure constants depend on
/// the field, so it is bound to the one field it was verified over and raises
/// ValueError for any other. `field` names that field, and is None for a
/// monomial algebra.
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

    pub(crate) fn pinned(algebra: Arc<Algebra>) -> PyAlgebra {
        PyAlgebra {
            kind: AlgebraKind::General(algebra),
        }
    }

    /// The verified runtime algebra over `field`. A monomial algebra builds
    /// one per field on first use and caches it; a general-relation algebra
    /// returns its own and raises ValueError for any other field.
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
                    "this algebra was built over F_{}; a general-relation algebra is \
                     field-dependent, so it cannot be used over F_{}",
                    algebra.field().modulus(),
                    field.modulus()
                )))
            }
        }
    }

    /// The runtime algebra for a construction that no field-free presentation
    /// can serve. A general-relation algebra carries its field, so `field` may
    /// be None; a monomial one needs it and raises ValueError otherwise. `what`
    /// names the construction in that message ("a certificate", "an AR
    /// quiver").
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
                "a monomial presentation is field-free and {what} is not; \
                 pass a field to build {what} over it"
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
    #[pyo3(text_signature = "(quiver, forbidden)")]
    fn new(quiver: &PyQuiver, forbidden: Vec<Vec<u32>>) -> PyResult<Self> {
        let forbidden: Vec<Vec<ArrowId>> = forbidden
            .into_iter()
            .map(|word| word.into_iter().map(ArrowId).collect())
            .collect();
        let ideal = MonomialIdeal::new(quiver.inner.clone(), forbidden).map_err(value_error)?;
        Ok(PyAlgebra::wrap(
            MonomialPresentation::new(ideal).map_err(value_error)?,
        ))
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
    /// result is bound to the certificate's field, exactly like a
    /// `from_relations` algebra, whatever kind of algebra dumped the bytes.
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
    #[pyo3(signature = (json, *, max_basis = None, max_word_len = None, max_steps = None, max_origin_terms = None, max_ambiguities = None))]
    fn from_certificate(
        py: Python<'_>,
        json: &str,
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
        // A certificate can verify and still describe a non-admissible ideal, whose
        // arrow ideal never reaches zero. That is bad input, not a crate defect.
        let algebra = Algebra::from_verified_with_limits(verified, &limits).map_err(build_error)?;
        Ok(PyAlgebra::pinned(algebra))
    }

    /// Path algebra of linearly oriented A_n: vertices 0..n, arrows i -> i+1.
    #[staticmethod]
    #[pyo3(text_signature = "(n)")]
    fn linear_an(n: usize) -> PyAlgebra {
        PyAlgebra::wrap(analyzed(monomial::linear_an_ideal(n)))
    }

    /// Kronecker-type algebra: vertices 0, 1 and m parallel arrows 0 -> 1;
    /// hereditary, dim = m + 2.
    #[staticmethod]
    #[pyo3(text_signature = "(m)")]
    fn kronecker(m: usize) -> PyAlgebra {
        PyAlgebra::wrap(analyzed(monomial::kronecker_ideal(m)))
    }

    /// k[x]/(x^2): one vertex, one loop x, forbidden word xx.
    #[staticmethod]
    #[pyo3(text_signature = "()")]
    fn dual_numbers() -> PyAlgebra {
        PyAlgebra::wrap(analyzed(
            monomial::truncated_poly_ideal(2).expect("x^2 is an admissible relation"),
        ))
    }

    /// k[x]/(x^n): one vertex, one loop x, forbidden word x^n; raises ValueError
    /// for n < 2 (the ideal would not be admissible).
    #[staticmethod]
    #[pyo3(text_signature = "(n)")]
    fn truncated_poly(n: usize) -> PyResult<PyAlgebra> {
        Ok(PyAlgebra::wrap(analyzed(
            monomial::truncated_poly_ideal(n).map_err(value_error)?,
        )))
    }

    /// Linear Nakayama algebra over linearly oriented A_n with dim P_i = kupisch[i];
    /// raises ValueError on an invalid Kupisch series (needs kupisch[n-1] == 1,
    /// interior entries >= 2, and kupisch[i+1] >= kupisch[i] - 1).
    #[staticmethod]
    #[pyo3(text_signature = "(kupisch)")]
    fn linear_nakayama(kupisch: Vec<usize>) -> PyResult<PyAlgebra> {
        Ok(PyAlgebra::wrap(analyzed(
            monomial::linear_nakayama_ideal(&kupisch).map_err(value_error)?,
        )))
    }

    /// Cyclic Nakayama algebra over the cycle 0 -> 1 -> ... -> n-1 -> 0 with
    /// dim P_i = kupisch[i]; raises ValueError on an invalid series (all entries
    /// >= 2 and cyclically kupisch[i+1] >= kupisch[i] - 1).
    #[staticmethod]
    #[pyo3(text_signature = "(kupisch)")]
    fn cyclic_nakayama(kupisch: Vec<usize>) -> PyResult<PyAlgebra> {
        Ok(PyAlgebra::wrap(analyzed(
            monomial::cyclic_nakayama_ideal(&kupisch).map_err(value_error)?,
        )))
    }

    /// Cyclic quiver on n vertices with rad^2 = 0: every length-2 path forbidden;
    /// dim = 2n.
    #[staticmethod]
    #[pyo3(text_signature = "(n)")]
    fn radical_square_zero_cycle(n: usize) -> PyAlgebra {
        PyAlgebra::wrap(analyzed(monomial::radical_square_zero_cycle_ideal(n)))
    }

    /// Linearly oriented A_n with zero relations: each (start, length) pair kills
    /// the unique path of that length from vertex start. kA_3/(ab) is
    /// an_with_relations(3, [(0, 2)]). Raises ValueError when a zero path runs past
    /// the last vertex or has length < 2.
    #[staticmethod]
    #[pyo3(text_signature = "(n, zero_paths)")]
    fn an_with_relations(n: usize, zero_paths: Vec<(usize, usize)>) -> PyResult<PyAlgebra> {
        Ok(PyAlgebra::wrap(analyzed(
            monomial::an_with_relations_ideal(n, &zero_paths).map_err(value_error)?,
        )))
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

    /// The bound prime field of a general-relation algebra; None for a
    /// monomial algebra, which pairs with any field.
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

    /// The canonical JSON bytes of the verified completion certificate; feed
    /// them to Algebra.from_certificate to rebuild the algebra. A
    /// general-relation algebra serializes its own certificate, and `field`
    /// must be omitted or equal to the bound field. A monomial presentation is
    /// field-free and a certificate is not, so a monomial algebra requires
    /// `field` and serializes the certificate of its algebra over that field.
    #[pyo3(signature = (field = None))]
    fn certificate_json(&self, py: Python<'_>, field: Option<&PyPrimeField>) -> PyResult<String> {
        let algebra = self.algebra_for(py, field, "a certificate")?;
        Ok(algebra.certificate().to_canonical_json())
    }

    /// A right module from raw data: dims[v] is the dimension at vertex v, and
    /// maps[a] is a dims[source(a)] x dims[target(a)] integer matrix (list of rows)
    /// for arrow a, acting on row vectors; entries are reduced mod p. A path acts
    /// by the product of its arrow matrices in left-to-right word order. Raises
    /// ValueError when shapes disagree with the quiver or a relation acts as a
    /// nonzero matrix.
    #[pyo3(text_signature = "($self, field, dims, maps)")]
    fn module(
        &self,
        py: Python<'_>,
        field: &PyPrimeField,
        dims: Vec<usize>,
        maps: Vec<Vec<Vec<i64>>>,
    ) -> PyResult<PyRightModule> {
        let f = field.inner;
        let algebra = self.over(py, f)?;
        let quiver = algebra.quiver();
        let mut mats = Vec::with_capacity(maps.len());
        for (i, rows) in maps.iter().enumerate() {
            // The expected column count, so that e.g. dims [0, 1] accepts maps [[]].
            let cols = quiver
                .arrows()
                .get(i)
                .and_then(|&(_, t)| dims.get(t as usize).copied())
                .unwrap_or(0);
            mats.push(dense_from_rows(
                f,
                rows,
                cols,
                &format!("map for arrow {i}"),
            )?);
        }
        Ok(Module::new(algebra, dims, mats)
            .map_err(value_error)?
            .into())
    }

    /// A right module from sparse arrow matrices. `maps[a]` is a list of
    /// `(row, column, value)` entries for arrow `a`. Omitted coordinates are
    /// zero, values are reduced mod p, and repeated coordinates are rejected.
    #[pyo3(text_signature = "($self, field, dims, maps)")]
    fn module_sparse(
        &self,
        py: Python<'_>,
        field: &PyPrimeField,
        dims: Vec<usize>,
        maps: Vec<Vec<(usize, usize, i64)>>,
    ) -> PyResult<PyRightModule> {
        let algebra = self.over(py, field.inner)?;
        let quiver = algebra.quiver();
        check_sparse_module_shape(quiver, &dims, maps.len())?;
        let matrices = maps
            .iter()
            .enumerate()
            .map(|(arrow, entries)| {
                let (source, target) = quiver.arrows()[arrow];
                dense_from_sparse(
                    field.inner,
                    dims[source as usize],
                    dims[target as usize],
                    entries,
                    &format!("map for arrow {arrow}"),
                )
            })
            .collect::<PyResult<Vec<_>>>()?;
        Ok(Module::new(algebra, dims, matrices)
            .map_err(value_error)?
            .into())
    }

    /// The simple module S_v: one-dimensional at v, zero elsewhere, all arrows
    /// acting as zero. Raises ValueError when v is not a vertex.
    #[pyo3(text_signature = "($self, field, v)")]
    fn simple(&self, py: Python<'_>, field: &PyPrimeField, v: u32) -> PyResult<PyRightModule> {
        self.check_vertex(v)?;
        Ok(Module::simple(&self.over(py, field.inner)?, v).into())
    }

    /// The indecomposable projective P_v = e_v A: its basis at vertex w is the set
    /// of standard paths v -> w. Raises ValueError when v is not a vertex.
    #[pyo3(text_signature = "($self, field, v)")]
    fn projective(&self, py: Python<'_>, field: &PyPrimeField, v: u32) -> PyResult<PyRightModule> {
        self.check_vertex(v)?;
        Ok(Module::projective(&self.over(py, field.inner)?, v).into())
    }

    /// The valued Auslander-Reiten quiver of the algebra: one vertex per
    /// indecomposable of a complete enumeration, one arrow per nonzero space
    /// of irreducible maps.
    ///
    /// The enumeration route is fixed. A zero ideal over a quiver of Dynkin
    /// shape takes the Gabriel enumeration, any other Nakayama algebra takes
    /// the Nakayama enumeration, and any other algebra raises
    /// UnsupportedDomainError naming both failed routes. The quiver is
    /// complete for its domain; no budget cuts it short. A general-relation
    /// algebra carries its field, so `field` may be omitted; a monomial
    /// presentation is field-free and needs it.
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
    /// a monomial presentation is field-free and needs it.
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

    /// Computes relative normalized bar Hochschild cohomology through one
    /// degree under four explicit resource ceilings.
    ///
    /// A finished request returns HochschildCohomology. A ceiling or checked
    /// size overflow returns IncompleteHochschildCohomology with the exact
    /// completed prefix and first rejected reservation. A cut never raises.
    #[pyo3(text_signature = "($self, field, max_degree, limits)")]
    fn hochschild_cohomology<'py>(
        &self,
        py: Python<'py>,
        field: &PyPrimeField,
        max_degree: usize,
        limits: &PyBarLimits,
    ) -> PyResult<Bound<'py, PyAny>> {
        let algebra = self.over(py, field.inner)?;
        match py
            .allow_threads(|| bar_hochschild(&algebra, max_degree, limits.inner))
            .map_err(hochschild_error)?
        {
            HochschildOutcome::Complete(inner) => {
                Ok(Bound::new(py, PyHochschildCohomology { inner })?.into_any())
            }
            HochschildOutcome::Cut(inner) => {
                Ok(Bound::new(py, PyIncompleteHochschildCohomology { inner })?.into_any())
            }
        }
    }

    /// Lists every support tau-tilting pair of the algebra from the definition
    /// over an exhaustive catalog of its indecomposables.
    ///
    /// Completeness comes from the catalog's classification theorem and from
    /// nothing else. The module part of a basic pair is a direct sum of
    /// pairwise non-isomorphic indecomposables, so walking the subsets of a
    /// complete catalog reaches every pair. Only the two catalog domains have
    /// such a list: a path algebra of Dynkin type by Gabriel's theorem, and a
    /// Nakayama algebra by the Nakayama classification. Any other algebra
    /// raises UnsupportedDomainError naming both failed routes.
    ///
    /// This route is independent of the mutation-graph certificate. It uses no
    /// mutation, no approximation, and no theorem about the support
    /// tau-tilting quiver: only Hom, tau, and the four conditions of a pair.
    /// When both routes produce the same list, that is evidence, not one route
    /// restating the other.
    #[pyo3(signature = (field = None))]
    fn enumerate_over_catalog(
        &self,
        py: Python<'_>,
        field: Option<&PyPrimeField>,
    ) -> PyResult<PyCatalogEnumeration> {
        let algebra = self.algebra_for(py, field, "a catalog enumeration")?;
        let catalog = py
            .allow_threads(|| match IndecomposableCatalog::dynkin(&algebra) {
                Ok(catalog) => Ok(catalog),
                Err(dynkin) => IndecomposableCatalog::nakayama(&algebra).map_err(|nakayama| {
                    format!(
                        "no complete enumeration applies: the Dynkin route reports {dynkin}, \
                         the Nakayama route reports {nakayama}"
                    )
                }),
            })
            .map_err(UnsupportedDomainError::new_err)?;
        Ok(PyCatalogEnumeration {
            inner: Arc::new(
                py.allow_threads(|| supporttau::enumerate_over_catalog(&catalog))
                    .map_err(support_tau_error)?,
            ),
        })
    }

    /// The indecomposable injective I_v = D(A e_v): its basis at vertex w is dual
    /// to the standard paths w -> v. Raises ValueError when v is not a vertex.
    #[pyo3(text_signature = "($self, field, v)")]
    fn injective(&self, py: Python<'_>, field: &PyPrimeField, v: u32) -> PyResult<PyRightModule> {
        self.check_vertex(v)?;
        Ok(Module::injective(&self.over(py, field.inner)?, v).into())
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

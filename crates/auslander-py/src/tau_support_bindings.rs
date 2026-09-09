use super::*;

/// The certified translates behind a tau-rigid module.
///
/// The module itself is not stored: it is the direct sum of `summands`.
/// `translates[j]` is tau of `summands[j]`. That translate is zero exactly
/// when the summand is projective. `vanishing_pairs` lists the ordered
/// summand positions `(i, j)` whose `Hom(X_i, tau X_j)` was checked zero:
/// every pair with a nonzero translate. A vanishing claim has no element to
/// exhibit, so those positions are the whole record and `verify` recomputes.
/// Instances are immutable and come only from `TauRigidity.vanishing`.

#[pyclass(name = "TauRigidModule", module = "auslander", frozen)]
pub(crate) struct PyTauRigidModule {
    pub(crate) inner: TauRigidModule,
}

#[pymethods]
impl PyTauRigidModule {
    /// The summands, in the order they were decomposed. An empty list is the
    /// zero module, which is tau-rigid with no pairs to check.
    #[getter]
    fn summands(&self) -> Vec<PyRightModule> {
        self.inner
            .summands()
            .iter()
            .map(|(_, x)| x.into())
            .collect()
    }

    /// tau of each summand, in summand order. Zero on a projective summand.
    #[getter]
    fn translates(&self) -> Vec<PyRightModule> {
        self.inner.translates().iter().map(|t| t.into()).collect()
    }

    /// The ordered summand pairs (i, j) whose Hom(X_i, tau X_j) was checked
    /// zero, in lexicographic order. A pair with tau X_j = 0 is not listed.
    #[getter]
    fn vanishing_pairs(&self) -> Vec<(usize, usize)> {
        self.inner.vanishing_pairs()
    }

    /// Whether the certified module is the zero module.
    #[getter]
    fn is_zero_module(&self) -> bool {
        self.inner.is_zero_module()
    }

    /// Recomputes every translate through the certified double route and
    /// rebuilds every Hom space, then requires each one to vanish again.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "TauRigidModule(summands={}, vanishing_pairs={})",
            self.inner.summands().len(),
            self.inner.vanishing_pairs().len()
        )
    }
}

/// The outcome of `Module.tau_rigidity`, witnessed either way.
///
/// `is_tau_rigid` True comes with `vanishing`, a TauRigidModule holding one
/// certified translate per summand and the positions of the ordered summand
/// pairs it checked. False comes with `morphism`, a nonzero X_i -> tau X_j,
/// which is a nonzero element of Hom(M, tau M) by additivity of tau and Hom.
/// Neither branch is a failure and neither raises. Instances are immutable.
#[pyclass(name = "TauRigidity", module = "auslander", frozen)]
pub(crate) struct PyTauRigidity {
    pub(crate) outcome: TauRigidityOutcome,
}

impl PyTauRigidity {
    /// The negative branch's witness, or None on the positive branch.
    fn negative(&self) -> Option<&NonTauRigidWitness> {
        match &self.outcome {
            TauRigidityOutcome::TauRigid(_) => None,
            TauRigidityOutcome::NotTauRigid(w) => Some(w),
        }
    }
}

#[pymethods]
impl PyTauRigidity {
    /// Whether Hom(M, tau M) is zero.
    #[getter]
    fn is_tau_rigid(&self) -> bool {
        self.outcome.is_tau_rigid()
    }

    /// The certified TauRigidModule when `is_tau_rigid` is True; None
    /// otherwise.
    #[getter]
    fn vanishing(&self) -> Option<PyTauRigidModule> {
        match &self.outcome {
            TauRigidityOutcome::TauRigid(m) => Some(PyTauRigidModule { inner: m.clone() }),
            TauRigidityOutcome::NotTauRigid(_) => None,
        }
    }

    /// The nonzero morphism X_i -> tau X_j when `is_tau_rigid` is False; None
    /// otherwise. Its endpoints are the summand and the translate.
    #[getter]
    fn morphism(&self) -> Option<PyMorphism> {
        self.negative().map(|w| w.morphism().into())
    }

    /// The positions (i, j) of the summands the morphism runs between when
    /// `is_tau_rigid` is False; None otherwise.
    #[getter]
    fn summand_pair(&self) -> Option<(usize, usize)> {
        self.negative()
            .map(|w| (w.source_index(), w.target_index()))
    }

    /// Rechecks the witness of whichever branch this outcome carries, against
    /// freshly recomputed translates and Hom spaces.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| match &self.outcome {
            TauRigidityOutcome::TauRigid(m) => m.verify(),
            TauRigidityOutcome::NotTauRigid(w) => w.verify(),
        })
    }

    fn __repr__(&self) -> String {
        let answer = if self.is_tau_rigid() { "True" } else { "False" };
        format!("TauRigidity(is_tau_rigid={answer})")
    }
}

/// The condition a candidate pair failed, with the witness for that failure.
///
/// `condition()` is 1 to 4, numbered as in `docs/support-tau-tilting.md` section 6 and
/// checked in that order, so the rejection names the first condition that
/// failed. Condition 3 carries `witness`, the nonzero morphism
/// X_i -> tau X_j. Condition 2 carries `hom_from_projective` and condition 4
/// carries `summand_counts`, both dicts of counts. Condition 1 carries
/// nothing. A rejection is a mathematical answer, so it is a value here and
/// never an exception. Instances are immutable.
#[pyclass(name = "PairRejection", module = "auslander", frozen)]
pub(crate) struct PyPairRejection {
    pub(crate) inner: PairRejection,
}

#[pymethods]
impl PyPairRejection {
    /// The number of the failed condition, 1 to 4.
    #[pyo3(text_signature = "($self)")]
    fn condition(&self) -> u32 {
        self.inner.condition()
    }

    /// A stable tag for the condition: "different_algebras",
    /// "hom_from_projective_nonzero", "not_tau_rigid", or "summand_count".
    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner {
            PairRejection::DifferentAlgebras => "different_algebras",
            PairRejection::HomFromProjectiveNonzero { .. } => "hom_from_projective_nonzero",
            PairRejection::NotTauRigid(_) => "not_tau_rigid",
            PairRejection::SummandCount { .. } => "summand_count",
        }
    }

    /// The nonzero morphism X_i -> tau X_j that proves condition 3. None for
    /// the other three conditions, which are decided by identity and by
    /// counting. Condition 2 is one of them: `Hom(P_v, M) = M_v` for right
    /// modules, so `hom_from_projective` is the whole proof.
    #[getter]
    fn witness(&self) -> Option<PyMorphism> {
        match &self.inner {
            PairRejection::NotTauRigid(w) => Some(w.morphism().into()),
            _ => None,
        }
    }

    /// The counts behind condition 2 as a dict with keys "vertex" and "dim";
    /// None for the other conditions.
    ///
    /// The vertex lies in the support of P and `dim` is `dim M_v`, which for
    /// right modules is `dim Hom(P_v, M)`.
    #[getter]
    fn hom_from_projective(&self) -> Option<BTreeMap<&'static str, usize>> {
        match self.inner {
            PairRejection::HomFromProjectiveNonzero { vertex, dim } => {
                Some(BTreeMap::from([("dim", dim), ("vertex", vertex as usize)]))
            }
            _ => None,
        }
    }

    /// The counts behind condition 4 as a dict with keys "module", "projective",
    /// and "expected"; None for the other conditions.
    #[getter]
    fn summand_counts(&self) -> Option<BTreeMap<&'static str, usize>> {
        match self.inner {
            PairRejection::SummandCount {
                module,
                projective,
                expected,
            } => Some(BTreeMap::from([
                ("expected", expected),
                ("module", module),
                ("projective", projective),
            ])),
            _ => None,
        }
    }

    fn __str__(&self) -> String {
        self.inner.to_string()
    }

    fn __repr__(&self) -> String {
        format!(
            "PairRejection(condition={}, kind={:?})",
            self.condition(),
            self.kind()
        )
    }
}

/// Where a Python SupportTauTiltingPair reads its answer.
///
/// A classified candidate owns its answer. A pair inside a graph, a catalog
/// enumeration, or a mutation is addressed inside the value that holds it,
/// which the `Arc` keeps alive: the crate's pair type is not `Clone`.
pub(crate) enum PairHome {
    Classified(SupportTauTiltingClassification),
    Closed(Arc<ClosedSupportTauTiltingGraph>, usize),
    Partial(Arc<IncompleteSupportTauTiltingGraph>, usize),
    Catalog(Arc<CatalogEnumeration>, usize),
    Mutated(Arc<Mutation>),
}

impl PairHome {
    /// The certified pair, or None for a rejected candidate.
    fn pair(&self) -> Option<&SupportTauTiltingPair> {
        match self {
            PairHome::Classified(c) => c.pair(),
            PairHome::Closed(graph, i) => Some(graph.vertices()[*i].pair()),
            PairHome::Partial(graph, i) => Some(graph.vertices_found()[*i].pair()),
            PairHome::Catalog(listing, i) => Some(&listing.pairs()[*i]),
            PairHome::Mutated(mutation) => Some(mutation.target()),
        }
    }

    /// The failed condition, or None when the candidate is a pair. Only a
    /// classified candidate can be a rejection; every other home holds a pair
    /// the crate already certified.
    fn rejection(&self) -> Option<&PairRejection> {
        match self {
            PairHome::Classified(c) => c.rejection(),
            _ => None,
        }
    }
}

/// A candidate pair (M, P) classified against the four conditions of a support
/// tau-tilting pair.
///
/// `is_pair` True means all four hold: M and P share an algebra and are basic,
/// Hom(P, M) = 0, M is tau-rigid, and |M| + |P| = n. Then `module_summands`,
/// `projective_support`, and `is_tau_tilting` are set. False means one
/// condition failed, and `rejection` names it with the data behind it. A failed
/// condition is a mathematical answer, so it never raises. Instances are
/// immutable and come from `SupportTauTiltingPair.classify`, from a graph, from
/// a catalog enumeration, and from `Mutation.target`.
#[pyclass(name = "SupportTauTiltingPair", module = "auslander", frozen)]
pub(crate) struct PySupportTauTiltingPair {
    pub(crate) home: Arc<PairHome>,
}

#[pymethods]
impl PySupportTauTiltingPair {
    /// Classifies (M, P), where M is the direct sum of `modules` and P is the
    /// projective support `vertices`.
    ///
    /// An empty `modules` list is the zero module, so `classify(A, [], every
    /// vertex)` is the pair (0, A). A general-relation algebra carries its
    /// field, so `field` may be omitted; a monomial presentation is field-free
    /// and needs it. Raises ValueError when a module was built from another
    /// algebra object, when M is not basic, and when a vertex is out of range;
    /// raises CertificationBlockedError when a summand could not be certified.
    #[staticmethod]
    #[pyo3(signature = (algebra, modules, vertices, field = None))]
    fn classify(
        py: Python<'_>,
        algebra: &PyAlgebra,
        modules: Vec<PyRef<'_, PyRightModule>>,
        vertices: Vec<u32>,
        field: Option<&PyPrimeField>,
    ) -> PyResult<PySupportTauTiltingPair> {
        let algebra = algebra.algebra_for(py, field, "a support tau-tilting pair")?;
        let modules: Vec<Module> = modules.iter().map(|m| m.inner.clone()).collect();
        let (module, projective) = pair_parts(&algebra, &modules, &vertices)?;
        let classification = py
            .allow_threads(|| SupportTauTiltingPair::classify(module, projective))
            .map_err(support_tau_error)?;
        Ok(PySupportTauTiltingPair {
            home: Arc::new(PairHome::Classified(classification)),
        })
    }

    /// Whether every condition holds.
    #[getter]
    fn is_pair(&self) -> bool {
        self.home.pair().is_some()
    }

    /// The failed condition when `is_pair` is False; None otherwise.
    #[getter]
    fn rejection(&self) -> Option<PyPairRejection> {
        self.home
            .rejection()
            .map(|r| PyPairRejection { inner: r.clone() })
    }

    /// The indecomposable summands of M, in decomposition order; None for a
    /// rejection.
    #[getter]
    fn module_summands(&self) -> Option<Vec<PyRightModule>> {
        self.home.pair().map(|p| {
            p.module()
                .summands()
                .iter()
                .map(|x| x.module().into())
                .collect()
        })
    }

    /// The vertices of the projective support P, ascending; None for a
    /// rejection.
    #[getter]
    fn projective_support(&self) -> Option<Vec<u32>> {
        self.home.pair().map(|p| p.projective().vertices().to_vec())
    }

    /// Whether the projective part is empty, which makes M a tau-tilting
    /// module; None for a rejection.
    #[getter]
    fn is_tau_tilting(&self) -> Option<bool> {
        self.home.pair().map(SupportTauTiltingPair::is_tau_tilting)
    }

    /// |M| + |P|, which equals the number of vertices; None for a rejection.
    #[getter]
    fn summand_count(&self) -> Option<usize> {
        self.home.pair().map(SupportTauTiltingPair::summand_count)
    }

    /// Rechecks the answer this value carries.
    ///
    /// On a pair every condition is recomputed against the live parts: P is
    /// rebuilt from its support, Hom(P, M) is rebuilt, and every summand's tau
    /// runs again through the certified double route. On a rejection condition
    /// 3 rebuilds the Hom space its morphism lives in and condition 4 rechecks
    /// the counts. Conditions 1 and 2 store no live module to recheck against,
    /// so they report True.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| match (self.home.pair(), self.home.rejection()) {
            (Some(pair), _) => pair.verify(),
            (None, Some(PairRejection::NotTauRigid(w))) => w.verify(),
            (
                None,
                Some(PairRejection::SummandCount {
                    module,
                    projective,
                    expected,
                }),
            ) => module + projective != *expected,
            (None, _) => true,
        })
    }

    /// What module-summand slot `slot` admits: a Mutation, or a FacWitness
    /// proving X_j lies in Fac(M/X_j) and the slot therefore admits no left
    /// mutation.
    ///
    /// Neither outcome is a failure and neither raises. Raises ValueError when
    /// the slot is not a module summand and when this value is a rejection.
    #[pyo3(text_signature = "($self, slot)")]
    fn mutate_at<'py>(&self, py: Python<'py>, slot: usize) -> PyResult<Bound<'py, PyAny>> {
        let Some(pair) = self.home.pair() else {
            return Err(PyValueError::new_err(
                "this value is a rejection, not a pair, so it has no slots to mutate at",
            ));
        };
        match py
            .allow_threads(|| mutate_at(pair, slot))
            .map_err(mutation_error)?
        {
            SlotOutcome::NoLeftMutation(inner) => {
                Ok(Bound::new(py, PyFacWitness { inner })?.into_any())
            }
            SlotOutcome::LeftMutation(mutation) => Ok(Bound::new(
                py,
                PyMutation {
                    home: MutationHome::Own(Arc::new(*mutation)),
                },
            )?
            .into_any()),
        }
    }

    fn __repr__(&self) -> String {
        match (self.home.pair(), self.home.rejection()) {
            (Some(pair), _) => format!(
                "SupportTauTiltingPair(module_dims={:?}, projective_support={:?})",
                pair.module().dim_vectors(),
                pair.projective().vertices()
            ),
            (None, Some(rejection)) => format!(
                "SupportTauTiltingPair(rejected, condition={})",
                rejection.condition()
            ),
            (None, None) => "SupportTauTiltingPair(rejected)".to_string(),
        }
    }
}

/// A candidate pair (M, P) classified against the conditions of an almost
/// complete pair.
///
/// The conditions are those of a support tau-tilting pair with |M| + |P| = n - 1
/// in place of n, and they are numbered and reported the same way. An almost
/// complete pair has exactly two completions to a support tau-tilting pair
/// (Adachi, Iyama, and Reiten, Theorem 2.18), and those two completions are the
/// ends of a mutation. Instances are immutable and come from
/// `AlmostCompletePair.classify`.
#[pyclass(name = "AlmostCompletePair", module = "auslander", frozen)]
pub(crate) struct PyAlmostCompletePair {
    pub(crate) inner: AlmostCompleteClassification,
}

#[pymethods]
impl PyAlmostCompletePair {
    /// Classifies (M, P) against |M| + |P| = n - 1. Arguments and rejections
    /// are those of `SupportTauTiltingPair.classify`.
    #[staticmethod]
    #[pyo3(signature = (algebra, modules, vertices, field = None))]
    fn classify(
        py: Python<'_>,
        algebra: &PyAlgebra,
        modules: Vec<PyRef<'_, PyRightModule>>,
        vertices: Vec<u32>,
        field: Option<&PyPrimeField>,
    ) -> PyResult<PyAlmostCompletePair> {
        let algebra = algebra.algebra_for(py, field, "an almost complete pair")?;
        let modules: Vec<Module> = modules.iter().map(|m| m.inner.clone()).collect();
        let (module, projective) = pair_parts(&algebra, &modules, &vertices)?;
        Ok(PyAlmostCompletePair {
            inner: py
                .allow_threads(|| AlmostCompletePair::classify(module, projective))
                .map_err(support_tau_error)?,
        })
    }

    /// Whether every condition holds.
    #[getter]
    fn is_pair(&self) -> bool {
        self.inner.is_pair()
    }

    /// The failed condition when `is_pair` is False; None otherwise.
    #[getter]
    fn rejection(&self) -> Option<PyPairRejection> {
        self.inner
            .rejection()
            .map(|r| PyPairRejection { inner: r.clone() })
    }

    /// The indecomposable summands of M, in decomposition order; None for a
    /// rejection.
    #[getter]
    fn module_summands(&self) -> Option<Vec<PyRightModule>> {
        self.inner.pair().map(|p| {
            p.module()
                .summands()
                .iter()
                .map(|x| x.module().into())
                .collect()
        })
    }

    /// The vertices of the projective support P, ascending; None for a
    /// rejection.
    #[getter]
    fn projective_support(&self) -> Option<Vec<u32>> {
        self.inner
            .pair()
            .map(|p| p.projective().vertices().to_vec())
    }

    /// |M| + |P|, which equals the number of vertices minus one; None for a
    /// rejection.
    #[getter]
    fn summand_count(&self) -> Option<usize> {
        self.inner.pair().map(AlmostCompletePair::summand_count)
    }

    /// Rechecks the answer this value carries, as
    /// `SupportTauTiltingPair.verify` does.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| match (self.inner.pair(), self.inner.rejection()) {
            (Some(pair), _) => pair.verify(),
            (None, Some(PairRejection::NotTauRigid(w))) => w.verify(),
            (
                None,
                Some(PairRejection::SummandCount {
                    module,
                    projective,
                    expected,
                }),
            ) => module + projective != *expected,
            (None, _) => true,
        })
    }

    fn __repr__(&self) -> String {
        match (self.inner.pair(), self.inner.rejection()) {
            (Some(pair), _) => format!(
                "AlmostCompletePair(module_dims={:?}, projective_support={:?})",
                pair.module().dim_vectors(),
                pair.projective().vertices()
            ),
            (None, Some(rejection)) => format!(
                "AlmostCompletePair(rejected, condition={})",
                rejection.condition()
            ),
            (None, None) => "AlmostCompletePair(rejected)".to_string(),
        }
    }
}

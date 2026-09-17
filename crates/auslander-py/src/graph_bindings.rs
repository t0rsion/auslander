use super::*;

/// Budgets for one `Algebra.support_tau_tilting_graph` run.
///
/// Every keyword is optional and an omitted one keeps the default:
/// `max_vertices` 10000, `max_directed_mutations` 100000, `max_work_units`
/// 50000000, `max_matrix_entries` 4000000. Those defaults admit every finite
/// type through E_7, which has 4160 pairs, and stop before E_8's 25080. There
/// is no wall-clock limit: a time limit would make the outcome depend on the
/// machine, and the walk is required to be deterministic across processes and
/// platforms.
///
/// `max_work_units` is the one budget that covers the whole walk. The other
/// three each gate one kind of step, and none of them caps memory: in
/// particular `max_matrix_entries` gates one Hom system per slot, not the
/// largest system the walk allocates. Instances are immutable.

#[pyclass(name = "MutationGraphLimits", module = "auslander", frozen)]
pub(crate) struct PyMutationGraphLimits {
    pub(crate) inner: MutationGraphLimits,
}

#[pymethods]
impl PyMutationGraphLimits {
    /// MutationGraphLimits(*, max_vertices=None, max_directed_mutations=None,
    /// max_work_units=None, max_matrix_entries=None).
    #[new]
    #[pyo3(signature = (*, max_vertices = None, max_directed_mutations = None, max_work_units = None, max_matrix_entries = None))]
    fn new(
        max_vertices: Option<usize>,
        max_directed_mutations: Option<usize>,
        max_work_units: Option<u64>,
        max_matrix_entries: Option<usize>,
    ) -> Self {
        PyMutationGraphLimits {
            inner: graph_limits_from(
                max_vertices,
                max_directed_mutations,
                max_work_units,
                max_matrix_entries,
            ),
        }
    }

    /// Distinct vertices the walk may hold.
    #[getter]
    fn max_vertices(&self) -> usize {
        self.inner.max_vertices
    }

    /// Left-mutation edges the walk may record.
    #[getter]
    fn max_directed_mutations(&self) -> usize {
        self.inner.max_directed_mutations
    }

    /// Work units the walk may charge. A closed graph never reports more
    /// than this. The closure recheck that gates a closed graph is not
    /// charged here: it runs after the walk, over the result.
    #[getter]
    fn max_work_units(&self) -> u64 {
        self.inner.max_work_units
    }

    /// Entries of the Fac system Hom(U, X_j), checked before the mutation
    /// layer allocates it at a slot.
    ///
    /// This is not the largest Hom system the walk allocates. Fingerprinting,
    /// decomposition, target classification, and the systems inside tau all
    /// run without consulting it, because none of them can be sized before the
    /// call that builds it. `max_work_units` is what bounds those, by size as
    /// well as by call count.
    #[getter]
    fn max_matrix_entries(&self) -> usize {
        self.inner.max_matrix_entries
    }

    fn __repr__(&self) -> String {
        format!(
            "MutationGraphLimits(max_vertices={}, max_directed_mutations={}, \
             max_work_units={}, max_matrix_entries={})",
            self.inner.max_vertices,
            self.inner.max_directed_mutations,
            self.inner.max_work_units,
            self.inner.max_matrix_entries
        )
    }
}

/// What the walk had done when a budget ran out.
///
/// `limit` names the budget: "max_vertices", "max_directed_mutations",
/// "max_work_units", or "max_matrix_entries". Every field is a count the walk
/// owns, so two runs over one algebra with one limit set produce equal
/// diagnostics. Instances are immutable and come only from
/// `IncompleteSupportTauTiltingGraph.diagnostics`.
#[pyclass(name = "GraphBudgetDiagnostics", module = "auslander", frozen)]
pub(crate) struct PyGraphBudgetDiagnostics {
    pub(crate) inner: GraphBudgetDiagnostics,
}

#[pymethods]
impl PyGraphBudgetDiagnostics {
    /// The budget that ran out.
    #[getter]
    fn limit(&self) -> String {
        self.inner.limit().to_string()
    }

    /// Distinct vertices held when the limit was hit.
    #[getter]
    fn vertices_found(&self) -> usize {
        self.inner.vertices_found()
    }

    /// Module-summand slots decided, counting both branches.
    #[getter]
    fn verified_slots(&self) -> usize {
        self.inner.verified_slots()
    }

    /// Module-summand slots of the discovered vertices still undecided.
    #[getter]
    fn open_slots(&self) -> usize {
        self.inner.open_slots()
    }

    /// Left mutations that landed on a pair no vertex was isomorphic to.
    #[getter]
    fn new_vertices(&self) -> usize {
        self.inner.new_vertices()
    }

    /// Left mutations that landed on an existing vertex.
    #[getter]
    fn repeated_endpoints(&self) -> usize {
        self.inner.repeated_endpoints()
    }

    /// Vertices waiting in the breadth-first queue.
    #[getter]
    fn frontier(&self) -> usize {
        self.inner.frontier()
    }

    /// The vertex the walk was at.
    #[getter]
    fn vertex(&self) -> usize {
        self.inner.vertex()
    }

    /// The slot the walk was at, or None when the limit was hit between slots.
    #[getter]
    fn slot(&self) -> Option<usize> {
        self.inner.slot()
    }

    /// Work units charged.
    #[getter]
    fn work_units(&self) -> u64 {
        self.inner.work_units()
    }

    fn __str__(&self) -> String {
        self.inner.to_string()
    }

    fn __repr__(&self) -> String {
        format!(
            "GraphBudgetDiagnostics(limit={:?}, vertices_found={}, work_units={})",
            self.limit(),
            self.inner.vertices_found(),
            self.inner.work_units()
        )
    }
}

/// Where a certification was blocked, and why.
///
/// A blocker is never budget exhaustion. It means the crate could not certify a
/// step, so no completeness claim can rest on the walk. The three sources are an
/// undetermined split, an undetermined indecomposability gate, and an undecided
/// isomorphism test inside the tau cross-check. Instances are immutable and come
/// only from `IncompleteSupportTauTiltingGraph.diagnostics`.
#[pyclass(name = "CertificationBlocker", module = "auslander", frozen)]
pub(crate) struct PyCertificationBlocker {
    pub(crate) inner: CertificationBlocker,
}

#[pymethods]
impl PyCertificationBlocker {
    /// What could not be certified.
    #[getter]
    fn reason(&self) -> String {
        self.inner.reason().to_string()
    }

    /// The vertex the walk was at.
    #[getter]
    fn vertex(&self) -> usize {
        self.inner.vertex()
    }

    /// The slot the walk was at, or None when the block hit while building a
    /// vertex.
    #[getter]
    fn slot(&self) -> Option<usize> {
        self.inner.slot()
    }

    /// Distinct vertices held when the block hit.
    #[getter]
    fn vertices_found(&self) -> usize {
        self.inner.vertices_found()
    }

    /// Work units charged.
    #[getter]
    fn work_units(&self) -> u64 {
        self.inner.work_units()
    }

    fn __str__(&self) -> String {
        self.inner.to_string()
    }

    fn __repr__(&self) -> String {
        format!(
            "CertificationBlocker(vertex={}, slot={:?}, reason={:?})",
            self.inner.vertex(),
            self.inner.slot(),
            self.inner.reason()
        )
    }
}

/// A closed mutation graph: every basic support tau-tilting pair of the
/// algebra, with the certificate that the list is complete.
///
/// The walk ran from (A, 0) under left mutation until its frontier emptied,
/// then rechecked the certificate before this value existed. Every
/// module-summand slot of every vertex carries one of two things: a verified
/// left mutation whose target is a vertex of this set, or a certified
/// FacWitness proving that the slot admits no left mutation. A finite set with
/// that property is every basic support tau-tilting pair, up to isomorphism of
/// pairs (Adachi, Iyama, and Reiten, Theorem 2.35(b) applied to a finite
/// left-closed set). Distinctness is a proof too: two vertices are distinct
/// exactly when the pair isomorphism test proves them non-isomorphic.
/// Instances are immutable and come only from
/// `Algebra.support_tau_tilting_graph`, which runs `verify()` itself before
/// handing one back, so `pairs()` never reads a list the certificate rejects.
#[pyclass(name = "ClosedSupportTauTiltingGraph", module = "auslander", frozen)]
pub(crate) struct PyClosedSupportTauTiltingGraph {
    pub(crate) inner: Arc<ClosedSupportTauTiltingGraph>,
}

#[pymethods]
impl PyClosedSupportTauTiltingGraph {
    /// Every basic support tau-tilting pair of the algebra, in discovery order
    /// from (A, 0).
    #[pyo3(text_signature = "($self)")]
    fn pairs(&self) -> Vec<PySupportTauTiltingPair> {
        (0..self.inner.len())
            .map(|i| PySupportTauTiltingPair {
                home: Arc::new(PairHome::Closed(self.inner.clone(), i)),
            })
            .collect()
    }

    /// The left-mutation edges, in discovery order. Each carries its
    /// `source_vertex` and `target_vertex`.
    #[pyo3(text_signature = "($self)")]
    fn mutations(&self) -> Vec<PyMutation> {
        (0..self.inner.mutations().len())
            .map(|i| PyMutation {
                home: MutationHome::Closed(self.inner.clone(), i),
            })
            .collect()
    }

    /// Pair counts by |M|, indexed from zero to the number of vertices of the
    /// quiver.
    #[pyo3(text_signature = "($self)")]
    fn histogram(&self) -> Vec<usize> {
        self.inner.histogram()
    }

    /// Work units the walk charged, by call and by module size and never by
    /// time, so the count is the same in every profile and on every platform.
    /// It counts the walk and not the closure recheck that gates this object.
    #[pyo3(text_signature = "($self)")]
    fn work_units(&self) -> u64 {
        self.inner.work_units()
    }

    /// Rechecks the closure certificate: every vertex is a verified pair over
    /// this algebra, the vertices are pairwise non-isomorphic, every slot of
    /// every vertex carries a mutation or a Fac witness, and every mutation
    /// lands on a vertex of the set.
    ///
    /// This object cannot exist unless the same recheck already passed, so the
    /// answer is True or the crate has a defect. Call it to recheck a graph
    /// that crossed a process boundary, not to decide whether the list is
    /// complete.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    /// The number of pairs.
    fn __len__(&self) -> usize {
        self.inner.len()
    }

    fn __repr__(&self) -> String {
        format!(
            "ClosedSupportTauTiltingGraph(pairs={}, mutations={}, work_units={})",
            self.inner.len(),
            self.inner.mutations().len(),
            self.inner.work_units()
        )
    }
}

/// A mutation walk that stopped short of closure, with the part it certified.
///
/// There is no completeness claim here and no `pairs()` accessor. The vertices
/// are `vertices_found` and the edges are `verified_mutations`; each is
/// certified on its own, and `verify_parts()` rechecks them. `reason` is
/// "budget_exhausted" or "certification_blocked" and `diagnostics` carries the
/// counts of that stop.
///
/// A truncated set is a biased sample, not a nearly complete list. On a
/// tau-tilting infinite algebra the descending walk runs down one ray forever:
/// over the Kronecker algebra it descends the preprojective ray and reaches no
/// preinjective vertex at all. The safe direction holds, because at the moment
/// of truncation the deepest vertex still has an unvisited slot, so no false
/// completeness certificate is possible. Instances are immutable and come only
/// from `Algebra.support_tau_tilting_graph`.
#[pyclass(
    name = "IncompleteSupportTauTiltingGraph",
    module = "auslander",
    frozen
)]
pub(crate) struct PyIncompleteSupportTauTiltingGraph {
    pub(crate) inner: Arc<IncompleteSupportTauTiltingGraph>,
}

#[pymethods]
impl PyIncompleteSupportTauTiltingGraph {
    /// The pairs the walk reached, in discovery order from (A, 0). A part of
    /// the support tau-tilting quiver, not a list of every pair.
    #[getter]
    fn vertices_found(&self) -> Vec<PySupportTauTiltingPair> {
        (0..self.inner.vertices_found().len())
            .map(|i| PySupportTauTiltingPair {
                home: Arc::new(PairHome::Partial(self.inner.clone(), i)),
            })
            .collect()
    }

    /// The left mutations the walk verified.
    #[getter]
    fn verified_mutations(&self) -> Vec<PyMutation> {
        (0..self.inner.verified_mutations().len())
            .map(|i| PyMutation {
                home: MutationHome::Partial(self.inner.clone(), i),
            })
            .collect()
    }

    /// Why the walk stopped: "budget_exhausted" or "certification_blocked".
    #[getter]
    fn reason(&self) -> &'static str {
        match self.inner.reason() {
            IncompleteReason::BudgetExhausted(_) => "budget_exhausted",
            IncompleteReason::CertificationBlocked(_) => "certification_blocked",
        }
    }

    /// The counts of the stop: a GraphBudgetDiagnostics for an exhausted
    /// budget, a CertificationBlocker for a step that could not be certified.
    #[getter]
    fn diagnostics<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        match self.inner.reason() {
            IncompleteReason::BudgetExhausted(d) => {
                Ok(Bound::new(py, PyGraphBudgetDiagnostics { inner: d.clone() })?.into_any())
            }
            IncompleteReason::CertificationBlocked(b) => {
                Ok(Bound::new(py, PyCertificationBlocker { inner: b.clone() })?.into_any())
            }
        }
    }

    /// Work units charged before the walk stopped.
    #[pyo3(text_signature = "($self)")]
    fn work_units(&self) -> u64 {
        self.inner.work_units()
    }

    /// Rechecks each vertex and each mutation on its own. This is not a
    /// completeness check and cannot become one.
    #[pyo3(text_signature = "($self)")]
    fn verify_parts(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify_parts())
    }

    fn __repr__(&self) -> String {
        format!(
            "IncompleteSupportTauTiltingGraph(vertices_found={}, reason={:?}, work_units={})",
            self.inner.vertices_found().len(),
            self.reason(),
            self.inner.work_units()
        )
    }
}

/// Every support tau-tilting pair of one algebra, listed from the definition
/// over an exhaustive catalog of its indecomposables.
///
/// Completeness comes from the catalog's classification theorem. `provenance`
/// is "dynkin_zero_ideal", "nakayama", or "gentle_tree". `verify()` checks each
/// pair and pairwise distinctness. It does not recheck the classification
/// theorem.
///
/// This route is independent of the mutation-graph certificate: no mutation, no
/// approximation, no theorem about the support tau-tilting quiver, only Hom,
/// tau, and the four conditions of a pair. Instances are immutable and come only
/// from `Algebra.enumerate_over_catalog`.
#[pyclass(name = "CatalogEnumeration", module = "auslander", frozen)]
pub(crate) struct PyCatalogEnumeration {
    pub(crate) inner: Arc<CatalogEnumeration>,
}

#[pymethods]
impl PyCatalogEnumeration {
    /// The pairs, in walk order: module subsets in lexicographic order over
    /// catalog positions, and within one subset the projective supports in
    /// lexicographic order over vertices.
    #[pyo3(text_signature = "($self)")]
    fn pairs(&self) -> Vec<PySupportTauTiltingPair> {
        (0..self.inner.len())
            .map(|i| PySupportTauTiltingPair {
                home: Arc::new(PairHome::Catalog(self.inner.clone(), i)),
            })
            .collect()
    }

    /// The catalog provenance: `nakayama`, `dynkin_zero_ideal`, or `gentle_tree`.
    #[getter]
    fn provenance(&self) -> &'static str {
        match self.inner.provenance() {
            CatalogProvenance::Nakayama => "nakayama",
            CatalogProvenance::DynkinZeroIdeal => "dynkin_zero_ideal",
            CatalogProvenance::GentleTree => "gentle_tree",
        }
    }

    /// The number of catalog entries the walk ran over.
    #[getter]
    fn catalog_len(&self) -> usize {
        self.inner.catalog_len()
    }

    /// The number of subsets the depth-first search visited, counting the empty
    /// subset. Deterministic and profile-independent.
    #[getter]
    fn nodes_visited(&self) -> usize {
        self.inner.nodes_visited()
    }

    /// Pair counts by |M|, indexed from zero to the number of vertices.
    #[pyo3(text_signature = "($self)")]
    fn histogram(&self) -> Vec<usize> {
        self.inner.histogram()
    }

    /// Rechecks every pair and that the pairs are pairwise non-isomorphic.
    /// Completeness is the catalog's theorem and is not rechecked here.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    /// The number of pairs.
    fn __len__(&self) -> usize {
        self.inner.len()
    }

    fn __repr__(&self) -> String {
        format!(
            "CatalogEnumeration(pairs={}, provenance={:?}, catalog_len={})",
            self.inner.len(),
            self.provenance(),
            self.inner.catalog_len()
        )
    }
}

/// The witness placing one module in add(T): a summand-by-summand match against
/// the basic decomposition of T.
///
/// `module` is the module placed in add(T), `target` is T, and `summands` and
/// `target_summands` are their indecomposable summands. `verify()` rechecks
/// every match by composing the two morphisms both ways. Instances are
/// immutable.
#[pyclass(name = "AddClosureWitness", module = "auslander", frozen)]
pub(crate) struct PyAddClosureWitness {
    pub(crate) inner: AddClosureWitness,
}

#[pymethods]
impl PyAddClosureWitness {
    /// The module placed in add(T).
    #[getter]
    fn module(&self) -> PyRightModule {
        self.inner.module().into()
    }

    /// T, the module whose add closure the placement is against.
    #[getter]
    fn target(&self) -> PyRightModule {
        self.inner.target().into()
    }

    /// The indecomposable summands of `module`, in decomposition order.
    #[getter]
    fn summands(&self) -> Vec<PyRightModule> {
        wrap_all(self.inner.summands())
    }

    /// The indecomposable summands of T, in decomposition order.
    #[getter]
    fn target_summands(&self) -> Vec<PyRightModule> {
        wrap_all(self.inner.target_summands())
    }

    /// The summand of T each summand of `module` matched, in summand order.
    #[getter]
    fn matches(&self) -> Vec<usize> {
        self.inner
            .matches()
            .iter()
            .map(|m| m.target_index())
            .collect()
    }

    /// Rechecks every stored match against the live modules.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "AddClosureWitness(module_dims={:?}, target_dims={:?}, matches={})",
            self.inner.module().dim_vector(),
            self.inner.target().dim_vector(),
            self.inner.matches().len()
        )
    }
}

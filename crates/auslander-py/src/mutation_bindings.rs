use super::*;

/// The proof that X_j lies in Fac(M/X_j), so slot j admits no left mutation.
///
/// X lies in Fac(U) exactly when finitely many maps U -> X have images summing
/// to all of X. `maps` is that family and `image_dims` is the dimension of the
/// sum at each vertex, which equals the dimension vector of X_j. The witness
/// does not claim the family spans Hom(U, X_j): spanning is stronger than the
/// definition of Fac and nothing here needs it. By Adachi, Iyama, and Reiten,
/// Definition-Proposition 2.28, the mutation at this slot is then a right
/// mutation. This is a statement about the slot, not a failure. Instances are
/// immutable.

#[pyclass(name = "FacWitness", module = "auslander", frozen)]
pub(crate) struct PyFacWitness {
    pub(crate) inner: FacWitness,
}

#[pymethods]
impl PyFacWitness {
    /// U = M/X_j, the module part with the slot summand dropped.
    #[getter]
    fn module(&self) -> PyRightModule {
        self.inner.module().into()
    }

    /// X_j, the summand the slot addresses.
    #[getter]
    fn summand(&self) -> PyRightModule {
        self.inner.summand().into()
    }

    /// The maps U -> X_j whose images were summed.
    #[getter]
    fn maps(&self) -> Vec<PyMorphism> {
        wrap_all(self.inner.maps())
    }

    /// The dimension of the sum of the images at each vertex.
    #[getter]
    fn image_dims(&self) -> Vec<usize> {
        self.inner.image_dims().to_vec()
    }

    /// Recomputes the rank equality from the stored maps: U is the direct sum
    /// of the stored summands, every map runs from U to X_j, and the images
    /// sum to the dimension vector of X_j at every vertex. No Hom space is
    /// rebuilt. A dropped map fails as soon as the remaining images stop
    /// covering X_j.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "FacWitness(module_dims={:?}, summand_dims={:?}, maps={})",
            self.inner.module().dim_vector(),
            self.inner.summand().dim_vector(),
            self.inner.maps().len()
        )
    }
}

/// Where a Python Mutation reads its data: a standalone `mutate_at` result, or
/// an edge inside a graph.
pub(crate) enum MutationHome {
    Own(Arc<Mutation>),
    Closed(Arc<ClosedSupportTauTiltingGraph>, usize),
    Partial(Arc<IncompleteSupportTauTiltingGraph>, usize),
}

impl MutationHome {
    fn mutation(&self) -> &Mutation {
        match self {
            MutationHome::Own(mutation) => mutation,
            MutationHome::Closed(graph, i) => graph.mutations()[*i].mutation(),
            MutationHome::Partial(graph, i) => graph.verified_mutations()[*i].mutation(),
        }
    }

    /// The graph edge this mutation is, or None for a standalone mutation.
    fn edge(&self) -> Option<&VerifiedMutation> {
        match self {
            MutationHome::Own(_) => None,
            MutationHome::Closed(graph, i) => Some(&graph.mutations()[*i]),
            MutationHome::Partial(graph, i) => Some(&graph.verified_mutations()[*i]),
        }
    }

    /// The pair the mutation lands on. Inside a graph that is the stored
    /// vertex, bound to the mutation's own target by a checked isomorphism.
    fn target(&self) -> PairHome {
        match self {
            MutationHome::Own(mutation) => PairHome::Mutated(mutation.clone()),
            MutationHome::Closed(graph, i) => {
                PairHome::Closed(graph.clone(), graph.mutations()[*i].target())
            }
            MutationHome::Partial(graph, i) => {
                PairHome::Partial(graph.clone(), graph.verified_mutations()[*i].target())
            }
        }
    }
}

/// A left mutation at one module-summand slot, with the pair it lands on.
///
/// The exchange takes one of two shapes (Adachi, Iyama, and Reiten, Theorem
/// 2.30). `shape` "moves_to_projective" drops X_j from the module part and adds
/// `exchanged_vertex` to the projective support; "replaced_by_module" keeps the
/// support and puts `multiplicity` copies of one indecomposable into the module
/// part. `source_vertex` and `target_vertex` are the graph vertex indices of an
/// edge and are None for a mutation taken on its own. Instances are immutable.
#[pyclass(name = "Mutation", module = "auslander", frozen)]
pub(crate) struct PyMutation {
    pub(crate) home: MutationHome,
}

#[pymethods]
impl PyMutation {
    /// The module-summand slot the mutation was taken at.
    #[getter]
    fn slot(&self) -> usize {
        self.home.mutation().slot()
    }

    /// "moves_to_projective" or "replaced_by_module".
    #[getter]
    fn shape(&self) -> &'static str {
        match self.home.mutation().shape() {
            ExchangeShape::MovesToProjective { .. } => "moves_to_projective",
            ExchangeShape::ReplacedByModule { .. } => "replaced_by_module",
        }
    }

    /// The vertex that joins the projective support, for a
    /// "moves_to_projective" mutation; None otherwise.
    #[getter]
    fn exchanged_vertex(&self) -> Option<u32> {
        match self.home.mutation().shape() {
            ExchangeShape::MovesToProjective { vertex } => Some(*vertex),
            ExchangeShape::ReplacedByModule { .. } => None,
        }
    }

    /// The number of cokernel summands, for a "replaced_by_module" mutation;
    /// None otherwise.
    #[getter]
    fn multiplicity(&self) -> Option<usize> {
        match self.home.mutation().shape() {
            ExchangeShape::ReplacedByModule { multiplicity } => Some(*multiplicity),
            ExchangeShape::MovesToProjective { .. } => None,
        }
    }

    /// The pair the mutation lands on. Inside a graph that is the pair stored
    /// at `target_vertex`, which a checked isomorphism binds to the mutation's
    /// own target.
    #[getter]
    fn target(&self) -> PySupportTauTiltingPair {
        PySupportTauTiltingPair {
            home: Arc::new(self.home.target()),
        }
    }

    /// The graph vertex the mutation starts from; None for a mutation taken
    /// outside a graph.
    #[getter]
    fn source_vertex(&self) -> Option<usize> {
        self.home.edge().map(VerifiedMutation::source)
    }

    /// The graph vertex the mutation lands on; None for a mutation taken
    /// outside a graph.
    #[getter]
    fn target_vertex(&self) -> Option<usize> {
        self.home.edge().map(VerifiedMutation::target)
    }

    /// Recomputes the five checks of the mutation witness and the target pair.
    /// For a graph edge it also rechecks the isomorphism binding the target to
    /// the stored vertex.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| {
            self.home.mutation().verify() && self.home.edge().is_none_or(|e| e.endpoint().verify())
        })
    }

    fn __repr__(&self) -> String {
        format!(
            "Mutation(slot={}, shape={:?}, source_vertex={:?}, target_vertex={:?})",
            self.slot(),
            self.shape(),
            self.source_vertex(),
            self.target_vertex()
        )
    }
}

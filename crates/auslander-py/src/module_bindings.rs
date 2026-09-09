use super::*;

/// A finite-dimensional right kQ/I-module, validated at construction.
///
/// The module assigns to each vertex v the row-vector space k^dims[v] and to each
/// arrow a matrix acting on row vectors; paths act by matrix products in
/// left-to-right word order. Instances come only from Algebra methods
/// (`module`, `simple`, `projective`, `injective`), and two modules can be compared
/// homologically only when they were built from the same Algebra object
/// over equal fields.

#[pyclass(name = "Module", module = "auslander")]
pub(crate) struct PyRightModule {
    pub(crate) inner: Module,
}

impl From<Module> for PyRightModule {
    fn from(inner: Module) -> Self {
        PyRightModule { inner }
    }
}

impl From<&Module> for PyRightModule {
    fn from(module: &Module) -> Self {
        PyRightModule {
            inner: module.clone(),
        }
    }
}

pub(crate) fn check_same_context(m: &Module, n: &Module) -> PyResult<()> {
    if Arc::ptr_eq(m.algebra(), n.algebra()) {
        return Ok(());
    }
    // The runtime algebra is cached per field, so two modules from one
    // Algebra object share their Arc exactly when their fields agree.
    if m.field() != n.field() {
        return Err(PyValueError::new_err(format!(
            "modules are over different fields F_{} and F_{}",
            m.field().modulus(),
            n.field().modulus()
        )));
    }
    Err(PyValueError::new_err(
        "modules were built from different Algebra objects; \
         hom and ext need both sides over the same algebra object",
    ))
}

#[pymethods]
impl PyRightModule {
    /// The dimension vector: dims[v] = dim_k M_v.
    #[getter]
    fn dims(&self) -> Vec<usize> {
        self.inner.dim_vector().to_vec()
    }

    /// dim_k M, the sum of the dimension vector.
    #[getter]
    fn total_dim(&self) -> usize {
        self.inner.total_dim()
    }

    /// The arrow matrices as canonical integers in `0..p`.
    ///
    /// `maps[a]` has shape `dims[source(a)] x dims[target(a)]`. The result is
    /// accepted by `Algebra.module` with the same field and dimension vector.
    #[getter]
    fn maps(&self) -> Vec<Vec<Vec<u64>>> {
        let arrows = self.inner.algebra().quiver().num_arrows();
        (0..arrows)
            .map(|arrow| self.inner.map(ArrowId(arrow as u32)).entries_u64())
            .collect()
    }

    /// The nonzero arrow-matrix entries as `(row, column, value)` triples.
    ///
    /// The result is accepted by `Algebra.module_sparse` with the same field
    /// and dimension vector.
    #[getter]
    fn sparse_maps(&self) -> Vec<Vec<(usize, usize, u64)>> {
        let arrows = self.inner.algebra().quiver().num_arrows();
        (0..arrows)
            .map(|arrow| sparse_entries(self.inner.map(ArrowId(arrow as u32))))
            .collect()
    }

    /// A basis of Hom_A(self, other) as a list of Morphism objects, not every
    /// morphism: the hom space is a k-vector space and arbitrary morphisms are
    /// its linear combinations. Raises ValueError when the modules do not share
    /// one algebra object and field.
    #[pyo3(text_signature = "($self, other)")]
    fn hom(&self, py: Python<'_>, other: &PyRightModule) -> PyResult<Vec<PyMorphism>> {
        check_same_context(&self.inner, &other.inner)?;
        let basis = py
            .allow_threads(|| hom::hom(&self.inner, &other.inner))
            .map_err(value_error)?;
        Ok(basis.into_iter().map(PyMorphism::from).collect())
    }

    /// `Hom_A(self, other)` modulo maps that factor through projectives.
    ///
    /// The result retains bases of the projective-factor subspace and the
    /// deterministic quotient representatives.
    #[pyo3(text_signature = "($self, other)")]
    fn stable_hom(&self, py: Python<'_>, other: &PyRightModule) -> PyResult<PyStableHomSpace> {
        check_same_context(&self.inner, &other.inner)?;
        Ok(PyStableHomSpace {
            inner: py
                .allow_threads(|| almost_split::stable_hom(&self.inner, &other.inner))
                .map_err(almost_split_error)?,
        })
    }

    /// `dim_k stable Hom_A(self, other)`.
    #[pyo3(text_signature = "($self, other)")]
    fn stable_hom_dim(&self, py: Python<'_>, other: &PyRightModule) -> PyResult<usize> {
        check_same_context(&self.inner, &other.inner)?;
        py.allow_threads(|| almost_split::stable_hom(&self.inner, &other.inner))
            .map(|space| space.dim())
            .map_err(almost_split_error)
    }

    /// A morphism self -> target from one dims_self[v] x dims_target[v] integer
    /// matrix (list of rows) per vertex, acting on row vectors; entries are
    /// reduced mod p. A-linearity (every commuting square) is checked; raises
    /// ValueError when shapes disagree, a square fails, or the modules do not
    /// share one algebra object and field.
    #[pyo3(text_signature = "($self, target, maps)")]
    fn morphism(&self, target: &PyRightModule, maps: Vec<Vec<Vec<i64>>>) -> PyResult<PyMorphism> {
        check_same_context(&self.inner, &target.inner)?;
        let field = self.inner.field();
        let mut mats = Vec::with_capacity(maps.len());
        for (v, rows) in maps.iter().enumerate() {
            let cols = target.inner.dim_vector().get(v).copied().unwrap_or(0);
            mats.push(dense_from_rows(
                field,
                rows,
                cols,
                &format!("map at vertex {v}"),
            )?);
        }
        Ok(hom::Morphism::new(&self.inner, &target.inner, mats)
            .map_err(value_error)?
            .into())
    }

    /// dim_k Hom_A(self, other). Raises ValueError when the modules do not share
    /// one algebra object and field.
    #[pyo3(text_signature = "($self, other)")]
    fn hom_dim(&self, py: Python<'_>, other: &PyRightModule) -> PyResult<usize> {
        check_same_context(&self.inner, &other.inner)?;
        py.allow_threads(|| hom::hom_dim(&self.inner, &other.inner))
            .map_err(value_error)
    }

    /// dim_k Ext^k_A(self, other), exact for every k; Ext^0 is Hom. Raises
    /// ValueError when the modules do not share one algebra object and field.
    /// Raises OverflowError when k has no representable successor.
    #[pyo3(text_signature = "($self, other, k)")]
    fn ext_dim(&self, py: Python<'_>, other: &PyRightModule, k: usize) -> PyResult<usize> {
        check_same_context(&self.inner, &other.inner)?;
        py.allow_threads(|| ext::ext_dim(&self.inner, &other.inner, k))
            .map_err(ext_error)
    }

    /// [dim Ext^0(self, other), ..., dim Ext^max_k(self, other)], each entry exact.
    /// Raises ValueError when the modules do not share one algebra object and field.
    /// Raises OverflowError when max_k has no representable successor.
    #[pyo3(text_signature = "($self, other, max_k)")]
    fn ext_table(
        &self,
        py: Python<'_>,
        other: &PyRightModule,
        max_k: usize,
    ) -> PyResult<Vec<usize>> {
        check_same_context(&self.inner, &other.inner)?;
        py.allow_threads(|| ext::ext_table(&self.inner, &other.inner, max_k))
            .map_err(ext_error)
    }

    /// Dimension vectors along the radical series M ⊇ rad M ⊇ rad^2 M ⊇ ...,
    /// ending with the zero module.
    #[pyo3(text_signature = "($self)")]
    fn radical_series_dims(&self, py: Python<'_>) -> Vec<Vec<usize>> {
        py.allow_threads(|| dim_vectors(&radical::radical_series(&self.inner)))
    }

    /// The Loewy length: the least l with rad^l M = 0 (0 for the zero module).
    #[pyo3(text_signature = "($self)")]
    fn loewy_length(&self, py: Python<'_>) -> usize {
        py.allow_threads(|| radical::loewy_length(&self.inner))
    }

    /// The dimension vector of top M = M / rad M.
    #[pyo3(text_signature = "($self)")]
    fn top_dims(&self, py: Python<'_>) -> Vec<usize> {
        py.allow_threads(|| radical::top(&self.inner).0.dim_vector().to_vec())
    }

    /// The dimension vector of soc M, the largest submodule killed by the radical.
    #[pyo3(text_signature = "($self)")]
    fn socle_dims(&self, py: Python<'_>) -> Vec<usize> {
        py.allow_threads(|| radical::socle(&self.inner).0.dim_vector().to_vec())
    }

    /// The projective cover as a pair (P(M), the cover P(M) -> M): P(M) is the
    /// direct sum of P_v with multiplicity dim (top M)_v and the cover is an
    /// epimorphism inducing an isomorphism on tops, so its kernel lies in
    /// rad P(M). The cover has this module as its target, so it composes with
    /// anything else built from the same algebra object. Dual to
    /// injective_envelope.
    #[pyo3(text_signature = "($self)")]
    fn projective_cover(&self, py: Python<'_>) -> (PyRightModule, PyMorphism) {
        let (cover, epi) = py.allow_threads(|| projective_cover(&self.inner));
        (cover.into(), epi.into())
    }

    /// A minimal projective resolution prefix with at most `steps` differentials.
    /// The result records how it ended; see Resolution.status.
    #[pyo3(text_signature = "($self, steps)")]
    fn resolve(&self, py: Python<'_>, steps: usize) -> PyResolution {
        PyResolution {
            module: self.inner.clone(),
            inner: py.allow_threads(|| resolve(&self.inner, steps)),
        }
    }

    /// The `degree`-th syzygy with its minimal resolution witness.
    #[pyo3(text_signature = "($self, degree=1)", signature = (degree = 1))]
    fn syzygy(&self, py: Python<'_>, degree: usize) -> PySyzygy {
        PySyzygy {
            inner: py.allow_threads(|| syzygy(&self.inner, degree)),
        }
    }

    /// The injective envelope as a pair (I(M), the embedding M -> I(M)):
    /// I(M) is the direct sum of I_v with multiplicity dim (soc M)_v and the
    /// embedding is a monomorphism with essential image, dual to the minimality
    /// of a projective cover. The embedding has this module as its source, so it
    /// composes with anything else built from the same algebra object. An
    /// exhausted completion budget while building the opposite algebra raises
    /// TruncationError.
    #[pyo3(text_signature = "($self)")]
    fn injective_envelope(&self, py: Python<'_>) -> PyResult<(PyRightModule, PyMorphism)> {
        let (envelope, embedding) = py
            .allow_threads(|| injective::injective_envelope(&self.inner))
            .map_err(downstream_build_error)?;
        Ok((envelope.into(), embedding.into()))
    }

    /// A minimal injective coresolution prefix with at most `steps`
    /// differentials. The result records how it ended; see
    /// InjectiveCoresolution.status. An exhausted completion budget while
    /// building the opposite algebra raises TruncationError.
    #[pyo3(text_signature = "($self, steps)")]
    fn coresolve(&self, py: Python<'_>, steps: usize) -> PyResult<PyInjectiveCoresolution> {
        Ok(PyInjectiveCoresolution {
            inner: py
                .allow_threads(|| injective::coresolve(&self.inner, steps))
                .map_err(downstream_build_error)?,
        })
    }

    /// The `degree`-th cosyzygy with its minimal coresolution witness.
    ///
    /// An exhausted completion budget while building the opposite algebra
    /// raises `TruncationError`.
    #[pyo3(text_signature = "($self, degree=1)", signature = (degree = 1))]
    fn cosyzygy(&self, py: Python<'_>, degree: usize) -> PyResult<PyCosyzygy> {
        Ok(PyCosyzygy {
            inner: py
                .allow_threads(|| cosyzygy(&self.inner, degree))
                .map_err(downstream_build_error)?,
        })
    }

    /// The injective dimension, decided up to `bound` differentials: Exact(n)
    /// with n <= bound when the minimal coresolution reaches zero by step
    /// `bound`, AtLeast(bound + 1) otherwise. The coresolution is minimal, so
    /// the lower bound is genuine. The zero module is injective, so its
    /// injective dimension is Exact(0). An exhausted completion budget while
    /// building the opposite algebra raises TruncationError.
    #[pyo3(text_signature = "($self, bound)")]
    fn injective_dimension(&self, py: Python<'_>, bound: usize) -> PyResult<PyBounded> {
        Ok(PyBounded {
            inner: py
                .allow_threads(|| injective::injective_dimension(&self.inner, bound))
                .map_err(downstream_build_error)?,
        })
    }

    /// A verified direct-sum decomposition of the module with one certificate
    /// per summand; the zero module decomposes into no summands. The summands
    /// are ordinary Modules over the same algebra object, so they interact
    /// with everything else built from it. Deterministic: all randomness is
    /// seeded per call.
    #[pyo3(text_signature = "($self)")]
    fn decompose(&self, py: Python<'_>) -> PyDecomposition {
        PyDecomposition {
            inner: py.allow_threads(|| decompose::decompose(&self.inner)),
        }
    }

    /// Groups the summands of a full decomposition into isomorphism classes
    /// with multiplicities, as a KrullSchmidtResult: `classes` when every
    /// summand was certified indecomposable, an explicit `reason` otherwise,
    /// never a partial grouping.
    #[pyo3(text_signature = "($self)")]
    fn krull_schmidt(&self, py: Python<'_>) -> PyKrullSchmidtResult {
        PyKrullSchmidtResult {
            outcome: py.allow_threads(|| decompose::krull_schmidt(&self.inner)),
        }
    }

    /// The Auslander-Reiten translate `τM`. Zero exactly when the module is
    /// projective.
    ///
    /// Both computation routes, the Nakayama kernel and transpose-then-dual,
    /// always run and are cross-checked. A certified disagreement raises
    /// DefectError, a RuntimeError subclass: a library-bug signal distinct
    /// from the ValueError used for input errors. An exhausted completion
    /// budget while building the opposite algebra raises TruncationError with
    /// the diagnostics attached. A cross-check the isomorphism test could not
    /// decide either way raises TauAgreementUnknown, which is a limit of that
    /// test rather than evidence that the routes differ.
    #[pyo3(text_signature = "($self)")]
    fn tau(&self, py: Python<'_>) -> PyResult<PyRightModule> {
        match py.allow_threads(|| ar::tau(&self.inner)) {
            Ok(inner) => Ok(inner.into()),
            Err(e) => Err(tau_error(e)),
        }
    }

    /// The Ext space Ext^degree_A(self, other), with the cochain data
    /// `ext_dim` discards: a basis of classes, each with a representative
    /// cocycle. Raises ValueError when the modules do not share one algebra
    /// object and field. Raises OverflowError when degree has no representable
    /// successor.
    #[pyo3(text_signature = "($self, other, degree)")]
    fn ext_space(
        &self,
        py: Python<'_>,
        other: &PyRightModule,
        degree: usize,
    ) -> PyResult<PyExtSpace> {
        check_same_context(&self.inner, &other.inner)?;
        Ok(PyExtSpace {
            inner: py
                .allow_threads(|| ext::ExtSpace::new(&self.inner, &other.inner, degree))
                .map_err(ext_error)?,
        })
    }

    /// The bounded graded self-Ext algebra through `bound`, including every
    /// Yoneda product whose output degree is at most `bound`.
    ///
    /// A finite minimal resolution returns `ExtAlgebra`. Otherwise the method
    /// returns `IncompleteExtAlgebra`, whose exact layer includes every degree
    /// through `bound` and names the first omitted degree. Neither outcome
    /// claims that an omitted Ext group vanishes.
    #[pyo3(text_signature = "($self, bound)")]
    fn ext_algebra<'py>(&self, py: Python<'py>, bound: usize) -> PyResult<Bound<'py, PyAny>> {
        match py
            .allow_threads(|| ExtAlgebraOutcome::compute(&self.inner, bound))
            .map_err(ext_algebra_error)?
        {
            ExtAlgebraOutcome::Complete(inner) => {
                Ok(Bound::new(py, PyExtAlgebra { inner })?.into_any())
            }
            ExtAlgebraOutcome::Cut(inner) => {
                Ok(Bound::new(py, PyIncompleteExtAlgebra { inner })?.into_any())
            }
        }
    }

    /// The almost-split sequence ending at this module, or
    /// `AlmostSplitOutcome.PROJECTIVE` when the module is projective.
    ///
    /// The module goes through the indecomposability gate first, so the zero
    /// module, a decomposable module, and a module the gate left undetermined
    /// raise NotIndecomposableError, a ValueError subclass carrying the gate's
    /// report. A failed internal cross-check raises DefectError, a
    /// RuntimeError subclass: it signals a bug in this library, never bad
    /// input.
    #[pyo3(text_signature = "($self)")]
    fn almost_split<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        let module = py
            .allow_threads(|| IndecomposableModule::new(&self.inner))
            .map_err(|e| indec_error("the module", e))?;
        let outcome = py
            .allow_threads(|| almost_split::almost_split(&module))
            .map_err(almost_split_error)?;
        match outcome {
            AlmostSplitOutcome::Projective => Ok(projective_outcome(py)?.into_bound(py).into_any()),
            AlmostSplitOutcome::Sequence(inner) => {
                Ok(Bound::new(py, PyAlmostSplitSequence { module, inner })?.into_any())
            }
        }
    }

    /// The radical rad(self, other) of the module category: the maps that are
    /// not isomorphisms, as a subspace of Hom(self, other). Both endpoints
    /// must pass the indecomposability gate, so both raise
    /// NotIndecomposableError otherwise; the message names the failed
    /// endpoint. Raises ValueError when the modules do not share one algebra
    /// object and field.
    #[pyo3(text_signature = "($self, other)")]
    fn category_radical(
        &self,
        py: Python<'_>,
        other: &PyRightModule,
    ) -> PyResult<PyCategoryRadical> {
        check_same_context(&self.inner, &other.inner)?;
        let x = py
            .allow_threads(|| IndecomposableModule::new(&self.inner))
            .map_err(|e| indec_error("the source module", e))?;
        let y = py
            .allow_threads(|| IndecomposableModule::new(&other.inner))
            .map_err(|e| indec_error("the target module", e))?;
        Ok(PyCategoryRadical {
            inner: py
                .allow_threads(|| arquiver::category_radical(&x, &y))
                .map_err(ar_quiver_error)?,
        })
    }

    /// Decides self ≅ other as an IsoResult: isomorphic True comes with a
    /// verified witness (checked two-sided inverse), False with a proof-shaped
    /// obstruction, and None means undetermined, not "no".
    /// Raises ValueError when the modules do not share one algebra object and
    /// field.
    #[pyo3(text_signature = "($self, other)")]
    fn is_isomorphic(&self, py: Python<'_>, other: &PyRightModule) -> PyResult<PyIsoResult> {
        check_same_context(&self.inner, &other.inner)?;
        Ok(PyIsoResult {
            outcome: py
                .allow_threads(|| iso::is_isomorphic(&self.inner, &other.inner))
                .map_err(value_error)?,
        })
    }

    /// Decides Hom(M, tau M) = 0 as a TauRigidity, witnessed either way.
    ///
    /// The module is decomposed first and the decision runs summandwise, which
    /// is exact by additivity of tau and Hom. Neither answer is a failure and
    /// neither raises: a tau-rigid module comes back with one certified
    /// translate per summand and the positions of the pairs it checked, and a
    /// module that is not tau-rigid comes back with one nonzero morphism
    /// X_i -> tau X_j. A translate that could not be certified raises as
    /// `Module.tau` documents.
    #[pyo3(text_signature = "($self)")]
    fn tau_rigidity(&self, py: Python<'_>) -> PyResult<PyTauRigidity> {
        Ok(PyTauRigidity {
            outcome: py
                .allow_threads(|| taurigid::is_tau_rigid(&self.inner))
                .map_err(tau_rigid_error)?,
        })
    }

    fn __repr__(&self) -> String {
        format!(
            "Module(dims={:?}, field=F_{})",
            self.inner.dim_vector(),
            self.inner.field().modulus()
        )
    }
}

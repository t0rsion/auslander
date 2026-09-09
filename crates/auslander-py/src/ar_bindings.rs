use super::*;

/// The outcome of `Module.almost_split` for a projective module.
///
/// The class has one member, `AlmostSplitOutcome.PROJECTIVE`, and
/// `Module.almost_split` returns that very object, so `is` decides the case.
/// No almost-split sequence ends at a projective.

#[pyclass(name = "AlmostSplitOutcome", module = "auslander", frozen, eq, hash)]
#[derive(PartialEq, Eq, Hash)]
pub(crate) struct PyAlmostSplitOutcome;

static PROJECTIVE_OUTCOME: GILOnceCell<Py<PyAlmostSplitOutcome>> = GILOnceCell::new();

/// The single PROJECTIVE member, built once, so the value `almost_split`
/// returns and the class attribute are one object.
pub(crate) fn projective_outcome(py: Python<'_>) -> PyResult<Py<PyAlmostSplitOutcome>> {
    Ok(PROJECTIVE_OUTCOME
        .get_or_try_init(py, || Py::new(py, PyAlmostSplitOutcome))?
        .clone_ref(py))
}

#[pymethods]
impl PyAlmostSplitOutcome {
    /// The projective outcome: the module is projective, so no almost-split
    /// sequence ends at it.
    #[classattr]
    #[pyo3(name = "PROJECTIVE")]
    fn projective(py: Python<'_>) -> PyResult<Py<PyAlmostSplitOutcome>> {
        projective_outcome(py)
    }

    fn __repr__(&self) -> String {
        "AlmostSplitOutcome.PROJECTIVE".to_string()
    }
}

/// An almost-split sequence 0 -> start -> middle -> end -> 0 with the witness
/// that certifies it.
///
/// `start` is the AR translate of `end`. The sequence realizes a chosen class
/// of the socle of Ext^1(end, start) as a module over the endomorphism algebra
/// of `end`. That class is deterministic, not canonical. Any other nonzero
/// socle class gives an almost-split sequence isomorphic to this one after
/// suitable automorphisms of the end terms, not an equivalent extension with
/// fixed ends.
///
/// `verify()` rechecks every gate of the construction from the stored witness
/// and the live modules, and `verification_summary()` reports the gates one by
/// one. Instances are immutable and come only from `Module.almost_split`.
#[pyclass(name = "AlmostSplitSequence", module = "auslander", frozen)]
pub(crate) struct PyAlmostSplitSequence {
    pub(crate) module: IndecomposableModule,
    pub(crate) inner: almost_split::AlmostSplitSequence,
}

impl PyAlmostSplitSequence {
    /// The AR duality witness. `Module.almost_split` runs the AR duality
    /// route, so the catalog variant is unreachable through this package.
    fn ar_duality(&self) -> PyResult<&almost_split::ArDualityWitness> {
        match self.inner.witness() {
            AlmostSplitWitness::ArDuality(witness) => Ok(witness),
            AlmostSplitWitness::ExhaustiveCatalog(_) => Err(engine_error(
                "the sequence carries a catalog witness, which this package never builds",
            )),
        }
    }
}

#[pymethods]
impl PyAlmostSplitSequence {
    /// The left end, the AR translate of `end`.
    #[getter]
    fn start(&self) -> PyRightModule {
        self.inner.sequence().sub().into()
    }

    /// The middle term.
    #[getter]
    fn middle(&self) -> PyRightModule {
        self.inner.sequence().middle().into()
    }

    /// The right end: the module the sequence was built for.
    #[getter]
    fn end(&self) -> PyRightModule {
        self.inner.sequence().quotient().into()
    }

    /// The inclusion start -> middle.
    #[getter]
    fn inclusion(&self) -> PyMorphism {
        self.inner.sequence().inclusion().into()
    }

    /// The projection middle -> end.
    #[getter]
    fn projection(&self) -> PyMorphism {
        self.inner.sequence().projection().into()
    }

    /// The chosen AR class in Ext^1(end, start) that the sequence realizes:
    /// the first row of the socle basis. Deterministic, not canonical.
    #[pyo3(text_signature = "($self)")]
    fn ext1_class(&self) -> PyExtClass {
        PyExtClass {
            inner: self.inner.chosen_ar_class().clone(),
        }
    }

    /// Which route certified the sequence: "ar_duality" for the socle
    /// construction of AR duality, "exhaustive_catalog" for the catalog
    /// route. `Module.almost_split` always runs the AR duality route.
    #[getter]
    fn witness_route(&self) -> &'static str {
        match self.inner.witness() {
            AlmostSplitWitness::ArDuality(_) => "ar_duality",
            AlmostSplitWitness::ExhaustiveCatalog(_) => "exhaustive_catalog",
        }
    }

    /// Rechecks the whole witness against freshly recomputed data: the
    /// radical basis and the action matrices of the endomorphism algebra, the
    /// socle kernel, the two dimension equalities, the recovery of the class
    /// from the sequence, the non-split witness, and exactness.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> PyResult<bool> {
        let witness = self.ar_duality()?;
        Ok(py.allow_threads(|| {
            witness.verify(
                &self.module,
                self.inner.sequence(),
                self.inner.chosen_ar_class(),
            )
        }))
    }

    /// The gates of the construction one by one, as a dict of check name to
    /// result: "action_traces" (the chosen class is annihilated by every
    /// radical endomorphism), "socle_membership" (the class is the stored
    /// socle row and is nonzero), "duality_dimensions" (dim Ext^1(end, start)
    /// equals dim of the stable endomorphism algebra), "socle_dimension" (the
    /// socle dimension equals the residue degree), "non_split" (the dual
    /// vector proves no retraction exists), and "sequence_exact" (the
    /// exactness checks pass again). `verify()` is the stronger statement: it
    /// recomputes the stored data instead of reading it.
    #[pyo3(text_signature = "($self)")]
    fn verification_summary(&self, py: Python<'_>) -> PyResult<BTreeMap<&'static str, bool>> {
        let witness = self.ar_duality()?;
        Ok(py.allow_threads(|| {
            let sequence = self.inner.sequence();
            let class = self.inner.chosen_ar_class();
            let action_traces = witness.action_traces().len()
                == witness.radical_basis_coords().rows()
                && witness
                    .action_traces()
                    .iter()
                    .all(|trace| trace.iter().all(|c| c.is_zero()));
            let socle_membership = witness.chosen_row() < witness.socle_rref().rows()
                && class.coordinates() == witness.socle_rref().row(witness.chosen_row())
                && !class.is_zero();
            let duality_dimensions = witness.ext_dim() == witness.stable_end_dim()
                && witness.ext_dim() == class.space().dim();
            let socle_dimension = witness.socle_dim() == witness.socle_rref().rows()
                && witness.socle_dim() == witness.residue_degree()
                && witness.residue_degree() == self.module.residue_degree();
            let non_split = witness.non_split().verify(sequence);
            let sequence_exact = sequence::ShortExactSequence::new(
                sequence.inclusion().clone(),
                sequence.projection().clone(),
            )
            .is_ok();
            BTreeMap::from([
                ("action_traces", action_traces),
                ("duality_dimensions", duality_dimensions),
                ("non_split", non_split),
                ("sequence_exact", sequence_exact),
                ("socle_dimension", socle_dimension),
                ("socle_membership", socle_membership),
            ])
        }))
    }

    fn __repr__(&self) -> String {
        format!(
            "AlmostSplitSequence(start_dims={:?}, middle_dims={:?}, end_dims={:?})",
            self.inner.sequence().sub().dim_vector(),
            self.inner.sequence().middle().dim_vector(),
            self.inner.sequence().quotient().dim_vector()
        )
    }
}

/// The radical rad(X, Y) of the module category between two certified
/// indecomposables, as a subspace of Hom(X, Y).
///
/// The radical holds the maps that are not isomorphisms: the whole hom space
/// when X and Y are not isomorphic, and the maps whose composite with a fixed
/// isomorphism lands in the radical of End(X) when they are. The computation
/// is exact and needs no catalog. Instances are immutable and come only from
/// `Module.category_radical`.
#[pyclass(name = "CategoryRadical", module = "auslander", frozen)]
pub(crate) struct PyCategoryRadical {
    pub(crate) inner: HomSubspace,
}

#[pymethods]
impl PyCategoryRadical {
    /// dim_k rad(X, Y).
    #[getter]
    fn dim(&self) -> usize {
        self.inner.dim()
    }

    /// A basis of the radical as a list of Morphism objects, not every
    /// radical map: arbitrary radical maps are its linear combinations.
    #[pyo3(text_signature = "($self)")]
    fn basis(&self) -> Vec<PyMorphism> {
        (0..self.inner.dim())
            .map(|r| self.inner.basis_morphism(r).into())
            .collect()
    }

    fn __repr__(&self) -> String {
        format!(
            "CategoryRadical(dim={}, source_dims={:?}, target_dims={:?})",
            self.inner.dim(),
            self.inner.source().dim_vector(),
            self.inner.target().dim_vector()
        )
    }
}

/// One vertex of an AR quiver: an indecomposable module with the data the
/// quiver labels it by.
///
/// `id` is the index of the vertex in `ArQuiver.vertices()` and in the catalog
/// behind it. `residue_degree` is the degree d of the residue field F_{p^d} of
/// the local endomorphism algebra; it is 1 on both catalog domains of this
/// release. Instances are immutable.
#[pyclass(name = "ArVertex", module = "auslander", frozen)]
pub(crate) struct PyArVertex {
    pub(crate) quiver: Arc<ArQuiver>,
    pub(crate) index: usize,
}

#[pymethods]
impl PyArVertex {
    /// The index of the vertex in `ArQuiver.vertices()`.
    #[getter]
    fn id(&self) -> usize {
        self.quiver.vertices()[self.index].id()
    }

    /// The module at the vertex.
    #[getter]
    fn module(&self) -> PyRightModule {
        self.quiver.vertices()[self.index].module().module().into()
    }

    /// The degree d of the residue field F_{p^d} of the module's local
    /// endomorphism algebra.
    #[getter]
    fn residue_degree(&self) -> usize {
        self.quiver.vertices()[self.index].residue_degree()
    }

    /// Whether the module is projective.
    #[getter]
    fn projective(&self) -> bool {
        self.quiver.vertices()[self.index].projective()
    }

    /// Whether the module is injective.
    #[getter]
    fn injective(&self) -> bool {
        self.quiver.vertices()[self.index].injective()
    }

    fn __repr__(&self) -> String {
        let vertex = &self.quiver.vertices()[self.index];
        format!(
            "ArVertex(id={}, dims={:?}, residue_degree={})",
            vertex.id(),
            vertex.module().module().dim_vector(),
            vertex.residue_degree()
        )
    }
}

/// One arrow of an AR quiver: a pair of vertices with a nonzero space of
/// irreducible maps, together with its three dimensions.
///
/// `base_field_dim` is dim_k Irr(X, Y) over the prime field.
/// `dim_over_source_residue` and `dim_over_target_residue` are its dimensions
/// over the two residue fields; they differ from `base_field_dim` exactly when
/// a residue degree exceeds 1. `plain_multiplicity` is the arrow multiplicity
/// of an unvalued AR quiver; it raises ValuedArrowError on a valued arrow
/// instead of reducing three dimensions to one integer. Instances are
/// immutable.
#[pyclass(name = "ArArrow", module = "auslander", frozen)]
pub(crate) struct PyArArrow {
    pub(crate) quiver: Arc<ArQuiver>,
    pub(crate) index: usize,
}

#[pymethods]
impl PyArArrow {
    /// The id of the source vertex.
    #[getter]
    fn source(&self) -> usize {
        self.quiver.arrows()[self.index].source()
    }

    /// The id of the target vertex.
    #[getter]
    fn target(&self) -> usize {
        self.quiver.arrows()[self.index].target()
    }

    /// dim_k Irr(X, Y) over the prime field.
    #[getter]
    fn base_field_dim(&self) -> usize {
        self.quiver.arrows()[self.index].base_dim()
    }

    /// The dimension of Irr(X, Y) over the residue field of the source.
    #[getter]
    fn dim_over_source_residue(&self) -> usize {
        self.quiver.arrows()[self.index].over_source_residue()
    }

    /// The dimension of Irr(X, Y) over the residue field of the target.
    #[getter]
    fn dim_over_target_residue(&self) -> usize {
        self.quiver.arrows()[self.index].over_target_residue()
    }

    /// The arrow multiplicity of an unvalued AR quiver, defined only when both
    /// residue degrees are 1; raises ValuedArrowError, a ValueError subclass,
    /// otherwise. A valued arrow carries three dimensions, and none of them is
    /// the multiplicity.
    #[getter]
    fn plain_multiplicity(&self) -> PyResult<usize> {
        match self.quiver.arrows()[self.index].valuation() {
            ArrowValuation::Plain(m) => Ok(m),
            ArrowValuation::Valued {
                base_dim,
                over_source,
                over_target,
            } => Err(ValuedArrowError::new_err(format!(
                "the arrow is valued: dim_k Irr = {base_dim} over the prime field, \
                 {over_source} over the source residue field, {over_target} over the target \
                 residue field; read those three dimensions instead"
            ))),
        }
    }

    /// Representatives of a basis of Irr(X, Y) as Morphism objects, one per
    /// dimension over the prime field.
    #[pyo3(text_signature = "($self)")]
    fn representatives(&self) -> Vec<PyMorphism> {
        wrap_all(self.quiver.arrows()[self.index].representatives())
    }

    fn __repr__(&self) -> String {
        let arrow = &self.quiver.arrows()[self.index];
        format!(
            "ArArrow(source={}, target={}, base_field_dim={})",
            arrow.source(),
            arrow.target(),
            arrow.base_dim()
        )
    }
}

/// The valued Auslander-Reiten quiver of an algebra.
///
/// One vertex per indecomposable of a complete enumeration, one arrow per
/// nonzero space of irreducible maps, ordered by source id then target id. The
/// quiver is complete for its domain: the enumeration behind it is a
/// classification theorem (Nakayama or Gabriel) and no budget cuts the
/// construction short, so there is no partial AR quiver. Instances are
/// immutable and come only from `Algebra.ar_quiver`.
#[pyclass(name = "ArQuiver", module = "auslander", frozen)]
pub(crate) struct PyArQuiver {
    pub(crate) inner: Arc<ArQuiver>,
}

#[pymethods]
impl PyArQuiver {
    /// The vertices in catalog order.
    #[pyo3(text_signature = "($self)")]
    fn vertices(&self) -> Vec<PyArVertex> {
        (0..self.inner.vertices().len())
            .map(|index| PyArVertex {
                quiver: self.inner.clone(),
                index,
            })
            .collect()
    }

    /// The arrows, ordered by source id then target id.
    #[pyo3(text_signature = "($self)")]
    fn arrows(&self) -> Vec<PyArArrow> {
        (0..self.inner.arrows().len())
            .map(|index| PyArArrow {
                quiver: self.inner.clone(),
                index,
            })
            .collect()
    }

    /// The number of vertices, one per indecomposable of the enumeration.
    fn __len__(&self) -> usize {
        self.inner.vertices().len()
    }

    fn __repr__(&self) -> String {
        format!(
            "ArQuiver(vertices={}, arrows={})",
            self.inner.vertices().len(),
            self.inner.arrows().len()
        )
    }
}

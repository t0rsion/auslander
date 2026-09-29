use super::*;

use auslander::derived_classification::{
    ClassSeparation, ClassificationError, ClassificationLimits, DerivedAtlasArtifact, DerivedClass,
    DerivedClassification, DerivedMerge, MutationWalk, UnresolvedPair,
    classify_derived as classify,
};

/// The discovery ceilings of `ClassificationLimits()`: the walk limits of
/// the committed `F_2` study record, 8 stored tilting complexes per walk.
fn default_walk_limits() -> DiscoveryLimits {
    ClassificationLimits::with_walk_vertices(8).discovery
}

fn classification_error(error: ClassificationError) -> PyErr {
    match error {
        ClassificationError::FieldMismatch(_) => PyValueError::new_err(format!(
            "{error}; build every member over one field, for example with Algebra.over(field)"
        )),
        ClassificationError::Invariant { .. } | ClassificationError::Contradiction { .. } => {
            DefectError::new_err(error.to_string())
        }
        ClassificationError::Discovery { .. } | ClassificationError::Target { .. } => {
            engine_error(error)
        }
    }
}

/// Caller limits for one `classify_derived` run.
///
/// `invariants` defaults to `InvariantLimits()`. `discovery` bounds each
/// mutation walk, and every walk gets the whole budget. Its default stores
/// at most 8 tilting complexes per walk: `EquivalenceDiscoveryLimits(
/// max_vertices=8, max_directed_mutations=32, max_total_terms=256,
/// max_matrix_entries=16384)`. `through_silting`, when
/// given, replaces the flag of `discovery`. `target` bounds each target
/// recovery and defaults to `TargetLimits()`.
#[pyclass(name = "ClassificationLimits", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyClassificationLimits {
    pub(crate) inner: ClassificationLimits,
}

#[pymethods]
impl PyClassificationLimits {
    #[new]
    #[pyo3(signature = (invariants = None, discovery = None, target = None, through_silting = None))]
    fn new(
        invariants: Option<&PyInvariantLimits>,
        discovery: Option<&PyEquivalenceDiscoveryLimits>,
        target: Option<&PyTargetLimits>,
        through_silting: Option<bool>,
    ) -> PyClassificationLimits {
        let mut discovery = discovery.map_or_else(default_walk_limits, |limits| limits.inner);
        discovery.through_silting = through_silting.unwrap_or(discovery.through_silting);
        PyClassificationLimits {
            inner: ClassificationLimits {
                invariants: invariant_limits(invariants),
                discovery,
                target: target.map_or_else(TargetLimits::default, |limits| limits.inner.clone()),
            },
        }
    }

    #[getter]
    fn invariants(&self) -> PyInvariantLimits {
        PyInvariantLimits {
            inner: self.inner.invariants,
        }
    }

    #[getter]
    fn discovery(&self) -> PyEquivalenceDiscoveryLimits {
        PyEquivalenceDiscoveryLimits {
            inner: self.inner.discovery,
        }
    }

    /// Whether each walk passes through silting complexes.
    #[getter]
    fn through_silting(&self) -> bool {
        self.inner.discovery.through_silting
    }

    #[getter]
    fn target(&self) -> PyTargetLimits {
        PyTargetLimits {
            inner: self.inner.target.clone(),
        }
    }

    fn __repr__(&self) -> String {
        format!(
            "ClassificationLimits(invariants={}, discovery={})",
            self.invariants().__repr__(),
            self.discovery().__repr__()
        )
    }
}

/// One certified derived equivalence between two family members.
///
/// `recipe` mutates the regular complex of member `source` to a tilting
/// complex `T`, as `(direction, summand)` pairs. `recovered_target` is
/// `End(T)^op`, and `isomorphism` maps it onto member `member`. A duplicate
/// merge joins two presentations with equal gentle keys or certificates; its
/// recipe is empty.
#[pyclass(name = "DerivedMerge", module = "auslander", frozen)]
pub(crate) struct PyDerivedMerge {
    inner: DerivedMerge,
}

#[pymethods]
impl PyDerivedMerge {
    /// The walked member, where the recipe starts.
    #[getter]
    fn source(&self) -> usize {
        self.inner.source()
    }

    /// The matched member.
    #[getter]
    fn member(&self) -> usize {
        self.inner.member()
    }

    #[getter]
    fn recipe(&self) -> Vec<(&'static str, usize)> {
        self.inner
            .recipe()
            .iter()
            .map(|step| {
                (
                    approximation_direction_name(step.direction()),
                    step.summand(),
                )
            })
            .collect()
    }

    #[getter]
    fn is_duplicate(&self) -> bool {
        self.inner.is_duplicate()
    }

    #[getter]
    fn recovered_target(&self) -> PyAlgebra {
        PyAlgebra::pinned(self.inner.path().target().clone())
    }

    #[getter]
    fn isomorphism(&self) -> PyAlgebraIsomorphism {
        PyAlgebraIsomorphism {
            inner: self.inner.isomorphism().clone(),
        }
    }

    fn __repr__(&self) -> String {
        format!(
            "DerivedMerge(source={}, member={}, recipe={:?})",
            self.inner.source(),
            self.inner.member(),
            self.recipe()
        )
    }
}

/// One class of derived equivalent family members.
///
/// `members` is increasing and `representative` is the least member. The
/// merges form a spanning tree of the members.
#[pyclass(name = "DerivedClass", module = "auslander", frozen)]
pub(crate) struct PyDerivedClass {
    inner: DerivedClass,
}

#[pymethods]
impl PyDerivedClass {
    #[getter]
    fn members(&self) -> Vec<usize> {
        self.inner.members().to_vec()
    }

    #[getter]
    fn representative(&self) -> usize {
        self.inner.representative()
    }

    #[getter]
    fn merges(&self) -> Vec<PyDerivedMerge> {
        self.inner
            .merges()
            .iter()
            .map(|merge| PyDerivedMerge {
                inner: merge.clone(),
            })
            .collect()
    }

    fn __len__(&self) -> usize {
        self.inner.members().len()
    }

    fn __repr__(&self) -> String {
        format!(
            "DerivedClass(representative={}, members={:?})",
            self.inner.representative(),
            self.inner.members()
        )
    }
}

/// A separated pair of classes and the witness for one member of each.
///
/// The witness names the first differing invariant in table order, the
/// least over every member pair of the two classes.
#[pyclass(name = "ClassSeparation", module = "auslander", frozen)]
pub(crate) struct PyClassSeparation {
    inner: ClassSeparation,
}

#[pymethods]
impl PyClassSeparation {
    /// The class indices, the first one smaller.
    #[getter]
    fn classes(&self) -> (usize, usize) {
        self.inner.classes()
    }

    /// The witnessed member of each class.
    #[getter]
    fn members(&self) -> (usize, usize) {
        self.inner.members()
    }

    #[getter]
    fn witness(&self) -> PyDerivedInequivalenceWitness {
        PyDerivedInequivalenceWitness {
            inner: self.inner.witness().clone(),
        }
    }

    fn __repr__(&self) -> String {
        format!(
            "ClassSeparation(classes={:?}, members={:?}, kind={:?})",
            self.inner.classes(),
            self.inner.members(),
            variant_name(&self.inner.witness().kind())
        )
    }
}

/// A pair of classes that neither a merge nor an invariant settles.
///
/// `walks` indexes `DerivedClassification.walks`: every walk from a member
/// of either class. Their stops say why the pair is open.
#[pyclass(name = "UnresolvedPair", module = "auslander", frozen)]
pub(crate) struct PyUnresolvedPair {
    inner: UnresolvedPair,
}

#[pymethods]
impl PyUnresolvedPair {
    /// The class indices, the first one smaller.
    #[getter]
    fn classes(&self) -> (usize, usize) {
        self.inner.classes()
    }

    #[getter]
    fn walks(&self) -> Vec<usize> {
        self.inner.walks().to_vec()
    }

    fn __repr__(&self) -> String {
        format!(
            "UnresolvedPair(classes={:?}, walks={:?})",
            self.inner.classes(),
            self.inner.walks()
        )
    }
}

/// The record of one mutation walk from a family member.
///
/// `stop` is the discovery stop, as in `IncompleteEquivalenceGraph.stop`.
/// `stop_limit` is the ceiling that stopped the walk, or None for
/// `exhausted_frontier` and `cancelled`. `vertices` counts certified tilting
/// complexes, `blocked` the completed mutations that gave no vertex, and
/// `target_cuts` the recoveries that hit a target limit. In a result of
/// `verify_derived_atlas`, the stop and the counters other than `member` and
/// `merges` are the recorded values: replay does not rerun a walk.
#[pyclass(name = "MutationWalk", module = "auslander", frozen)]
pub(crate) struct PyMutationWalk {
    inner: MutationWalk,
}

#[pymethods]
impl PyMutationWalk {
    #[getter]
    fn member(&self) -> usize {
        self.inner.member()
    }

    #[getter]
    fn stop(&self) -> String {
        variant_name(self.inner.stop())
    }

    #[getter]
    fn stop_limit(&self) -> Option<u64> {
        discovery_stop_limit(self.inner.stop())
    }

    #[getter]
    fn vertices(&self) -> usize {
        self.inner.vertices()
    }

    #[getter]
    fn blocked(&self) -> usize {
        self.inner.blocked()
    }

    /// The vertices whose target was recovered or cut. Fewer than
    /// `vertices` only after cancellation.
    #[getter]
    fn examined(&self) -> usize {
        self.inner.examined()
    }

    #[getter]
    fn target_cuts(&self) -> usize {
        self.inner.target_cuts()
    }

    /// The recovered targets that matched no member.
    #[getter]
    fn unmatched(&self) -> usize {
        self.inner.unmatched()
    }

    /// The merges this walk added.
    #[getter]
    fn merges(&self) -> usize {
        self.inner.merges()
    }

    fn __repr__(&self) -> String {
        format!(
            "MutationWalk(member={}, stop={:?}, vertices={}, merges={})",
            self.inner.member(),
            self.stop(),
            self.inner.vertices(),
            self.inner.merges()
        )
    }
}

/// The certified derived classification of a finite family over one field.
///
/// Every class is joined by replayable merges. Every pair of classes is in
/// `separations`, with a witness that recomputes one differing invariant,
/// or in `unresolved`. `status` is `complete` exactly when no pair is
/// unresolved. A limit or a cancellation never turns an unresolved pair
/// into a merge or a separation. `verify()` replays every merge and
/// recomputes every witness without discovery. `to_artifact()` returns the
/// portable derived atlas. `explain()` says why each unresolved pair is
/// open and which limit to raise.
#[pyclass(name = "DerivedClassification", module = "auslander", frozen)]
pub(crate) struct PyDerivedClassification {
    pub(crate) inner: Arc<DerivedClassification>,
    /// The atlas this result was replayed from, `None` for a computed result.
    pub(crate) atlas: Option<Arc<DerivedAtlasArtifact>>,
}

#[pymethods]
impl PyDerivedClassification {
    /// The family, in input order. Member `i` is `family[i]`.
    #[getter]
    fn family(&self) -> Vec<PyAlgebra> {
        self.inner
            .family()
            .iter()
            .cloned()
            .map(PyAlgebra::pinned)
            .collect()
    }

    #[getter]
    fn limits(&self) -> PyClassificationLimits {
        PyClassificationLimits {
            inner: self.inner.limits().clone(),
        }
    }

    /// The invariants of each member, in family order.
    #[getter]
    fn invariants(&self) -> Vec<PyDerivedInvariants> {
        self.inner
            .invariants()
            .iter()
            .map(|inner| PyDerivedInvariants {
                inner: inner.clone(),
            })
            .collect()
    }

    /// The connected components of the member pairs that no finished
    /// invariant separates, each increasing, ordered by least member.
    #[getter]
    fn groups(&self) -> Vec<Vec<usize>> {
        self.inner.groups().to_vec()
    }

    /// The classes, ordered by representative.
    #[getter]
    fn classes(&self) -> Vec<PyDerivedClass> {
        self.inner
            .classes()
            .iter()
            .map(|inner| PyDerivedClass {
                inner: inner.clone(),
            })
            .collect()
    }

    /// One separation per separated pair of classes, in pair order.
    #[getter]
    fn separations(&self) -> Vec<PyClassSeparation> {
        self.inner
            .separations()
            .iter()
            .map(|inner| PyClassSeparation {
                inner: inner.clone(),
            })
            .collect()
    }

    /// Every unresolved pair of classes, in pair order.
    #[getter]
    fn unresolved(&self) -> Vec<PyUnresolvedPair> {
        self.inner
            .unresolved()
            .iter()
            .map(|inner| PyUnresolvedPair {
                inner: inner.clone(),
            })
            .collect()
    }

    /// Every mutation walk, in the order it ran.
    #[getter]
    fn walks(&self) -> Vec<PyMutationWalk> {
        self.inner
            .walks()
            .iter()
            .map(|inner| PyMutationWalk {
                inner: inner.clone(),
            })
            .collect()
    }

    /// `complete` or `incomplete`.
    #[getter]
    fn status(&self) -> &'static str {
        self.inner.status().as_str()
    }

    /// `replayed` for a result rebuilt from a derived atlas, `computed`
    /// otherwise.
    #[getter]
    fn verification(&self) -> &'static str {
        match self.atlas {
            Some(_) => "replayed",
            None => "computed",
        }
    }

    /// The index of the class that contains `member`.
    fn class_of(&self, member: usize) -> PyResult<usize> {
        self.inner
            .classes()
            .iter()
            .position(|class| class.members().contains(&member))
            .ok_or_else(|| {
                PyValueError::new_err(format!(
                    "member {member} out of range for a family of {}",
                    self.inner.family().len()
                ))
            })
    }

    /// Replays every merge and recomputes every separation witness.
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    /// An `Explanation` of the status, with one line per unresolved pair.
    fn explain<'py>(slf: &Bound<'py, Self>) -> PyResult<Bound<'py, PyAny>> {
        python_helper(slf.as_any(), "explanation", "explain")
    }

    fn __repr__(slf: &Bound<'_, Self>) -> PyResult<String> {
        python_helper(slf.as_any(), "display", "show")?
            .getattr("text")?
            .extract()
    }

    fn _repr_html_(slf: &Bound<'_, Self>) -> PyResult<String> {
        python_helper(slf.as_any(), "display", "show")?
            .getattr("html")?
            .extract()
    }
}

/// Classifies `family` up to derived equivalence.
///
/// `limits` defaults to `ClassificationLimits()`. Cancellation through
/// `control` stops the current walk and each later walk before its first
/// mutation; every pair those walks could have merged stays unresolved.
/// Field-free presentations need `field`. Raises ValueError when members
/// live over different fields, with a hint to use `Algebra.over(field)`, and
/// DefectError on an internal contradiction.
#[pyfunction]
#[pyo3(signature = (family, limits = None, control = None, field = None))]
pub(crate) fn classify_derived(
    py: Python<'_>,
    family: Vec<PyRef<'_, PyAlgebra>>,
    limits: Option<&PyClassificationLimits>,
    control: Option<&PyComputationControl>,
    field: Option<&PyPrimeField>,
) -> PyResult<PyDerivedClassification> {
    let family = family
        .iter()
        .map(|member| member.algebra_for(py, field, "a derived classification"))
        .collect::<PyResult<Vec<_>>>()?;
    let limits = limits.map_or_else(
        || PyClassificationLimits::new(None, None, None, None).inner,
        |limits| limits.inner.clone(),
    );
    let control = control_of(control);
    py.allow_threads(|| classify(&family, &limits, &control))
        .map(|inner| PyDerivedClassification {
            inner: Arc::new(inner),
            atlas: None,
        })
        .map_err(classification_error)
}

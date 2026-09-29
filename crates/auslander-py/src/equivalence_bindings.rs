use super::*;

/// Resource ceilings for deterministic tilting-complex discovery.
///
/// With `through_silting=True`, a walk also stores silting complexes that are
/// not tilting and mutates them further. Targets come from tilting vertices
/// only. Off by default.

#[pyclass(name = "EquivalenceDiscoveryLimits", module = "auslander", frozen)]
pub(crate) struct PyEquivalenceDiscoveryLimits {
    pub(crate) inner: DiscoveryLimits,
}

#[pymethods]
impl PyEquivalenceDiscoveryLimits {
    #[new]
    #[pyo3(signature = (
        max_vertices=1024,
        max_directed_mutations=16384,
        max_total_terms=65536,
        max_matrix_entries=16777216,
        max_hom_spaces=4096,
        through_silting=false
    ))]
    fn new(
        max_vertices: u64,
        max_directed_mutations: u64,
        max_total_terms: u64,
        max_matrix_entries: u64,
        max_hom_spaces: u64,
        through_silting: bool,
    ) -> PyEquivalenceDiscoveryLimits {
        PyEquivalenceDiscoveryLimits {
            inner: DiscoveryLimits {
                max_vertices,
                max_directed_mutations,
                max_total_terms,
                max_matrix_entries,
                tilting: TiltingComplexLimits { max_hom_spaces },
                through_silting,
            },
        }
    }

    #[getter]
    fn max_vertices(&self) -> u64 {
        self.inner.max_vertices
    }

    #[getter]
    fn max_directed_mutations(&self) -> u64 {
        self.inner.max_directed_mutations
    }

    #[getter]
    fn max_total_terms(&self) -> u64 {
        self.inner.max_total_terms
    }

    #[getter]
    fn max_matrix_entries(&self) -> u64 {
        self.inner.max_matrix_entries
    }

    #[getter]
    fn max_hom_spaces(&self) -> u64 {
        self.inner.tilting.max_hom_spaces
    }

    #[getter]
    fn through_silting(&self) -> bool {
        self.inner.through_silting
    }

    pub(crate) fn __repr__(&self) -> String {
        let limits = &self.inner;
        format!(
            "EquivalenceDiscoveryLimits(max_vertices={}, max_directed_mutations={}, \
             max_total_terms={}, max_matrix_entries={}, max_hom_spaces={}, through_silting={})",
            limits.max_vertices,
            limits.max_directed_mutations,
            limits.max_total_terms,
            limits.max_matrix_entries,
            limits.tilting.max_hom_spaces,
            if limits.through_silting {
                "True"
            } else {
                "False"
            }
        )
    }
}

/// The ceiling that stopped a walk, or None when no ceiling did.
pub(crate) fn discovery_stop_limit(stop: &DiscoveryStop) -> Option<u64> {
    match *stop {
        DiscoveryStop::MutationLimit { limit, .. }
        | DiscoveryStop::VertexLimit { limit, .. }
        | DiscoveryStop::TermLimit { limit, .. }
        | DiscoveryStop::MatrixLimit { limit, .. } => Some(limit),
        DiscoveryStop::ExhaustedFrontier | DiscoveryStop::Cancelled { .. } => None,
    }
}

pub(crate) fn approximation_direction_name(direction: ApproximationDirection) -> &'static str {
    match direction {
        ApproximationDirection::Left => "left",
        ApproximationDirection::Right => "right",
    }
}

/// A checked bounded mutation graph with no closure claim.
#[pyclass(name = "IncompleteEquivalenceGraph", module = "auslander", frozen)]
pub(crate) struct PyIncompleteEquivalenceGraph {
    pub(crate) inner: IncompleteEquivalenceGraph,
}

#[pymethods]
impl PyIncompleteEquivalenceGraph {
    /// The number of certified tilting-complex vertices.
    #[getter]
    fn vertex_count(&self) -> usize {
        self.inner.keys().len()
    }

    /// Stable keys for certified vertices in breadth-first order.
    #[getter]
    fn keys(&self) -> Vec<String> {
        self.inner
            .keys()
            .iter()
            .map(|key| key.as_str().to_owned())
            .collect()
    }

    /// Tuples of source, target, direction, and summand for certified edges.
    #[getter]
    fn edges(&self) -> Vec<(usize, usize, &'static str, usize)> {
        self.inner
            .edges()
            .iter()
            .map(|edge| {
                (
                    edge.source(),
                    edge.target(),
                    approximation_direction_name(edge.direction()),
                    edge.summand(),
                )
            })
            .collect()
    }

    /// Tuples of source, direction, summand, and blocker kind.
    #[getter]
    fn blocked(&self) -> Vec<(usize, &'static str, usize, &'static str)> {
        self.inner
            .blocked()
            .iter()
            .map(|blocked| {
                let kind = match blocked.reason() {
                    BlockedMutationReason::SiltingOnly { .. } => "silting_only",
                    BlockedMutationReason::Undetermined(_) => "undetermined",
                };
                (
                    blocked.source(),
                    approximation_direction_name(blocked.direction()),
                    blocked.summand(),
                    kind,
                )
            })
            .collect()
    }

    /// The exact reason discovery stopped.
    #[getter]
    fn stop(&self) -> String {
        variant_name(self.inner.stop())
    }

    #[getter]
    fn completed_mutations(&self) -> usize {
        self.inner.completed_mutations()
    }

    #[getter]
    fn total_terms(&self) -> usize {
        self.inner.total_terms()
    }

    #[getter]
    fn matrix_entries(&self) -> usize {
        self.inner.matrix_entries()
    }

    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "IncompleteEquivalenceGraph(vertices={}, edges={}, stop={:?})",
            self.inner.keys().len(),
            self.inner.edges().len(),
            self.stop()
        )
    }
}

/// Walk the bounded tilting-complex mutation graph from the regular generator.
#[pyfunction]
#[pyo3(signature = (algebra, field=None, limits=None, control=None))]
pub(crate) fn discover_equivalences(
    py: Python<'_>,
    algebra: &PyAlgebra,
    field: Option<&PyPrimeField>,
    limits: Option<&PyEquivalenceDiscoveryLimits>,
    control: Option<&PyComputationControl>,
) -> PyResult<PyIncompleteEquivalenceGraph> {
    let algebra = algebra.algebra_for(py, field, "derived-equivalence discovery")?;
    let limits = limits.map_or_else(DiscoveryLimits::default, |value| value.inner);
    let control = control.map_or_else(ComputationControl::new, |value| value.inner.clone());
    Ok(PyIncompleteEquivalenceGraph {
        inner: py
            .allow_threads(|| discover_tilting_equivalences(&algebra, limits, &control))
            .map_err(engine_error)?,
    })
}

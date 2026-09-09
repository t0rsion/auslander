use super::*;

/// Resource ceilings for deterministic tilting-complex discovery.

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
        max_work_units=16384,
        max_hom_spaces=4096
    ))]
    fn new(
        max_vertices: usize,
        max_directed_mutations: usize,
        max_total_terms: usize,
        max_matrix_entries: usize,
        max_work_units: usize,
        max_hom_spaces: usize,
    ) -> PyEquivalenceDiscoveryLimits {
        PyEquivalenceDiscoveryLimits {
            inner: DiscoveryLimits {
                max_vertices,
                max_directed_mutations,
                max_total_terms,
                max_matrix_entries,
                max_work_units,
                tilting: TiltingComplexLimits { max_hom_spaces },
            },
        }
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
    fn stop(&self) -> &'static str {
        match self.inner.stop() {
            DiscoveryStop::ExhaustedFrontier => "exhausted_frontier",
            DiscoveryStop::Cancelled { .. } => "cancelled",
            DiscoveryStop::MutationLimit { .. } => "mutation_limit",
            DiscoveryStop::WorkLimit { .. } => "work_limit",
            DiscoveryStop::VertexLimit { .. } => "vertex_limit",
            DiscoveryStop::TermLimit { .. } => "term_limit",
            DiscoveryStop::MatrixLimit { .. } => "matrix_limit",
        }
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

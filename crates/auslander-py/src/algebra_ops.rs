use super::*;

#[pymethods]
impl PyAlgebra {
    /// Returns this algebra bound to `field`, or checks an existing binding.
    #[pyo3(name = "over", signature = (field), text_signature = "($self, field)")]
    fn py_over(&self, py: Python<'_>, field: &PyPrimeField) -> PyResult<PyAlgebra> {
        Ok(PyAlgebra::pinned(self.over(py, field.inner)?))
    }

    /// The canonical JSON bytes of the verified completion certificate.
    /// Field-free presentations need `field`; bound algebras may omit it.
    #[pyo3(signature = (field = None), text_signature = "($self, field=None)")]
    fn certificate_json(&self, py: Python<'_>, field: Option<&PyPrimeField>) -> PyResult<String> {
        let algebra = self.algebra_for(py, field, "a certificate")?;
        Ok(algebra.certificate().to_canonical_json())
    }

    /// Builds a right module from row-vector arrow matrices.
    /// `maps[a]` has shape `dims[source(a)] x dims[target(a)]`.
    #[pyo3(signature = (dims, maps, field = None), text_signature = "($self, dims, maps, field=None)")]
    fn module(
        &self,
        py: Python<'_>,
        dims: Vec<usize>,
        maps: Vec<Vec<Vec<i64>>>,
        field: Option<&PyPrimeField>,
    ) -> PyResult<PyRightModule> {
        let algebra = self.algebra_for(py, field, "a module")?;
        let f = algebra.field();
        let quiver = algebra.quiver();
        let mut matrices = Vec::with_capacity(maps.len());
        for (arrow, rows) in maps.iter().enumerate() {
            let cols = quiver
                .arrows()
                .get(arrow)
                .and_then(|&(_, target)| dims.get(target as usize).copied())
                .unwrap_or(0);
            matrices.push(dense_from_rows(
                f,
                rows,
                cols,
                &format!("map for arrow {arrow}"),
            )?);
        }
        Ok(Module::new(algebra, dims, matrices)
            .map_err(value_error)?
            .into())
    }

    /// Builds a right module from sparse row-vector arrow matrices.
    /// Omitted coordinates are zero, and repeated coordinates are rejected.
    #[pyo3(signature = (dims, maps, field = None), text_signature = "($self, dims, maps, field=None)")]
    fn module_sparse(
        &self,
        py: Python<'_>,
        dims: Vec<usize>,
        maps: Vec<Vec<(usize, usize, i64)>>,
        field: Option<&PyPrimeField>,
    ) -> PyResult<PyRightModule> {
        let algebra = self.algebra_for(py, field, "a module")?;
        let f = algebra.field();
        let quiver = algebra.quiver();
        check_sparse_module_shape(quiver, &dims, maps.len())?;
        let matrices = maps
            .iter()
            .enumerate()
            .map(|(arrow, entries)| {
                let (source, target) = quiver.arrows()[arrow];
                dense_from_sparse(
                    f,
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

    /// Builds the simple module at `vertex`.
    #[pyo3(signature = (vertex, field = None), text_signature = "($self, vertex, field=None)")]
    fn simple(
        &self,
        py: Python<'_>,
        vertex: u32,
        field: Option<&PyPrimeField>,
    ) -> PyResult<PyRightModule> {
        self.check_vertex(vertex)?;
        let algebra = self.algebra_for(py, field, "a simple module")?;
        Ok(Module::simple(&algebra, vertex).into())
    }

    /// Builds the indecomposable projective module at `vertex`.
    #[pyo3(signature = (vertex, field = None), text_signature = "($self, vertex, field=None)")]
    fn projective(
        &self,
        py: Python<'_>,
        vertex: u32,
        field: Option<&PyPrimeField>,
    ) -> PyResult<PyRightModule> {
        self.check_vertex(vertex)?;
        let algebra = self.algebra_for(py, field, "a projective module")?;
        Ok(Module::projective(&algebra, vertex).into())
    }

    /// Computes relative normalized bar Hochschild cohomology through `max_degree`.
    #[pyo3(signature = (max_degree, limits, field = None), text_signature = "($self, max_degree, limits, field=None)")]
    fn hochschild_cohomology<'py>(
        &self,
        py: Python<'py>,
        max_degree: usize,
        limits: &PyBarLimits,
        field: Option<&PyPrimeField>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let algebra = self.algebra_for(py, field, "Hochschild cohomology")?;
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

    /// Builds the indecomposable injective module at `vertex`.
    #[pyo3(signature = (vertex, field = None), text_signature = "($self, vertex, field=None)")]
    fn injective(
        &self,
        py: Python<'_>,
        vertex: u32,
        field: Option<&PyPrimeField>,
    ) -> PyResult<PyRightModule> {
        self.check_vertex(vertex)?;
        let algebra = self.algebra_for(py, field, "an injective module")?;
        Ok(Module::injective(&algebra, vertex).into())
    }
}

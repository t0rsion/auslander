use super::*;

/// A basis element or checked construction of Hom_A(M, N): an A-linear map given
/// by one matrix per vertex, acting on row vectors.
///
/// Instances come from Module.hom (a basis of the hom space) or Module.morphism
/// (a checked construction). Every Morphism satisfies all commuting squares.

#[pyclass(name = "Morphism", module = "auslander")]
pub(crate) struct PyMorphism {
    pub(crate) inner: hom::Morphism,
}

impl From<hom::Morphism> for PyMorphism {
    fn from(inner: hom::Morphism) -> Self {
        PyMorphism { inner }
    }
}

impl From<&hom::Morphism> for PyMorphism {
    fn from(morphism: &hom::Morphism) -> Self {
        PyMorphism {
            inner: morphism.clone(),
        }
    }
}

#[pymethods]
impl PyMorphism {
    /// The source module M of f: M -> N.
    #[getter]
    fn source(&self) -> PyRightModule {
        self.inner.source().into()
    }

    /// The target module N of f: M -> N.
    #[getter]
    fn target(&self) -> PyRightModule {
        self.inner.target().into()
    }

    /// The vertex matrices as canonical integers in 0..p: maps[v] is the
    /// dims_source[v] x dims_target[v] matrix at vertex v, one list per row, in
    /// the same shape `algebra.module` and `Module.morphism` accept.
    #[getter]
    fn maps(&self) -> Vec<Vec<Vec<u64>>> {
        let n = self.inner.source().algebra().quiver().num_vertices();
        (0..n).map(|v| self.inner.map_at(v).entries_u64()).collect()
    }

    /// The nonzero vertex-matrix entries as `(row, column, value)` triples.
    #[getter]
    fn sparse_maps(&self) -> Vec<Vec<(usize, usize, u64)>> {
        let n = self.inner.source().algebra().quiver().num_vertices();
        (0..n)
            .map(|vertex| sparse_entries(self.inner.map_at(vertex)))
            .collect()
    }

    /// The matrix at vertex v alone, as canonical integers in 0..p; `maps`
    /// rebuilds every vertex matrix per access. Raises ValueError when v is not
    /// a vertex.
    #[pyo3(text_signature = "($self, v)")]
    fn map_at(&self, v: u32) -> PyResult<Vec<Vec<u64>>> {
        let n = self.inner.source().algebra().quiver().num_vertices();
        if v >= n {
            return Err(PyValueError::new_err(format!(
                "vertex {v} out of range: the quiver has vertices 0..{n}"
            )));
        }
        Ok(self.inner.map_at(v).entries_u64())
    }

    /// Whether every vertex matrix is square and invertible, i.e. the morphism
    /// is an isomorphism.
    #[pyo3(text_signature = "($self)")]
    fn is_isomorphism(&self) -> bool {
        self.inner.is_isomorphism()
    }

    /// Whether every vertex matrix is zero.
    #[getter]
    fn is_zero(&self) -> bool {
        self.inner.is_zero()
    }

    /// The composite "first self, then other": at each vertex the matrix
    /// product self_v · other_v. It runs from the source of self to the target
    /// of other. Raises ValueError unless the target of self is the source
    /// object of other.
    #[pyo3(text_signature = "($self, other)")]
    fn then(&self, other: &PyMorphism) -> PyResult<PyMorphism> {
        Ok(self.inner.then(&other.inner).map_err(value_error)?.into())
    }

    fn __repr__(&self) -> String {
        format!(
            "Morphism(source_dims={:?}, target_dims={:?})",
            self.inner.source().dim_vector(),
            self.inner.target().dim_vector()
        )
    }
}

/// `Hom_A(M, N)` modulo maps that factor through projective modules.
///
/// The denominator and quotient bases are deterministic. `reduce` writes a
/// supplied morphism as one quotient representative plus one projective-factor
/// map.
#[pyclass(name = "StableHomSpace", module = "auslander")]
pub(crate) struct PyStableHomSpace {
    pub(crate) inner: HomQuotient,
}

#[pymethods]
impl PyStableHomSpace {
    /// The source module `M`.
    #[getter]
    fn source(&self) -> PyRightModule {
        self.inner.source().into()
    }

    /// The target module `N`.
    #[getter]
    fn target(&self) -> PyRightModule {
        self.inner.target().into()
    }

    /// `dim_k stable Hom_A(M, N)`.
    #[getter]
    fn dim(&self) -> usize {
        self.inner.dim()
    }

    /// The rank of the subspace of maps that factor through projectives.
    #[getter]
    fn projective_factor_dim(&self) -> usize {
        self.inner.subspace().dim()
    }

    /// A deterministic basis of maps that factor through projectives.
    #[getter]
    fn projective_factor_basis(&self) -> Vec<PyMorphism> {
        (0..self.inner.subspace().dim())
            .map(|index| self.inner.subspace().basis_morphism(index).into())
            .collect()
    }

    /// Deterministic representatives of the stable-Hom basis.
    #[getter]
    fn basis(&self) -> Vec<PyMorphism> {
        let field = self.inner.source().field();
        (0..self.inner.dim())
            .map(|index| {
                let mut coordinates = vec![field.zero(); self.inner.dim()];
                coordinates[index] = field.one();
                self.inner.representative(&coordinates).into()
            })
            .collect()
    }

    /// Whether `morphism` factors through a projective module.
    #[pyo3(text_signature = "($self, morphism)")]
    fn is_projective_factor(&self, morphism: &PyMorphism) -> PyResult<bool> {
        self.inner
            .subspace()
            .contains(&morphism.inner)
            .map_err(value_error)
    }

    /// The quotient representative with the supplied coordinates.
    #[pyo3(text_signature = "($self, coordinates)")]
    fn representative(&self, coordinates: Vec<i64>) -> PyResult<PyMorphism> {
        if coordinates.len() != self.inner.dim() {
            return Err(PyValueError::new_err(format!(
                "stable Hom coordinates have length {}, expected {}",
                coordinates.len(),
                self.inner.dim()
            )));
        }
        let field = self.inner.source().field();
        let coordinates: Vec<Fp> = coordinates
            .into_iter()
            .map(|entry| field.elem(entry))
            .collect();
        Ok(self.inner.representative(&coordinates).into())
    }

    /// Split a morphism into stable coordinates and a projective-factor map.
    #[pyo3(text_signature = "($self, morphism)")]
    fn reduce(&self, morphism: &PyMorphism) -> PyResult<(Vec<u64>, PyMorphism)> {
        let (coordinates, projective_factor) =
            self.inner.reduce(&morphism.inner).map_err(value_error)?;
        Ok((row_u64(&coordinates), projective_factor.into()))
    }

    fn __repr__(&self) -> String {
        format!(
            "StableHomSpace(dim={}, projective_factor_dim={})",
            self.inner.dim(),
            self.inner.subspace().dim()
        )
    }
}

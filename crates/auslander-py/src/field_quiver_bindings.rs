use super::*;

/// The prime field F_p = Z/pZ.
///
/// Primality is checked at construction; p must be a prime below 2^31.

#[pyclass(name = "PrimeField", module = "auslander")]
pub(crate) struct PyPrimeField {
    pub(crate) inner: PrimeField,
}

#[pymethods]
impl PyPrimeField {
    /// F_p for a prime p < 2^31; raises ValueError otherwise.
    #[new]
    #[pyo3(text_signature = "(p)")]
    fn new(p: u64) -> PyResult<Self> {
        Ok(PyPrimeField {
            inner: PrimeField::new(p).map_err(value_error)?,
        })
    }

    /// The characteristic p.
    #[getter]
    fn p(&self) -> u64 {
        self.inner.modulus()
    }

    fn __repr__(&self) -> String {
        format!("PrimeField({})", self.inner.modulus())
    }
}

/// A finite quiver: vertices 0..num_vertices and a list of (source, target) arrows.
///
/// Arrow i of the list gets id i; forbidden words and module maps refer to arrows
/// by these ids. Paths compose left to right: the word [a, b] means "first a,
/// then b" and requires target(a) == source(b).
#[pyclass(name = "Quiver", module = "auslander")]
pub(crate) struct PyQuiver {
    pub(crate) inner: Quiver,
}

#[pymethods]
impl PyQuiver {
    /// A quiver on vertices 0..num_vertices with the given (source, target) arrows;
    /// raises ValueError when an endpoint is out of range.
    #[new]
    #[pyo3(text_signature = "(num_vertices, arrows)")]
    fn new(num_vertices: u32, arrows: Vec<(u32, u32)>) -> PyResult<Self> {
        Ok(PyQuiver {
            inner: Quiver::new(num_vertices, &arrows).map_err(value_error)?,
        })
    }

    /// The number of vertices.
    #[getter]
    fn num_vertices(&self) -> u32 {
        self.inner.num_vertices()
    }

    /// The number of arrows.
    #[getter]
    fn num_arrows(&self) -> usize {
        self.inner.num_arrows()
    }

    /// The arrows as (source, target) pairs, arrow i at index i.
    #[getter]
    fn arrows(&self) -> Vec<(u32, u32)> {
        self.inner.arrows().to_vec()
    }

    fn __repr__(&self) -> String {
        format!(
            "Quiver(vertices={}, arrows={})",
            self.inner.num_vertices(),
            self.inner.num_arrows()
        )
    }
}

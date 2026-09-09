use super::*;

/// A complete bounded self-Ext algebra with deterministic Yoneda tensors.
///
/// Complete means that the minimal resolution ended within `bound`. Every
/// stored degree and product is exact. Higher degrees vanish.
#[pyclass(name = "ExtAlgebra", module = "auslander", frozen)]

pub(crate) struct PyExtAlgebra {
    pub(crate) inner: RustExtAlgebra,
}

#[pymethods]
impl PyExtAlgebra {
    /// The module whose self-Ext algebra is stored.
    #[getter]
    fn module(&self) -> PyRightModule {
        self.inner.module().into()
    }

    /// The last stored cohomological degree.
    #[getter]
    fn bound(&self) -> usize {
        self.inner.bound()
    }

    /// The dimensions from degree zero through `bound`.
    #[getter]
    fn dimensions(&self) -> Vec<usize> {
        ext_algebra_dimensions(&self.inner)
    }

    /// The finite resolution status that makes this result complete.
    #[getter]
    fn resolution_status(&self) -> PyResolutionStatus {
        PyResolutionStatus {
            end: self.inner.resolution_end(),
        }
    }

    /// The deterministic self-Ext space in `degree`.
    #[pyo3(text_signature = "($self, degree)")]
    fn degree(&self, degree: usize) -> PyResult<PyExtSpace> {
        ext_algebra_space(&self.inner, degree)
    }

    /// The standard coordinate basis in `degree`.
    #[pyo3(text_signature = "($self, degree)")]
    fn basis(&self, degree: usize) -> PyResult<Vec<PyExtClass>> {
        ext_algebra_basis(&self.inner, degree)
    }

    /// The checked degree-zero Yoneda unit.
    #[getter]
    fn unit(&self) -> PyExtClass {
        PyExtClass {
            inner: self.inner.unit().clone(),
        }
    }

    /// The tensor for products in the ordered degree pair.
    #[pyo3(text_signature = "($self, left_degree, right_degree)")]
    fn multiplication(
        &self,
        left_degree: usize,
        right_degree: usize,
    ) -> PyResult<PyExtMultiplication> {
        ext_algebra_multiplication(&self.inner, left_degree, right_degree)
    }

    /// Multiplies two classes through the stored tensor.
    #[pyo3(text_signature = "($self, left, right)")]
    fn multiply(&self, left: &PyExtClass, right: &PyExtClass) -> PyResult<PyExtClass> {
        ext_algebra_multiply(&self.inner, left, right)
    }

    /// Every basis-pair product in canonical graded order.
    #[pyo3(text_signature = "($self)")]
    fn product_records(&self) -> Vec<PyExtProductRecord> {
        ext_algebra_product_records(&self.inner)
    }

    /// Rebuilds every space, tensor, witness, unit, and algebra law.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "ExtAlgebra(bound={}, dimensions={:?})",
            self.inner.bound(),
            self.dimensions()
        )
    }
}

/// An exact bounded self-Ext layer whose next syzygy is nonzero.
///
/// Every degree through `bound` and every stored product is exact. The value
/// makes no claim about the first omitted degree or any degree after it.
#[pyclass(name = "IncompleteExtAlgebra", module = "auslander", frozen)]
pub(crate) struct PyIncompleteExtAlgebra {
    pub(crate) inner: ExtAlgebraCut,
}

#[pymethods]
impl PyIncompleteExtAlgebra {
    /// The module whose self-Ext layer is stored.
    #[getter]
    fn module(&self) -> PyRightModule {
        self.inner.algebra().module().into()
    }

    /// The last exact stored degree.
    #[getter]
    fn bound(&self) -> usize {
        self.inner.algebra().bound()
    }

    /// The first degree outside the stored exact layer.
    #[getter]
    fn first_omitted_degree(&self) -> usize {
        self.inner.first_omitted_degree()
    }

    /// The dimensions from degree zero through `bound`.
    #[getter]
    fn dimensions(&self) -> Vec<usize> {
        ext_algebra_dimensions(self.inner.algebra())
    }

    /// The cut resolution status that proves the next syzygy is nonzero.
    #[getter]
    fn resolution_status(&self) -> PyResolutionStatus {
        PyResolutionStatus {
            end: self.inner.algebra().resolution_end(),
        }
    }

    /// The deterministic self-Ext space in `degree`.
    #[pyo3(text_signature = "($self, degree)")]
    fn degree(&self, degree: usize) -> PyResult<PyExtSpace> {
        ext_algebra_space(self.inner.algebra(), degree)
    }

    /// The standard coordinate basis in `degree`.
    #[pyo3(text_signature = "($self, degree)")]
    fn basis(&self, degree: usize) -> PyResult<Vec<PyExtClass>> {
        ext_algebra_basis(self.inner.algebra(), degree)
    }

    /// The checked degree-zero Yoneda unit.
    #[getter]
    fn unit(&self) -> PyExtClass {
        PyExtClass {
            inner: self.inner.algebra().unit().clone(),
        }
    }

    /// The tensor for products in the ordered degree pair.
    #[pyo3(text_signature = "($self, left_degree, right_degree)")]
    fn multiplication(
        &self,
        left_degree: usize,
        right_degree: usize,
    ) -> PyResult<PyExtMultiplication> {
        ext_algebra_multiplication(self.inner.algebra(), left_degree, right_degree)
    }

    /// Multiplies two classes through the stored tensor.
    #[pyo3(text_signature = "($self, left, right)")]
    fn multiply(&self, left: &PyExtClass, right: &PyExtClass) -> PyResult<PyExtClass> {
        ext_algebra_multiply(self.inner.algebra(), left, right)
    }

    /// Every basis-pair product in canonical graded order.
    #[pyo3(text_signature = "($self)")]
    fn product_records(&self) -> Vec<PyExtProductRecord> {
        ext_algebra_product_records(self.inner.algebra())
    }

    /// Rebuilds the exact layer and rechecks the first omitted degree.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "IncompleteExtAlgebra(bound={}, first_omitted_degree={}, dimensions={:?})",
            self.bound(),
            self.inner.first_omitted_degree(),
            self.dimensions()
        )
    }
}

/// One deterministic Yoneda product tensor between two stored Ext degrees.
#[pyclass(name = "ExtMultiplication", module = "auslander", frozen)]
pub(crate) struct PyExtMultiplication {
    pub(crate) inner: MultiplicationTensor,
    pub(crate) left_basis: Vec<ext::ExtClass>,
    pub(crate) right_basis: Vec<ext::ExtClass>,
}

#[pymethods]
impl PyExtMultiplication {
    #[getter]
    fn left_degree(&self) -> usize {
        self.inner.left_degree()
    }

    #[getter]
    fn right_degree(&self) -> usize {
        self.inner.right_degree()
    }

    #[getter]
    fn output_degree(&self) -> usize {
        self.inner.output_degree()
    }

    #[getter]
    fn shape(&self) -> (usize, usize, usize) {
        (
            self.inner.left_dim(),
            self.inner.right_dim(),
            self.inner.output_dim(),
        )
    }

    /// The flat tensor in `(left basis, right basis, output coordinate)` order.
    #[getter]
    fn coefficients(&self) -> Vec<u64> {
        row_u64(self.inner.coefficients())
    }

    /// Coordinates of one basis-pair product.
    #[pyo3(text_signature = "($self, left, right)")]
    fn basis_product(&self, left: usize, right: usize) -> PyResult<Vec<u64>> {
        self.inner
            .basis_product(left, right)
            .map(row_u64)
            .ok_or_else(|| {
                PyValueError::new_err(format!(
                    "basis pair ({left}, {right}) is outside tensor shape ({}, {})",
                    self.inner.left_dim(),
                    self.inner.right_dim()
                ))
            })
    }

    /// The stored checked class for one basis-pair product.
    #[pyo3(text_signature = "($self, left, right)")]
    fn product(&self, left: usize, right: usize) -> PyResult<PyExtClass> {
        self.inner
            .product(left, right)
            .cloned()
            .map(|inner| PyExtClass { inner })
            .ok_or_else(|| {
                PyValueError::new_err(format!(
                    "basis pair ({left}, {right}) is outside tensor shape ({}, {})",
                    self.inner.left_dim(),
                    self.inner.right_dim()
                ))
            })
    }

    /// The chain-lift witness for one basis-pair product.
    #[pyo3(text_signature = "($self, left, right)")]
    fn witness(&self, left: usize, right: usize) -> PyResult<PyExtProductWitness> {
        let inner = self.inner.witness(left, right).cloned().ok_or_else(|| {
            PyValueError::new_err(format!(
                "basis pair ({left}, {right}) is outside tensor shape ({}, {})",
                self.inner.left_dim(),
                self.inner.right_dim()
            ))
        })?;
        Ok(PyExtProductWitness {
            inner,
            left: self.left_basis[left].clone(),
            right: self.right_basis[right].clone(),
        })
    }

    fn __repr__(&self) -> String {
        format!(
            "ExtMultiplication(degrees=({}, {}, {}), shape={:?})",
            self.inner.left_degree(),
            self.inner.right_degree(),
            self.inner.output_degree(),
            self.shape()
        )
    }
}

/// One canonical basis-pair Yoneda product with its checked chain lifts.
#[pyclass(name = "ExtProductRecord", module = "auslander", frozen)]
pub(crate) struct PyExtProductRecord {
    pub(crate) left_degree: usize,
    pub(crate) left_basis: usize,
    pub(crate) right_degree: usize,
    pub(crate) right_basis: usize,
    pub(crate) coordinates: Vec<Fp>,
    pub(crate) product: ext::ExtClass,
    pub(crate) witness: ProductWitness,
    pub(crate) left: ext::ExtClass,
    pub(crate) right: ext::ExtClass,
}

#[pymethods]
impl PyExtProductRecord {
    #[getter]
    fn left_degree(&self) -> usize {
        self.left_degree
    }

    #[getter]
    fn left_basis(&self) -> usize {
        self.left_basis
    }

    #[getter]
    fn right_degree(&self) -> usize {
        self.right_degree
    }

    #[getter]
    fn right_basis(&self) -> usize {
        self.right_basis
    }

    #[getter]
    fn coordinates(&self) -> Vec<u64> {
        row_u64(&self.coordinates)
    }

    #[getter]
    fn product(&self) -> PyExtClass {
        PyExtClass {
            inner: self.product.clone(),
        }
    }

    #[getter]
    fn witness(&self) -> PyExtProductWitness {
        PyExtProductWitness {
            inner: self.witness.clone(),
            left: self.left.clone(),
            right: self.right.clone(),
        }
    }

    /// Rechecks the stored class and chain lifts against the two basis factors.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self, py: Python<'_>) -> bool {
        self.product.coordinates() == self.coordinates
            && py.allow_threads(|| self.witness.verify(&self.left, &self.right, &self.product))
    }

    fn __repr__(&self) -> String {
        format!(
            "ExtProductRecord(left=({}, {}), right=({}, {}), coordinates={:?})",
            self.left_degree,
            self.left_basis,
            self.right_degree,
            self.right_basis,
            self.coordinates()
        )
    }
}

use super::*;

#[pyclass(name = "ExtSpace", module = "auslander", frozen)]
pub(crate) struct PyExtSpace {
    pub(crate) inner: ext::ExtSpace,
}

#[pymethods]
impl PyExtSpace {
    /// dim_k Ext^degree(source, target), the same number `Module.ext_dim`
    /// reports.
    #[getter]
    fn dim(&self) -> usize {
        self.inner.dim()
    }

    /// The source module M.
    #[getter]
    fn source(&self) -> PyRightModule {
        self.inner.source().into()
    }

    /// The target module N.
    #[getter]
    fn target(&self) -> PyRightModule {
        self.inner.target().into()
    }

    /// The cohomological degree k.
    #[getter]
    fn degree(&self) -> usize {
        self.inner.degree()
    }

    /// The basis of the space as ExtClass objects: the class of coordinate
    /// vector e_i at index i.
    #[pyo3(text_signature = "($self)")]
    fn basis(&self) -> Vec<PyExtClass> {
        let field = self.inner.source().field();
        (0..self.inner.dim())
            .map(|i| {
                let mut coords = vec![field.zero(); self.inner.dim()];
                coords[i] = field.one();
                PyExtClass {
                    inner: self
                        .inner
                        .class_from_coordinates(&coords)
                        .expect("a unit vector has the space's dimension and canonical entries"),
                }
            })
            .collect()
    }

    /// The class with these coordinates over the basis, entries reduced mod p;
    /// raises ValueError when the number of coordinates is not `dim`.
    #[pyo3(text_signature = "($self, coords)")]
    fn class_from_coordinates(&self, coords: Vec<i64>) -> PyResult<PyExtClass> {
        let field = self.inner.source().field();
        let coords: Vec<Fp> = coords.into_iter().map(|c| field.elem(c)).collect();
        Ok(PyExtClass {
            inner: self
                .inner
                .class_from_coordinates(&coords)
                .map_err(ext_class_error)?,
        })
    }

    /// The Yoneda unit, the class of the identity in Ext^0(M, M); raises
    /// ValueError unless the space has degree 0 and both endpoints are the
    /// same module object.
    #[pyo3(text_signature = "($self)")]
    fn identity_class(&self) -> PyResult<PyExtClass> {
        Ok(PyExtClass {
            inner: self.inner.identity_class().map_err(ext_class_error)?,
        })
    }

    /// The zero class of the space.
    #[pyo3(text_signature = "($self)")]
    fn zero_class(&self) -> PyExtClass {
        PyExtClass {
            inner: self.inner.zero_class(),
        }
    }

    fn __repr__(&self) -> String {
        format!(
            "ExtSpace(degree={}, dim={}, source_dims={:?}, target_dims={:?})",
            self.inner.degree(),
            self.inner.dim(),
            self.inner.source().dim_vector(),
            self.inner.target().dim_vector()
        )
    }
}

/// An element of an ExtSpace: coordinates over the space's basis.
///
/// Arithmetic and comparison need compatible spaces, which means the same
/// source object, the same target object, and equal degrees. Incompatible
/// operands raise IncompatibleSpacesError, a ValueError subclass, so `==`
/// never answers False for classes that were never comparable. `then` is the
/// Yoneda product in the endpoint order of morphism composition:
/// Ext^m(M, N) x Ext^n(N, L) -> Ext^{m+n}(M, L). Instances are immutable.
#[pyclass(name = "ExtClass", module = "auslander", frozen)]
pub(crate) struct PyExtClass {
    pub(crate) inner: ext::ExtClass,
}

#[pymethods]
impl PyExtClass {
    /// The source module of the class's space.
    #[getter]
    fn source(&self) -> PyRightModule {
        self.inner.space().source().into()
    }

    /// The target module of the class's space.
    #[getter]
    fn target(&self) -> PyRightModule {
        self.inner.space().target().into()
    }

    /// The cohomological degree of the class's space.
    #[getter]
    fn degree(&self) -> usize {
        self.inner.space().degree()
    }

    /// The coordinates over the space's basis, as canonical integers in 0..p.
    #[getter]
    fn coordinates(&self) -> Vec<u64> {
        row_u64(self.inner.coordinates())
    }

    /// Whether every coordinate is zero.
    #[getter]
    fn is_zero(&self) -> bool {
        self.inner.is_zero()
    }

    /// A representative cocycle P_degree -> target as a Morphism. Different
    /// representatives of one class differ by a coboundary; this one is the
    /// combination of the space's basis representatives.
    #[pyo3(text_signature = "($self)")]
    fn representative(&self) -> PyMorphism {
        self.inner.representative().into()
    }

    /// The Yoneda product of this class with `other`, in composition order:
    /// this class in Ext^m(M, N) and `other` in Ext^n(N, L) give a class in
    /// Ext^{m+n}(M, L). Raises IncompatibleSpacesError when this class's
    /// target is not `other`'s source.
    #[pyo3(text_signature = "($self, other)")]
    fn then(&self, py: Python<'_>, other: &PyExtClass) -> PyResult<PyExtClass> {
        Ok(PyExtClass {
            inner: py
                .allow_threads(|| self.inner.then(&other.inner))
                .map_err(ext_class_error)?,
        })
    }

    /// The Yoneda product and the deterministic chain lifts that compute it.
    #[pyo3(text_signature = "($self, other)")]
    fn then_with_witness(
        &self,
        py: Python<'_>,
        other: &PyExtClass,
    ) -> PyResult<(PyExtClass, PyExtProductWitness)> {
        let (product, witness) = py
            .allow_threads(|| self.inner.then_with_witness(&other.inner))
            .map_err(ext_class_error)?;
        Ok((
            PyExtClass { inner: product },
            PyExtProductWitness {
                inner: witness,
                left: self.inner.clone(),
                right: other.inner.clone(),
            },
        ))
    }

    /// The extension 0 -> target -> E -> source -> 0 realizing this class, as
    /// a ShortExactSequence; the zero class gives the split sequence. Raises
    /// ValueError unless the degree is 1, the only degree in which a class is
    /// an extension.
    #[pyo3(text_signature = "($self)")]
    fn extension(&self, py: Python<'_>) -> PyResult<PyShortExactSequence> {
        Ok(PyShortExactSequence {
            inner: py
                .allow_threads(|| sequence::ShortExactSequence::from_ext1(&self.inner))
                .map_err(sequence_error)?,
        })
    }

    fn __add__(&self, other: &PyExtClass) -> PyResult<PyExtClass> {
        Ok(PyExtClass {
            inner: self.inner.add(&other.inner).map_err(ext_class_error)?,
        })
    }

    fn __neg__(&self) -> PyExtClass {
        PyExtClass {
            inner: self.inner.neg(),
        }
    }

    fn __mul__(&self, scalar: i64) -> PyExtClass {
        let field = self.inner.space().source().field();
        PyExtClass {
            inner: self.inner.scale(field.elem(scalar)),
        }
    }

    fn __rmul__(&self, scalar: i64) -> PyExtClass {
        self.__mul__(scalar)
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        let Ok(other) = other.extract::<PyRef<'_, PyExtClass>>() else {
            return Err(IncompatibleSpacesError::new_err(
                "an Ext class compares only with another Ext class of a compatible space",
            ));
        };
        self.inner.equals(&other.inner).map_err(ext_class_error)
    }

    fn __repr__(&self) -> String {
        format!(
            "ExtClass(degree={}, coordinates={:?})",
            self.inner.space().degree(),
            self.coordinates()
        )
    }
}

/// The deterministic chain lifts behind one Yoneda product.
#[pyclass(name = "ExtProductWitness", module = "auslander", frozen)]
pub(crate) struct PyExtProductWitness {
    pub(crate) inner: ProductWitness,
    pub(crate) left: ext::ExtClass,
    pub(crate) right: ext::ExtClass,
}

#[pymethods]
impl PyExtProductWitness {
    /// The lifts `phi_0, ..., phi_n` in degree order.
    #[getter]
    fn lifts(&self) -> Vec<PyMorphism> {
        wrap_all(self.inner.lifts())
    }

    /// Rechecks the lifts against the two retained factors and `product`.
    #[pyo3(text_signature = "($self, product)")]
    fn verify(&self, py: Python<'_>, product: &PyExtClass) -> bool {
        py.allow_threads(|| self.inner.verify(&self.left, &self.right, &product.inner))
    }

    fn __repr__(&self) -> String {
        format!(
            "ExtProductWitness(left_degree={}, right_degree={}, lifts={})",
            self.left.space().degree(),
            self.right.space().degree(),
            self.inner.lifts().len()
        )
    }
}

pub(crate) fn ext_algebra_dimensions(algebra: &RustExtAlgebra) -> Vec<usize> {
    algebra.spaces().iter().map(ext::ExtSpace::dim).collect()
}

pub(crate) fn ext_algebra_space(algebra: &RustExtAlgebra, degree: usize) -> PyResult<PyExtSpace> {
    let inner = algebra.space(degree).ok_or_else(|| {
        PyValueError::new_err(format!(
            "Ext degree {degree} is outside 0..={}",
            algebra.bound()
        ))
    })?;
    Ok(PyExtSpace {
        inner: inner.clone(),
    })
}

pub(crate) fn ext_algebra_basis(
    algebra: &RustExtAlgebra,
    degree: usize,
) -> PyResult<Vec<PyExtClass>> {
    let basis = algebra.basis(degree).ok_or_else(|| {
        PyValueError::new_err(format!(
            "Ext degree {degree} is outside 0..={}",
            algebra.bound()
        ))
    })?;
    Ok(basis
        .iter()
        .cloned()
        .map(|inner| PyExtClass { inner })
        .collect())
}

pub(crate) fn ext_algebra_multiplication(
    algebra: &RustExtAlgebra,
    left_degree: usize,
    right_degree: usize,
) -> PyResult<PyExtMultiplication> {
    let inner = algebra
        .multiplication(left_degree, right_degree)
        .ok_or_else(|| {
            PyValueError::new_err(format!(
                "Ext degree sum {left_degree} + {right_degree} is outside 0..={}",
                algebra.bound()
            ))
        })?;
    Ok(PyExtMultiplication {
        inner: inner.clone(),
        left_basis: algebra
            .basis(left_degree)
            .expect("a stored tensor has its left grade")
            .to_vec(),
        right_basis: algebra
            .basis(right_degree)
            .expect("a stored tensor has its right grade")
            .to_vec(),
    })
}

pub(crate) fn ext_algebra_product_records(algebra: &RustExtAlgebra) -> Vec<PyExtProductRecord> {
    algebra
        .product_records()
        .map(|record| PyExtProductRecord {
            left_degree: record.left_degree(),
            left_basis: record.left_basis(),
            right_degree: record.right_degree(),
            right_basis: record.right_basis(),
            coordinates: record.coordinates().to_vec(),
            product: record.class().clone(),
            witness: record.witness().clone(),
            left: algebra
                .basis(record.left_degree())
                .expect("a product record has its left grade")[record.left_basis()]
            .clone(),
            right: algebra
                .basis(record.right_degree())
                .expect("a product record has its right grade")[record.right_basis()]
            .clone(),
        })
        .collect()
}

pub(crate) fn ext_algebra_multiply(
    algebra: &RustExtAlgebra,
    left: &PyExtClass,
    right: &PyExtClass,
) -> PyResult<PyExtClass> {
    Ok(PyExtClass {
        inner: algebra
            .multiply(&left.inner, &right.inner)
            .map_err(ext_algebra_product_error)?,
    })
}

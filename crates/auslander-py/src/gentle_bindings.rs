use super::*;

use auslander::algebra_isomorphism::{AlgebraIsomorphism, GentleMatchError};
use auslander::gentle::{
    GentleDerivedInvariant, GentleError, GentleKey, GentlePresentation, GentleThread, Sign,
    connected_gentle_algebras, connected_gentle_keys,
};

/// A failed gentle recognition as NotGentleError with `kind` attached.
pub(crate) fn gentle_error(error: &GentleError, message: String) -> PyErr {
    let kind = variant_name(error);
    attach(NotGentleError::new_err(message), |value| {
        value.setattr("kind", kind)
    })
}

fn gentle_match_error(error: GentleMatchError) -> PyErr {
    match &error {
        GentleMatchError::SourceNotGentle(inner) | GentleMatchError::TargetNotGentle(inner) => {
            gentle_error(inner, error.to_string())
        }
        GentleMatchError::FieldMismatch { .. } | GentleMatchError::DifferentKeys => {
            value_error(error)
        }
    }
}

fn sign_value(sign: Sign) -> i8 {
    match sign {
        Sign::Plus => 1,
        Sign::Minus => -1,
    }
}

fn arrow_pairs(pairs: &[(ArrowId, ArrowId)]) -> Vec<(u32, u32)> {
    pairs
        .iter()
        .map(|&(left, right)| (left.0, right.0))
        .collect()
}

/// The canonical form of a connected gentle presentation up to isomorphism
/// of bound quivers.
///
/// Two presentations have equal keys exactly when they are isomorphic as
/// bound quivers. `algebra(field)` rebuilds the canonical presentation.
#[pyclass(name = "GentleKey", module = "auslander", frozen, eq, ord, hash)]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct PyGentleKey {
    inner: GentleKey,
}

#[pymethods]
impl PyGentleKey {
    #[getter]
    fn vertices(&self) -> u32 {
        self.inner.vertices()
    }

    /// The arrows as `(source, target)` pairs in canonical order.
    #[getter]
    fn arrows(&self) -> Vec<(u32, u32)> {
        self.inner.arrows().to_vec()
    }

    /// Every relation `a·b` as the pair `(a, b)` of canonical arrow ids.
    #[getter]
    fn relations(&self) -> Vec<(u32, u32)> {
        arrow_pairs(self.inner.relations())
    }

    /// The algebra of the canonical presentation over `field`.
    fn algebra(&self, py: Python<'_>, field: &PyPrimeField) -> PyResult<PyAlgebra> {
        py.allow_threads(|| self.inner.algebra(field.inner))
            .map(PyAlgebra::pinned)
            .map_err(build_error)
    }

    fn __repr__(&self) -> String {
        format!(
            "GentleKey(vertices={}, arrows={:?}, relations={:?})",
            self.inner.vertices(),
            self.inner.arrows(),
            self.relations()
        )
    }
}

/// The complete derived invariant of a gentle presentation: the
/// Avella-Alaminos-Geiss function, the genus, and the winding class.
///
/// Two finite-dimensional connected gentle algebras over one field are
/// derived equivalent exactly when their values are equal (Amiot, Plamondon,
/// and Schroll, arXiv:1904.02555, Theorem 5.4). `winding_class` is
/// `planar`, `gcd k`, `odd`, `even`, or `arf a`.
#[pyclass(
    name = "GentleDerivedInvariant",
    module = "auslander",
    frozen,
    eq,
    ord,
    hash
)]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct PyGentleDerivedInvariant {
    inner: GentleDerivedInvariant,
}

#[pymethods]
impl PyGentleDerivedInvariant {
    #[getter]
    fn aag_function(&self) -> Vec<(usize, usize)> {
        self.inner.aag_function().pairs().to_vec()
    }

    #[getter]
    fn genus(&self) -> usize {
        self.inner.genus()
    }

    #[getter]
    fn winding_class(&self) -> String {
        self.inner.winding_class().to_string()
    }

    fn __repr__(&self) -> String {
        format!(
            "GentleDerivedInvariant(aag_function={}, genus={}, winding_class={:?})",
            self.inner.aag_function(),
            self.inner.genus(),
            self.winding_class()
        )
    }
}

/// A maximal permitted or forbidden thread of a gentle presentation.
///
/// `arrows` lists arrow ids in path order; a trivial thread has none and
/// starts and ends at one vertex. `sigma` and `epsilon` are the signs `1` or
/// `-1` of Butler and Ringel at the start and the end.
#[pyclass(name = "GentleThread", module = "auslander", frozen)]
pub(crate) struct PyGentleThread {
    inner: GentleThread,
}

#[pymethods]
impl PyGentleThread {
    #[getter]
    fn start(&self) -> u32 {
        self.inner.start()
    }

    #[getter]
    fn end(&self) -> u32 {
        self.inner.end()
    }

    #[getter]
    fn arrows(&self) -> Vec<u32> {
        self.inner.arrows().iter().map(|arrow| arrow.0).collect()
    }

    #[getter]
    fn sigma(&self) -> i8 {
        sign_value(self.inner.sigma())
    }

    #[getter]
    fn epsilon(&self) -> i8 {
        sign_value(self.inner.epsilon())
    }

    fn __len__(&self) -> usize {
        self.inner.length()
    }

    fn __repr__(&self) -> String {
        format!(
            "GentleThread(start={}, end={}, arrows={:?})",
            self.inner.start(),
            self.inner.end(),
            self.arrows()
        )
    }
}

fn threads(threads: &[GentleThread]) -> Vec<PyGentleThread> {
    threads
        .iter()
        .map(|thread| PyGentleThread {
            inner: thread.clone(),
        })
        .collect()
}

/// A recognized gentle presentation: the stored quiver and relations with
/// their sign functions and threads.
///
/// `Algebra.gentle()` builds it. Recognition reads the stored presentation.
/// Loops, parallel arrows, and cycles are allowed.
#[pyclass(name = "GentlePresentation", module = "auslander", frozen)]
pub(crate) struct PyGentlePresentation {
    inner: GentlePresentation,
}

#[pymethods]
impl PyGentlePresentation {
    #[getter]
    fn algebra(&self) -> PyAlgebra {
        PyAlgebra::pinned(self.inner.algebra().clone())
    }

    /// Every relation `a·b` as the pair `(a, b)` of arrow ids.
    #[getter]
    fn relations(&self) -> Vec<(u32, u32)> {
        arrow_pairs(self.inner.relations())
    }

    /// The Avella-Alaminos-Geiss function as sorted pairs `(n, m)`.
    ///
    /// Derived equivalent gentle algebras have equal functions.
    #[getter]
    fn aag_function(&self) -> Vec<(usize, usize)> {
        self.inner.aag_function().pairs().to_vec()
    }

    /// The genus `(n - M - b + 2) / 2` of the surface model, with `M`
    /// permitted threads and `b` pairs in the AAG function.
    #[getter]
    fn genus(&self) -> usize {
        self.inner.genus()
    }

    /// The complete derived invariant of this presentation.
    fn complete_invariant(&self) -> PyGentleDerivedInvariant {
        PyGentleDerivedInvariant {
            inner: self.inner.complete_invariant(),
        }
    }

    /// The canonical key of this presentation.
    #[getter]
    fn key(&self) -> PyGentleKey {
        PyGentleKey {
            inner: self.inner.key(),
        }
    }

    #[getter]
    fn permitted_threads(&self) -> Vec<PyGentleThread> {
        threads(self.inner.permitted_threads())
    }

    #[getter]
    fn forbidden_threads(&self) -> Vec<PyGentleThread> {
        threads(self.inner.forbidden_threads())
    }

    /// The oriented cycles whose consecutive arrow pairs are all relations,
    /// as lists of arrow ids.
    #[getter]
    fn full_relation_cycles(&self) -> Vec<Vec<u32>> {
        self.inner
            .full_relation_cycles()
            .iter()
            .map(|cycle| cycle.iter().map(|arrow| arrow.0).collect())
            .collect()
    }

    fn __repr__(&self) -> String {
        format!(
            "GentlePresentation(vertices={}, arrows={}, relations={}, genus={}, aag_function={})",
            self.inner.algebra().quiver().num_vertices(),
            self.inner.algebra().quiver().num_arrows(),
            self.inner.relations().len(),
            self.inner.genus(),
            self.inner.aag_function()
        )
    }
}

/// An algebra map `A -> B` given by a vertex bijection and one normal-word
/// coordinate vector per arrow of `A`.
///
/// `verify()` decides from this data alone that the map is an isomorphism.
/// `AlgebraIsomorphism.from_gentle(source, target)` builds the bound-quiver
/// isomorphism of two gentle presentations with equal keys.
#[pyclass(name = "AlgebraIsomorphism", module = "auslander", frozen)]
pub(crate) struct PyAlgebraIsomorphism {
    pub(crate) inner: AlgebraIsomorphism,
}

#[pymethods]
impl PyAlgebraIsomorphism {
    /// The isomorphism between two gentle presentations with equal keys.
    ///
    /// Raises NotGentleError when a presentation is not gentle, and
    /// ValueError when the fields or the keys differ.
    #[staticmethod]
    #[pyo3(signature = (source, target, field = None))]
    fn from_gentle(
        py: Python<'_>,
        source: &PyAlgebra,
        target: &PyAlgebra,
        field: Option<&PyPrimeField>,
    ) -> PyResult<PyAlgebraIsomorphism> {
        let source = source.algebra_for(py, field, "an isomorphism")?;
        let target = target.algebra_for(py, field, "an isomorphism")?;
        AlgebraIsomorphism::from_gentle(&source, &target)
            .map(|inner| PyAlgebraIsomorphism { inner })
            .map_err(gentle_match_error)
    }

    #[getter]
    fn source(&self) -> PyAlgebra {
        PyAlgebra::pinned(self.inner.source().clone())
    }

    #[getter]
    fn target(&self) -> PyAlgebra {
        PyAlgebra::pinned(self.inner.target().clone())
    }

    /// Vertex `v` of the source goes to `vertex_map[v]`.
    #[getter]
    fn vertex_map(&self) -> Vec<u32> {
        self.inner.vertex_map().to_vec()
    }

    /// The image of each source arrow over the normal-word basis of the
    /// target, entries in `0..p`.
    #[getter]
    fn arrow_images(&self) -> Vec<Vec<u64>> {
        self.inner
            .arrow_images()
            .iter()
            .map(|image| row_u64(image))
            .collect()
    }

    /// Checks the vertex bijection, the arrow corners, the relations, the
    /// span of the arrow space modulo `rad^2`, and the dimensions.
    fn verify(&self, py: Python<'_>) -> bool {
        py.allow_threads(|| self.inner.verify())
    }

    fn __repr__(&self) -> String {
        format!(
            "AlgebraIsomorphism(vertex_map={:?}, arrows={})",
            self.inner.vertex_map(),
            self.inner.arrow_images().len()
        )
    }
}

#[pymethods]
impl PyAlgebra {
    /// Recognizes the stored presentation as gentle.
    ///
    /// Raises NotGentleError, with `kind` naming the failed condition, when
    /// recognition fails. A failure proves nothing about the algebra: an
    /// isomorphic presentation can be gentle. Field-free presentations need
    /// `field`.
    #[pyo3(signature = (field = None))]
    fn gentle(
        &self,
        py: Python<'_>,
        field: Option<&PyPrimeField>,
    ) -> PyResult<PyGentlePresentation> {
        let algebra = self.algebra_for(py, field, "a gentle presentation")?;
        GentlePresentation::new(&algebra)
            .map(|inner| PyGentlePresentation { inner })
            .map_err(|error| gentle_error(&error, error.to_string()))
    }
}

/// The canonical key of every connected gentle presentation with exactly
/// `vertices` vertices and a finite-dimensional algebra, sorted.
///
/// There is one key per isomorphism class of bound quiver. Loops, parallel
/// arrows, and full relation cycles are included. `vertices = 1` gives 2
/// algebras and `vertices = 4` gives 894.
#[pyfunction(name = "connected_gentle_keys")]
pub(crate) fn py_connected_gentle_keys(py: Python<'_>, vertices: u32) -> Vec<PyGentleKey> {
    py.allow_threads(|| connected_gentle_keys(vertices))
        .into_iter()
        .map(|inner| PyGentleKey { inner })
        .collect()
}

/// The algebra over `field` of every key of `connected_gentle_keys`, in key
/// order.
#[pyfunction(name = "connected_gentle_algebras")]
pub(crate) fn py_connected_gentle_algebras(
    py: Python<'_>,
    vertices: u32,
    field: &PyPrimeField,
) -> PyResult<Vec<PyAlgebra>> {
    let family = py
        .allow_threads(|| connected_gentle_algebras(vertices, field.inner))
        .map_err(build_error)?;
    Ok(family.into_iter().map(PyAlgebra::pinned).collect())
}

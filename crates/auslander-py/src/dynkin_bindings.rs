use super::*;

/// One of the five simply laced diagram families. A and D are parametrized by
/// an integer; E6, E7 and E8 each name a single diagram.

#[pyclass(name = "DiagramFamily", module = "auslander", frozen, eq, hash)]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum PyDiagramFamily {
    A,
    D,
    E6,
    E7,
    E8,
}

/// A family with the parameter its family takes: the checked form of the
/// (family, n) pair a diagram constructor receives. The Dynkin and Euclidean
/// families carry the same constraints, so both constructors validate through
/// this one type.
pub(crate) enum DiagramName {
    A(usize),
    D(usize),
    E6,
    E7,
    E8,
}

/// The checked (family, n) pair, or the ValueError naming the constraint it
/// broke: A needs an integer n >= 1, D an integer n >= 4, and E6, E7, E8 take
/// n = None. `what` names the type in the message ("DynkinType").
pub(crate) fn checked_diagram(
    what: &str,
    family: PyDiagramFamily,
    n: Option<usize>,
) -> PyResult<DiagramName> {
    match family {
        PyDiagramFamily::A => checked_diagram_parameter(what, "A", n, 1).map(DiagramName::A),
        PyDiagramFamily::D => checked_diagram_parameter(what, "D", n, 4).map(DiagramName::D),
        exceptional => checked_exceptional_diagram(what, exceptional, n),
    }
}

pub(crate) fn checked_diagram_parameter(
    what: &str,
    family: &str,
    n: Option<usize>,
    minimum: usize,
) -> PyResult<usize> {
    n.filter(|&value| value >= minimum).ok_or_else(|| {
        PyValueError::new_err(format!("{what}: {family} needs an integer n >= {minimum}"))
    })
}

pub(crate) fn checked_exceptional_diagram(
    what: &str,
    family: PyDiagramFamily,
    n: Option<usize>,
) -> PyResult<DiagramName> {
    let diagram = match family {
        PyDiagramFamily::E6 => DiagramName::E6,
        PyDiagramFamily::E7 => DiagramName::E7,
        PyDiagramFamily::E8 => DiagramName::E8,
        _ => unreachable!("A and D parameters are checked separately"),
    };
    n.is_none()
        .then_some(diagram)
        .ok_or_else(|| PyValueError::new_err(format!("{what}: E6, E7 and E8 take n=None")))
}

/// A simply laced Dynkin diagram: A(n) for n >= 1, D(n) for n >= 4, E6, E7, E8.
///
/// The parameter constraints are enforced at construction, as is the invariant
/// that n is an integer for the A and D families and None for E6, E7 and E8, so
/// `num_vertices` and `indecomposable_count` are exact for every instance.
/// Instances are immutable and compare by family and parameter. str() gives the
/// usual name ("A_3", "D_4", "E_6").
#[pyclass(name = "DynkinType", module = "auslander", frozen, eq, hash)]
#[derive(PartialEq, Eq, Hash)]
pub(crate) struct PyDynkinType {
    pub(crate) inner: DynkinType,
}

#[pymethods]
impl PyDynkinType {
    /// DynkinType(family, n=None); raises ValueError unless A comes with an
    /// integer n >= 1, D with an integer n >= 4, and E6, E7, E8 with n=None.
    #[new]
    #[pyo3(signature = (family, n = None), text_signature = "(family, n=None)")]
    fn new(family: PyDiagramFamily, n: Option<usize>) -> PyResult<Self> {
        let inner = match checked_diagram("DynkinType", family, n)? {
            DiagramName::A(n) => DynkinType::A(n),
            DiagramName::D(n) => DynkinType::D(n),
            DiagramName::E6 => DynkinType::E6,
            DiagramName::E7 => DynkinType::E7,
            DiagramName::E8 => DynkinType::E8,
        };
        // The getters are total on constructed instances, so a parameter whose
        // vertex count or root count exceeds usize is rejected here rather than
        // panicking later.
        if inner.num_vertices().is_none() || inner.indecomposable_count().is_none() {
            return Err(PyOverflowError::new_err(
                "DynkinType: n is too large for its vertex count and root count to be represented",
            ));
        }
        Ok(PyDynkinType { inner })
    }

    /// DiagramFamily.A, D, E6, E7 or E8.
    #[getter]
    fn family(&self) -> PyDiagramFamily {
        match self.inner {
            DynkinType::A(_) => PyDiagramFamily::A,
            DynkinType::D(_) => PyDiagramFamily::D,
            DynkinType::E6 => PyDiagramFamily::E6,
            DynkinType::E7 => PyDiagramFamily::E7,
            DynkinType::E8 => PyDiagramFamily::E8,
        }
    }

    /// The parameter of the A and D families; None for E6, E7 and E8.
    #[getter]
    fn n(&self) -> Option<usize> {
        match self.inner {
            DynkinType::A(n) | DynkinType::D(n) => Some(n),
            DynkinType::E6 | DynkinType::E7 | DynkinType::E8 => None,
        }
    }

    /// The number of vertices of the diagram.
    #[getter]
    fn num_vertices(&self) -> usize {
        self.inner
            .num_vertices()
            .expect("a constructed DynkinType names a diagram")
    }

    /// The number of positive roots, equal by Gabriel's theorem to the number of
    /// isomorphism classes of indecomposable representations of any quiver with
    /// this underlying graph: n(n + 1)/2 for A_n, n(n - 1) for D_n, and 36, 63,
    /// 120 for E6, E7, E8.
    #[getter]
    fn indecomposable_count(&self) -> usize {
        self.inner
            .indecomposable_count()
            .expect("a constructed DynkinType names a diagram")
    }

    fn __str__(&self) -> String {
        self.inner.to_string()
    }

    fn __repr__(&self) -> String {
        match self.inner {
            DynkinType::A(n) => format!("DynkinType(DiagramFamily.A, n={n})"),
            DynkinType::D(n) => format!("DynkinType(DiagramFamily.D, n={n})"),
            DynkinType::E6 => "DynkinType(DiagramFamily.E6)".to_string(),
            DynkinType::E7 => "DynkinType(DiagramFamily.E7)".to_string(),
            DynkinType::E8 => "DynkinType(DiagramFamily.E8)".to_string(),
        }
    }
}

/// A simply laced Euclidean (affine) diagram: A(n) for n >= 1, D(n) for n >= 4,
/// E6, E7, E8.
///
/// The subscript is the rank of the finite diagram the affine one extends, so
/// the diagram itself has one vertex more. The parameter constraints are
/// enforced at construction, so `num_vertices` is exact for every instance.
/// Instances are immutable and compare by family and parameter. str() gives the
/// usual name ("affine A_1", "affine D_4").
#[pyclass(name = "EuclideanType", module = "auslander", frozen, eq, hash)]
#[derive(PartialEq, Eq, Hash)]
pub(crate) struct PyEuclideanType {
    pub(crate) inner: EuclideanType,
}

#[pymethods]
impl PyEuclideanType {
    /// EuclideanType(family, n=None); raises ValueError unless A comes with an
    /// integer n >= 1, D with an integer n >= 4, and E6, E7, E8 with n=None.
    #[new]
    #[pyo3(signature = (family, n = None), text_signature = "(family, n=None)")]
    fn new(family: PyDiagramFamily, n: Option<usize>) -> PyResult<Self> {
        let inner = match checked_diagram("EuclideanType", family, n)? {
            DiagramName::A(n) => EuclideanType::A(n),
            DiagramName::D(n) => EuclideanType::D(n),
            DiagramName::E6 => EuclideanType::E6,
            DiagramName::E7 => EuclideanType::E7,
            DiagramName::E8 => EuclideanType::E8,
        };
        // `num_vertices` is total on constructed instances, so a parameter whose
        // vertex count exceeds usize is rejected here rather than panicking
        // later.
        if inner.num_vertices().is_none() {
            return Err(PyOverflowError::new_err(
                "EuclideanType: n is too large for its vertex count to be represented",
            ));
        }
        Ok(PyEuclideanType { inner })
    }

    /// DiagramFamily.A, D, E6, E7 or E8.
    #[getter]
    fn family(&self) -> PyDiagramFamily {
        match self.inner {
            EuclideanType::A(_) => PyDiagramFamily::A,
            EuclideanType::D(_) => PyDiagramFamily::D,
            EuclideanType::E6 => PyDiagramFamily::E6,
            EuclideanType::E7 => PyDiagramFamily::E7,
            EuclideanType::E8 => PyDiagramFamily::E8,
        }
    }

    /// The parameter of the A and D families; None for E6, E7 and E8.
    #[getter]
    fn n(&self) -> Option<usize> {
        match self.inner {
            EuclideanType::A(n) | EuclideanType::D(n) => Some(n),
            EuclideanType::E6 | EuclideanType::E7 | EuclideanType::E8 => None,
        }
    }

    /// The number of vertices of the diagram, one more than the subscript for
    /// the A and D families.
    #[getter]
    fn num_vertices(&self) -> usize {
        self.inner
            .num_vertices()
            .expect("a constructed EuclideanType names a diagram")
    }

    fn __str__(&self) -> String {
        self.inner.to_string()
    }

    fn __repr__(&self) -> String {
        match self.inner {
            EuclideanType::A(n) => format!("EuclideanType(DiagramFamily.A, n={n})"),
            EuclideanType::D(n) => format!("EuclideanType(DiagramFamily.D, n={n})"),
            EuclideanType::E6 => "EuclideanType(DiagramFamily.E6)".to_string(),
            EuclideanType::E7 => "EuclideanType(DiagramFamily.E7)".to_string(),
            EuclideanType::E8 => "EuclideanType(DiagramFamily.E8)".to_string(),
        }
    }
}

/// The Ext space Ext^k_A(M, N) with the data behind its dimension kept: a
/// basis of classes, each with a representative cocycle P_k -> N.
///
/// Coordinates run over one fixed complement basis of the coboundaries inside
/// the cocycles, so classes of one space are compared and combined by their
/// coordinates alone. `dim` equals `M.ext_dim(N, k)`. Degree 0 is not special:
/// Ext^0(M, N) is Hom(M, N), and `identity_class()` of Ext^0(M, M) is the
/// Yoneda unit. Instances are immutable and come only from
/// `Module.ext_space`.
pub(crate) fn dynkin_error(e: dynkin::DynkinError) -> PyErr {
    let err = match e {
        dynkin::DynkinError::NonzeroIdeal { .. } => NonzeroIdealError::new_err(e.to_string()),
        dynkin::DynkinError::NotDynkin { .. } => NotDynkinError::new_err(e.to_string()),
    };
    attach(err, |value| match e {
        // The Groebner relation count; for monomial input these relations are
        // exactly the minimal forbidden words.
        dynkin::DynkinError::NonzeroIdeal { relations } => {
            value.setattr("forbidden_words", relations)
        }
        dynkin::DynkinError::NotDynkin { euclidean } => value.setattr(
            "euclidean",
            euclidean.map(|inner| PyEuclideanType { inner }),
        ),
    })
}

/// The Dynkin type of the quiver's underlying graph, or None when that graph is
/// no Dynkin diagram.
///
/// The None is a definite answer about the graph, not partiality: recognition is
/// an exact integer computation. The type depends only on the underlying graph,
/// never on the orientation and never on an ideal of relations, so this takes a
/// Quiver; pass `algebra.quiver` to classify an algebra.
#[pyfunction]
#[pyo3(text_signature = "(quiver)")]
pub(crate) fn dynkin_type(quiver: &PyQuiver) -> Option<PyDynkinType> {
    dynkin::dynkin_type(&quiver.inner).map(|inner| PyDynkinType { inner })
}

/// The Euclidean (affine) type of the quiver's underlying graph, or None when
/// that graph is no Euclidean diagram; the None is a definite answer about the
/// graph, as for `dynkin_type`.
#[pyfunction]
#[pyo3(text_signature = "(quiver)")]
pub(crate) fn euclidean_type(quiver: &PyQuiver) -> Option<PyEuclideanType> {
    dynkin::euclidean_type(&quiver.inner).map(|inner| PyEuclideanType { inner })
}

/// The generalized Cartan matrix of the quiver's underlying graph: 2 on the
/// diagonal and minus the number of edges joining i and j off it. None exactly
/// when the quiver has a loop, since a vertex carrying a loop contributes no row
/// with diagonal entry 2.
#[pyfunction]
#[pyo3(text_signature = "(quiver)")]
pub(crate) fn generalized_cartan_matrix(quiver: &PyQuiver) -> Option<Vec<Vec<i64>>> {
    dynkin::generalized_cartan_matrix(&quiver.inner)
}

/// The positive roots of the quiver's underlying graph, in the quiver's own
/// vertex indexing, ordered by height and then lexicographically; None when the
/// graph is no Dynkin diagram, where the list would be infinite or undefined.
#[pyfunction]
#[pyo3(text_signature = "(quiver)")]
pub(crate) fn positive_roots(quiver: &PyQuiver) -> Option<Vec<Vec<usize>>> {
    dynkin::positive_roots(&quiver.inner)
}

/// A quiver whose underlying graph is the named Dynkin diagram, oriented away
/// from the branch vertex. The abstract diagram is unbounded, but a Quiver
/// indexes its vertices by u32; raises ValueError when the diagram's vertex
/// count exceeds that limit.
#[pyfunction]
#[pyo3(text_signature = "(diagram)")]
pub(crate) fn dynkin_quiver(diagram: &PyDynkinType) -> PyResult<PyQuiver> {
    dynkin::dynkin_quiver(diagram.inner)
        .map(|inner| PyQuiver { inner })
        .ok_or_else(|| {
            PyValueError::new_err(
                "dynkin_quiver: the diagram's vertex count exceeds the u32 limit of Quiver",
            )
        })
}

/// A quiver whose underlying graph is the named Euclidean diagram. The cyclic
/// cases are oriented acyclically, so their path algebras are finite
/// dimensional. The abstract diagram is unbounded, but a Quiver indexes its
/// vertices by u32; raises ValueError when the diagram's vertex count exceeds
/// that limit.
#[pyfunction]
#[pyo3(text_signature = "(diagram)")]
pub(crate) fn euclidean_quiver(diagram: &PyEuclideanType) -> PyResult<PyQuiver> {
    dynkin::euclidean_quiver(diagram.inner)
        .map(|inner| PyQuiver { inner })
        .ok_or_else(|| {
            PyValueError::new_err(
                "euclidean_quiver: the diagram's vertex count exceeds the u32 limit of Quiver",
            )
        })
}

/// Every indecomposable right module of a hereditary path algebra kQ with Q of
/// Dynkin type, one per positive root of the underlying graph (Gabriel), as
/// (Module, Certificate) pairs ordered as `positive_roots` orders the roots.
///
/// Each module is built from a simple one by a chain of Bernstein-Gelfand-
/// Ponomarev reflection functors, so nothing is enumerated over the field and
/// the count is the number of positive roots for every prime. Every certificate
/// has kind "indecomposable": it comes from the exact decomposition machinery
/// and independently confirms what the construction proves. Raises
/// NonzeroIdealError, carrying `forbidden_words`, when the algebra is a proper
/// quotient of kQ, and NotDynkinError, carrying `euclidean`, when the underlying
/// graph is no Dynkin diagram.
#[pyfunction]
#[pyo3(text_signature = "(algebra, field)")]
pub(crate) fn dynkin_indecomposables(
    py: Python<'_>,
    algebra: &PyAlgebra,
    field: &PyPrimeField,
) -> PyResult<Vec<(PyRightModule, PyCertificate)>> {
    let algebra = algebra.over(py, field.inner)?;
    Ok(py
        .allow_threads(|| dynkin::dynkin_indecomposables(&algebra))
        .map_err(dynkin_error)?
        .into_iter()
        .map(|(m, c)| (m.into(), PyCertificate { inner: c }))
        .collect())
}

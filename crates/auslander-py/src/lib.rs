//! Python façade for the `auslander` crate: prime fields, quivers, bound
//! quiver algebras with monomial or general admissible relations, and their
//! right modules.
//!
//! The surface is small and algebra-owned: modules are created only through
//! `Algebra` methods, so every Python-visible `Module` is a validated
//! `kQ/I`-module. Library errors cross the boundary as `ValueError` carrying the
//! Rust `Display` message. A rejection with variants gets one `ValueError`
//! subclass per variant, with its payload attached as attributes, so the failed
//! precondition is never reduced to a message string. Engine limits and defects
//! are `RuntimeError`, never `ValueError`.

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use pyo3::create_exception;
use pyo3::exceptions::{PyOverflowError, PyRuntimeError, PyValueError};
use pyo3::prelude::*;
use pyo3::sync::GILOnceCell;

use auslander::algebra::{self, Algebra, AlgebraBuildError, MonomialPresentation};
use auslander::almost_split::{self, AlmostSplitError, AlmostSplitOutcome, AlmostSplitWitness};
use auslander::ar::{self, Tau};
use auslander::arquiver::{self, ArQuiver, ArQuiverError, ArrowValuation};
use auslander::completion::{CompletionLimits, TruncationDiagnostics, TruncationReason};
use auslander::decompose::{self, Certificate, KrullSchmidtOutcome};
use auslander::dynkin::{self, DynkinType, EuclideanType};
use auslander::enumerate;
use auslander::ext::{self, ExtClassError};
use auslander::field::{Fp, PrimeField};
use auslander::hom;
use auslander::homspace::HomSubspace;
use auslander::indec::{IndecError, IndecomposableModule};
use auslander::injective::{self, InjectiveCoresolution};
use auslander::iso::{self, IsoOutcome, Obstruction};
use auslander::linalg::DenseMat;
use auslander::module::Module;
use auslander::quiver::{ArrowId, Quiver};
use auslander::radical;
use auslander::relation::{Presentation, Relation};
use auslander::resolution::{
    Bounded, ProjectiveResolution, ResolutionEnd, projective_cover, projective_dimension, resolve,
};
use auslander::sequence::{self, SequenceError, SplitStatus};
use auslander::verify;

fn value_error(e: impl std::fmt::Display) -> PyErr {
    PyValueError::new_err(e.to_string())
}

/// An engine limit or defect (a failed pipeline run inside the library), not
/// bad input. It becomes a RuntimeError, like the tau cross-check failures.
fn engine_error(e: impl std::fmt::Display) -> PyErr {
    PyRuntimeError::new_err(e.to_string())
}

/// An exhausted completion budget as a TruncationError with the diagnostics
/// counts attached as attributes, so the consumed budget survives the boundary.
fn truncation_error(d: &TruncationDiagnostics) -> PyErr {
    let reason = match d.reason {
        TruncationReason::BasisBudget => "basis_budget",
        TruncationReason::WordLenBudget => "word_len_budget",
        TruncationReason::StepBudget => "step_budget",
    };
    let err = TruncationError::new_err(format!(
        "completion ran out of budget ({reason}): basis {}, pending ambiguities {}, steps {}",
        d.basis_len, d.pending_ambiguities, d.steps_used
    ));
    Python::with_gil(|py| {
        let value = err.value(py);
        let attached = value
            .setattr("basis_len", d.basis_len)
            .and_then(|()| value.setattr("pending_ambiguities", d.pending_ambiguities))
            .and_then(|()| value.setattr("steps_used", d.steps_used))
            .and_then(|()| value.setattr("reason", reason));
        match attached {
            Ok(()) => err,
            Err(failure) => failure,
        }
    })
}

/// A build failure of an initial construction, where the presentation is
/// user input. Rejected input is ValueError with the Rust message; an
/// infinite-dimensional quotient is rejected input too, and its message
/// carries the witness words. An exhausted budget is TruncationError (a
/// RuntimeError). A certificate the verifier rejected for any other reason
/// is an engine defect: plain RuntimeError.
fn build_error(e: AlgebraBuildError) -> PyErr {
    match e {
        AlgebraBuildError::Monomial(_)
        | AlgebraBuildError::Relation(_)
        | AlgebraBuildError::InfiniteDimensional { .. } => value_error(e),
        AlgebraBuildError::Truncated(d) => truncation_error(&d),
        AlgebraBuildError::Verification(_) => engine_error(e),
    }
}

/// A build failure of a derived completion (the opposite algebra under
/// tau, injective envelopes, coresolutions, and injective dimensions).
/// An exhausted budget is TruncationError with the diagnostics attached.
/// Everything else is RuntimeError: the reversed relations come from a
/// verified algebra, so an infinite opposite or a rejected reversed
/// relation is a library defect, not user input.
fn downstream_build_error(e: AlgebraBuildError) -> PyErr {
    match e {
        AlgebraBuildError::Truncated(d) => truncation_error(&d),
        other => engine_error(other),
    }
}

/// A failed AR translate, mapped as `Module.tau` documents: an exhausted
/// budget is TruncationError, a certified disagreement is RuntimeError, and an
/// undecided cross-check is TauAgreementUnknown.
fn tau_error(e: ar::TauError) -> PyErr {
    match e {
        ar::TauError::Opposite(build) => downstream_build_error(build),
        e @ ar::TauError::RoutesDisagree { .. } => PyRuntimeError::new_err(e.to_string()),
        e @ ar::TauError::AgreementUnknown { .. } => TauAgreementUnknown::new_err(e.to_string()),
    }
}

/// A module the indecomposability gate refused, as NotIndecomposableError with
/// the gate's report attached: `kind` is "zero", "decomposable" or
/// "undetermined", `summands` counts the certified summands of a decomposable
/// module, and `attempts` counts the exhausted split attempts of an
/// undetermined one. `what` names the rejected endpoint.
fn indec_error(what: &str, e: IndecError) -> PyErr {
    let kind = match e {
        IndecError::Zero => "zero",
        IndecError::Decomposable { .. } => "decomposable",
        IndecError::Undetermined { .. } => "undetermined",
    };
    let summands = match e {
        IndecError::Decomposable { summands } => Some(summands),
        _ => None,
    };
    let attempts = match e {
        IndecError::Undetermined { attempts } => Some(attempts),
        _ => None,
    };
    let err =
        NotIndecomposableError::new_err(format!("{what} is not certified indecomposable: {e}"));
    Python::with_gil(|py| {
        let value = err.value(py);
        let attached = value
            .setattr("kind", kind)
            .and_then(|()| value.setattr("summands", summands))
            .and_then(|()| value.setattr("attempts", attempts));
        match attached {
            Ok(()) => err,
            Err(failure) => failure,
        }
    })
}

/// A rejected Ext class operation. Operands that do not share one space are
/// IncompatibleSpacesError, so a comparison never quietly answers False;
/// everything else is rejected input, so ValueError.
fn ext_class_error(e: ExtClassError) -> PyErr {
    match e {
        ExtClassError::IncompatibleSpaces | ExtClassError::MiddleMismatch => {
            IncompatibleSpacesError::new_err(e.to_string())
        }
        other => value_error(other),
    }
}

/// A rejected short exact sequence operation. A wrong degree is caller input,
/// so ValueError; every other variant reports a structural check on a sequence
/// this package built itself, so RuntimeError.
fn sequence_error(e: SequenceError) -> PyErr {
    match e {
        SequenceError::WrongDegree { .. } => value_error(e),
        other => engine_error(other),
    }
}

/// A failed AR-quiver or category-radical call. An algebra outside the two
/// catalog domains is UnsupportedDomainError naming both failed routes,
/// mismatched endpoints are ValueError, and a failed internal division or
/// containment is DefectError.
fn ar_quiver_error(e: ArQuiverError) -> PyErr {
    match e {
        ArQuiverError::UnsupportedDomain { .. } => UnsupportedDomainError::new_err(e.to_string()),
        ArQuiverError::Hom(_) | ArQuiverError::Space(_) => value_error(e),
        ArQuiverError::Injective(build) => downstream_build_error(build),
        e @ (ArQuiverError::RadicalSquareNotContained { .. }
        | ArQuiverError::ResidueDegreeDoesNotDivide { .. }) => DefectError::new_err(e.to_string()),
    }
}

/// A failed almost-split construction. A translate that fails the
/// indecomposability gate and a failed internal cross-check are both crate
/// defects, so DefectError; the remaining variants keep the mapping of the
/// layer they come from.
fn almost_split_error(e: AlmostSplitError) -> PyErr {
    match e {
        AlmostSplitError::Tau(inner) => tau_error(inner),
        AlmostSplitError::Ext(inner) => ext_class_error(inner),
        AlmostSplitError::Sequence(inner) => sequence_error(inner),
        AlmostSplitError::Radical(inner) => ar_quiver_error(inner),
        e @ (AlmostSplitError::TauIndecomposability(_) | AlmostSplitError::Defect(_)) => {
            DefectError::new_err(e.to_string())
        }
        e @ (AlmostSplitError::Hom(_) | AlmostSplitError::Space(_)) => engine_error(e),
    }
}

/// The canonical representatives in `0..p` of a row of field elements. An `Fp`
/// keeps its representative to itself outside the library, so the row travels
/// through a one-row matrix.
fn row_u64(row: &[Fp]) -> Vec<u64> {
    DenseMat::from_rows(&[row.to_vec()])
        .entries_u64()
        .pop()
        .expect("one row in, one row out")
}

/// One matrix from a list of integer rows, entries reduced mod p. A matrix given
/// as zero rows carries no column count of its own, so `cols_when_empty` supplies
/// the expected one; raises ValueError on rows of differing lengths.
fn dense_from_rows(
    field: PrimeField,
    rows: &[Vec<i64>],
    cols_when_empty: usize,
    what: &str,
) -> PyResult<DenseMat> {
    let cols = rows.first().map_or(cols_when_empty, Vec::len);
    let mut mat = DenseMat::zero(rows.len(), cols);
    for (r, row) in rows.iter().enumerate() {
        if row.len() != cols {
            return Err(PyValueError::new_err(format!(
                "{what} has rows of differing lengths ({} vs {cols})",
                row.len()
            )));
        }
        for (c, &v) in row.iter().enumerate() {
            mat.set(r, c, field.elem(v));
        }
    }
    Ok(mat)
}

/// The prime field F_p = Z/pZ.
///
/// Primality is checked at construction; p must be a prime below 2^31.
#[pyclass(name = "PrimeField", module = "auslander")]
struct PyPrimeField {
    inner: PrimeField,
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
struct PyQuiver {
    inner: Quiver,
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

/// How a Python Algebra holds its verified runtime algebras.
enum AlgebraKind {
    /// Field-free monomial combinatorics. Each field gets one verified
    /// runtime algebra, built on first use and cached.
    Monomial {
        presentation: Box<MonomialPresentation>,
        per_field: Mutex<BTreeMap<u64, Arc<Algebra>>>,
    },
    /// A general-relation algebra, bound to the one field it was verified
    /// over.
    General(Arc<Algebra>),
}

/// The bound quiver algebra kQ/I over a checked prime field.
///
/// Two kinds share this class. `Algebra(quiver, forbidden)` and the named
/// constructors build a monomial algebra: forbidden words are lists of arrow
/// ids, each of length >= 2 (admissibility) and composable left to right. A
/// monomial presentation is field-free; a field enters only when building
/// modules, and each field gets one verified runtime algebra, built on first
/// use and cached. `Algebra.from_relations` and `Algebra.from_certificate`
/// build a general-relation algebra. Its dimension and structure constants
/// depend on the field, so it is bound to the one field it was verified over
/// and raises ValueError for any other; `field` names that field (None for a
/// monomial algebra). Every runtime algebra passes completion and independent
/// certificate verification before use, so `dim` and the Cartan matrix are
/// exact. Modules interact (hom, ext) only when built from the same Algebra
/// object over equal fields. `MonomialAlgebra` is an alias of this class.
#[pyclass(name = "Algebra", module = "auslander")]
struct PyAlgebra {
    kind: AlgebraKind,
}

impl PyAlgebra {
    fn wrap(presentation: MonomialPresentation) -> PyAlgebra {
        PyAlgebra {
            kind: AlgebraKind::Monomial {
                presentation: Box::new(presentation),
                per_field: Mutex::new(BTreeMap::new()),
            },
        }
    }

    fn pinned(algebra: Arc<Algebra>) -> PyAlgebra {
        PyAlgebra {
            kind: AlgebraKind::General(algebra),
        }
    }

    /// The verified runtime algebra over `field`. A monomial algebra builds
    /// one per field on first use and caches it; a general-relation algebra
    /// returns its own and raises ValueError for any other field.
    fn over(&self, field: PrimeField) -> PyResult<Arc<Algebra>> {
        match &self.kind {
            AlgebraKind::Monomial {
                presentation,
                per_field,
            } => {
                let mut cache = per_field.lock().expect("no panics while holding the lock");
                if let Some(found) = cache.get(&field.modulus()) {
                    return Ok(found.clone());
                }
                let built = Algebra::from_monomial(
                    field,
                    presentation,
                    &algebra::monomial_completion_limits(presentation),
                )
                .map_err(build_error)?;
                cache.insert(field.modulus(), built.clone());
                Ok(built)
            }
            AlgebraKind::General(algebra) => {
                if algebra.field().modulus() == field.modulus() {
                    return Ok(algebra.clone());
                }
                Err(PyValueError::new_err(format!(
                    "this algebra was built over F_{}; a general-relation algebra is \
                     field-dependent, so it cannot be used over F_{}",
                    algebra.field().modulus(),
                    field.modulus()
                )))
            }
        }
    }

    fn quiver_ref(&self) -> &Quiver {
        match &self.kind {
            AlgebraKind::Monomial { presentation, .. } => presentation.quiver(),
            AlgebraKind::General(algebra) => algebra.quiver(),
        }
    }

    fn check_vertex(&self, v: u32) -> PyResult<()> {
        let n = self.quiver_ref().num_vertices();
        if v >= n {
            return Err(PyValueError::new_err(format!(
                "vertex {v} out of range: the quiver has vertices 0..{n}"
            )));
        }
        Ok(())
    }
}

#[pymethods]
impl PyAlgebra {
    /// kQ/(forbidden) with a certified finite standard-path basis; raises ValueError
    /// when a forbidden word is too short or not a path, or when the algebra would
    /// be infinite-dimensional.
    #[new]
    #[pyo3(text_signature = "(quiver, forbidden)")]
    fn new(quiver: &PyQuiver, forbidden: Vec<Vec<u32>>) -> PyResult<Self> {
        let forbidden: Vec<Vec<ArrowId>> = forbidden
            .into_iter()
            .map(|word| word.into_iter().map(ArrowId).collect())
            .collect();
        Ok(PyAlgebra::wrap(
            MonomialPresentation::new(quiver.inner.clone(), forbidden).map_err(value_error)?,
        ))
    }

    /// kQ/I for a general admissible ideal over one prime field. Each relation
    /// is a list of (coefficient, path) terms; a path is a list of arrow ids
    /// composed left to right, and coefficients are integers reduced mod p.
    /// The terms of one relation must share one source and one target, every
    /// path needs length >= 2, and a coefficient that reduces to zero is
    /// rejected. Construction runs completion and verifies the emitted
    /// certificate; the result is bound to `field` and refuses any other.
    /// The optional keywords cap the completion budgets; an exhausted budget
    /// raises TruncationError. Raises ValueError on a rejected relation and on
    /// an infinite-dimensional quotient (the message carries a cyclic word
    /// witness).
    #[staticmethod]
    #[pyo3(signature = (quiver, relations, field, *, max_basis = None, max_word_len = None, max_steps = None))]
    fn from_relations(
        quiver: &PyQuiver,
        relations: Vec<Vec<(i64, Vec<u32>)>>,
        field: &PyPrimeField,
        max_basis: Option<usize>,
        max_word_len: Option<usize>,
        max_steps: Option<usize>,
    ) -> PyResult<PyAlgebra> {
        let f = field.inner;
        let mut checked = Vec::with_capacity(relations.len());
        for (i, terms) in relations.into_iter().enumerate() {
            let terms = terms
                .into_iter()
                .map(|(coeff, word)| (f.elem(coeff), word.into_iter().map(ArrowId).collect()))
                .collect();
            checked.push(
                Relation::new(&quiver.inner, f, terms)
                    .map_err(|e| PyValueError::new_err(format!("relation {i} rejected: {e}")))?,
            );
        }
        let presentation = Presentation::new(quiver.inner.clone(), f, checked)
            .map_err(|e| PyValueError::new_err(format!("relation rejected: {e}")))?;
        let mut limits = CompletionLimits::default();
        if let Some(n) = max_basis {
            limits.max_basis = n;
        }
        if let Some(n) = max_word_len {
            limits.max_word_len = n;
        }
        if let Some(n) = max_steps {
            limits.max_steps = n;
        }
        Ok(PyAlgebra::pinned(
            Algebra::new(presentation, &limits).map_err(build_error)?,
        ))
    }

    /// The algebra rebuilt from certificate bytes: the bytes are verified from
    /// scratch, then the algebra is built from the verified data alone. The
    /// result is bound to the certificate's field, exactly like a
    /// `from_relations` algebra, whatever kind of algebra dumped the bytes.
    /// The optional keywords set the rebuilt algebra's completion limits,
    /// used only by later derived completions such as tau and the injective
    /// constructions; omitted keywords keep the defaults. Certificate bytes
    /// never carry budgets: untrusted input must not choose resource
    /// envelopes, so preserving raised budgets across a reload takes these
    /// explicit keywords. Raises ValueError with the verifier's message when
    /// the bytes fail any check, an infinite-dimensional quotient included.
    #[staticmethod]
    #[pyo3(signature = (json, *, max_basis = None, max_word_len = None, max_steps = None))]
    fn from_certificate(
        json: &str,
        max_basis: Option<usize>,
        max_word_len: Option<usize>,
        max_steps: Option<usize>,
    ) -> PyResult<PyAlgebra> {
        let verified = verify::verify(json).map_err(value_error)?;
        let mut limits = CompletionLimits::default();
        if let Some(n) = max_basis {
            limits.max_basis = n;
        }
        if let Some(n) = max_word_len {
            limits.max_word_len = n;
        }
        if let Some(n) = max_steps {
            limits.max_steps = n;
        }
        Ok(PyAlgebra::pinned(Algebra::from_verified_with_limits(
            verified, &limits,
        )))
    }

    /// Path algebra of linearly oriented A_n: vertices 0..n, arrows i -> i+1.
    #[staticmethod]
    #[pyo3(text_signature = "(n)")]
    fn linear_an(n: usize) -> PyAlgebra {
        PyAlgebra::wrap(algebra::linear_an_presentation(n))
    }

    /// Kronecker-type algebra: vertices 0, 1 and m parallel arrows 0 -> 1;
    /// hereditary, dim = m + 2.
    #[staticmethod]
    #[pyo3(text_signature = "(m)")]
    fn kronecker(m: usize) -> PyAlgebra {
        PyAlgebra::wrap(algebra::kronecker_presentation(m))
    }

    /// k[x]/(x^2): one vertex, one loop x, forbidden word xx.
    #[staticmethod]
    #[pyo3(text_signature = "()")]
    fn dual_numbers() -> PyAlgebra {
        PyAlgebra::wrap(
            algebra::truncated_poly_presentation(2).expect("x^2 is an admissible relation"),
        )
    }

    /// k[x]/(x^n): one vertex, one loop x, forbidden word x^n; raises ValueError
    /// for n < 2 (the ideal would not be admissible).
    #[staticmethod]
    #[pyo3(text_signature = "(n)")]
    fn truncated_poly(n: usize) -> PyResult<PyAlgebra> {
        Ok(PyAlgebra::wrap(
            algebra::truncated_poly_presentation(n).map_err(value_error)?,
        ))
    }

    /// Linear Nakayama algebra over linearly oriented A_n with dim P_i = kupisch[i];
    /// raises ValueError on an invalid Kupisch series (needs kupisch[n-1] == 1,
    /// interior entries >= 2, and kupisch[i+1] >= kupisch[i] - 1).
    #[staticmethod]
    #[pyo3(text_signature = "(kupisch)")]
    fn linear_nakayama(kupisch: Vec<usize>) -> PyResult<PyAlgebra> {
        Ok(PyAlgebra::wrap(
            algebra::linear_nakayama_presentation(&kupisch).map_err(value_error)?,
        ))
    }

    /// Cyclic Nakayama algebra over the cycle 0 -> 1 -> ... -> n-1 -> 0 with
    /// dim P_i = kupisch[i]; raises ValueError on an invalid series (all entries
    /// >= 2 and cyclically kupisch[i+1] >= kupisch[i] - 1).
    #[staticmethod]
    #[pyo3(text_signature = "(kupisch)")]
    fn cyclic_nakayama(kupisch: Vec<usize>) -> PyResult<PyAlgebra> {
        Ok(PyAlgebra::wrap(
            algebra::cyclic_nakayama_presentation(&kupisch).map_err(value_error)?,
        ))
    }

    /// Cyclic quiver on n vertices with rad^2 = 0: every length-2 path forbidden;
    /// dim = 2n.
    #[staticmethod]
    #[pyo3(text_signature = "(n)")]
    fn radical_square_zero_cycle(n: usize) -> PyAlgebra {
        PyAlgebra::wrap(algebra::radical_square_zero_cycle_presentation(n))
    }

    /// Linearly oriented A_n with zero relations: each (start, length) pair kills
    /// the unique path of that length from vertex start. kA_3/(ab) is
    /// an_with_relations(3, [(0, 2)]). Raises ValueError when a zero path runs past
    /// the last vertex or has length < 2.
    #[staticmethod]
    #[pyo3(text_signature = "(n, zero_paths)")]
    fn an_with_relations(n: usize, zero_paths: Vec<(usize, usize)>) -> PyResult<PyAlgebra> {
        Ok(PyAlgebra::wrap(
            algebra::an_with_relations_presentation(n, &zero_paths).map_err(value_error)?,
        ))
    }

    /// dim_k of the algebra: the number of basis paths, trivial paths included.
    /// A monomial algebra reports its field-independent standard-path count; a
    /// general-relation algebra reports the normal-word count over its bound
    /// field.
    #[getter]
    fn dim(&self) -> usize {
        match &self.kind {
            AlgebraKind::Monomial { presentation, .. } => presentation.dim(),
            AlgebraKind::General(algebra) => algebra.dim(),
        }
    }

    /// The bound prime field of a general-relation algebra; None for a
    /// monomial algebra, which pairs with any field.
    #[getter]
    fn field(&self) -> Option<PyPrimeField> {
        match &self.kind {
            AlgebraKind::Monomial { .. } => None,
            AlgebraKind::General(algebra) => Some(PyPrimeField {
                inner: algebra.field(),
            }),
        }
    }

    /// The effective completion limits as a dict with keys "max_basis",
    /// "max_word_len", and "max_steps". Derived completions (tau, injective
    /// envelopes, coresolutions, injective dimensions) run with them. A
    /// general-relation algebra reports its stored limits; a field-free
    /// monomial algebra reports the limits derived from its presentation.
    #[getter]
    fn completion_limits(&self) -> BTreeMap<&'static str, usize> {
        let limits = match &self.kind {
            AlgebraKind::Monomial { presentation, .. } => {
                algebra::monomial_completion_limits(presentation)
            }
            AlgebraKind::General(algebra) => algebra.completion_limits().clone(),
        };
        BTreeMap::from([
            ("max_basis", limits.max_basis),
            ("max_word_len", limits.max_word_len),
            ("max_steps", limits.max_steps),
        ])
    }

    /// Number of vertices of the underlying quiver.
    #[getter]
    fn num_vertices(&self) -> u32 {
        self.quiver_ref().num_vertices()
    }

    /// Number of arrows of the underlying quiver (the length `module` expects of
    /// its maps argument).
    #[getter]
    fn num_arrows(&self) -> usize {
        self.quiver_ref().num_arrows()
    }

    /// The underlying quiver, as a fresh Quiver object; the argument the
    /// diagram-recognition functions take.
    #[getter]
    fn quiver(&self) -> PyQuiver {
        PyQuiver {
            inner: self.quiver_ref().clone(),
        }
    }

    /// The Cartan matrix C with C[i][j] = dim e_i A e_j, the number of basis
    /// paths i -> j; row i is the dimension vector of the projective P_i.
    #[pyo3(text_signature = "($self)")]
    fn cartan_matrix(&self) -> Vec<Vec<usize>> {
        match &self.kind {
            AlgebraKind::Monomial { presentation, .. } => presentation.cartan_matrix(),
            AlgebraKind::General(algebra) => algebra.cartan_matrix(),
        }
    }

    /// The canonical JSON bytes of the verified completion certificate; feed
    /// them to Algebra.from_certificate to rebuild the algebra. A
    /// general-relation algebra serializes its own certificate, and `field`
    /// must be omitted or equal to the bound field. A monomial presentation is
    /// field-free and a certificate is not, so a monomial algebra requires
    /// `field` and serializes the certificate of its algebra over that field.
    #[pyo3(signature = (field = None))]
    fn certificate_json(&self, field: Option<&PyPrimeField>) -> PyResult<String> {
        let algebra = match (&self.kind, field) {
            (AlgebraKind::General(algebra), None) => algebra.clone(),
            (_, Some(field)) => self.over(field.inner)?,
            (AlgebraKind::Monomial { .. }, None) => {
                return Err(PyValueError::new_err(
                    "a monomial presentation is field-free and a certificate is not; \
                     pass a field to serialize the certificate of the algebra over it",
                ));
            }
        };
        Ok(algebra.certificate().to_canonical_json())
    }

    /// A right module from raw data: dims[v] is the dimension at vertex v, and
    /// maps[a] is a dims[source(a)] x dims[target(a)] integer matrix (list of rows)
    /// for arrow a, acting on row vectors; entries are reduced mod p. A path acts
    /// by the product of its arrow matrices in left-to-right word order. Raises
    /// ValueError when shapes disagree with the quiver or a relation acts as a
    /// nonzero matrix.
    #[pyo3(text_signature = "($self, field, dims, maps)")]
    fn module(
        &self,
        field: &PyPrimeField,
        dims: Vec<usize>,
        maps: Vec<Vec<Vec<i64>>>,
    ) -> PyResult<PyRightModule> {
        let f = field.inner;
        let algebra = self.over(f)?;
        let quiver = algebra.quiver();
        let mut mats = Vec::with_capacity(maps.len());
        for (i, rows) in maps.iter().enumerate() {
            // The expected column count, so that e.g. dims [0, 1] accepts maps [[]].
            let cols = quiver
                .arrows()
                .get(i)
                .and_then(|&(_, t)| dims.get(t as usize).copied())
                .unwrap_or(0);
            mats.push(dense_from_rows(
                f,
                rows,
                cols,
                &format!("map for arrow {i}"),
            )?);
        }
        Ok(PyRightModule {
            inner: Module::new(algebra, dims, mats).map_err(value_error)?,
        })
    }

    /// The simple module S_v: one-dimensional at v, zero elsewhere, all arrows
    /// acting as zero. Raises ValueError when v is not a vertex.
    #[pyo3(text_signature = "($self, field, v)")]
    fn simple(&self, field: &PyPrimeField, v: u32) -> PyResult<PyRightModule> {
        self.check_vertex(v)?;
        Ok(PyRightModule {
            inner: Module::simple(&self.over(field.inner)?, v),
        })
    }

    /// The indecomposable projective P_v = e_v A: its basis at vertex w is the set
    /// of standard paths v -> w. Raises ValueError when v is not a vertex.
    #[pyo3(text_signature = "($self, field, v)")]
    fn projective(&self, field: &PyPrimeField, v: u32) -> PyResult<PyRightModule> {
        self.check_vertex(v)?;
        Ok(PyRightModule {
            inner: Module::projective(&self.over(field.inner)?, v),
        })
    }

    /// The valued Auslander-Reiten quiver of the algebra: one vertex per
    /// indecomposable of a complete enumeration, one arrow per nonzero space
    /// of irreducible maps. The enumeration route is fixed: a zero ideal over
    /// a quiver of Dynkin shape takes the Gabriel enumeration, any other
    /// Nakayama algebra takes the Nakayama enumeration, and any other algebra
    /// raises UnsupportedDomainError naming both failed routes. The quiver is
    /// complete for its domain; no budget cuts it short. A general-relation
    /// algebra carries its field, so `field` may be omitted; a monomial
    /// presentation is field-free and needs it.
    #[pyo3(signature = (field = None))]
    fn ar_quiver(&self, field: Option<&PyPrimeField>) -> PyResult<PyArQuiver> {
        let algebra = match (&self.kind, field) {
            (AlgebraKind::General(algebra), None) => algebra.clone(),
            (_, Some(field)) => self.over(field.inner)?,
            (AlgebraKind::Monomial { .. }, None) => {
                return Err(PyValueError::new_err(
                    "a monomial presentation is field-free and an AR quiver is not; \
                     pass a field to build the AR quiver over it",
                ));
            }
        };
        Ok(PyArQuiver {
            inner: Arc::new(arquiver::ar_quiver(&algebra).map_err(ar_quiver_error)?),
        })
    }

    /// The indecomposable injective I_v = D(A e_v): its basis at vertex w is dual
    /// to the standard paths w -> v. Raises ValueError when v is not a vertex.
    #[pyo3(text_signature = "($self, field, v)")]
    fn injective(&self, field: &PyPrimeField, v: u32) -> PyResult<PyRightModule> {
        self.check_vertex(v)?;
        Ok(PyRightModule {
            inner: Module::injective(&self.over(field.inner)?, v),
        })
    }

    fn __repr__(&self) -> String {
        match &self.kind {
            AlgebraKind::Monomial { presentation, .. } => format!(
                "Algebra(dim={}, vertices={})",
                presentation.dim(),
                presentation.quiver().num_vertices()
            ),
            AlgebraKind::General(algebra) => format!(
                "Algebra(dim={}, vertices={}, field=F_{})",
                algebra.dim(),
                algebra.quiver().num_vertices(),
                algebra.field().modulus()
            ),
        }
    }
}

/// A finite-dimensional right kQ/I-module, validated at construction.
///
/// The module assigns to each vertex v the row-vector space k^dims[v] and to each
/// arrow a matrix acting on row vectors; paths act by matrix products in
/// left-to-right word order. Instances come only from Algebra methods
/// (`module`, `simple`, `projective`, `injective`), and two modules can be compared
/// homologically only when they were built from the same Algebra object
/// over equal fields.
#[pyclass(name = "Module", module = "auslander")]
struct PyRightModule {
    inner: Module,
}

fn check_same_context(m: &Module, n: &Module) -> PyResult<()> {
    if Arc::ptr_eq(m.algebra(), n.algebra()) {
        return Ok(());
    }
    // The runtime algebra is cached per field, so two modules from one
    // Algebra object share their Arc exactly when their fields agree.
    if m.field() != n.field() {
        return Err(PyValueError::new_err(format!(
            "modules are over different fields F_{} and F_{}",
            m.field().modulus(),
            n.field().modulus()
        )));
    }
    Err(PyValueError::new_err(
        "modules were built from different Algebra objects; \
         hom and ext need both sides over the same algebra object",
    ))
}

#[pymethods]
impl PyRightModule {
    /// The dimension vector: dims[v] = dim_k M_v.
    #[getter]
    fn dims(&self) -> Vec<usize> {
        self.inner.dim_vector().to_vec()
    }

    /// The dimension vector; alias of `dims`.
    #[getter]
    fn dim_vector(&self) -> Vec<usize> {
        self.inner.dim_vector().to_vec()
    }

    /// dim_k M, the sum of the dimension vector.
    #[getter]
    fn total_dim(&self) -> usize {
        self.inner.total_dim()
    }

    /// A basis of Hom_A(self, other) as a list of Morphism objects, not every
    /// morphism: the hom space is a k-vector space and arbitrary morphisms are
    /// its linear combinations. Raises ValueError when the modules do not share
    /// one algebra object and field.
    #[pyo3(text_signature = "($self, other)")]
    fn hom(&self, other: &PyRightModule) -> PyResult<Vec<PyMorphism>> {
        check_same_context(&self.inner, &other.inner)?;
        let basis = hom::hom(&self.inner, &other.inner).map_err(value_error)?;
        Ok(basis
            .into_iter()
            .map(|inner| PyMorphism { inner })
            .collect())
    }

    /// A morphism self -> target from one dims_self[v] x dims_target[v] integer
    /// matrix (list of rows) per vertex, acting on row vectors; entries are
    /// reduced mod p. A-linearity (every commuting square) is checked; raises
    /// ValueError when shapes disagree, a square fails, or the modules do not
    /// share one algebra object and field.
    #[pyo3(text_signature = "($self, target, maps)")]
    fn morphism(&self, target: &PyRightModule, maps: Vec<Vec<Vec<i64>>>) -> PyResult<PyMorphism> {
        check_same_context(&self.inner, &target.inner)?;
        let field = self.inner.field();
        let mut mats = Vec::with_capacity(maps.len());
        for (v, rows) in maps.iter().enumerate() {
            let cols = target.inner.dim_vector().get(v).copied().unwrap_or(0);
            mats.push(dense_from_rows(
                field,
                rows,
                cols,
                &format!("map at vertex {v}"),
            )?);
        }
        Ok(PyMorphism {
            inner: hom::Morphism::new(&self.inner, &target.inner, mats).map_err(value_error)?,
        })
    }

    /// dim_k Hom_A(self, other). Raises ValueError when the modules do not share
    /// one algebra object and field.
    #[pyo3(text_signature = "($self, other)")]
    fn hom_dim(&self, other: &PyRightModule) -> PyResult<usize> {
        check_same_context(&self.inner, &other.inner)?;
        hom::hom_dim(&self.inner, &other.inner).map_err(value_error)
    }

    /// dim_k Ext^k_A(self, other), exact for every k; Ext^0 is Hom. Raises
    /// ValueError when the modules do not share one algebra object and field.
    #[pyo3(text_signature = "($self, other, k)")]
    fn ext_dim(&self, other: &PyRightModule, k: usize) -> PyResult<usize> {
        check_same_context(&self.inner, &other.inner)?;
        ext::ext_dim(&self.inner, &other.inner, k).map_err(value_error)
    }

    /// [dim Ext^0(self, other), ..., dim Ext^max_k(self, other)], each entry exact.
    /// Raises ValueError when the modules do not share one algebra object and field.
    #[pyo3(text_signature = "($self, other, max_k)")]
    fn ext_table(&self, other: &PyRightModule, max_k: usize) -> PyResult<Vec<usize>> {
        check_same_context(&self.inner, &other.inner)?;
        ext::ext_table(&self.inner, &other.inner, max_k).map_err(value_error)
    }

    /// Dimension vectors along the radical series M ⊇ rad M ⊇ rad^2 M ⊇ ...,
    /// ending with the zero module.
    #[pyo3(text_signature = "($self)")]
    fn radical_series_dims(&self) -> Vec<Vec<usize>> {
        radical::radical_series(&self.inner)
            .iter()
            .map(|m| m.dim_vector().to_vec())
            .collect()
    }

    /// The Loewy length: the least l with rad^l M = 0 (0 for the zero module).
    #[pyo3(text_signature = "($self)")]
    fn loewy_length(&self) -> usize {
        radical::loewy_length(&self.inner)
    }

    /// The dimension vector of top M = M / rad M.
    #[pyo3(text_signature = "($self)")]
    fn top_dims(&self) -> Vec<usize> {
        radical::top(&self.inner).0.dim_vector().to_vec()
    }

    /// The dimension vector of soc M, the largest submodule killed by the radical.
    #[pyo3(text_signature = "($self)")]
    fn socle_dims(&self) -> Vec<usize> {
        radical::socle(&self.inner).0.dim_vector().to_vec()
    }

    /// The projective cover as a pair (P(M), the cover P(M) -> M): P(M) is the
    /// direct sum of P_v with multiplicity dim (top M)_v and the cover is an
    /// epimorphism inducing an isomorphism on tops, so its kernel lies in
    /// rad P(M). The cover has this module as its target, so it composes with
    /// anything else built from the same algebra object. Dual to
    /// injective_envelope.
    #[pyo3(text_signature = "($self)")]
    fn projective_cover(&self) -> (PyRightModule, PyMorphism) {
        let (cover, epi) = projective_cover(&self.inner);
        (PyRightModule { inner: cover }, PyMorphism { inner: epi })
    }

    /// A minimal projective resolution prefix with at most `steps` differentials.
    /// The result records how it ended; see Resolution.status.
    #[pyo3(text_signature = "($self, steps)")]
    fn resolve(&self, steps: usize) -> PyResolution {
        PyResolution {
            module: self.inner.clone(),
            inner: resolve(&self.inner, steps),
        }
    }

    /// The injective envelope as a pair (I(M), the embedding M -> I(M)):
    /// I(M) is the direct sum of I_v with multiplicity dim (soc M)_v and the
    /// embedding is a monomorphism with essential image, dual to the minimality
    /// of a projective cover. The embedding has this module as its source, so it
    /// composes with anything else built from the same algebra object. An
    /// exhausted completion budget while building the opposite algebra raises
    /// TruncationError.
    #[pyo3(text_signature = "($self)")]
    fn injective_envelope(&self) -> PyResult<(PyRightModule, PyMorphism)> {
        let (envelope, embedding) =
            injective::injective_envelope(&self.inner).map_err(downstream_build_error)?;
        Ok((
            PyRightModule { inner: envelope },
            PyMorphism { inner: embedding },
        ))
    }

    /// A minimal injective coresolution prefix with at most `steps`
    /// differentials. The result records how it ended; see
    /// InjectiveCoresolution.status. An exhausted completion budget while
    /// building the opposite algebra raises TruncationError.
    #[pyo3(text_signature = "($self, steps)")]
    fn coresolve(&self, steps: usize) -> PyResult<PyInjectiveCoresolution> {
        Ok(PyInjectiveCoresolution {
            inner: injective::coresolve(&self.inner, steps).map_err(downstream_build_error)?,
        })
    }

    /// The injective dimension, decided up to `bound` differentials: Exact(n)
    /// with n <= bound when the minimal coresolution reaches zero by step
    /// `bound`, AtLeast(bound + 1) otherwise. The coresolution is minimal, so
    /// the lower bound is genuine. The zero module is injective, so its
    /// injective dimension is Exact(0). An exhausted completion budget while
    /// building the opposite algebra raises TruncationError.
    #[pyo3(text_signature = "($self, bound)")]
    fn injective_dimension(&self, bound: usize) -> PyResult<PyBounded> {
        Ok(PyBounded {
            inner: injective::injective_dimension(&self.inner, bound)
                .map_err(downstream_build_error)?,
        })
    }

    /// A verified direct-sum decomposition of the module with one certificate
    /// per summand; the zero module decomposes into no summands. The summands
    /// are ordinary Modules over the same algebra object, so they interact
    /// with everything else built from it. Deterministic: all randomness is
    /// seeded per call.
    #[pyo3(text_signature = "($self)")]
    fn decompose(&self) -> PyDecomposition {
        PyDecomposition {
            inner: decompose::decompose(&self.inner),
        }
    }

    /// Groups the summands of a full decomposition into isomorphism classes
    /// with multiplicities, as a KrullSchmidtResult: `classes` when every
    /// summand was certified indecomposable, an explicit `reason` otherwise,
    /// never a partial grouping.
    #[pyo3(text_signature = "($self)")]
    fn krull_schmidt(&self) -> PyKrullSchmidtResult {
        PyKrullSchmidtResult {
            outcome: decompose::krull_schmidt(&self.inner),
        }
    }

    /// The Auslander-Reiten translate τM as a Module, or None when τM = 0,
    /// which happens exactly when the module is projective. This None is a
    /// definite mathematical answer (the translate is the zero module), not a
    /// partiality convention. Both computation routes (Nakayama kernel and
    /// transpose-then-dual) always run and are cross-checked. A certified
    /// disagreement raises RuntimeError, a library-bug signal distinct from the
    /// ValueError used for input errors. An exhausted completion budget while
    /// building the opposite algebra raises TruncationError with the
    /// diagnostics attached. A cross-check the isomorphism test could not
    /// decide either way raises TauAgreementUnknown, which is a limit of that
    /// test rather than evidence that the routes differ.
    #[pyo3(text_signature = "($self)")]
    fn tau(&self) -> PyResult<Option<PyRightModule>> {
        match ar::tau(&self.inner) {
            Ok(Tau::Zero) => Ok(None),
            Ok(Tau::Module(inner)) => Ok(Some(PyRightModule { inner })),
            Err(e) => Err(tau_error(e)),
        }
    }

    /// The Ext space Ext^degree_A(self, other), with the cochain data
    /// `ext_dim` discards: a basis of classes, each with a representative
    /// cocycle. Raises ValueError when the modules do not share one algebra
    /// object and field.
    #[pyo3(text_signature = "($self, other, degree)")]
    fn ext_space(&self, other: &PyRightModule, degree: usize) -> PyResult<PyExtSpace> {
        check_same_context(&self.inner, &other.inner)?;
        Ok(PyExtSpace {
            inner: ext::ExtSpace::new(&self.inner, &other.inner, degree).map_err(value_error)?,
        })
    }

    /// The almost-split sequence ending at this module, as an
    /// AlmostSplitSequence, or AlmostSplitOutcome.PROJECTIVE when the module
    /// is projective. A projective module is a valid outcome, not an error:
    /// no almost-split sequence ends at it. The module goes through the
    /// indecomposability gate first, so the zero module, a decomposable
    /// module, and a module the gate left undetermined raise
    /// NotIndecomposableError, a ValueError subclass carrying the gate's
    /// report. A failed internal cross-check raises DefectError, a
    /// RuntimeError subclass: it signals a bug in this library, never bad
    /// input.
    #[pyo3(text_signature = "($self)")]
    fn almost_split<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        let module =
            IndecomposableModule::new(&self.inner).map_err(|e| indec_error("the module", e))?;
        match almost_split::almost_split(&module).map_err(almost_split_error)? {
            AlmostSplitOutcome::Projective => Ok(projective_outcome(py)?.into_bound(py).into_any()),
            AlmostSplitOutcome::Sequence(inner) => {
                Ok(Bound::new(py, PyAlmostSplitSequence { module, inner })?.into_any())
            }
        }
    }

    /// The radical rad(self, other) of the module category: the maps that are
    /// not isomorphisms, as a subspace of Hom(self, other). Both endpoints
    /// must pass the indecomposability gate, so both raise
    /// NotIndecomposableError otherwise; the message names the failed
    /// endpoint. Raises ValueError when the modules do not share one algebra
    /// object and field.
    #[pyo3(text_signature = "($self, other)")]
    fn category_radical(&self, other: &PyRightModule) -> PyResult<PyCategoryRadical> {
        check_same_context(&self.inner, &other.inner)?;
        let x = IndecomposableModule::new(&self.inner)
            .map_err(|e| indec_error("the source module", e))?;
        let y = IndecomposableModule::new(&other.inner)
            .map_err(|e| indec_error("the target module", e))?;
        Ok(PyCategoryRadical {
            inner: arquiver::category_radical(&x, &y).map_err(ar_quiver_error)?,
        })
    }

    /// Decides self ≅ other as an IsoResult: isomorphic True comes with a
    /// verified witness (checked two-sided inverse), False with a proof-shaped
    /// obstruction, and None means undetermined, not "no".
    /// Raises ValueError when the modules do not share one algebra object and
    /// field.
    #[pyo3(text_signature = "($self, other)")]
    fn is_isomorphic(&self, other: &PyRightModule) -> PyResult<PyIsoResult> {
        check_same_context(&self.inner, &other.inner)?;
        Ok(PyIsoResult {
            outcome: iso::is_isomorphic(&self.inner, &other.inner).map_err(value_error)?,
        })
    }

    fn __repr__(&self) -> String {
        format!(
            "Module(dims={:?}, field=F_{})",
            self.inner.dim_vector(),
            self.inner.field().modulus()
        )
    }
}

/// A basis element or checked construction of Hom_A(M, N): an A-linear map given
/// by one matrix per vertex, acting on row vectors.
///
/// Instances come from Module.hom (a basis of the hom space) or Module.morphism
/// (a checked construction). Every Morphism satisfies all commuting squares.
#[pyclass(name = "Morphism", module = "auslander")]
struct PyMorphism {
    inner: hom::Morphism,
}

#[pymethods]
impl PyMorphism {
    /// The vertex matrices as canonical integers in 0..p: maps[v] is the
    /// dims_source[v] x dims_target[v] matrix at vertex v, one list per row, in
    /// the same shape `algebra.module` and `Module.morphism` accept.
    #[getter]
    fn maps(&self) -> Vec<Vec<Vec<u64>>> {
        let n = self.inner.source().algebra().quiver().num_vertices();
        (0..n).map(|v| self.inner.map_at(v).entries_u64()).collect()
    }

    /// Whether every vertex matrix is square and invertible, i.e. the morphism
    /// is an isomorphism.
    #[pyo3(text_signature = "($self)")]
    fn is_isomorphism(&self) -> bool {
        self.inner.is_isomorphism()
    }

    fn __repr__(&self) -> String {
        format!(
            "Morphism(source_dims={:?}, target_dims={:?})",
            self.inner.source().dim_vector(),
            self.inner.target().dim_vector()
        )
    }
}

fn obstruction_string(o: &Obstruction) -> String {
    match o {
        Obstruction::DimensionVector { source, target } => {
            format!("dimension vectors differ: {source:?} vs {target:?}")
        }
        Obstruction::LoewySeries { source, target } => {
            format!("radical series differ: {source:?} vs {target:?}")
        }
        Obstruction::HomDimension {
            end_source,
            end_target,
            forward,
            backward,
        } => format!(
            "hom dimensions are asymmetric: dim End = {end_source} vs {end_target}, \
             dim Hom = {forward} vs {backward}"
        ),
        Obstruction::RadicalCriterion => "radical criterion: both modules are indecomposable \
             and every composite through Hom(N, M) lies in rad End(M)"
            .to_string(),
        Obstruction::UnmatchedSummand { dim_vector } => format!(
            "an indecomposable summand with dimension vector {dim_vector:?} \
             matches no summand of the other module"
        ),
    }
}

/// The outcome of Module.is_isomorphic.
///
/// Exactly one of three shapes: `isomorphic` True with a `witness` Morphism
/// verified to have a two-sided inverse; `isomorphic` False with a
/// proof-shaped `obstruction` string (see `obstruction_kind` for programmatic
/// dispatch); or `isomorphic` None with a `reason` string when neither a
/// witness nor an obstruction could be certified. None is distinguishable
/// from False and claims nothing either way. Instances are immutable and come
/// only from Module.is_isomorphic.
#[pyclass(name = "IsoResult", module = "auslander", frozen)]
struct PyIsoResult {
    outcome: IsoOutcome,
}

#[pymethods]
impl PyIsoResult {
    /// True (isomorphic, see `witness`), False (not isomorphic, see
    /// `obstruction`), or None (undetermined, see `reason`).
    #[getter]
    fn isomorphic(&self) -> Option<bool> {
        match &self.outcome {
            IsoOutcome::Isomorphic(_) => Some(true),
            IsoOutcome::NotIsomorphic(_) => Some(false),
            IsoOutcome::Unknown { .. } => None,
        }
    }

    /// The verified isomorphism when `isomorphic` is True; None otherwise.
    #[getter]
    fn witness(&self) -> Option<PyMorphism> {
        match &self.outcome {
            IsoOutcome::Isomorphic(w) => Some(PyMorphism { inner: w.clone() }),
            _ => None,
        }
    }

    /// The proof of non-isomorphism when `isomorphic` is False; None otherwise.
    #[getter]
    fn obstruction(&self) -> Option<String> {
        match &self.outcome {
            IsoOutcome::NotIsomorphic(o) => Some(obstruction_string(o)),
            _ => None,
        }
    }

    /// A stable tag for the obstruction when `isomorphic` is False
    /// ("dimension_vector", "loewy_series", "hom_dimension",
    /// "radical_criterion", or "unmatched_summand"); None otherwise.
    #[getter]
    fn obstruction_kind(&self) -> Option<&'static str> {
        match &self.outcome {
            IsoOutcome::NotIsomorphic(o) => Some(match o {
                Obstruction::DimensionVector { .. } => "dimension_vector",
                Obstruction::LoewySeries { .. } => "loewy_series",
                Obstruction::HomDimension { .. } => "hom_dimension",
                Obstruction::RadicalCriterion => "radical_criterion",
                Obstruction::UnmatchedSummand { .. } => "unmatched_summand",
            }),
            _ => None,
        }
    }

    /// Why certification failed when `isomorphic` is None; None otherwise.
    #[getter]
    fn reason(&self) -> Option<String> {
        match &self.outcome {
            IsoOutcome::Unknown { reason } => Some(reason.clone()),
            _ => None,
        }
    }

    fn __repr__(&self) -> String {
        match &self.outcome {
            IsoOutcome::Isomorphic(_) => "IsoResult(isomorphic=True)".to_string(),
            IsoOutcome::NotIsomorphic(o) => format!(
                "IsoResult(isomorphic=False, obstruction={:?})",
                obstruction_string(o)
            ),
            IsoOutcome::Unknown { reason } => {
                format!("IsoResult(isomorphic=None, reason={reason:?})")
            }
        }
    }
}

/// What decompose proved about one summand.
///
/// `kind` is "indecomposable" (the summand's endomorphism algebra is local, an
/// exact computation, so this is proof) or "undetermined" (every splitting
/// route was exhausted without a decision; nothing is claimed either way, and
/// `attempts` is the number of exhausted seeded split attempts). Instances are
/// immutable and come only from Decomposition.certificates and
/// nakayama_indecomposables.
#[pyclass(name = "Certificate", module = "auslander", frozen)]
struct PyCertificate {
    inner: Certificate,
}

#[pymethods]
impl PyCertificate {
    /// "indecomposable" or "undetermined".
    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner {
            Certificate::Indecomposable => "indecomposable",
            Certificate::Undetermined { .. } => "undetermined",
        }
    }

    /// The number of exhausted split attempts when `kind` is "undetermined";
    /// None when the summand is certified indecomposable.
    #[getter]
    fn attempts(&self) -> Option<u32> {
        match self.inner {
            Certificate::Indecomposable => None,
            Certificate::Undetermined { attempts } => Some(attempts),
        }
    }

    fn __repr__(&self) -> String {
        match self.inner {
            Certificate::Indecomposable => "Certificate(kind='indecomposable')".to_string(),
            Certificate::Undetermined { attempts } => {
                format!("Certificate(kind='undetermined', attempts={attempts})")
            }
        }
    }
}

/// A verified direct-sum decomposition M ≅ S_0 ⊕ ... ⊕ S_{k-1} with one
/// certificate per summand.
///
/// The split identities (each inclusion followed by its projection is the
/// identity, cross terms vanish, the projection-inclusion composites sum to
/// the identity of M) were checked at construction, so holding a
/// Decomposition is proof of the direct sum. certificates[k] is a Certificate
/// whose kind is "indecomposable" (End(S_k) is local, an exact computation)
/// or "undetermined" (every splitting route was exhausted without a decision;
/// nothing is claimed about that summand either way). Instances come only
/// from Module.decompose.
#[pyclass(name = "Decomposition", module = "auslander")]
struct PyDecomposition {
    inner: decompose::Decomposition,
}

#[pymethods]
impl PyDecomposition {
    /// The summands, in certificate order, as Modules over the same algebra
    /// object as the decomposed module.
    #[getter]
    fn summands(&self) -> Vec<PyRightModule> {
        self.inner
            .summands()
            .iter()
            .map(|m| PyRightModule { inner: m.clone() })
            .collect()
    }

    /// The inclusions summands[k] -> M, in summand order.
    #[getter]
    fn inclusions(&self) -> Vec<PyMorphism> {
        self.inner
            .split()
            .inclusions()
            .iter()
            .map(|f| PyMorphism { inner: f.clone() })
            .collect()
    }

    /// The projections M -> summands[k], in summand order.
    #[getter]
    fn projections(&self) -> Vec<PyMorphism> {
        self.inner
            .split()
            .projections()
            .iter()
            .map(|f| PyMorphism { inner: f.clone() })
            .collect()
    }

    /// One Certificate per summand, in summand order.
    #[getter]
    fn certificates(&self) -> Vec<PyCertificate> {
        self.inner
            .certificates()
            .iter()
            .map(|&inner| PyCertificate { inner })
            .collect()
    }

    fn __repr__(&self) -> String {
        let kinds: Vec<&'static str> = self
            .certificates()
            .iter()
            .map(PyCertificate::kind)
            .collect();
        format!(
            "Decomposition(summands={}, certificates={kinds:?})",
            self.inner.summands().len(),
        )
    }
}

/// The outcome of Module.krull_schmidt.
///
/// Exactly one of `classes` and `reason` is set: `classes` lists
/// (representative Module, multiplicity) pairs (a multiset unique up to
/// isomorphism by Krull-Schmidt) when every summand was certified
/// indecomposable, and `reason` says why grouping failed otherwise (no
/// partial grouping is ever claimed). Instances are immutable and come only
/// from Module.krull_schmidt.
#[pyclass(name = "KrullSchmidtResult", module = "auslander", frozen)]
struct PyKrullSchmidtResult {
    outcome: KrullSchmidtOutcome,
}

#[pymethods]
impl PyKrullSchmidtResult {
    /// The isomorphism classes as (representative Module, multiplicity)
    /// pairs, or None when a summand stayed undetermined.
    #[getter]
    fn classes(&self) -> Option<Vec<(PyRightModule, usize)>> {
        match &self.outcome {
            KrullSchmidtOutcome::Classes(classes) => Some(
                classes
                    .iter()
                    .map(|c| {
                        (
                            PyRightModule {
                                inner: c.representative.clone(),
                            },
                            c.multiplicity,
                        )
                    })
                    .collect(),
            ),
            KrullSchmidtOutcome::Unknown { .. } => None,
        }
    }

    /// Why grouping failed, or None when `classes` is set.
    #[getter]
    fn reason(&self) -> Option<String> {
        match &self.outcome {
            KrullSchmidtOutcome::Classes(_) => None,
            KrullSchmidtOutcome::Unknown { reason } => Some(reason.clone()),
        }
    }

    fn __repr__(&self) -> String {
        match &self.outcome {
            KrullSchmidtOutcome::Classes(classes) => {
                let entries: Vec<(Vec<usize>, usize)> = classes
                    .iter()
                    .map(|c| (c.representative.dim_vector().to_vec(), c.multiplicity))
                    .collect();
                format!("KrullSchmidtResult(classes={entries:?})")
            }
            KrullSchmidtOutcome::Unknown { reason } => {
                format!("KrullSchmidtResult(reason={reason:?})")
            }
        }
    }
}

/// How a computed resolution prefix ended: FINITE (reached zero) or CUT (step
/// budget ran out with the next syzygy nonzero).
#[pyclass(name = "ResolutionKind", module = "auslander", frozen, eq)]
#[derive(Clone, Copy, PartialEq)]
enum PyResolutionKind {
    #[pyo3(name = "FINITE")]
    Finite,
    #[pyo3(name = "CUT")]
    Cut,
}

/// How a resolution prefix ended: kind FINITE with at = None means the
/// resolution reached zero; kind CUT with at = n means exactly n differentials
/// were computed and the (n+1)-st syzygy is nonzero, with nothing claimed
/// beyond it. The invariant kind == FINITE iff at is None is enforced at
/// construction, and instances are immutable.
#[pyclass(name = "ResolutionStatus", module = "auslander", frozen, eq)]
#[derive(PartialEq)]
struct PyResolutionStatus {
    end: ResolutionEnd,
}

#[pymethods]
impl PyResolutionStatus {
    /// ResolutionStatus(kind, at=None); raises ValueError unless FINITE comes
    /// with at=None and CUT with an integer at.
    #[new]
    #[pyo3(signature = (kind, at = None), text_signature = "(kind, at=None)")]
    fn new(kind: PyResolutionKind, at: Option<usize>) -> PyResult<Self> {
        let end = match (kind, at) {
            (PyResolutionKind::Finite, None) => ResolutionEnd::Finite,
            (PyResolutionKind::Cut, Some(at)) => ResolutionEnd::Cut { at },
            (PyResolutionKind::Finite, Some(_)) => {
                return Err(PyValueError::new_err(
                    "ResolutionStatus: FINITE takes at=None",
                ));
            }
            (PyResolutionKind::Cut, None) => {
                return Err(PyValueError::new_err(
                    "ResolutionStatus: CUT needs an integer at",
                ));
            }
        };
        Ok(PyResolutionStatus { end })
    }

    /// ResolutionKind.FINITE or ResolutionKind.CUT.
    #[getter]
    fn kind(&self) -> PyResolutionKind {
        match self.end {
            ResolutionEnd::Finite => PyResolutionKind::Finite,
            ResolutionEnd::Cut { .. } => PyResolutionKind::Cut,
        }
    }

    /// The number of computed differentials for CUT; None for FINITE.
    #[getter]
    fn at(&self) -> Option<usize> {
        match self.end {
            ResolutionEnd::Finite => None,
            ResolutionEnd::Cut { at } => Some(at),
        }
    }

    fn __repr__(&self) -> String {
        match self.end {
            ResolutionEnd::Finite => "ResolutionStatus(ResolutionKind.FINITE)".to_string(),
            ResolutionEnd::Cut { at } => {
                format!("ResolutionStatus(ResolutionKind.CUT, at={at})")
            }
        }
    }
}

/// A minimal projective resolution prefix ... -> P_1 -> P_0 -> M -> 0.
///
/// `terms[k]` is P_k and `maps[k]` the differential from terms[k + 1] to
/// terms[k], so there is one map fewer than there are terms; `augmentation` is
/// the projective cover P_0 -> M. `status` says how the computed prefix ended;
/// see ResolutionStatus. Minimality: every differential lands in the radical
/// of its target. InjectiveCoresolution states the dual condition.
#[pyclass(name = "Resolution", module = "auslander")]
struct PyResolution {
    module: Module,
    inner: ProjectiveResolution,
}

#[pymethods]
impl PyResolution {
    /// The terms P_0, P_1, ... as Modules over the same algebra object as the
    /// resolved module.
    #[getter]
    fn terms(&self) -> Vec<PyRightModule> {
        self.inner
            .terms
            .iter()
            .map(|m| PyRightModule { inner: m.clone() })
            .collect()
    }

    /// Dimension vectors of the terms: terms_dims[k] is the dim vector of P_k.
    #[getter]
    fn terms_dims(&self) -> Vec<Vec<usize>> {
        self.inner
            .terms
            .iter()
            .map(|t| t.dim_vector().to_vec())
            .collect()
    }

    /// The differentials, maps[k] going from terms[k + 1] to terms[k].
    #[getter]
    fn maps(&self) -> Vec<PyMorphism> {
        self.inner
            .maps
            .iter()
            .map(|f| PyMorphism { inner: f.clone() })
            .collect()
    }

    /// The augmentation P_0 -> M, the projective cover of the resolved module.
    #[getter]
    fn augmentation(&self) -> PyMorphism {
        PyMorphism {
            inner: self.inner.augmentation.clone(),
        }
    }

    /// How the prefix ended, as an immutable ResolutionStatus: kind FINITE (the
    /// resolution reached zero, so pd M = len(terms_dims) - 1 for nonzero M) or
    /// kind CUT with at = n (exactly n differentials computed, the (n+1)-st
    /// syzygy nonzero).
    #[getter]
    fn status(&self) -> PyResolutionStatus {
        PyResolutionStatus {
            end: self.inner.end,
        }
    }

    /// The projective dimension of the resolved module, decided up to `bound`
    /// differentials: Exact(n) with n <= bound, or AtLeast(bound + 1): the
    /// resolution is minimal, so the lower bound is genuine.
    #[pyo3(text_signature = "($self, bound)")]
    fn pd(&self, bound: usize) -> PyBounded {
        PyBounded {
            inner: projective_dimension(&self.module, bound),
        }
    }

    fn __repr__(&self) -> String {
        let status = match self.inner.end {
            ResolutionEnd::Finite => "finite".to_string(),
            ResolutionEnd::Cut { at } => format!("('cut', {at})"),
        };
        format!(
            "Resolution(terms={}, status={status})",
            self.inner.terms.len()
        )
    }
}

/// A minimal injective coresolution prefix 0 -> M -> I^0 -> I^1 -> ...
///
/// `terms[k]` is I^k and `maps[k]` the differential d^k from I^k to I^{k+1}, so
/// there is one map fewer than there are terms; `coaugmentation` is the
/// injective envelope M -> I^0. `status` says how the computed prefix ended, in
/// the same ResolutionStatus shape a projective resolution reports. Minimality
/// is the dual of "differentials land in the radical": soc I^k lies in the
/// kernel of d^k at every step.
#[pyclass(name = "InjectiveCoresolution", module = "auslander")]
struct PyInjectiveCoresolution {
    inner: InjectiveCoresolution,
}

#[pymethods]
impl PyInjectiveCoresolution {
    /// The terms I^0, I^1, ... as Modules over the same algebra object as the
    /// coresolved module.
    #[getter]
    fn terms(&self) -> Vec<PyRightModule> {
        self.inner
            .terms
            .iter()
            .map(|m| PyRightModule { inner: m.clone() })
            .collect()
    }

    /// Dimension vectors of the terms: terms_dims[k] is the dim vector of I^k.
    #[getter]
    fn terms_dims(&self) -> Vec<Vec<usize>> {
        self.inner
            .terms
            .iter()
            .map(|t| t.dim_vector().to_vec())
            .collect()
    }

    /// The differentials, maps[k] going from terms[k] to terms[k + 1].
    #[getter]
    fn maps(&self) -> Vec<PyMorphism> {
        self.inner
            .maps
            .iter()
            .map(|f| PyMorphism { inner: f.clone() })
            .collect()
    }

    /// The coaugmentation M -> I^0, the injective envelope of the coresolved
    /// module.
    #[getter]
    fn coaugmentation(&self) -> PyMorphism {
        PyMorphism {
            inner: self.inner.coaugmentation.clone(),
        }
    }

    /// How the prefix ended, as an immutable ResolutionStatus: kind FINITE (the
    /// coresolution reached zero, so id M = len(terms_dims) - 1 for nonzero M)
    /// or kind CUT with at = n (exactly n differentials computed, the (n+1)-st
    /// cosyzygy nonzero).
    #[getter]
    fn status(&self) -> PyResolutionStatus {
        PyResolutionStatus {
            end: self.inner.end,
        }
    }

    fn __repr__(&self) -> String {
        let status = match self.inner.end {
            ResolutionEnd::Finite => "finite".to_string(),
            ResolutionEnd::Cut { at } => format!("('cut', {at})"),
        };
        format!(
            "InjectiveCoresolution(terms={}, status={status})",
            self.inner.terms.len()
        )
    }
}

/// A homological invariant known exactly or bounded from below.
///
/// Exactly one of `exact` and `at_least` is set. AtLeast(n) asserts only that the
/// true value is >= n; it does not claim the value finite or infinite. There is no
/// "None means infinite" convention anywhere in this package.
#[pyclass(name = "Bounded", module = "auslander")]
struct PyBounded {
    inner: Bounded<usize>,
}

#[pymethods]
impl PyBounded {
    /// The exact value, or None when only a lower bound is known.
    #[getter]
    fn exact(&self) -> Option<usize> {
        match self.inner {
            Bounded::Exact(n) => Some(n),
            Bounded::AtLeast(_) => None,
        }
    }

    /// The genuine lower bound, or None when the value is known exactly.
    #[getter]
    fn at_least(&self) -> Option<usize> {
        match self.inner {
            Bounded::Exact(_) => None,
            Bounded::AtLeast(n) => Some(n),
        }
    }

    fn __repr__(&self) -> String {
        match self.inner {
            Bounded::Exact(n) => format!("Exact({n})"),
            Bounded::AtLeast(n) => format!("AtLeast({n})"),
        }
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        other
            .extract::<PyRef<'_, PyBounded>>()
            .is_ok_and(|o| o.inner == self.inner)
    }
}

/// The global dimension of the algebra, decided up to `bound` differentials:
/// gldim A = max_v pd S_v. Returns Exact when every simple resolves within the
/// bound, AtLeast(bound + 1) otherwise.
#[pyfunction]
#[pyo3(text_signature = "(algebra, field, bound)")]
fn global_dimension(
    algebra: &PyAlgebra,
    field: &PyPrimeField,
    bound: usize,
) -> PyResult<PyBounded> {
    Ok(PyBounded {
        inner: ext::global_dimension(&algebra.over(field.inner)?, bound),
    })
}

/// Every indecomposable right module of a Nakayama algebra, as
/// (Module, Certificate) pairs: the uniserial quotients P_i / rad^l P_i for
/// 1 <= l <= dim P_i, ordered by vertex then by length l, so the count is
/// dim_k A (the sum of the Kupisch series). Every certificate has kind
/// "indecomposable": it comes from the exact decomposition machinery, which
/// must certify a uniserial module. Raises ValueError when a vertex has more
/// than one incoming or outgoing arrow, i.e. the algebra is not Nakayama and
/// the list would not be exhaustive.
#[pyfunction]
#[pyo3(text_signature = "(algebra, field)")]
fn nakayama_indecomposables(
    algebra: &PyAlgebra,
    field: &PyPrimeField,
) -> PyResult<Vec<(PyRightModule, PyCertificate)>> {
    Ok(
        enumerate::nakayama_indecomposables(&algebra.over(field.inner)?)
            .map_err(value_error)?
            .into_iter()
            .map(|(inner, c)| (PyRightModule { inner }, PyCertificate { inner: c }))
            .collect(),
    )
}

/// One of the five simply laced diagram families. A and D are parametrized by
/// an integer; E6, E7 and E8 each name a single diagram.
#[pyclass(name = "DiagramFamily", module = "auslander", frozen, eq)]
#[derive(Clone, Copy, PartialEq)]
enum PyDiagramFamily {
    A,
    D,
    E6,
    E7,
    E8,
}

/// A simply laced Dynkin diagram: A(n) for n >= 1, D(n) for n >= 4, E6, E7, E8.
///
/// The parameter constraints are enforced at construction, as is the invariant
/// that n is an integer for the A and D families and None for E6, E7 and E8, so
/// `num_vertices` and `indecomposable_count` are exact for every instance.
/// Instances are immutable and compare by family and parameter. str() gives the
/// usual name ("A_3", "D_4", "E_6").
#[pyclass(name = "DynkinType", module = "auslander", frozen, eq)]
#[derive(PartialEq)]
struct PyDynkinType {
    inner: DynkinType,
}

#[pymethods]
impl PyDynkinType {
    /// DynkinType(family, n=None); raises ValueError unless A comes with an
    /// integer n >= 1, D with an integer n >= 4, and E6, E7, E8 with n=None.
    #[new]
    #[pyo3(signature = (family, n = None), text_signature = "(family, n=None)")]
    fn new(family: PyDiagramFamily, n: Option<usize>) -> PyResult<Self> {
        let inner = match (family, n) {
            (PyDiagramFamily::A, Some(n)) if n >= 1 => DynkinType::A(n),
            (PyDiagramFamily::D, Some(n)) if n >= 4 => DynkinType::D(n),
            (PyDiagramFamily::E6, None) => DynkinType::E6,
            (PyDiagramFamily::E7, None) => DynkinType::E7,
            (PyDiagramFamily::E8, None) => DynkinType::E8,
            (PyDiagramFamily::A, _) => {
                return Err(PyValueError::new_err(
                    "DynkinType: A needs an integer n >= 1",
                ));
            }
            (PyDiagramFamily::D, _) => {
                return Err(PyValueError::new_err(
                    "DynkinType: D needs an integer n >= 4",
                ));
            }
            (_, Some(_)) => {
                return Err(PyValueError::new_err(
                    "DynkinType: E6, E7 and E8 take n=None",
                ));
            }
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
#[pyclass(name = "EuclideanType", module = "auslander", frozen, eq)]
#[derive(PartialEq)]
struct PyEuclideanType {
    inner: EuclideanType,
}

#[pymethods]
impl PyEuclideanType {
    /// EuclideanType(family, n=None); raises ValueError unless A comes with an
    /// integer n >= 1, D with an integer n >= 4, and E6, E7, E8 with n=None.
    #[new]
    #[pyo3(signature = (family, n = None), text_signature = "(family, n=None)")]
    fn new(family: PyDiagramFamily, n: Option<usize>) -> PyResult<Self> {
        let inner = match (family, n) {
            (PyDiagramFamily::A, Some(n)) if n >= 1 => EuclideanType::A(n),
            (PyDiagramFamily::D, Some(n)) if n >= 4 => EuclideanType::D(n),
            (PyDiagramFamily::E6, None) => EuclideanType::E6,
            (PyDiagramFamily::E7, None) => EuclideanType::E7,
            (PyDiagramFamily::E8, None) => EuclideanType::E8,
            (PyDiagramFamily::A, _) => {
                return Err(PyValueError::new_err(
                    "EuclideanType: A needs an integer n >= 1",
                ));
            }
            (PyDiagramFamily::D, _) => {
                return Err(PyValueError::new_err(
                    "EuclideanType: D needs an integer n >= 4",
                ));
            }
            (_, Some(_)) => {
                return Err(PyValueError::new_err(
                    "EuclideanType: E6, E7 and E8 take n=None",
                ));
            }
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
#[pyclass(name = "ExtSpace", module = "auslander", frozen)]
struct PyExtSpace {
    inner: ext::ExtSpace,
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
        PyRightModule {
            inner: self.inner.source().clone(),
        }
    }

    /// The target module N.
    #[getter]
    fn target(&self) -> PyRightModule {
        PyRightModule {
            inner: self.inner.target().clone(),
        }
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
struct PyExtClass {
    inner: ext::ExtClass,
}

#[pymethods]
impl PyExtClass {
    /// The source module of the class's space.
    #[getter]
    fn source(&self) -> PyRightModule {
        PyRightModule {
            inner: self.inner.space().source().clone(),
        }
    }

    /// The target module of the class's space.
    #[getter]
    fn target(&self) -> PyRightModule {
        PyRightModule {
            inner: self.inner.space().target().clone(),
        }
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
        PyMorphism {
            inner: self.inner.representative(),
        }
    }

    /// The Yoneda product of this class with `other`, in composition order:
    /// this class in Ext^m(M, N) and `other` in Ext^n(N, L) give a class in
    /// Ext^{m+n}(M, L). Raises IncompatibleSpacesError when this class's
    /// target is not `other`'s source.
    #[pyo3(text_signature = "($self, other)")]
    fn then(&self, other: &PyExtClass) -> PyResult<PyExtClass> {
        Ok(PyExtClass {
            inner: self.inner.then(&other.inner).map_err(ext_class_error)?,
        })
    }

    /// The extension 0 -> target -> E -> source -> 0 realizing this class, as
    /// a ShortExactSequence; the zero class gives the split sequence. Raises
    /// ValueError unless the degree is 1, the only degree in which a class is
    /// an extension.
    #[pyo3(text_signature = "($self)")]
    fn extension(&self) -> PyResult<PyShortExactSequence> {
        Ok(PyShortExactSequence {
            inner: sequence::ShortExactSequence::from_ext1(&self.inner).map_err(sequence_error)?,
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

/// A retraction and a section proving a sequence split.
///
/// `retraction` is r: E -> N with inclusion followed by r the identity of N,
/// and `section` is s: M -> E with s followed by the projection the identity
/// of M. Both are Morphisms, so A-linearity holds by construction. Instances
/// are immutable and come only from `ShortExactSequence.split_status`.
#[pyclass(name = "SplitWitness", module = "auslander", frozen)]
struct PySplitWitness {
    inner: sequence::SplitWitness,
}

#[pymethods]
impl PySplitWitness {
    /// The retraction r: E -> N.
    #[getter]
    fn retraction(&self) -> PyMorphism {
        PyMorphism {
            inner: self.inner.retraction().clone(),
        }
    }

    /// The section s: M -> E.
    #[getter]
    fn section(&self) -> PyMorphism {
        PyMorphism {
            inner: self.inner.section().clone(),
        }
    }

    fn __repr__(&self) -> String {
        format!(
            "SplitWitness(middle_dims={:?}, sub_dims={:?})",
            self.inner.retraction().source().dim_vector(),
            self.inner.retraction().target().dim_vector()
        )
    }
}

/// A dual vector proving a sequence non-split.
///
/// The retraction system is a linear system in the entries of a candidate
/// retraction, built in a fixed equation order. `dual` is a vector y with
/// y A = 0 and y b = 1; the second identity pins its scale. Its existence
/// proves the system unsolvable by multiplication alone, so no retraction
/// exists. Instances are immutable and come only from
/// `ShortExactSequence.split_status`.
#[pyclass(name = "NonSplitWitness", module = "auslander", frozen)]
struct PyNonSplitWitness {
    inner: sequence::NonSplitWitness,
}

#[pymethods]
impl PyNonSplitWitness {
    /// The dual vector as canonical integers in 0..p, one entry per equation
    /// of the retraction system.
    #[getter]
    fn dual(&self) -> Vec<u64> {
        row_u64(self.inner.dual())
    }

    fn __repr__(&self) -> String {
        format!("NonSplitWitness(equations={})", self.inner.dual().len())
    }
}

/// A short exact sequence 0 -> sub -> middle -> quotient -> 0.
///
/// Exactness was checked at construction, per vertex: the inclusion is mono,
/// the projection is epi, the composite is zero, and the middle dimension is
/// the sum of the other two. Together these force image equals kernel, so
/// holding a ShortExactSequence is proof of exactness. Instances are
/// immutable and come from `ExtClass.extension`.
#[pyclass(name = "ShortExactSequence", module = "auslander", frozen)]
struct PyShortExactSequence {
    inner: sequence::ShortExactSequence,
}

#[pymethods]
impl PyShortExactSequence {
    /// The sub module N.
    #[getter]
    fn sub(&self) -> PyRightModule {
        PyRightModule {
            inner: self.inner.sub().clone(),
        }
    }

    /// The middle module E.
    #[getter]
    fn middle(&self) -> PyRightModule {
        PyRightModule {
            inner: self.inner.middle().clone(),
        }
    }

    /// The quotient module M.
    #[getter]
    fn quotient(&self) -> PyRightModule {
        PyRightModule {
            inner: self.inner.quotient().clone(),
        }
    }

    /// The inclusion N -> E.
    #[getter]
    fn inclusion(&self) -> PyMorphism {
        PyMorphism {
            inner: self.inner.inclusion().clone(),
        }
    }

    /// The projection E -> M.
    #[getter]
    fn projection(&self) -> PyMorphism {
        PyMorphism {
            inner: self.inner.projection().clone(),
        }
    }

    /// The class of this extension in Ext^1(quotient, sub). The space is
    /// rebuilt for this call, so the class of an extension built from a class
    /// carries the same coordinates as the original.
    #[pyo3(text_signature = "($self)")]
    fn ext1_class(&self) -> PyResult<PyExtClass> {
        let space =
            ext::ExtSpace::new(self.inner.quotient(), self.inner.sub(), 1).map_err(value_error)?;
        Ok(PyExtClass {
            inner: self.inner.ext1_class(&space).map_err(sequence_error)?,
        })
    }

    /// Whether the sequence splits, decided by solving the retraction system.
    /// Both answers carry a proof; see `split_status`.
    #[getter]
    fn is_split(&self) -> bool {
        matches!(self.inner.split_status(), SplitStatus::Split(_))
    }

    /// The proof behind `is_split`: a SplitWitness with a retraction and a
    /// section, or a NonSplitWitness with the dual vector of the unsolvable
    /// retraction system.
    #[getter]
    fn split_status<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        match self.inner.split_status() {
            SplitStatus::Split(inner) => Ok(Bound::new(py, PySplitWitness { inner })?.into_any()),
            SplitStatus::NonSplit(inner) => {
                Ok(Bound::new(py, PyNonSplitWitness { inner })?.into_any())
            }
        }
    }

    /// Rechecks the sequence: rebuilds it through the exactness checks and
    /// rechecks the split-status witness by multiplication.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self) -> bool {
        if sequence::ShortExactSequence::new(
            self.inner.inclusion().clone(),
            self.inner.projection().clone(),
        )
        .is_err()
        {
            return false;
        }
        match self.inner.split_status() {
            SplitStatus::Split(w) => w.verify(&self.inner),
            SplitStatus::NonSplit(w) => w.verify(&self.inner),
        }
    }

    fn __repr__(&self) -> String {
        format!(
            "ShortExactSequence(sub_dims={:?}, middle_dims={:?}, quotient_dims={:?})",
            self.inner.sub().dim_vector(),
            self.inner.middle().dim_vector(),
            self.inner.quotient().dim_vector()
        )
    }
}

/// The outcome of `Module.almost_split` for a projective module.
///
/// The class has one member, `AlmostSplitOutcome.PROJECTIVE`, and
/// `Module.almost_split` returns that very object, so `is` decides the case.
/// No almost-split sequence ends at a projective module; that is mathematics,
/// not a failure, and it is never reported as None.
#[pyclass(name = "AlmostSplitOutcome", module = "auslander", frozen, eq)]
#[derive(PartialEq)]
struct PyAlmostSplitOutcome;

static PROJECTIVE_OUTCOME: GILOnceCell<Py<PyAlmostSplitOutcome>> = GILOnceCell::new();

/// The single PROJECTIVE member, built once, so the value `almost_split`
/// returns and the class attribute are one object.
fn projective_outcome(py: Python<'_>) -> PyResult<Py<PyAlmostSplitOutcome>> {
    Ok(PROJECTIVE_OUTCOME
        .get_or_try_init(py, || Py::new(py, PyAlmostSplitOutcome))?
        .clone_ref(py))
}

#[pymethods]
impl PyAlmostSplitOutcome {
    /// The projective outcome: the module is projective, so no almost-split
    /// sequence ends at it.
    #[classattr]
    #[pyo3(name = "PROJECTIVE")]
    fn projective(py: Python<'_>) -> PyResult<Py<PyAlmostSplitOutcome>> {
        projective_outcome(py)
    }

    fn __repr__(&self) -> String {
        "AlmostSplitOutcome.PROJECTIVE".to_string()
    }
}

/// An almost-split sequence 0 -> start -> middle -> end -> 0 with the witness
/// that certifies it.
///
/// `start` is the AR translate of `end`. The sequence realizes a chosen class
/// of the socle of Ext^1(end, start) as a module over the endomorphism algebra
/// of `end`; the class is deterministic, not canonical, and any nonzero socle
/// class gives an almost-split sequence isomorphic to this one after suitable
/// automorphisms of the end terms, not an equivalent extension with fixed
/// ends. `verify()` rechecks every gate of the
/// construction from the stored witness and the live modules, and
/// `verification_summary()` reports the gates one by one. Instances are
/// immutable and come only from `Module.almost_split`.
#[pyclass(name = "AlmostSplitSequence", module = "auslander", frozen)]
struct PyAlmostSplitSequence {
    module: IndecomposableModule,
    inner: almost_split::AlmostSplitSequence,
}

impl PyAlmostSplitSequence {
    /// The AR duality witness. `Module.almost_split` runs the AR duality
    /// route, so the catalog variant is unreachable through this package.
    fn ar_duality(&self) -> PyResult<&almost_split::ArDualityWitness> {
        match self.inner.witness() {
            AlmostSplitWitness::ArDuality(witness) => Ok(witness),
            AlmostSplitWitness::ExhaustiveCatalog(_) => Err(engine_error(
                "the sequence carries a catalog witness, which this package never builds",
            )),
        }
    }
}

#[pymethods]
impl PyAlmostSplitSequence {
    /// The left end, the AR translate of `end`.
    #[getter]
    fn start(&self) -> PyRightModule {
        PyRightModule {
            inner: self.inner.sequence().sub().clone(),
        }
    }

    /// The middle term.
    #[getter]
    fn middle(&self) -> PyRightModule {
        PyRightModule {
            inner: self.inner.sequence().middle().clone(),
        }
    }

    /// The right end: the module the sequence was built for.
    #[getter]
    fn end(&self) -> PyRightModule {
        PyRightModule {
            inner: self.inner.sequence().quotient().clone(),
        }
    }

    /// The inclusion start -> middle.
    #[getter]
    fn inclusion(&self) -> PyMorphism {
        PyMorphism {
            inner: self.inner.sequence().inclusion().clone(),
        }
    }

    /// The projection middle -> end.
    #[getter]
    fn projection(&self) -> PyMorphism {
        PyMorphism {
            inner: self.inner.sequence().projection().clone(),
        }
    }

    /// The chosen AR class in Ext^1(end, start) that the sequence realizes:
    /// the first row of the socle basis. Deterministic, not canonical.
    #[pyo3(text_signature = "($self)")]
    fn ext1_class(&self) -> PyExtClass {
        PyExtClass {
            inner: self.inner.chosen_ar_class().clone(),
        }
    }

    /// Which route certified the sequence: "ar_duality" for the socle
    /// construction of AR duality, "exhaustive_catalog" for the catalog
    /// route. `Module.almost_split` always runs the AR duality route.
    #[getter]
    fn witness_route(&self) -> &'static str {
        match self.inner.witness() {
            AlmostSplitWitness::ArDuality(_) => "ar_duality",
            AlmostSplitWitness::ExhaustiveCatalog(_) => "exhaustive_catalog",
        }
    }

    /// Rechecks the whole witness against freshly recomputed data: the
    /// radical basis and the action matrices of the endomorphism algebra, the
    /// socle kernel, the two dimension equalities, the recovery of the class
    /// from the sequence, the non-split witness, and exactness.
    #[pyo3(text_signature = "($self)")]
    fn verify(&self) -> PyResult<bool> {
        let witness = self.ar_duality()?;
        Ok(witness.verify(
            &self.module,
            self.inner.sequence(),
            self.inner.chosen_ar_class(),
        ))
    }

    /// The gates of the construction one by one, as a dict of check name to
    /// result: "action_traces" (the chosen class is annihilated by every
    /// radical endomorphism), "socle_membership" (the class is the stored
    /// socle row and is nonzero), "duality_dimensions" (dim Ext^1(end, start)
    /// equals dim of the stable endomorphism algebra), "socle_dimension" (the
    /// socle dimension equals the residue degree), "non_split" (the dual
    /// vector proves no retraction exists), and "sequence_exact" (the
    /// exactness checks pass again). `verify()` is the stronger statement: it
    /// recomputes the stored data instead of reading it.
    #[pyo3(text_signature = "($self)")]
    fn verification_summary(&self) -> PyResult<BTreeMap<&'static str, bool>> {
        let witness = self.ar_duality()?;
        let sequence = self.inner.sequence();
        let class = self.inner.chosen_ar_class();
        let action_traces = witness.action_traces().len() == witness.radical_basis_coords().rows()
            && witness
                .action_traces()
                .iter()
                .all(|trace| trace.iter().all(|c| c.is_zero()));
        let socle_membership = witness.chosen_row() < witness.socle_rref().rows()
            && class.coordinates() == witness.socle_rref().row(witness.chosen_row())
            && !class.is_zero();
        let duality_dimensions = witness.ext_dim() == witness.stable_end_dim()
            && witness.ext_dim() == class.space().dim();
        let socle_dimension = witness.socle_dim() == witness.socle_rref().rows()
            && witness.socle_dim() == witness.residue_degree()
            && witness.residue_degree() == self.module.residue_degree();
        let non_split = witness.non_split().verify(sequence);
        let sequence_exact = sequence::ShortExactSequence::new(
            sequence.inclusion().clone(),
            sequence.projection().clone(),
        )
        .is_ok();
        Ok(BTreeMap::from([
            ("action_traces", action_traces),
            ("duality_dimensions", duality_dimensions),
            ("non_split", non_split),
            ("sequence_exact", sequence_exact),
            ("socle_dimension", socle_dimension),
            ("socle_membership", socle_membership),
        ]))
    }

    fn __repr__(&self) -> String {
        format!(
            "AlmostSplitSequence(start_dims={:?}, middle_dims={:?}, end_dims={:?})",
            self.inner.sequence().sub().dim_vector(),
            self.inner.sequence().middle().dim_vector(),
            self.inner.sequence().quotient().dim_vector()
        )
    }
}

/// The radical rad(X, Y) of the module category between two certified
/// indecomposables, as a subspace of Hom(X, Y).
///
/// The radical holds the maps that are not isomorphisms: the whole hom space
/// when X and Y are not isomorphic, and the maps whose composite with a fixed
/// isomorphism lands in the radical of End(X) when they are. The computation
/// is exact and needs no catalog. Instances are immutable and come only from
/// `Module.category_radical`.
#[pyclass(name = "CategoryRadical", module = "auslander", frozen)]
struct PyCategoryRadical {
    inner: HomSubspace,
}

#[pymethods]
impl PyCategoryRadical {
    /// dim_k rad(X, Y).
    #[getter]
    fn dim(&self) -> usize {
        self.inner.dim()
    }

    /// A basis of the radical as a list of Morphism objects, not every
    /// radical map: arbitrary radical maps are its linear combinations.
    #[pyo3(text_signature = "($self)")]
    fn basis(&self) -> Vec<PyMorphism> {
        (0..self.inner.dim())
            .map(|r| PyMorphism {
                inner: self.inner.basis_morphism(r),
            })
            .collect()
    }

    fn __repr__(&self) -> String {
        format!(
            "CategoryRadical(dim={}, source_dims={:?}, target_dims={:?})",
            self.inner.dim(),
            self.inner.source().dim_vector(),
            self.inner.target().dim_vector()
        )
    }
}

/// One vertex of an AR quiver: an indecomposable module with the data the
/// quiver labels it by.
///
/// `id` is the index of the vertex in `ArQuiver.vertices()` and in the catalog
/// behind it. `residue_degree` is the degree d of the residue field F_{p^d} of
/// the local endomorphism algebra; it is 1 on both catalog domains of this
/// release. Instances are immutable.
#[pyclass(name = "ArVertex", module = "auslander", frozen)]
struct PyArVertex {
    quiver: Arc<ArQuiver>,
    index: usize,
}

#[pymethods]
impl PyArVertex {
    /// The index of the vertex in `ArQuiver.vertices()`.
    #[getter]
    fn id(&self) -> usize {
        self.quiver.vertices()[self.index].id()
    }

    /// The module at the vertex.
    #[getter]
    fn module(&self) -> PyRightModule {
        PyRightModule {
            inner: self.quiver.vertices()[self.index].module().module().clone(),
        }
    }

    /// The degree d of the residue field F_{p^d} of the module's local
    /// endomorphism algebra.
    #[getter]
    fn residue_degree(&self) -> usize {
        self.quiver.vertices()[self.index].residue_degree()
    }

    /// Whether the module is projective.
    #[getter]
    fn projective(&self) -> bool {
        self.quiver.vertices()[self.index].projective()
    }

    /// Whether the module is injective.
    #[getter]
    fn injective(&self) -> bool {
        self.quiver.vertices()[self.index].injective()
    }

    fn __repr__(&self) -> String {
        let vertex = &self.quiver.vertices()[self.index];
        format!(
            "ArVertex(id={}, dims={:?}, residue_degree={})",
            vertex.id(),
            vertex.module().module().dim_vector(),
            vertex.residue_degree()
        )
    }
}

/// One arrow of an AR quiver: a pair of vertices with a nonzero space of
/// irreducible maps, together with its three dimensions.
///
/// `base_field_dim` is dim_k Irr(X, Y) over the prime field.
/// `dim_over_source_residue` and `dim_over_target_residue` are its dimensions
/// over the two residue fields; they differ from `base_field_dim` exactly when
/// a residue degree exceeds 1. `plain_multiplicity` is the arrow multiplicity
/// of an unvalued AR quiver; it raises ValuedArrowError on a valued arrow
/// instead of reducing three dimensions to one integer. Instances are
/// immutable.
#[pyclass(name = "ArArrow", module = "auslander", frozen)]
struct PyArArrow {
    quiver: Arc<ArQuiver>,
    index: usize,
}

#[pymethods]
impl PyArArrow {
    /// The id of the source vertex.
    #[getter]
    fn source(&self) -> usize {
        self.quiver.arrows()[self.index].source()
    }

    /// The id of the target vertex.
    #[getter]
    fn target(&self) -> usize {
        self.quiver.arrows()[self.index].target()
    }

    /// dim_k Irr(X, Y) over the prime field.
    #[getter]
    fn base_field_dim(&self) -> usize {
        self.quiver.arrows()[self.index].base_dim()
    }

    /// The dimension of Irr(X, Y) over the residue field of the source.
    #[getter]
    fn dim_over_source_residue(&self) -> usize {
        self.quiver.arrows()[self.index].over_source_residue()
    }

    /// The dimension of Irr(X, Y) over the residue field of the target.
    #[getter]
    fn dim_over_target_residue(&self) -> usize {
        self.quiver.arrows()[self.index].over_target_residue()
    }

    /// The arrow multiplicity of an unvalued AR quiver, defined only when both
    /// residue degrees are 1; raises ValuedArrowError, a ValueError subclass,
    /// otherwise. A valued arrow carries three dimensions, and none of them is
    /// the multiplicity.
    #[getter]
    fn plain_multiplicity(&self) -> PyResult<usize> {
        match self.quiver.arrows()[self.index].valuation() {
            ArrowValuation::Plain(m) => Ok(m),
            ArrowValuation::Valued {
                base_dim,
                over_source,
                over_target,
            } => Err(ValuedArrowError::new_err(format!(
                "the arrow is valued: dim_k Irr = {base_dim} over the prime field, \
                 {over_source} over the source residue field, {over_target} over the target \
                 residue field; read those three dimensions instead"
            ))),
        }
    }

    /// Representatives of a basis of Irr(X, Y) as Morphism objects, one per
    /// dimension over the prime field.
    #[pyo3(text_signature = "($self)")]
    fn representatives(&self) -> Vec<PyMorphism> {
        self.quiver.arrows()[self.index]
            .representatives()
            .iter()
            .map(|f| PyMorphism { inner: f.clone() })
            .collect()
    }

    fn __repr__(&self) -> String {
        let arrow = &self.quiver.arrows()[self.index];
        format!(
            "ArArrow(source={}, target={}, base_field_dim={})",
            arrow.source(),
            arrow.target(),
            arrow.base_dim()
        )
    }
}

/// The valued Auslander-Reiten quiver of an algebra.
///
/// One vertex per indecomposable of a complete enumeration, one arrow per
/// nonzero space of irreducible maps, ordered by source id then target id. The
/// quiver is complete for its domain: the enumeration behind it is a
/// classification theorem (Nakayama or Gabriel) and no budget cuts the
/// construction short, so there is no partial AR quiver. Instances are
/// immutable and come only from `Algebra.ar_quiver`.
#[pyclass(name = "ArQuiver", module = "auslander", frozen)]
struct PyArQuiver {
    inner: Arc<ArQuiver>,
}

#[pymethods]
impl PyArQuiver {
    /// The vertices in catalog order.
    #[pyo3(text_signature = "($self)")]
    fn vertices(&self) -> Vec<PyArVertex> {
        (0..self.inner.vertices().len())
            .map(|index| PyArVertex {
                quiver: self.inner.clone(),
                index,
            })
            .collect()
    }

    /// The arrows, ordered by source id then target id.
    #[pyo3(text_signature = "($self)")]
    fn arrows(&self) -> Vec<PyArArrow> {
        (0..self.inner.arrows().len())
            .map(|index| PyArArrow {
                quiver: self.inner.clone(),
                index,
            })
            .collect()
    }

    fn __repr__(&self) -> String {
        format!(
            "ArQuiver(vertices={}, arrows={})",
            self.inner.vertices().len(),
            self.inner.arrows().len()
        )
    }
}

create_exception!(
    auslander,
    TauAgreementUnknown,
    PyRuntimeError,
    "The two tau routes were computed but the isomorphism test could not certify \
     them equal or unequal. This is a limit of that test, not evidence that the \
     routes disagree; a certified disagreement raises RuntimeError itself."
);

create_exception!(
    auslander,
    BudgetExhaustedError,
    PyRuntimeError,
    "Base of the budget exhaustions: an enforced work budget ran out before \
     the computation finished. Nothing is claimed about the result; raise the \
     limits and run again. The variant is the subclass."
);

create_exception!(
    auslander,
    TruncationError,
    BudgetExhaustedError,
    "Completion ran out of budget before it produced a certificate. The \
     consumed budget is attached: `basis_len`, `pending_ambiguities`, \
     `steps_used`, and `reason` (\"basis_budget\", \"word_len_budget\", or \
     \"step_budget\"). Nothing is claimed about the algebra; raise the limits \
     and rebuild."
);

create_exception!(
    auslander,
    DefectError,
    PyRuntimeError,
    "An internal cross-check of this library failed: a computation checked a \
     consequence of a theorem whose hypotheses hold, and the check came out \
     false. This is a bug in auslander, never bad input, and it is reported \
     as such. Please report it with the input that produced it."
);

create_exception!(
    auslander,
    NotIndecomposableError,
    PyValueError,
    "The module did not pass the indecomposability gate, which the \
     almost-split and category-radical constructions need. `kind` is \"zero\", \
     \"decomposable\", or \"undetermined\"; `summands` counts the certified \
     summands of a decomposable module and `attempts` the exhausted split \
     attempts of an undetermined one. Undetermined claims nothing either way."
);

create_exception!(
    auslander,
    IncompatibleSpacesError,
    PyValueError,
    "The two Ext classes do not live in one space, so the operation is \
     undefined. Compatible spaces need the same source module object, the \
     same target module object, and equal degrees. Comparison raises this \
     rather than answering False, which would claim the classes differ."
);

create_exception!(
    auslander,
    UnsupportedDomainError,
    PyValueError,
    "No complete enumeration of the indecomposables applies to this algebra, \
     so it has no AR quiver in this release. The message names both failed \
     routes, the Dynkin one and the Nakayama one."
);

create_exception!(
    auslander,
    ValuedArrowError,
    PyValueError,
    "The arrow is valued: a residue degree above 1 makes the dimensions of \
     Irr(X, Y) over the prime field and over the two residue fields differ, so \
     no single integer is the multiplicity. Read `base_field_dim`, \
     `dim_over_source_residue`, and `dim_over_target_residue`."
);

create_exception!(
    auslander,
    DynkinError,
    PyValueError,
    "Base of the two rejections of dynkin_indecomposables; the variant is the \
     subclass, NonzeroIdealError or NotDynkinError."
);

create_exception!(
    auslander,
    NonzeroIdealError,
    DynkinError,
    "The algebra is a proper quotient of kQ, so Gabriel's theorem does not list \
     its indecomposables. `forbidden_words` is the number of relations in the \
     reduced Groebner basis; for a monomial algebra these are exactly its \
     minimal forbidden words."
);

create_exception!(
    auslander,
    NotDynkinError,
    DynkinError,
    "The underlying graph of the quiver is no Dynkin diagram, so kQ is not \
     representation finite. `euclidean` is the EuclideanType of that graph when \
     it has one and None otherwise."
);

/// The rejection as an exception of the matching subclass, its payload attached
/// as attributes so the variant survives the boundary.
fn dynkin_error(py: Python<'_>, e: dynkin::DynkinError) -> PyErr {
    let err = match e {
        dynkin::DynkinError::NonzeroIdeal { .. } => NonzeroIdealError::new_err(e.to_string()),
        dynkin::DynkinError::NotDynkin { .. } => NotDynkinError::new_err(e.to_string()),
    };
    let attached = match e {
        // The Groebner relation count; for monomial input these relations are
        // exactly the minimal forbidden words.
        dynkin::DynkinError::NonzeroIdeal { relations } => {
            err.value(py).setattr("forbidden_words", relations)
        }
        dynkin::DynkinError::NotDynkin { euclidean } => err.value(py).setattr(
            "euclidean",
            euclidean.map(|inner| PyEuclideanType { inner }),
        ),
    };
    match attached {
        Ok(()) => err,
        Err(failure) => failure,
    }
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
fn dynkin_type(quiver: &PyQuiver) -> Option<PyDynkinType> {
    dynkin::dynkin_type(&quiver.inner).map(|inner| PyDynkinType { inner })
}

/// The Euclidean (affine) type of the quiver's underlying graph, or None when
/// that graph is no Euclidean diagram; the None is a definite answer about the
/// graph, as for `dynkin_type`.
#[pyfunction]
#[pyo3(text_signature = "(quiver)")]
fn euclidean_type(quiver: &PyQuiver) -> Option<PyEuclideanType> {
    dynkin::euclidean_type(&quiver.inner).map(|inner| PyEuclideanType { inner })
}

/// The generalized Cartan matrix of the quiver's underlying graph: 2 on the
/// diagonal and minus the number of edges joining i and j off it. None exactly
/// when the quiver has a loop, since a vertex carrying a loop contributes no row
/// with diagonal entry 2.
#[pyfunction]
#[pyo3(text_signature = "(quiver)")]
fn generalized_cartan_matrix(quiver: &PyQuiver) -> Option<Vec<Vec<i64>>> {
    dynkin::generalized_cartan_matrix(&quiver.inner)
}

/// The positive roots of the quiver's underlying graph, in the quiver's own
/// vertex indexing, ordered by height and then lexicographically; None when the
/// graph is no Dynkin diagram, where the list would be infinite or undefined.
#[pyfunction]
#[pyo3(text_signature = "(quiver)")]
fn positive_roots(quiver: &PyQuiver) -> Option<Vec<Vec<usize>>> {
    dynkin::positive_roots(&quiver.inner)
}

/// A quiver whose underlying graph is the named Dynkin diagram, oriented away
/// from the branch vertex. The abstract diagram is unbounded, but a Quiver
/// indexes its vertices by u32; raises ValueError when the diagram's vertex
/// count exceeds that limit.
#[pyfunction]
#[pyo3(text_signature = "(diagram)")]
fn dynkin_quiver(diagram: &PyDynkinType) -> PyResult<PyQuiver> {
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
fn euclidean_quiver(diagram: &PyEuclideanType) -> PyResult<PyQuiver> {
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
fn dynkin_indecomposables(
    py: Python<'_>,
    algebra: &PyAlgebra,
    field: &PyPrimeField,
) -> PyResult<Vec<(PyRightModule, PyCertificate)>> {
    Ok(dynkin::dynkin_indecomposables(&algebra.over(field.inner)?)
        .map_err(|e| dynkin_error(py, e))?
        .into_iter()
        .map(|(inner, c)| (PyRightModule { inner }, PyCertificate { inner: c }))
        .collect())
}

/// Finite-dimensional basic algebras kQ/I over a checked prime field, where I
/// is an admissible ideal given by forbidden words or by general relations,
/// and their finite-dimensional right modules. Convention: paths compose left
/// to right, and modules are right modules whose arrow matrices act on row
/// vectors.
#[pymodule(name = "auslander")]
fn auslander_py(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PyPrimeField>()?;
    m.add_class::<PyQuiver>()?;
    m.add_class::<PyAlgebra>()?;
    // The v0.2 name of the class: one type under two names.
    m.add("MonomialAlgebra", m.py().get_type::<PyAlgebra>())?;
    m.add_class::<PyRightModule>()?;
    m.add_class::<PyMorphism>()?;
    m.add_class::<PyIsoResult>()?;
    m.add_class::<PyCertificate>()?;
    m.add_class::<PyDecomposition>()?;
    m.add_class::<PyKrullSchmidtResult>()?;
    m.add_class::<PyResolutionKind>()?;
    m.add_class::<PyResolutionStatus>()?;
    m.add_class::<PyResolution>()?;
    m.add_class::<PyInjectiveCoresolution>()?;
    m.add_class::<PyBounded>()?;
    m.add_class::<PyDiagramFamily>()?;
    m.add_class::<PyDynkinType>()?;
    m.add_class::<PyEuclideanType>()?;
    m.add_class::<PyExtSpace>()?;
    m.add_class::<PyExtClass>()?;
    m.add_class::<PySplitWitness>()?;
    m.add_class::<PyNonSplitWitness>()?;
    m.add_class::<PyShortExactSequence>()?;
    m.add_class::<PyAlmostSplitOutcome>()?;
    m.add_class::<PyAlmostSplitSequence>()?;
    m.add_class::<PyCategoryRadical>()?;
    m.add_class::<PyArVertex>()?;
    m.add_class::<PyArArrow>()?;
    m.add_class::<PyArQuiver>()?;
    m.add(
        "TauAgreementUnknown",
        m.py().get_type::<TauAgreementUnknown>(),
    )?;
    m.add(
        "BudgetExhaustedError",
        m.py().get_type::<BudgetExhaustedError>(),
    )?;
    m.add("TruncationError", m.py().get_type::<TruncationError>())?;
    m.add("DefectError", m.py().get_type::<DefectError>())?;
    m.add(
        "NotIndecomposableError",
        m.py().get_type::<NotIndecomposableError>(),
    )?;
    m.add(
        "IncompatibleSpacesError",
        m.py().get_type::<IncompatibleSpacesError>(),
    )?;
    m.add(
        "UnsupportedDomainError",
        m.py().get_type::<UnsupportedDomainError>(),
    )?;
    m.add("ValuedArrowError", m.py().get_type::<ValuedArrowError>())?;
    m.add("DynkinError", m.py().get_type::<DynkinError>())?;
    m.add("NonzeroIdealError", m.py().get_type::<NonzeroIdealError>())?;
    m.add("NotDynkinError", m.py().get_type::<NotDynkinError>())?;
    m.add_function(wrap_pyfunction!(global_dimension, m)?)?;
    m.add_function(wrap_pyfunction!(nakayama_indecomposables, m)?)?;
    m.add_function(wrap_pyfunction!(dynkin_type, m)?)?;
    m.add_function(wrap_pyfunction!(euclidean_type, m)?)?;
    m.add_function(wrap_pyfunction!(generalized_cartan_matrix, m)?)?;
    m.add_function(wrap_pyfunction!(positive_roots, m)?)?;
    m.add_function(wrap_pyfunction!(dynkin_quiver, m)?)?;
    m.add_function(wrap_pyfunction!(euclidean_quiver, m)?)?;
    m.add_function(wrap_pyfunction!(dynkin_indecomposables, m)?)?;
    Ok(())
}

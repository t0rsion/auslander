use super::*;

pub(crate) fn obstruction_string(o: &Obstruction) -> String {
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
pub(crate) struct PyIsoResult {
    pub(crate) outcome: IsoOutcome,
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
            IsoOutcome::Isomorphic(w) => Some(w.into()),
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
pub(crate) struct PyCertificate {
    pub(crate) inner: Certificate,
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
pub(crate) struct PyDecomposition {
    pub(crate) inner: decompose::Decomposition,
}

#[pymethods]
impl PyDecomposition {
    /// The summands, in certificate order, as Modules over the same algebra
    /// object as the decomposed module.
    #[getter]
    fn summands(&self) -> Vec<PyRightModule> {
        wrap_all(self.inner.summands())
    }

    /// The inclusions summands[k] -> M, in summand order.
    #[getter]
    fn inclusions(&self) -> Vec<PyMorphism> {
        wrap_all(self.inner.split().inclusions())
    }

    /// The projections M -> summands[k], in summand order.
    #[getter]
    fn projections(&self) -> Vec<PyMorphism> {
        wrap_all(self.inner.split().projections())
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

    /// The number of summands.
    fn __len__(&self) -> usize {
        self.inner.summands().len()
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
pub(crate) struct PyKrullSchmidtResult {
    pub(crate) outcome: KrullSchmidtOutcome,
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
                    .map(|c| ((&c.representative).into(), c.multiplicity))
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

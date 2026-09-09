use super::super::*;

/// One retained census representative with its raw coordinate provenance.
#[pyclass(name = "CensusRepresentative", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyCensusRepresentative {
    pub(crate) inner: CensusPortableRepresentative,
}

#[pymethods]
impl PyCensusRepresentative {
    /// The raw-domain cursor that produced this representative.
    #[getter]
    fn cursor(&self) -> u128 {
        self.inner.cursor()
    }

    /// The arrow-matrix entries in the census coordinate order.
    #[getter]
    fn coordinates(&self) -> Vec<u64> {
        self.inner.coordinates().to_vec()
    }

    fn __repr__(&self) -> String {
        format!(
            "CensusRepresentative(cursor={}, coordinates={:?})",
            self.cursor(),
            self.inner.coordinates()
        )
    }
}

/// One duplicate census assignment with its checked isomorphism witness.
#[pyclass(name = "CensusAssignment", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyCensusAssignment {
    pub(crate) inner: CensusPortableAssignment,
}

#[pymethods]
impl PyCensusAssignment {
    /// The raw-domain cursor assigned to a representative.
    #[getter]
    fn cursor(&self) -> u128 {
        self.inner.cursor()
    }

    /// The arrow-matrix entries in the census coordinate order.
    #[getter]
    fn coordinates(&self) -> Vec<u64> {
        self.inner.coordinates().to_vec()
    }

    /// The representative index receiving this assignment.
    #[getter]
    fn representative(&self) -> usize {
        self.inner.representative()
    }

    /// The candidate-to-representative witness matrices.
    #[getter]
    fn witness(&self) -> Vec<Vec<Vec<u64>>> {
        self.inner.witness().to_vec()
    }

    fn __repr__(&self) -> String {
        format!(
            "CensusAssignment(cursor={}, representative={})",
            self.cursor(),
            self.representative()
        )
    }
}

/// The typed reason for a census prefix cut.
#[pyclass(name = "CensusCutReason", module = "auslander", frozen)]
#[derive(Clone)]
pub(crate) struct PyCensusCutReason {
    pub(crate) inner: CensusCutReason,
}

#[pymethods]
impl PyCensusCutReason {
    /// The stable reason kind, such as `candidate_limit` or `work_limit`.
    #[getter]
    fn kind(&self) -> &'static str {
        census_cut_kind(&self.inner)
    }

    /// The limit attached to a bounded cut, when present.
    #[getter]
    fn limit(&self) -> Option<usize> {
        match self.inner {
            CensusCutReason::CandidateLimit { limit }
            | CensusCutReason::RepresentativeLimit { limit }
            | CensusCutReason::AssignmentLimit { limit }
            | CensusCutReason::IsomorphismLimit { limit }
            | CensusCutReason::WorkLimit { limit, .. } => Some(limit),
            CensusCutReason::Cancelled | CensusCutReason::UnknownIsomorphism { .. } => None,
        }
    }

    /// The work stage attached to a work cut, when present.
    #[getter]
    fn stage(&self) -> Option<&'static str> {
        match self.inner {
            CensusCutReason::WorkLimit { stage, .. } => Some(match stage {
                CensusWorkStage::Candidate => "candidate",
                CensusWorkStage::Isomorphism => "isomorphism",
            }),
            _ => None,
        }
    }

    /// The representative attached to an unknown-isomorphism cut, when present.
    #[getter]
    fn representative(&self) -> Option<usize> {
        match self.inner {
            CensusCutReason::UnknownIsomorphism { representative, .. } => Some(representative),
            _ => None,
        }
    }

    /// The engine reason attached to an unknown-isomorphism cut, when present.
    #[getter]
    fn detail(&self) -> Option<String> {
        match &self.inner {
            CensusCutReason::UnknownIsomorphism { reason, .. } => Some(reason.clone()),
            _ => None,
        }
    }

    fn __repr__(&self) -> String {
        format!("CensusCutReason(kind={:?})", self.kind())
    }
}

pub(crate) fn census_status(status: &CensusPortableStatus) -> &'static str {
    match status {
        CensusPortableStatus::Complete => "complete",
        CensusPortableStatus::Cut(_) => "cut",
    }
}

fn census_cut_kind(reason: &CensusCutReason) -> &'static str {
    match reason {
        CensusCutReason::Cancelled => "cancelled",
        CensusCutReason::CandidateLimit { .. } => "candidate_limit",
        CensusCutReason::RepresentativeLimit { .. } => "representative_limit",
        CensusCutReason::AssignmentLimit { .. } => "assignment_limit",
        CensusCutReason::IsomorphismLimit { .. } => "isomorphism_limit",
        CensusCutReason::WorkLimit { .. } => "work_limit",
        CensusCutReason::UnknownIsomorphism { .. } => "unknown_isomorphism",
    }
}

pub(crate) fn census_reason(status: &CensusPortableStatus) -> Option<PyCensusCutReason> {
    match status {
        CensusPortableStatus::Complete => None,
        CensusPortableStatus::Cut(reason) => Some(PyCensusCutReason {
            inner: reason.clone(),
        }),
    }
}

pub(crate) fn census_counts(portable: &CensusPortable) -> BTreeMap<&'static str, usize> {
    BTreeMap::from([
        ("candidates", portable.candidates()),
        ("accepted_modules", portable.accepted_modules()),
        ("rejected_candidates", portable.rejected_candidates()),
        ("isomorphism_checks", portable.isomorphism_checks()),
        ("work_units", portable.work_units()),
    ])
}

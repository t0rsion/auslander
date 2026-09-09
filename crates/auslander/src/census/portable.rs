use crate::algebra::AlgebraBuildError;
use crate::certificate::{CertParseError, Certificate};
use crate::verify::verify;

/// The versioned schema shared by portable computation values.
pub const CENSUS_PORTABLE_SCHEMA: &str = "auslander-computation-v1";

/// The payload kind for a portable census result or checkpoint.
pub const CENSUS_PORTABLE_KIND: &str = "census-v1";

/// The deterministic coordinate and enumeration engine identifier.
pub const CENSUS_ENGINE_ID: &str = "raw-arrow-matrix-v1";

/// Limits applied before the portable parser allocates declared containers.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CensusParseLimits {
    /// The greatest accepted input byte count.
    pub max_input_bytes: usize,
    /// The greatest byte count of the embedded completion certificate.
    pub max_certificate_bytes: usize,
    /// The greatest number of dimension entries.
    pub max_dimensions: usize,
    /// The greatest dimension at one vertex.
    pub max_dimension: usize,
    /// The greatest number of retained representatives.
    pub max_representatives: usize,
    /// The greatest number of retained assignments.
    pub max_assignments: usize,
    /// The greatest coordinate count in one module.
    pub max_coordinate_values: usize,
    /// The greatest number of witness matrices.
    pub max_witness_matrices: usize,
    /// The greatest number of rows in one witness matrix.
    pub max_witness_rows: usize,
    /// The greatest number of columns in one witness row.
    pub max_witness_columns: usize,
    /// The greatest number of scalar witness entries.
    pub max_witness_entries: usize,
    /// The greatest number of numeric values in the whole document.
    pub max_numeric_values: usize,
    /// The greatest number of elements across all parsed arrays.
    pub max_array_elements: usize,
    /// The greatest digit count in one unsigned integer.
    pub max_integer_digits: usize,
    /// The greatest byte count of a portable string.
    pub max_string_bytes: usize,
}

impl Default for CensusParseLimits {
    fn default() -> Self {
        Self {
            max_input_bytes: 16_777_216,
            max_certificate_bytes: 4_194_304,
            max_dimensions: 4_096,
            max_dimension: 1_000_000,
            max_representatives: 100_000,
            max_assignments: 1_000_000,
            max_coordinate_values: 1_000_000,
            max_witness_matrices: 4_096,
            max_witness_rows: 1_000_000,
            max_witness_columns: 1_000_000,
            max_witness_entries: 4_000_000,
            max_numeric_values: 20_000_000,
            max_array_elements: 4_000_000,
            max_integer_digits: 39,
            max_string_bytes: 4_096,
        }
    }
}

/// Limits applied while an embedded census result is independently verified.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CensusVerifyLimits {
    /// Limits applied by the portable parser.
    pub parse: CensusParseLimits,
    /// The greatest number of algebra vertices to reconstruct.
    pub max_vertices: usize,
    /// The greatest coordinate count in the reconstructed domain.
    pub max_coordinates: usize,
    /// The greatest candidate dimension at one vertex.
    pub max_dimension: usize,
    /// The greatest number of candidates replayed.
    pub max_candidates: usize,
    /// The greatest number of retained representatives during replay.
    pub max_representatives: usize,
    /// The greatest number of retained assignments during replay.
    pub max_assignments: usize,
    /// The greatest number of isomorphism checks during replay.
    pub max_isomorphism_checks: usize,
    /// The greatest work count during replay.
    pub max_work_units: usize,
}

impl Default for CensusVerifyLimits {
    fn default() -> Self {
        let census = CensusLimits::default();
        Self {
            parse: CensusParseLimits::default(),
            max_vertices: 4_096,
            max_coordinates: 1_000_000,
            max_dimension: 1_000_000,
            max_candidates: census.max_candidates,
            max_representatives: census.max_representatives,
            max_assignments: census.max_assignments,
            max_isomorphism_checks: census.max_isomorphism_checks,
            max_work_units: census.max_work_units,
        }
    }
}

/// The durable status of a portable census value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CensusPortableStatus {
    /// Every raw candidate was classified.
    Complete,
    /// The stored prefix stopped before the raw domain ended.
    Cut(CensusCutReason),
}

/// A serialized representative and its raw coordinate provenance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CensusPortableRepresentative {
    cursor: u128,
    coordinates: Vec<u64>,
}

impl CensusPortableRepresentative {
    accessor_methods! {
        /// The raw-domain cursor that produced this representative.
        pub cursor() -> u128 = |this| this.cursor;
        /// The canonical arrow-matrix entries of this representative.
        pub coordinates() -> &[u64] = |this| &this.coordinates;
    }
}

/// A serialized duplicate assignment and its isomorphism witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CensusPortableAssignment {
    cursor: u128,
    coordinates: Vec<u64>,
    representative: usize,
    witness: Vec<Vec<Vec<u64>>>,
}

impl CensusPortableAssignment {
    accessor_methods! {
        /// The raw-domain cursor assigned to a representative.
        pub cursor() -> u128 = |this| this.cursor;
        /// The canonical arrow-matrix entries of this assignment.
        pub coordinates() -> &[u64] = |this| &this.coordinates;
        /// The representative index receiving this assignment.
        pub representative() -> usize = |this| this.representative;
        /// The vertex matrices of the candidate-to-representative witness.
        pub witness() -> &[Vec<Vec<u64>>] = |this| &this.witness;
    }
}

/// A canonical portable census result or cut checkpoint.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CensusPortable {
    certificate: Certificate,
    dimensions: Vec<usize>,
    raw_space_size: u128,
    coordinate_count: usize,
    cursor: u128,
    limits: CensusLimits,
    candidates: usize,
    accepted_modules: usize,
    rejected_candidates: usize,
    isomorphism_checks: usize,
    work_units: usize,
    representatives: Vec<CensusPortableRepresentative>,
    assignments: Vec<CensusPortableAssignment>,
    status: CensusPortableStatus,
    fingerprint: String,
}

impl CensusPortable {
    /// Builds a portable value from a complete in-memory result.
    pub fn from_result(result: &CensusResult) -> Self {
        Self::from_state(&result.state, CensusPortableStatus::Complete)
    }

    /// Builds a portable value from an in-memory cut checkpoint.
    pub fn from_cut(cut: &CensusCut) -> Self {
        Self::from_state(&cut.state, CensusPortableStatus::Cut(cut.reason.clone()))
    }

    /// Builds a portable value from a complete result or cut checkpoint.
    pub fn from_outcome(outcome: &CensusOutcome) -> Result<Self, CensusPortableError> {
        match outcome {
            CensusOutcome::Complete(result) => Ok(Self::from_result(result)),
            CensusOutcome::Cut(cut) => Ok(Self::from_cut(cut)),
            CensusOutcome::Failed(_) => Err(CensusPortableError::FailedOutcome),
        }
    }

    fn from_state(state: &CensusState, status: CensusPortableStatus) -> Self {
        let certificate = state.domain.algebra.certificate().clone();
        let mut portable = Self {
            certificate,
            dimensions: state.domain.dimensions.clone(),
            raw_space_size: state.domain.raw_space_size,
            coordinate_count: state.domain.coordinate_count(),
            cursor: state.cursor,
            limits: state.limits,
            candidates: state.candidates,
            accepted_modules: state.accepted_modules,
            rejected_candidates: state.rejected_candidates,
            isomorphism_checks: state.isomorphism_checks,
            work_units: state.work_units,
            representatives: state
                .representatives
                .iter()
                .map(|representative| CensusPortableRepresentative {
                    cursor: representative.cursor,
                    coordinates: representative.coordinates.clone(),
                })
                .collect(),
            assignments: state
                .assignments
                .iter()
                .map(|assignment| CensusPortableAssignment {
                    cursor: assignment.cursor,
                    coordinates: assignment.coordinates.clone(),
                    representative: assignment.representative,
                    witness: assignment
                        .witness
                        .source()
                        .dim_vector()
                        .iter()
                        .enumerate()
                        .map(|(vertex, _)| assignment.witness.map_at(vertex as u32).entries_u64())
                        .collect(),
                })
                .collect(),
            status,
            fingerprint: String::new(),
        };
        portable.fingerprint = fingerprint(&portable.canonical_without_fingerprint());
        portable
    }

    accessor_methods! {
        /// The embedded verified completion certificate.
        pub certificate() -> &Certificate = |this| &this.certificate;
        /// The exact dimension vector used by the raw domain.
        pub dimensions() -> &[usize] = |this| &this.dimensions;
        /// The checked raw-domain cardinality.
        pub raw_space_size() -> u128 = |this| this.raw_space_size;
        /// The number of scalar arrow-matrix coordinates per candidate.
        pub coordinate_count() -> usize = |this| this.coordinate_count;
        /// The first unvisited raw cursor.
        pub cursor() -> u128 = |this| this.cursor;
        /// The exact limits used for enumeration.
        pub limits() -> CensusLimits = |this| this.limits;
        /// The retention policy used for duplicate records.
        pub retention() -> CensusRetention = |this| this.limits.retention;
        /// The number of fully processed raw candidates.
        pub candidates() -> usize = |this| this.candidates;
        /// The number of relation-valid candidates classified into a class.
        pub accepted_modules() -> usize = |this| this.accepted_modules;
        /// The number of relation-invalid candidates.
        pub rejected_candidates() -> usize = |this| this.rejected_candidates;
        /// The number of completed isomorphism checks.
        pub isomorphism_checks() -> usize = |this| this.isomorphism_checks;
        /// The exact candidate and comparison work count.
        pub work_units() -> usize = |this| this.work_units;
        /// The retained representatives in first-seen order.
        pub representatives() -> &[CensusPortableRepresentative] = |this| &this.representatives;
        /// The retained duplicate assignments in candidate order.
        pub assignments() -> &[CensusPortableAssignment] = |this| &this.assignments;
        /// The complete or cut status.
        pub status() -> &CensusPortableStatus = |this| &this.status;
        /// The canonical FNV-1a fingerprint of the preceding fields.
        pub fingerprint() -> &str = |this| &this.fingerprint;
    }

    /// Serializes this value to byte-exact canonical JSON.
    pub fn to_canonical_json(&self) -> String {
        let mut output = self.canonical_without_fingerprint();
        output.push_str(",\"fingerprint\":\"");
        output.push_str(&self.fingerprint);
        output.push_str("\"}");
        output
    }

    fn canonical_without_fingerprint(&self) -> String {
        let mut output = String::new();
        output.push_str("{\"schema\":\"");
        output.push_str(CENSUS_PORTABLE_SCHEMA);
        output.push_str("\",\"kind\":\"");
        output.push_str(CENSUS_PORTABLE_KIND);
        output.push_str("\",\"engine\":\"");
        output.push_str(CENSUS_ENGINE_ID);
        output.push_str("\",\"retention\":\"");
        output.push_str(self.limits.retention.as_str());
        output.push_str("\",\"certificate\":\"");
        push_escaped_string(&mut output, self.certificate.to_canonical_json().as_bytes());
        output.push('"');
        output.push_str(",\"dimensions\":");
        push_usizes(&mut output, &self.dimensions);
        output.push_str(",\"raw_space_size\":");
        push_decimal_string(&mut output, self.raw_space_size);
        output.push_str(",\"coordinate_count\":");
        output.push_str(&self.coordinate_count.to_string());
        output.push_str(",\"cursor\":");
        push_decimal_string(&mut output, self.cursor);
        output.push_str(",\"limits\":");
        push_limits(&mut output, self.limits);
        output.push_str(",\"counts\":");
        push_counts(
            &mut output,
            self.candidates,
            self.accepted_modules,
            self.rejected_candidates,
            self.isomorphism_checks,
        );
        output.push_str(",\"work_units\":");
        output.push_str(&self.work_units.to_string());
        output.push_str(",\"representatives\":[");
        for (index, representative) in self.representatives.iter().enumerate() {
            if index != 0 {
                output.push(',');
            }
            output.push_str("{\"cursor\":");
            push_decimal_string(&mut output, representative.cursor);
            output.push_str(",\"coordinates\":");
            push_usizes(&mut output, &representative.coordinates);
            output.push('}');
        }
        output.push_str("],\"assignments\":[");
        for (index, assignment) in self.assignments.iter().enumerate() {
            if index != 0 {
                output.push(',');
            }
            output.push_str("{\"cursor\":");
            push_decimal_string(&mut output, assignment.cursor);
            output.push_str(",\"coordinates\":");
            push_usizes(&mut output, &assignment.coordinates);
            output.push_str(",\"representative\":");
            output.push_str(&assignment.representative.to_string());
            output.push_str(",\"witness\":");
            push_witness(&mut output, &assignment.witness);
            output.push('}');
        }
        output.push_str("],\"status\":");
        push_status(&mut output, &self.status);
        output
    }

    /// Parses one canonical portable JSON value under explicit limits.
    pub fn from_json(text: &str, limits: CensusParseLimits) -> Result<Self, CensusPortableError> {
        let raw = CensusRawPortable::parse(text, limits)?;
        let certificate_text =
            String::from_utf8(raw.certificate).map_err(|_| CensusPortableError::Syntax {
                byte: 0,
                message: "embedded certificate bytes are not UTF-8".to_string(),
            })?;
        let certificate =
            Certificate::from_json(&certificate_text).map_err(CensusPortableError::Certificate)?;
        if raw.retention == CensusRetention::RepresentativesOnly && !raw.assignments.is_empty() {
            return Err(CensusPortableError::CountMismatch {
                field: "assignments for representatives_only retention".to_string(),
            });
        }
        let mut limits = raw.limits;
        limits.retention = raw.retention;
        let portable = Self {
            certificate,
            dimensions: raw.dimensions,
            raw_space_size: raw.raw_space_size,
            coordinate_count: raw.coordinate_count,
            cursor: raw.cursor,
            limits,
            candidates: raw.counts[0],
            accepted_modules: raw.counts[1],
            rejected_candidates: raw.counts[2],
            isomorphism_checks: raw.counts[3],
            work_units: raw.work_units,
            representatives: raw
                .representatives
                .into_iter()
                .map(|representative| CensusPortableRepresentative {
                    cursor: representative.cursor,
                    coordinates: representative.coordinates,
                })
                .collect(),
            assignments: raw
                .assignments
                .into_iter()
                .map(|assignment| CensusPortableAssignment {
                    cursor: assignment.cursor,
                    coordinates: assignment.coordinates,
                    representative: assignment.representative,
                    witness: assignment.witness,
                })
                .collect(),
            status: raw.status,
            fingerprint: raw.fingerprint,
        };
        if portable.to_canonical_json() != text {
            return Err(CensusPortableError::NonCanonical);
        }
        if !portable.has_valid_fingerprint() {
            return Err(CensusPortableError::FingerprintMismatch);
        }
        Ok(portable)
    }

    /// Whether the fingerprint matches the canonical preceding fields.
    pub fn has_valid_fingerprint(&self) -> bool {
        self.fingerprint == fingerprint(&self.canonical_without_fingerprint())
    }

    /// Independently reconstructs the algebra and replays this value.
    pub fn verify(
        &self,
        limits: CensusVerifyLimits,
    ) -> Result<VerifiedCensus, CensusPortableError> {
        self.check_verify_limits(&limits)?;
        if !self.has_valid_fingerprint() {
            return Err(CensusPortableError::FingerprintMismatch);
        }
        let (census, outcome) = self.replay(&limits)?;
        Ok(VerifiedCensus {
            portable: self.clone(),
            census,
            outcome,
        })
    }

    fn replay(
        &self,
        limits: &CensusVerifyLimits,
    ) -> Result<(Census, CensusOutcome), CensusPortableError> {
        let certificate_text = self.certificate.to_canonical_json();
        let verified = verify(&certificate_text)?;
        let algebra = Algebra::from_verified(verified)?;
        let domain = portable_domain(&algebra, self, limits)?;
        let state = self.state(&domain)?;
        if !verify_state_data(&state) {
            return Err(CensusPortableError::CountMismatch {
                field: "state".to_string(),
            });
        }
        let census = Census {
            domain: domain.clone(),
        };
        let outcome = match &self.status {
            CensusPortableStatus::Complete => CensusOutcome::Complete(CensusResult { state }),
            CensusPortableStatus::Cut(reason) => CensusOutcome::Cut(CensusCut {
                state,
                reason: reason.clone(),
            }),
        };
        if !outcome.verify() {
            return Err(CensusPortableError::ReplayMismatch {
                field: "result".to_string(),
            });
        }
        Ok((census, outcome))
    }

    fn check_verify_limits(&self, limits: &CensusVerifyLimits) -> Result<(), CensusPortableError> {
        self.check_certificate_limits(limits)?;
        self.check_record_limits(limits)?;
        self.check_counter_limits(limits)
    }

    fn check_certificate_limits(
        &self,
        limits: &CensusVerifyLimits,
    ) -> Result<(), CensusPortableError> {
        let certificate_bytes = self.certificate.to_canonical_json().len();
        check_limit(
            "certificate_bytes",
            certificate_bytes,
            limits.parse.max_certificate_bytes,
        )?;
        check_limit(
            "vertices",
            self.certificate.quiver.vertices as usize,
            limits.max_vertices,
        )
    }

    fn check_record_limits(&self, limits: &CensusVerifyLimits) -> Result<(), CensusPortableError> {
        if self.limits.retention == CensusRetention::RepresentativesOnly
            && !self.assignments.is_empty()
        {
            return Err(CensusPortableError::CountMismatch {
                field: "assignments for representatives_only retention".to_string(),
            });
        }
        check_limit(
            "representative_count",
            self.representatives.len(),
            limits.max_representatives,
        )?;
        check_limit(
            "assignment_count",
            self.assignments.len(),
            limits.max_assignments,
        )?;
        check_limit(
            "coordinate_count",
            self.coordinate_count,
            limits.max_coordinates,
        )
    }

    fn check_counter_limits(&self, limits: &CensusVerifyLimits) -> Result<(), CensusPortableError> {
        self.check_actual_counter_limits(limits)?;
        self.check_declared_limits(limits)
    }

    fn check_actual_counter_limits(
        &self,
        limits: &CensusVerifyLimits,
    ) -> Result<(), CensusPortableError> {
        let cursor = usize::try_from(self.cursor)
            .map_err(|_| CensusPortableError::CounterOverflow { field: "cursor" })?;
        check_limit("cursor", cursor, limits.max_candidates)?;
        check_limit("candidates", self.candidates, limits.max_candidates)?;
        check_limit(
            "accepted_modules",
            self.accepted_modules,
            limits.max_candidates,
        )?;
        check_limit(
            "rejected_candidates",
            self.rejected_candidates,
            limits.max_candidates,
        )?;
        check_limit(
            "isomorphism_checks",
            self.isomorphism_checks,
            limits.max_isomorphism_checks,
        )?;
        check_limit("work_units", self.work_units, limits.max_work_units)
    }

    fn check_declared_limits(
        &self,
        limits: &CensusVerifyLimits,
    ) -> Result<(), CensusPortableError> {
        check_limit(
            "max_candidates",
            self.limits.max_candidates,
            limits.max_candidates,
        )?;
        check_limit(
            "max_representatives",
            self.limits.max_representatives,
            limits.max_representatives,
        )?;
        if self.limits.retention == CensusRetention::AllAssignments {
            check_limit(
                "max_assignments",
                self.limits.max_assignments,
                limits.max_assignments,
            )?;
        }
        check_limit(
            "max_isomorphism_checks",
            self.limits.max_isomorphism_checks,
            limits.max_isomorphism_checks,
        )?;
        check_limit(
            "max_work_units",
            self.limits.max_work_units,
            limits.max_work_units,
        )
    }

    fn state(&self, domain: &CensusDomain) -> Result<CensusState, CensusPortableError> {
        let representatives = self
            .representatives
            .iter()
            .map(|representative| {
                let module = build_module_from_values(domain, &representative.coordinates)
                    .map_err(CensusPortableError::Module)?;
                Ok(CensusRepresentative {
                    cursor: representative.cursor,
                    coordinates: representative.coordinates.clone(),
                    module,
                })
            })
            .collect::<Result<Vec<_>, CensusPortableError>>()?;
        let assignments = self
            .assignments
            .iter()
            .map(|assignment| {
                let module = build_module_from_values(domain, &assignment.coordinates)
                    .map_err(CensusPortableError::Module)?;
                let representative =
                    representatives
                        .get(assignment.representative)
                        .ok_or_else(|| CensusPortableError::CountMismatch {
                            field: "assignment.representative".to_string(),
                        })?;
                let witness =
                    portable_witness(domain, &module, &representative.module, &assignment.witness)?;
                Ok(CensusAssignment {
                    cursor: assignment.cursor,
                    coordinates: assignment.coordinates.clone(),
                    representative: assignment.representative,
                    witness,
                })
            })
            .collect::<Result<Vec<_>, CensusPortableError>>()?;
        Ok(CensusState {
            domain: domain.clone(),
            limits: self.limits,
            cursor: self.cursor,
            candidates: self.candidates,
            accepted_modules: self.accepted_modules,
            rejected_candidates: self.rejected_candidates,
            isomorphism_checks: self.isomorphism_checks,
            work_units: self.work_units,
            representatives,
            assignments,
        })
    }
}

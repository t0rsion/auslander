/// A portable value with a freshly reconstructed algebra and live census state.
#[derive(Clone, Debug)]
pub struct VerifiedCensus {
    portable: CensusPortable,
    census: Census,
    outcome: CensusOutcome,
}

impl VerifiedCensus {
    accessor_methods! {
        /// The canonical portable value that was verified.
        pub portable() -> &CensusPortable = |this| &this.portable;
        /// The freshly reconstructed census request.
        pub census() -> &Census = |this| &this.census;
        /// The replay-verified complete result or cut checkpoint.
        pub outcome() -> &CensusOutcome = |this| &this.outcome;
    }

    /// Resumes a verified cut on the freshly reconstructed algebra.
    pub fn resume(
        &self,
        limits: CensusLimits,
        control: Option<&ComputationControl>,
    ) -> Result<CensusOutcome, CensusResumeError> {
        let CensusOutcome::Cut(cut) = &self.outcome else {
            return Err(CensusResumeError::InvalidCheckpoint);
        };
        if cut.state.limits.retention != limits.retention {
            return Err(CensusResumeError::RetentionMismatch {
                checkpoint: cut.state.limits.retention,
                requested: limits.retention,
            });
        }
        let mut state = cut.state.clone();
        state.limits = limits;
        Ok(enumerate_state(state, control))
    }
}

/// A rejected portable census value or verification attempt.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CensusPortableError {
    /// A declared parser container or scalar limit was exceeded.
    ParseLimit {
        path: String,
        used: usize,
        limit: usize,
    },
    /// The bounded parser rejected one byte.
    Syntax { byte: usize, message: String },
    /// The top-level schema identifier is not supported.
    Schema { found: String },
    /// The payload kind is not supported.
    Kind { found: String },
    /// The coordinate and enumeration engine is not supported.
    Engine { found: String },
    /// The retention mode is not supported.
    Retention { found: String },
    /// The parsed bytes are valid but not canonical JSON.
    NonCanonical,
    /// The embedded completion certificate is malformed.
    Certificate(CertParseError),
    /// The fingerprint is not sixteen lowercase hexadecimal digits.
    FingerprintShape,
    /// The fingerprint does not match the canonical preceding fields.
    FingerprintMismatch,
    /// The embedded completion certificate failed independent verification.
    Verify(crate::verify::VerifyError),
    /// The independently verified certificate could not rebuild an algebra.
    Algebra(AlgebraBuildError),
    /// The reconstructed census domain was rejected.
    Domain(CensusError),
    /// A serialized module failed relation or coordinate checks.
    Module(ModuleError),
    /// A serialized isomorphism witness failed shape or square checks.
    Witness(HomError),
    /// The stored domain metadata differs from the certificate domain.
    DomainMismatch { field: String },
    /// The stored counters do not describe the retained data.
    CountMismatch { field: String },
    /// Replay does not reproduce the stored prefix or result.
    ReplayMismatch { field: String },
    /// A declared verification workload exceeds the caller's ceiling.
    VerificationLimit {
        field: &'static str,
        declared: usize,
        limit: usize,
    },
    /// A serialized counter does not fit the host's `usize` type.
    CounterOverflow { field: &'static str },
    /// Failed in-memory outcomes are not durable checkpoints.
    FailedOutcome,
}

display_error! { CensusPortableError {
    Self::ParseLimit { path, used, limit } => "portable field {path} needs {used} units, limit {limit}";
    Self::Syntax { byte, message } => "invalid census JSON at byte {byte}: {message}";
    Self::Schema { found } => "unsupported census schema {found:?}";
    Self::Kind { found } => "unsupported census payload kind {found:?}";
    Self::Engine { found } => "unsupported census engine {found:?}";
    Self::Retention { found } => "unsupported census retention {found:?}";
    Self::NonCanonical => "census JSON is not canonical";
    Self::Certificate(error) => "embedded completion certificate rejected: {error}";
    Self::FingerprintShape => "census fingerprint must contain 16 lowercase hexadecimal digits";
    Self::FingerprintMismatch => "census fingerprint does not match its canonical fields";
    Self::Verify(error) => "embedded completion certificate failed verification: {error}";
    Self::Algebra(error) => "verified completion could not rebuild an algebra: {error}";
    Self::Domain(error) => "census domain rejected: {error}";
    Self::Module(error) => "serialized module rejected: {error}";
    Self::Witness(error) => "serialized isomorphism witness rejected: {error}";
    Self::DomainMismatch { field } => "census domain field {field} differs from the certificate domain";
    Self::CountMismatch { field } => "census count field {field} is inconsistent";
    Self::ReplayMismatch { field } => "census replay differs at {field}";
    Self::VerificationLimit { field, declared, limit } => "census verification field {field} has {declared}, limit {limit}";
    Self::CounterOverflow { field } => "census counter field {field} does not fit usize";
    Self::FailedOutcome => "failed census outcomes are not portable checkpoints";
} }

error_source! { CensusPortableError {
    Self::Certificate(error) => Some(error),
    Self::Verify(error) => Some(error),
    Self::Algebra(error) => Some(error),
    Self::Domain(error) => Some(error),
    Self::Module(error) => Some(error),
    Self::Witness(error) => Some(error),
    _ => None,
} }

from_variants! { CensusPortableError {
    crate::verify::VerifyError => Verify,
    AlgebraBuildError => Algebra,
    CensusError => Domain,
} }

fn check_limit(
    field: &'static str,
    declared: usize,
    limit: usize,
) -> Result<(), CensusPortableError> {
    if declared > limit {
        return Err(CensusPortableError::VerificationLimit {
            field,
            declared,
            limit,
        });
    }
    Ok(())
}

fn portable_domain(
    algebra: &Arc<Algebra>,
    portable: &CensusPortable,
    limits: &CensusVerifyLimits,
) -> Result<CensusDomain, CensusPortableError> {
    let vertices = algebra.quiver().num_vertices() as usize;
    check_limit("vertices", vertices, limits.max_vertices)?;
    check_limit(
        "dimensions",
        portable.dimensions.len(),
        limits.parse.max_dimensions,
    )?;
    let dimension = portable
        .dimensions
        .iter()
        .copied()
        .max()
        .unwrap_or_default();
    check_limit("dimension", dimension, limits.max_dimension)?;
    let coordinate_count = checked_coordinate_count(algebra, &portable.dimensions)?;
    check_limit("coordinate_count", coordinate_count, limits.max_coordinates)?;
    let domain = CensusDomain::new(algebra, portable.dimensions.clone())?;
    if portable.coordinate_count != coordinate_count {
        return Err(CensusPortableError::DomainMismatch {
            field: "coordinate_count".to_string(),
        });
    }
    if portable.raw_space_size != domain.raw_space_size() {
        return Err(CensusPortableError::DomainMismatch {
            field: "raw_space_size".to_string(),
        });
    }
    if portable.cursor > portable.raw_space_size {
        return Err(CensusPortableError::DomainMismatch {
            field: "cursor".to_string(),
        });
    }
    Ok(domain)
}

fn checked_coordinate_count(
    algebra: &Algebra,
    dimensions: &[usize],
) -> Result<usize, CensusPortableError> {
    if dimensions.len() != algebra.quiver().num_vertices() as usize {
        return Err(CensusPortableError::DomainMismatch {
            field: "dimensions".to_string(),
        });
    }
    let mut total = 0usize;
    for (index, &(source, target)) in algebra.quiver().arrows().iter().enumerate() {
        let rows = dimensions[source as usize];
        let columns = dimensions[target as usize];
        let entries =
            rows.checked_mul(columns)
                .ok_or_else(|| CensusPortableError::DomainMismatch {
                    field: format!("arrow {index} coordinate count"),
                })?;
        total = total
            .checked_add(entries)
            .ok_or_else(|| CensusPortableError::DomainMismatch {
                field: "coordinate_count".to_string(),
            })?;
    }
    Ok(total)
}

fn portable_witness(
    domain: &CensusDomain,
    source: &Module,
    target: &Module,
    witness: &[Vec<Vec<u64>>],
) -> Result<Morphism, CensusPortableError> {
    let dimensions = domain.dimensions();
    if witness.len() != dimensions.len() {
        return Err(CensusPortableError::CountMismatch {
            field: "witness.vertices".to_string(),
        });
    }
    let field = domain.algebra.field();
    let mut maps = Vec::with_capacity(witness.len());
    for (vertex, rows) in witness.iter().enumerate() {
        let dimension = dimensions[vertex];
        if rows.len() != dimension || rows.iter().any(|row| row.len() != dimension) {
            return Err(CensusPortableError::CountMismatch {
                field: format!("witness.vertex {vertex}"),
            });
        }
        let mut converted = Vec::with_capacity(rows.len());
        for (row, values) in rows.iter().enumerate() {
            let mut converted_row = Vec::with_capacity(values.len());
            for (column, &value) in values.iter().enumerate() {
                if value >= field.modulus() {
                    return Err(CensusPortableError::Witness(HomError::NonCanonicalEntry {
                        vertex: vertex as u32,
                        row,
                        col: column,
                    }));
                }
                converted_row.push(field.elem(value as i64));
            }
            converted.push(converted_row);
        }
        maps.push(DenseMat::from_rows_with_cols(&converted, dimension));
    }
    Morphism::new(source, target, maps).map_err(CensusPortableError::Witness)
}

fn push_escaped_string(output: &mut String, bytes: &[u8]) {
    for &byte in bytes {
        match byte {
            b'"' => output.push_str("\\\""),
            b'\\' => output.push_str("\\\\"),
            _ => output.push(byte as char),
        }
    }
}

fn push_decimal_string(output: &mut String, value: u128) {
    output.push('"');
    output.push_str(&value.to_string());
    output.push('"');
}

fn push_limits(output: &mut String, limits: CensusLimits) {
    output.push_str("{\"max_candidates\":");
    output.push_str(&limits.max_candidates.to_string());
    output.push_str(",\"max_representatives\":");
    output.push_str(&limits.max_representatives.to_string());
    output.push_str(",\"max_assignments\":");
    output.push_str(&limits.max_assignments.to_string());
    output.push_str(",\"max_isomorphism_checks\":");
    output.push_str(&limits.max_isomorphism_checks.to_string());
    output.push_str(",\"max_work_units\":");
    output.push_str(&limits.max_work_units.to_string());
    output.push('}');
}

fn push_counts(
    output: &mut String,
    candidates: usize,
    accepted_modules: usize,
    rejected_candidates: usize,
    isomorphism_checks: usize,
) {
    output.push_str("{\"candidates\":");
    output.push_str(&candidates.to_string());
    output.push_str(",\"accepted_modules\":");
    output.push_str(&accepted_modules.to_string());
    output.push_str(",\"rejected_candidates\":");
    output.push_str(&rejected_candidates.to_string());
    output.push_str(",\"isomorphism_checks\":");
    output.push_str(&isomorphism_checks.to_string());
    output.push('}');
}

fn push_usizes<T: std::fmt::Display>(output: &mut String, values: &[T]) {
    output.push('[');
    for (index, value) in values.iter().enumerate() {
        if index != 0 {
            output.push(',');
        }
        output.push_str(&value.to_string());
    }
    output.push(']');
}

fn push_witness(output: &mut String, witness: &[Vec<Vec<u64>>]) {
    output.push('[');
    for (vertex, rows) in witness.iter().enumerate() {
        if vertex != 0 {
            output.push(',');
        }
        push_rows(output, rows);
    }
    output.push(']');
}

fn push_rows(output: &mut String, rows: &[Vec<u64>]) {
    output.push('[');
    for (index, row) in rows.iter().enumerate() {
        if index != 0 {
            output.push(',');
        }
        push_usizes(output, row);
    }
    output.push(']');
}

fn push_status(output: &mut String, status: &CensusPortableStatus) {
    match status {
        CensusPortableStatus::Complete => output.push_str("{\"kind\":\"complete\"}"),
        CensusPortableStatus::Cut(reason) => {
            output.push_str("{\"kind\":\"cut\",\"reason\":");
            push_cut_reason(output, reason);
            output.push('}');
        }
    }
}

fn push_cut_reason(output: &mut String, reason: &CensusCutReason) {
    output.push('{');
    match reason {
        CensusCutReason::Cancelled => output.push_str("\"kind\":\"cancelled\""),
        CensusCutReason::CandidateLimit { limit } => {
            output.push_str("\"kind\":\"candidate_limit\",\"limit\":");
            output.push_str(&limit.to_string());
        }
        CensusCutReason::RepresentativeLimit { limit } => {
            output.push_str("\"kind\":\"representative_limit\",\"limit\":");
            output.push_str(&limit.to_string());
        }
        CensusCutReason::AssignmentLimit { limit } => {
            output.push_str("\"kind\":\"assignment_limit\",\"limit\":");
            output.push_str(&limit.to_string());
        }
        CensusCutReason::IsomorphismLimit { limit } => {
            output.push_str("\"kind\":\"isomorphism_limit\",\"limit\":");
            output.push_str(&limit.to_string());
        }
        CensusCutReason::WorkLimit { stage, limit } => {
            output.push_str("\"kind\":\"work_limit\",\"stage\":\"");
            output.push_str(match stage {
                CensusWorkStage::Candidate => "candidate",
                CensusWorkStage::Isomorphism => "isomorphism",
            });
            output.push_str("\",\"limit\":");
            output.push_str(&limit.to_string());
        }
        CensusCutReason::UnknownIsomorphism {
            representative,
            reason,
        } => {
            output.push_str("\"kind\":\"unknown_isomorphism\",\"representative\":");
            output.push_str(&representative.to_string());
            output.push_str(",\"reason\":\"");
            push_string(output, reason);
            output.push('"');
        }
    }
    output.push('}');
}

fn push_string(output: &mut String, value: &str) {
    assert!(
        value.bytes().all(|byte| byte.is_ascii()
            && !byte.is_ascii_control()
            && byte != b'"'
            && byte != b'\\'),
        "portable census strings must be printable ASCII without quotes or backslashes"
    );
    output.push_str(value);
}

fn fingerprint(text: &str) -> String {
    let mut value = 0xcbf29ce484222325u64;
    for byte in text.bytes() {
        value ^= u64::from(byte);
        value = value.wrapping_mul(0x100000001b3);
    }
    format!("{value:016x}")
}

/// Parses and independently verifies one untrusted census value.
pub fn verify_census_portable(
    text: &str,
    limits: CensusVerifyLimits,
) -> Result<VerifiedCensus, CensusPortableError> {
    CensusPortable::from_json(text, limits.parse)?.verify(limits)
}

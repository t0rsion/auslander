struct CensusRawPortable {
    certificate: String,
    dimensions: Vec<usize>,
    raw_space_size: u128,
    coordinate_count: usize,
    cursor: u128,
    limits: CensusLimits,
    counts: [u64; 4],
    work_units: u64,
    representatives: Vec<CensusPortableRepresentative>,
    assignments: Vec<CensusPortableAssignment>,
    status: CensusPortableStatus,
    fingerprint: String,
}

type CensusParse<T> = Result<T, CensusPortableError>;

impl CensusRawPortable {
    fn parse(text: &str, limits: CensusParseLimits) -> CensusParse<Self> {
        let mut c = Cursor::new(
            text,
            CursorLimits {
                input_bytes: limits.max_input_bytes,
                integer_digits: limits.max_integer_digits,
                string_bytes: limits.max_string_bytes,
                numeric_values: limits.max_numeric_values,
                array_elements: limits.max_array_elements,
            },
        )?;
        c.token(b'{')?;
        let retention = Self::header(&mut c)?;
        let mut raw = Self::domain(&mut c, &limits, retention)?;
        raw.records(&mut c, &limits)?;
        c.token(b'}')?;
        c.end()?;
        Ok(raw)
    }

    fn records(&mut self, c: &mut Cursor, limits: &CensusParseLimits) -> CensusParse<()> {
        self.representatives = c.next("representatives", |c| {
            c.array("$.representatives", limits.max_representatives, |c, _| {
                Self::representative(c, limits)
            })
        })?;
        let mut witness_entries = 0;
        self.assignments = c.next("assignments", |c| {
            c.array("$.assignments", limits.max_assignments, |c, _| {
                Self::assignment(c, limits, &mut witness_entries)
            })
        })?;
        self.status = c.next("status", Self::status)?;
        self.fingerprint = c.next("fingerprint", |c| c.string("$.fingerprint"))?;
        if !is_fingerprint(&self.fingerprint) {
            return Err(CensusPortableError::FingerprintShape);
        }
        Ok(())
    }

    fn header(c: &mut Cursor) -> CensusParse<CensusRetention> {
        let expected = [CENSUS_PORTABLE_SCHEMA, CENSUS_PORTABLE_KIND, CENSUS_ENGINE_ID];
        c.header::<CensusPortableError>("$.", expected)?;
        c.next("retention", Self::retention)
    }

    fn retention(c: &mut Cursor) -> CensusParse<CensusRetention> {
        let retention = c.string("$.retention")?;
        match retention.as_str() {
            "all_assignments" => Ok(CensusRetention::AllAssignments),
            "representatives_only" => Ok(CensusRetention::RepresentativesOnly),
            _ => Err(CensusPortableError::Retention { found: retention }),
        }
    }

    fn domain(
        c: &mut Cursor,
        limits: &CensusParseLimits,
        retention: CensusRetention,
    ) -> CensusParse<Self> {
        let certificate = c.next("certificate", |c| {
            c.escaped_string("$.certificate", limits.max_certificate_bytes)
        })?;
        let dimensions = c.next("dimensions", |c| Self::dimensions(c, limits))?;
        let raw_space_size = c.next("raw_space_size", |c| {
            decimal_u128(c, "$.raw_space_size", limits.max_integer_digits)
        })?;
        let coordinate_count = c.next("coordinate_count", |c| c.usize("$.coordinate_count"))?;
        if coordinate_count > limits.max_coordinate_values {
            return Err(CensusPortableError::ParseLimit {
                path: "$.coordinate_count".to_string(),
                used: coordinate_count,
                limit: limits.max_coordinate_values,
            });
        }
        let cursor = c.next("cursor", |c| {
            decimal_u128(c, "$.cursor", limits.max_integer_digits)
        })?;
        Self::counters(c, retention).map(|(limits, counts, work_units)| Self {
            certificate,
            dimensions,
            raw_space_size,
            coordinate_count,
            cursor,
            limits,
            counts,
            work_units,
            representatives: Vec::new(),
            assignments: Vec::new(),
            status: CensusPortableStatus::Complete,
            fingerprint: String::new(),
        })
    }

    fn counters(
        c: &mut Cursor,
        retention: CensusRetention,
    ) -> CensusParse<(CensusLimits, [u64; 4], u64)> {
        let [
            max_candidates,
            max_representatives,
            max_assignments,
            max_isomorphism_checks,
            max_work_units,
        ] = c.next("limits", |c| {
            c.uint_object(
                "$.limits",
                [
                    "max_candidates",
                    "max_representatives",
                    "max_assignments",
                    "max_isomorphism_checks",
                    "max_work_units",
                ],
            )
        })?;
        let counts = c.next("counts", |c| {
            c.uint_object(
                "$.counts",
                [
                    "candidates",
                    "accepted_modules",
                    "rejected_candidates",
                    "isomorphism_checks",
                ],
            )
        })?;
        let work_units = c.next("work_units", |c| c.u64("$.work_units"))?;
        let limits = CensusLimits {
            retention,
            max_candidates,
            max_representatives,
            max_assignments,
            max_isomorphism_checks,
            max_work_units,
        };
        Ok((limits, counts, work_units))
    }

    fn dimensions(c: &mut Cursor, limits: &CensusParseLimits) -> CensusParse<Vec<usize>> {
        c.array("$.dimensions", limits.max_dimensions, |c, _| {
            let dimension = c.usize("$.dimensions[]")?;
            if dimension > limits.max_dimension {
                return Err(CensusPortableError::ParseLimit {
                    path: "$.dimensions[]".to_string(),
                    used: dimension,
                    limit: limits.max_dimension,
                });
            }
            Ok(dimension)
        })
    }

    fn representative(
        c: &mut Cursor,
        limits: &CensusParseLimits,
    ) -> CensusParse<CensusPortableRepresentative> {
        c.token(b'{')?;
        c.key("cursor")?;
        let cursor = decimal_u128(c, "$.representatives[].cursor", limits.max_integer_digits)?;
        let path = "$.representatives[].coordinates";
        let coordinates = c.next("coordinates", |c| coordinates(c, path, limits))?;
        c.token(b'}')?;
        Ok(CensusPortableRepresentative {
            cursor,
            coordinates,
        })
    }

    fn assignment(
        c: &mut Cursor,
        limits: &CensusParseLimits,
        witness_entries: &mut usize,
    ) -> CensusParse<CensusPortableAssignment> {
        c.token(b'{')?;
        c.key("cursor")?;
        let cursor = decimal_u128(c, "$.assignments[].cursor", limits.max_integer_digits)?;
        let path = "$.assignments[].coordinates";
        let coordinates = c.next("coordinates", |c| coordinates(c, path, limits))?;
        let path = "$.assignments[].representative";
        let representative = c.next("representative", |c| c.usize(path))?;
        let witness = c.next("witness", |c| witness(c, limits, witness_entries))?;
        c.token(b'}')?;
        Ok(CensusPortableAssignment {
            cursor,
            coordinates,
            representative,
            witness,
        })
    }

    fn status(c: &mut Cursor) -> CensusParse<CensusPortableStatus> {
        c.token(b'{')?;
        c.key("kind")?;
        let status = match c.string("$.status.kind")?.as_str() {
            "complete" => CensusPortableStatus::Complete,
            "cut" => CensusPortableStatus::Cut(c.next("reason", cut_reason)?),
            _ => return Err(c.syntax("status kind must be \"complete\" or \"cut\"").into()),
        };
        c.token(b'}')?;
        Ok(status)
    }
}

fn coordinates(c: &mut Cursor, path: &str, limits: &CensusParseLimits) -> CensusParse<Vec<u64>> {
    Ok(c.array(path, limits.max_coordinate_values, |c, _| c.u64(path))?)
}

/// Reads the nested witness matrices. Each scalar counts against
/// `max_witness_entries` before it is stored.
fn witness(
    c: &mut Cursor,
    limits: &CensusParseLimits,
    entries: &mut usize,
) -> CensusParse<Vec<Vec<Vec<u64>>>> {
    let path = "$.assignments[].witness";
    c.array(path, limits.max_witness_matrices, |c, _| {
        c.array("$.assignments[].witness[]", limits.max_witness_rows, |c, _| {
            c.array("$.assignments[].witness[][]", limits.max_witness_columns, |c, _| {
                if *entries == limits.max_witness_entries {
                    return Err(CensusPortableError::ParseLimit {
                        path: path.to_string(),
                        used: *entries + 1,
                        limit: limits.max_witness_entries,
                    });
                }
                let value = c.u64(path)?;
                *entries += 1;
                Ok(value)
            })
        })
    })
}

fn cut_reason(c: &mut Cursor) -> CensusParse<CensusCutReason> {
    c.token(b'{')?;
    c.key("kind")?;
    let kind = c.string("$.status.reason.kind")?;
    let reason = cut_reason_fields(c, &kind)?;
    c.token(b'}')?;
    Ok(reason)
}

fn cut_reason_fields(c: &mut Cursor, kind: &str) -> CensusParse<CensusCutReason> {
    let limited: fn(u64) -> CensusCutReason = match kind {
        "cancelled" => return Ok(CensusCutReason::Cancelled),
        "candidate_limit" => |limit| CensusCutReason::CandidateLimit { limit },
        "representative_limit" => |limit| CensusCutReason::RepresentativeLimit { limit },
        "assignment_limit" => |limit| CensusCutReason::AssignmentLimit { limit },
        "isomorphism_limit" => |limit| CensusCutReason::IsomorphismLimit { limit },
        "work_limit" => return work_limit(c),
        "unknown_isomorphism" => return unknown_isomorphism(c),
        _ => return Err(c.syntax("unknown census cut reason").into()),
    };
    Ok(limited(reason_limit(c)?))
}

fn reason_limit(c: &mut Cursor) -> CensusParse<u64> {
    Ok(c.next("limit", |c| c.u64("$.status.reason.limit"))?)
}

fn work_limit(c: &mut Cursor) -> CensusParse<CensusCutReason> {
    let stage = c.next("stage", work_stage)?;
    let limit = reason_limit(c)?;
    Ok(CensusCutReason::WorkLimit { stage, limit })
}

fn unknown_isomorphism(c: &mut Cursor) -> CensusParse<CensusCutReason> {
    let path = "$.status.reason.representative";
    let representative = c.next("representative", |c| c.usize(path))?;
    let reason = c.next("reason", |c| c.string("$.status.reason.reason"))?;
    Ok(CensusCutReason::UnknownIsomorphism {
        representative,
        reason,
    })
}

fn work_stage(c: &mut Cursor) -> CensusParse<CensusWorkStage> {
    match c.string("$.status.reason.stage")?.as_str() {
        "candidate" => Ok(CensusWorkStage::Candidate),
        "isomorphism" => Ok(CensusWorkStage::Isomorphism),
        _ => Err(c
            .syntax("work-limit stage must be \"candidate\" or \"isomorphism\"")
            .into()),
    }
}

/// Reads a `u128` stored as a JSON string of decimal digits.
fn decimal_u128(c: &mut Cursor, path: &str, max_digits: usize) -> CensusParse<u128> {
    let digits = c.string(path)?;
    if digits.len() > max_digits {
        return Err(CensusPortableError::ParseLimit {
            path: path.to_string(),
            used: digits.len(),
            limit: max_digits,
        });
    }
    if digits.is_empty()
        || (digits.len() > 1 && digits.starts_with('0'))
        || !digits.bytes().all(|byte| byte.is_ascii_digit())
    {
        return Err(c.syntax("decimal string must contain unsigned digits").into());
    }
    digits
        .parse()
        .map_err(|_| c.syntax("decimal string exceeds u128").into())
}

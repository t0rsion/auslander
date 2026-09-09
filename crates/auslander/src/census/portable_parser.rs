struct CensusRawPortable {
    certificate: Vec<u8>,
    retention: CensusRetention,
    dimensions: Vec<usize>,
    raw_space_size: u128,
    coordinate_count: usize,
    cursor: u128,
    limits: CensusLimits,
    counts: [usize; 4],
    work_units: usize,
    representatives: Vec<CensusRawRepresentative>,
    assignments: Vec<CensusRawAssignment>,
    status: CensusPortableStatus,
    fingerprint: String,
}

struct CensusRawRepresentative {
    cursor: u128,
    coordinates: Vec<u64>,
}

struct CensusRawAssignment {
    cursor: u128,
    coordinates: Vec<u64>,
    representative: usize,
    witness: Vec<Vec<Vec<u64>>>,
}

struct CensusRawDomain {
    certificate: Vec<u8>,
    dimensions: Vec<usize>,
    raw_space_size: u128,
    coordinate_count: usize,
    cursor: u128,
}

struct CensusParser<'a> {
    bytes: &'a [u8],
    position: usize,
    limits: CensusParseLimits,
    numeric_values: usize,
    array_elements: usize,
    witness_entries: usize,
}

impl CensusRawPortable {
    fn parse(text: &str, limits: CensusParseLimits) -> Result<Self, CensusPortableError> {
        if text.len() > limits.max_input_bytes {
            return Err(CensusPortableError::ParseLimit {
                path: "$".to_string(),
                used: text.len(),
                limit: limits.max_input_bytes,
            });
        }
        let mut parser = CensusParser {
            bytes: text.as_bytes(),
            position: 0,
            limits,
            numeric_values: 0,
            array_elements: 0,
            witness_entries: 0,
        };
        parser.document()
    }
}

impl CensusParser<'_> {
    fn document(&mut self) -> Result<CensusRawPortable, CensusPortableError> {
        self.token(b'{')?;
        let retention = self.schema()?;
        let domain = self.domain_fields()?;
        let (limits, counts, work_units) = self.counter_fields()?;
        let (representatives, assignments, status, fingerprint) = self.record_fields()?;
        self.token(b'}')?;
        self.whitespace();
        if self.position != self.bytes.len() {
            return Err(self.syntax("trailing content"));
        }
        Ok(CensusRawPortable {
            certificate: domain.certificate,
            retention,
            dimensions: domain.dimensions,
            raw_space_size: domain.raw_space_size,
            coordinate_count: domain.coordinate_count,
            cursor: domain.cursor,
            limits,
            counts,
            work_units,
            representatives,
            assignments,
            status,
            fingerprint,
        })
    }

    fn schema(&mut self) -> Result<CensusRetention, CensusPortableError> {
        self.key("schema")?;
        let schema = self.string("$.schema")?;
        if schema != CENSUS_PORTABLE_SCHEMA {
            return Err(CensusPortableError::Schema { found: schema });
        }
        self.next("kind", |parser| parser.payload_kind())?;
        self.next("engine", |parser| parser.engine())?;
        self.next("retention", |parser| parser.retention())
    }

    fn payload_kind(&mut self) -> Result<(), CensusPortableError> {
        let kind = self.string("$.kind")?;
        if kind != CENSUS_PORTABLE_KIND {
            return Err(CensusPortableError::Kind { found: kind });
        }
        Ok(())
    }

    fn engine(&mut self) -> Result<(), CensusPortableError> {
        let engine = self.string("$.engine")?;
        if engine != CENSUS_ENGINE_ID {
            return Err(CensusPortableError::Engine { found: engine });
        }
        Ok(())
    }

    fn retention(&mut self) -> Result<CensusRetention, CensusPortableError> {
        let retention = self.string("$.retention")?;
        match retention.as_str() {
            "all_assignments" => Ok(CensusRetention::AllAssignments),
            "representatives_only" => Ok(CensusRetention::RepresentativesOnly),
            _ => Err(CensusPortableError::Retention { found: retention }),
        }
    }

    fn domain_fields(&mut self) -> Result<CensusRawDomain, CensusPortableError> {
        let certificate = self.next("certificate", |parser| {
            parser.escaped_certificate("$.certificate")
        })?;
        let dimensions = self.next("dimensions", |parser| parser.dimensions())?;
        let raw_space_size = self.next("raw_space_size", |parser| {
            parser.decimal_u128("$.raw_space_size")
        })?;
        let coordinate_count = self.next("coordinate_count", |parser| parser.number_usize())?;
        if coordinate_count > self.limits.max_coordinate_values {
            return Err(CensusPortableError::ParseLimit {
                path: "$.coordinate_count".to_string(),
                used: coordinate_count,
                limit: self.limits.max_coordinate_values,
            });
        }
        let cursor = self.next("cursor", |parser| parser.decimal_u128("$.cursor"))?;
        Ok(CensusRawDomain {
            certificate,
            dimensions,
            raw_space_size,
            coordinate_count,
            cursor,
        })
    }

    fn counter_fields(&mut self) -> Result<(CensusLimits, [usize; 4], usize), CensusPortableError> {
        let limits = self.next("limits", |parser| parser.limits())?;
        let counts = self.next("counts", |parser| parser.counts())?;
        let work_units = self.next("work_units", |parser| parser.number_usize())?;
        Ok((limits, counts, work_units))
    }

    fn limits(&mut self) -> Result<CensusLimits, CensusPortableError> {
        self.token(b'{')?;
        self.key("max_candidates")?;
        let max_candidates = self.number_usize()?;
        let max_representatives =
            self.next("max_representatives", |parser| parser.number_usize())?;
        let max_assignments = self.next("max_assignments", |parser| parser.number_usize())?;
        let max_isomorphism_checks =
            self.next("max_isomorphism_checks", |parser| parser.number_usize())?;
        let max_work_units = self.next("max_work_units", |parser| parser.number_usize())?;
        self.token(b'}')?;
        Ok(CensusLimits {
            retention: CensusRetention::AllAssignments,
            max_candidates,
            max_representatives,
            max_assignments,
            max_isomorphism_checks,
            max_work_units,
        })
    }

    fn counts(&mut self) -> Result<[usize; 4], CensusPortableError> {
        self.token(b'{')?;
        self.key("candidates")?;
        let candidates = self.number_usize()?;
        let accepted_modules = self.next("accepted_modules", |parser| parser.number_usize())?;
        let rejected_candidates =
            self.next("rejected_candidates", |parser| parser.number_usize())?;
        let isomorphism_checks = self.next("isomorphism_checks", |parser| parser.number_usize())?;
        self.token(b'}')?;
        Ok([
            candidates,
            accepted_modules,
            rejected_candidates,
            isomorphism_checks,
        ])
    }

    fn record_fields(
        &mut self,
    ) -> Result<
        (
            Vec<CensusRawRepresentative>,
            Vec<CensusRawAssignment>,
            CensusPortableStatus,
            String,
        ),
        CensusPortableError,
    > {
        let representatives = self.next("representatives", |parser| parser.representatives())?;
        let assignments = self.next("assignments", |parser| parser.assignments())?;
        let status = self.next("status", |parser| parser.status())?;
        let fingerprint = self.next("fingerprint", |parser| parser.fingerprint())?;
        Ok((representatives, assignments, status, fingerprint))
    }

    fn dimensions(&mut self) -> Result<Vec<usize>, CensusPortableError> {
        let max_dimension = self.limits.max_dimension;
        self.array("$.dimensions", self.limits.max_dimensions, |parser, _| {
            let dimension = parser.number_usize()?;
            if dimension > max_dimension {
                return Err(CensusPortableError::ParseLimit {
                    path: "$.dimensions[]".to_string(),
                    used: dimension,
                    limit: max_dimension,
                });
            }
            Ok(dimension)
        })
    }

    fn representatives(&mut self) -> Result<Vec<CensusRawRepresentative>, CensusPortableError> {
        let max_representatives = self.limits.max_representatives;
        self.array("$.representatives", max_representatives, |parser, _| {
            parser.representative()
        })
    }

    fn representative(&mut self) -> Result<CensusRawRepresentative, CensusPortableError> {
        self.token(b'{')?;
        self.key("cursor")?;
        let cursor = self.decimal_u128("$.representatives[].cursor")?;
        self.next("coordinates", |parser| {
            let coordinates = parser.coordinates("$.representatives[].coordinates")?;
            parser.token(b'}')?;
            Ok(CensusRawRepresentative {
                cursor,
                coordinates,
            })
        })
    }

    fn assignments(&mut self) -> Result<Vec<CensusRawAssignment>, CensusPortableError> {
        let max_assignments = self.limits.max_assignments;
        self.array("$.assignments", max_assignments, |parser, _| {
            parser.assignment()
        })
    }

    fn assignment(&mut self) -> Result<CensusRawAssignment, CensusPortableError> {
        self.token(b'{')?;
        self.key("cursor")?;
        let cursor = self.decimal_u128("$.assignments[].cursor")?;
        let coordinates = self.next("coordinates", |parser| {
            parser.coordinates("$.assignments[].coordinates")
        })?;
        let representative = self.next("representative", |parser| parser.number_usize())?;
        let witness = self.next("witness", |parser| parser.witness())?;
        self.token(b'}')?;
        Ok(CensusRawAssignment {
            cursor,
            coordinates,
            representative,
            witness,
        })
    }

    fn coordinates(&mut self, path: &str) -> Result<Vec<u64>, CensusPortableError> {
        self.array(path, self.limits.max_coordinate_values, |parser, _| {
            parser.number_u64()
        })
    }

    fn witness(&mut self) -> Result<Vec<Vec<Vec<u64>>>, CensusPortableError> {
        let path = "$.assignments[].witness";
        let max_rows = self.limits.max_witness_rows;
        let max_columns = self.limits.max_witness_columns;
        self.array(path, self.limits.max_witness_matrices, |parser, _| {
            parser.array("$.assignments[].witness[]", max_rows, |parser, _| {
                parser.array("$.assignments[].witness[][]", max_columns, |parser, _| {
                    parser.witness_value()
                })
            })
        })
    }

    fn witness_value(&mut self) -> Result<u64, CensusPortableError> {
        if self.witness_entries == self.limits.max_witness_entries {
            return Err(CensusPortableError::ParseLimit {
                path: "$.assignments[].witness".to_string(),
                used: self.witness_entries + 1,
                limit: self.limits.max_witness_entries,
            });
        }
        let value = self.number_u64()?;
        self.witness_entries += 1;
        Ok(value)
    }

    fn status(&mut self) -> Result<CensusPortableStatus, CensusPortableError> {
        self.token(b'{')?;
        self.key("kind")?;
        let kind = self.string("$.status.kind")?;
        match kind.as_str() {
            "complete" => {
                self.token(b'}')?;
                Ok(CensusPortableStatus::Complete)
            }
            "cut" => {
                let reason = self.next("reason", |parser| parser.cut_reason())?;
                self.token(b'}')?;
                Ok(CensusPortableStatus::Cut(reason))
            }
            _ => Err(self.syntax("status kind must be \"complete\" or \"cut\"")),
        }
    }

    fn cut_reason(&mut self) -> Result<CensusCutReason, CensusPortableError> {
        self.token(b'{')?;
        self.key("kind")?;
        let kind = self.string("$.status.reason.kind")?;
        let reason = self.read_cut_reason(&kind)?;
        self.token(b'}')?;
        Ok(reason)
    }

    fn read_cut_reason(&mut self, kind: &str) -> Result<CensusCutReason, CensusPortableError> {
        match kind {
            "cancelled" => Ok(CensusCutReason::Cancelled),
            "candidate_limit" => self
                .cut_limit()
                .map(|limit| CensusCutReason::CandidateLimit { limit }),
            "representative_limit" => self
                .cut_limit()
                .map(|limit| CensusCutReason::RepresentativeLimit { limit }),
            "assignment_limit" => self
                .cut_limit()
                .map(|limit| CensusCutReason::AssignmentLimit { limit }),
            "isomorphism_limit" => self
                .cut_limit()
                .map(|limit| CensusCutReason::IsomorphismLimit { limit }),
            "work_limit" => self.work_limit(),
            "unknown_isomorphism" => self.unknown_isomorphism(),
            _ => Err(self.syntax("unknown census cut reason")),
        }
    }

    fn cut_limit(&mut self) -> Result<usize, CensusPortableError> {
        self.next("limit", |parser| parser.number_usize())
    }

    fn work_limit(&mut self) -> Result<CensusCutReason, CensusPortableError> {
        let stage = self.next("stage", |parser| parser.work_stage())?;
        let limit = self.next("limit", |parser| parser.number_usize())?;
        Ok(CensusCutReason::WorkLimit { stage, limit })
    }

    fn unknown_isomorphism(&mut self) -> Result<CensusCutReason, CensusPortableError> {
        let representative = self.next("representative", |parser| parser.number_usize())?;
        let reason = self.next("reason", |parser| parser.string("reason"))?;
        Ok(CensusCutReason::UnknownIsomorphism {
            representative,
            reason,
        })
    }

    fn work_stage(&mut self) -> Result<CensusWorkStage, CensusPortableError> {
        match self.string("$.status.reason.stage")?.as_str() {
            "candidate" => Ok(CensusWorkStage::Candidate),
            "isomorphism" => Ok(CensusWorkStage::Isomorphism),
            _ => Err(self.syntax("work-limit stage must be \"candidate\" or \"isomorphism\"")),
        }
    }

    fn fingerprint(&mut self) -> Result<String, CensusPortableError> {
        let fingerprint = self.string("$.fingerprint")?;
        if fingerprint.len() != 16
            || !fingerprint
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        {
            return Err(CensusPortableError::FingerprintShape);
        }
        Ok(fingerprint)
    }

    fn next<T>(
        &mut self,
        key: &str,
        read: impl FnOnce(&mut Self) -> Result<T, CensusPortableError>,
    ) -> Result<T, CensusPortableError> {
        self.comma()?;
        self.key(key)?;
        read(self)
    }

    fn syntax(&self, message: &str) -> CensusPortableError {
        CensusPortableError::Syntax {
            byte: self.position,
            message: message.to_string(),
        }
    }

    fn whitespace(&mut self) {
        while self
            .bytes
            .get(self.position)
            .is_some_and(u8::is_ascii_whitespace)
        {
            self.position += 1;
        }
    }

    fn token(&mut self, expected: u8) -> Result<(), CensusPortableError> {
        self.whitespace();
        if self.bytes.get(self.position) != Some(&expected) {
            return Err(self.syntax(&format!("expected byte {}", expected as char)));
        }
        self.position += 1;
        Ok(())
    }

    fn comma(&mut self) -> Result<(), CensusPortableError> {
        self.token(b',')
    }

    fn key(&mut self, expected: &str) -> Result<(), CensusPortableError> {
        let key = self.string("object key")?;
        if key != expected {
            return Err(self.syntax(&format!("expected key {expected:?}")));
        }
        self.token(b':')
    }

    fn string(&mut self, path: &str) -> Result<String, CensusPortableError> {
        self.token(b'"')?;
        let start = self.position;
        let end = self.scan_string_end()?;
        let length = end - start;
        if length > self.limits.max_string_bytes {
            return Err(CensusPortableError::ParseLimit {
                path: path.to_string(),
                used: length,
                limit: self.limits.max_string_bytes,
            });
        }
        let value = std::str::from_utf8(&self.bytes[start..end])
            .map_err(|_| self.syntax("string is not UTF-8"))?
            .to_string();
        self.position += 1;
        Ok(value)
    }

    fn scan_string_end(&mut self) -> Result<usize, CensusPortableError> {
        while let Some(&byte) = self.bytes.get(self.position) {
            if byte == b'"' {
                return Ok(self.position);
            }
            if matches!(byte, b'\\' | 0..=0x1f | 0x80..=u8::MAX) {
                return Err(self.syntax("string contains a forbidden byte"));
            }
            self.position += 1;
        }
        Err(self.syntax("unterminated string"))
    }

    fn number_u128(&mut self) -> Result<u128, CensusPortableError> {
        self.whitespace();
        let start = self.position;
        while self
            .bytes
            .get(self.position)
            .is_some_and(u8::is_ascii_digit)
        {
            self.position += 1;
        }
        let digits = self.position - start;
        if digits == 0 {
            return Err(self.syntax("expected unsigned integer"));
        }
        if digits > self.limits.max_integer_digits {
            return Err(CensusPortableError::ParseLimit {
                path: "integer".to_string(),
                used: digits,
                limit: self.limits.max_integer_digits,
            });
        }
        if digits > 1 && self.bytes[start] == b'0' {
            return Err(self.syntax("integer has a leading zero"));
        }
        if matches!(self.bytes.get(self.position), Some(b'.' | b'e' | b'E')) {
            return Err(self.syntax("number must be an unsigned integer"));
        }
        if self.numeric_values == self.limits.max_numeric_values {
            return Err(CensusPortableError::ParseLimit {
                path: "numeric values".to_string(),
                used: self.numeric_values + 1,
                limit: self.limits.max_numeric_values,
            });
        }
        let value = std::str::from_utf8(&self.bytes[start..self.position])
            .expect("digits are ASCII")
            .parse()
            .map_err(|_| self.syntax("integer exceeds u128"))?;
        self.numeric_values += 1;
        Ok(value)
    }

    fn decimal_u128(&mut self, path: &str) -> Result<u128, CensusPortableError> {
        let digits = self.string(path)?;
        if digits.len() > self.limits.max_integer_digits {
            return Err(CensusPortableError::ParseLimit {
                path: path.to_string(),
                used: digits.len(),
                limit: self.limits.max_integer_digits,
            });
        }
        if digits.is_empty()
            || (digits.len() > 1 && digits.starts_with("0"))
            || !digits.bytes().all(|byte| byte.is_ascii_digit())
        {
            return Err(self.syntax("decimal string must contain unsigned digits"));
        }
        digits
            .parse()
            .map_err(|_| self.syntax("decimal string exceeds u128"))
    }

    fn number_u64(&mut self) -> Result<u64, CensusPortableError> {
        u64::try_from(self.number_u128()?).map_err(|_| self.syntax("integer exceeds u64"))
    }

    fn number_usize(&mut self) -> Result<usize, CensusPortableError> {
        usize::try_from(self.number_u128()?).map_err(|_| self.syntax("integer exceeds usize"))
    }

    fn escaped_certificate(&mut self, path: &str) -> Result<Vec<u8>, CensusPortableError> {
        self.token(b'"')?;
        let mut output = Vec::new();
        loop {
            let byte = *self
                .bytes
                .get(self.position)
                .ok_or_else(|| self.syntax("unterminated certificate string"))?;
            if byte == b'"' {
                self.position += 1;
                return Ok(output);
            }
            self.read_certificate_byte(byte, path, &mut output)?;
        }
    }

    fn read_certificate_byte(
        &mut self,
        byte: u8,
        path: &str,
        output: &mut Vec<u8>,
    ) -> Result<(), CensusPortableError> {
        match byte {
            b'\\' => {
                self.position += 1;
                let escaped = *self
                    .bytes
                    .get(self.position)
                    .ok_or_else(|| self.syntax("unterminated certificate escape"))?;
                if !matches!(escaped, b'"' | b'\\') {
                    return Err(self.syntax("certificate escape must be quote or backslash"));
                }
                self.position += 1;
                self.push_certificate_byte(output, escaped, path)
            }
            0..=0x1f | 0x80..=u8::MAX => {
                Err(self.syntax("certificate string contains a forbidden byte"))
            }
            _ => {
                self.position += 1;
                self.push_certificate_byte(output, byte, path)
            }
        }
    }

    fn push_certificate_byte(
        &self,
        output: &mut Vec<u8>,
        byte: u8,
        path: &str,
    ) -> Result<(), CensusPortableError> {
        if output.len() == self.limits.max_certificate_bytes {
            return Err(CensusPortableError::ParseLimit {
                path: path.to_string(),
                used: output.len() + 1,
                limit: self.limits.max_certificate_bytes,
            });
        }
        output.push(byte);
        Ok(())
    }

    fn array<T>(
        &mut self,
        path: &str,
        limit: usize,
        mut next: impl FnMut(&mut Self, usize) -> Result<T, CensusPortableError>,
    ) -> Result<Vec<T>, CensusPortableError> {
        self.token(b'[')?;
        self.whitespace();
        if self.bytes.get(self.position) == Some(&b']') {
            self.position += 1;
            return Ok(Vec::new());
        }
        let mut output = Vec::new();
        loop {
            if output.len() == limit {
                return Err(CensusPortableError::ParseLimit {
                    path: path.to_string(),
                    used: output.len() + 1,
                    limit,
                });
            }
            if self.array_elements == self.limits.max_array_elements {
                return Err(CensusPortableError::ParseLimit {
                    path: "array elements".to_string(),
                    used: self.array_elements + 1,
                    limit: self.limits.max_array_elements,
                });
            }
            self.array_elements += 1;
            output.push(next(self, output.len())?);
            if self.array_end()? {
                return Ok(output);
            }
        }
    }

    fn array_end(&mut self) -> Result<bool, CensusPortableError> {
        self.whitespace();
        match self.bytes.get(self.position) {
            Some(b',') => {
                self.position += 1;
                Ok(false)
            }
            Some(b']') => {
                self.position += 1;
                Ok(true)
            }
            _ => Err(self.syntax("expected comma or array end")),
        }
    }
}

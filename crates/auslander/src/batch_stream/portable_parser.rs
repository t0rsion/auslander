use super::portable_types::{
    HomologicalStreamBudget, HomologicalStreamConfig, HomologicalStreamCutReason,
    HomologicalStreamParseLimits, HomologicalStreamPortableError, HomologicalStreamPortableStatus,
};
use super::{HomologicalBatchStreamLimits, HomologicalBatchStreamRow, HomologicalBatchStreamWork};
use crate::resolution::ResolutionEnd;

pub(super) struct RawHomologicalStream {
    pub census: Vec<u8>,
    pub census_fingerprint: String,
    pub max_degree: usize,
    pub config: HomologicalStreamConfig,
    pub next_source: usize,
    pub rows: Vec<HomologicalBatchStreamRow>,
    pub work: HomologicalBatchStreamWork,
    pub chunk_sizes: Vec<usize>,
    pub status: HomologicalStreamPortableStatus,
    pub fingerprint: String,
}

struct RawPrefix {
    config: HomologicalStreamConfig,
    next_source: usize,
    rows: Vec<HomologicalBatchStreamRow>,
    work: HomologicalBatchStreamWork,
    chunk_sizes: Vec<usize>,
}

pub(super) fn parse(
    text: &str,
    limits: HomologicalStreamParseLimits,
) -> Result<RawHomologicalStream, HomologicalStreamPortableError> {
    if text.len() > limits.max_input_bytes {
        return Err(HomologicalStreamPortableError::ParseLimit {
            path: "$".to_string(),
            used: text.len(),
            limit: limits.max_input_bytes,
        });
    }
    let mut parser = Parser {
        bytes: text.as_bytes(),
        position: 0,
        limits,
        numeric_values: 0,
        array_elements: 0,
    };
    parser.document()
}

struct Parser<'a> {
    bytes: &'a [u8],
    position: usize,
    limits: HomologicalStreamParseLimits,
    numeric_values: usize,
    array_elements: usize,
}

impl Parser<'_> {
    fn document(&mut self) -> Result<RawHomologicalStream, HomologicalStreamPortableError> {
        self.token(b'{')?;
        self.preamble()?;
        let (census, census_fingerprint, max_degree) = self.domain_fields()?;
        let prefix = self.prefix_fields()?;
        let (status, fingerprint) = self.suffix_fields()?;
        self.token(b'}')?;
        self.whitespace();
        if self.position != self.bytes.len() {
            return Err(self.syntax("trailing content"));
        }
        Ok(RawHomologicalStream {
            census,
            census_fingerprint,
            max_degree,
            config: prefix.config,
            next_source: prefix.next_source,
            rows: prefix.rows,
            work: prefix.work,
            chunk_sizes: prefix.chunk_sizes,
            status,
            fingerprint,
        })
    }

    fn preamble(&mut self) -> Result<(), HomologicalStreamPortableError> {
        self.key("schema")?;
        self.expect_string("$.schema", "auslander-computation-v1")?;
        self.next("kind", |parser| {
            parser.expect_string("$.kind", super::HOMOLOGICAL_STREAM_PORTABLE_KIND)
        })?;
        self.next("engine", |parser| {
            parser.expect_string("$.engine", super::HOMOLOGICAL_STREAM_ENGINE_ID)
        })
    }

    fn domain_fields(
        &mut self,
    ) -> Result<(Vec<u8>, String, usize), HomologicalStreamPortableError> {
        let census = self.next("census", |parser| parser.census_string("$.census"))?;
        let census_fingerprint = self.next("census_fingerprint", |parser| {
            parser.string("$.census_fingerprint")
        })?;
        let max_degree = self.next("max_degree", |parser| parser.number("$.max_degree"))?;
        Ok((census, census_fingerprint, max_degree))
    }

    fn prefix_fields(&mut self) -> Result<RawPrefix, HomologicalStreamPortableError> {
        let config = self.next("config", |parser| parser.config())?;
        let next_source = self.next("next_source", |parser| parser.number("$.next_source"))?;
        let rows = self.next("rows", |parser| parser.rows())?;
        let work = self.next("work", |parser| parser.work())?;
        let chunk_sizes = self.next("chunk_sizes", |parser| {
            parser.usize_array("$.chunk_sizes", rows.len())
        })?;
        Ok(RawPrefix {
            config,
            next_source,
            rows,
            work,
            chunk_sizes,
        })
    }

    fn suffix_fields(
        &mut self,
    ) -> Result<(HomologicalStreamPortableStatus, String), HomologicalStreamPortableError> {
        let status = self.next("status", |parser| parser.status())?;
        let fingerprint = self.next("fingerprint", |parser| parser.string("$.fingerprint"))?;
        Ok((status, fingerprint))
    }

    fn config(&mut self) -> Result<HomologicalStreamConfig, HomologicalStreamPortableError> {
        self.token(b'{')?;
        self.key("chunk_limits")?;
        let chunk_limits = self.chunk_limits()?;
        let budget = self.next("budget", |parser| parser.budget())?;
        self.token(b'}')?;
        Ok(HomologicalStreamConfig {
            chunk_limits,
            budget,
        })
    }

    fn chunk_limits(
        &mut self,
    ) -> Result<HomologicalBatchStreamLimits, HomologicalStreamPortableError> {
        self.token(b'{')?;
        let max_live_sources =
            self.number_after_key("max_live_sources", "$.config.chunk_limits.max_live_sources")?;
        let max_pairs = self.next("max_pairs", |parser| {
            parser.number("$.config.chunk_limits.max_pairs")
        })?;
        let max_ext_cells = self.next("max_ext_cells", |parser| {
            parser.number("$.config.chunk_limits.max_ext_cells")
        })?;
        self.token(b'}')?;
        Ok(HomologicalBatchStreamLimits {
            max_live_sources,
            max_pairs,
            max_ext_cells,
        })
    }

    fn budget(&mut self) -> Result<HomologicalStreamBudget, HomologicalStreamPortableError> {
        self.token(b'{')?;
        let max_sources = self.number_after_key("max_sources", "$.config.budget.max_sources")?;
        let max_work_units = self.next("max_work_units", |parser| {
            parser.number("$.config.budget.max_work_units")
        })?;
        self.token(b'}')?;
        Ok(HomologicalStreamBudget {
            max_sources,
            max_work_units,
        })
    }

    fn rows(&mut self) -> Result<Vec<HomologicalBatchStreamRow>, HomologicalStreamPortableError> {
        self.token(b'[')?;
        let mut rows = Vec::new();
        self.whitespace();
        if self.peek() == Some(b']') {
            self.position += 1;
            return Ok(rows);
        }
        loop {
            self.array_element("$.rows", rows.len(), self.limits.max_rows)?;
            rows.push(self.row(rows.len())?);
            self.whitespace();
            match self.peek() {
                Some(b',') => {
                    self.position += 1;
                }
                Some(b']') => {
                    self.position += 1;
                    return Ok(rows);
                }
                _ => return Err(self.syntax("expected comma or row-array end")),
            }
        }
    }

    fn row(
        &mut self,
        index: usize,
    ) -> Result<HomologicalBatchStreamRow, HomologicalStreamPortableError> {
        self.token(b'{')?;
        let source = self.number_after_key("source", &format!("$.rows[{index}].source"))?;
        let target = self.next("target", |parser| {
            parser.number(&format!("$.rows[{index}].target"))
        })?;
        let hom_dim = self.next("hom_dim", |parser| {
            parser.number(&format!("$.rows[{index}].hom_dim"))
        })?;
        let stable_hom_dim = self.next("stable_hom_dim", |parser| {
            parser.number(&format!("$.rows[{index}].stable_hom_dim"))
        })?;
        let ext_dimensions = self.next("ext_dimensions", |parser| {
            parser.usize_array(
                &format!("$.rows[{index}].ext_dimensions"),
                parser.limits.max_ext_dimensions,
            )
        })?;
        let resolution_end = self.next("resolution_end", |parser| parser.resolution_end(index))?;
        self.token(b'}')?;
        Ok(HomologicalBatchStreamRow::from_parts(
            source,
            target,
            hom_dim,
            stable_hom_dim,
            ext_dimensions,
            resolution_end,
        ))
    }

    fn resolution_end(
        &mut self,
        index: usize,
    ) -> Result<ResolutionEnd, HomologicalStreamPortableError> {
        self.token(b'{')?;
        self.key("kind")?;
        let kind = self.string(&format!("$.rows[{index}].resolution_end.kind"))?;
        let result = match kind.as_str() {
            "finite" => {
                self.token(b'}')?;
                ResolutionEnd::Finite
            }
            "cut" => {
                let at = self.next("at", |parser| {
                    parser.number(&format!("$.rows[{index}].resolution_end.at"))
                })?;
                self.token(b'}')?;
                ResolutionEnd::Cut { at }
            }
            _ => return Err(self.syntax("resolution end kind must be finite or cut")),
        };
        Ok(result)
    }

    fn work(&mut self) -> Result<HomologicalBatchStreamWork, HomologicalStreamPortableError> {
        self.token(b'{')?;
        let (chunks, sources, resolutions, target_covers) = self.work_counts()?;
        let (hom_spaces, projective_factor_spaces, ext_tables, peak_live_sources) =
            self.work_spaces()?;
        self.token(b'}')?;
        Ok(HomologicalBatchStreamWork {
            chunks,
            sources,
            resolutions,
            target_covers,
            hom_spaces,
            projective_factor_spaces,
            ext_tables,
            peak_live_sources,
        })
    }

    fn work_counts(
        &mut self,
    ) -> Result<(usize, usize, usize, usize), HomologicalStreamPortableError> {
        let chunks = self.number_after_key("chunks", "$.work.chunks")?;
        let sources = self.next("sources", |parser| parser.number("$.work.sources"))?;
        let resolutions = self.next("resolutions", |parser| parser.number("$.work.resolutions"))?;
        let target_covers = self.next("target_covers", |parser| {
            parser.number("$.work.target_covers")
        })?;
        Ok((chunks, sources, resolutions, target_covers))
    }

    fn work_spaces(
        &mut self,
    ) -> Result<(usize, usize, usize, usize), HomologicalStreamPortableError> {
        let hom_spaces = self.next("hom_spaces", |parser| parser.number("$.work.hom_spaces"))?;
        let projective_factor_spaces = self.next("projective_factor_spaces", |parser| {
            parser.number("$.work.projective_factor_spaces")
        })?;
        let ext_tables = self.next("ext_tables", |parser| parser.number("$.work.ext_tables"))?;
        let peak_live_sources = self.next("peak_live_sources", |parser| {
            parser.number("$.work.peak_live_sources")
        })?;
        Ok((
            hom_spaces,
            projective_factor_spaces,
            ext_tables,
            peak_live_sources,
        ))
    }

    fn status(
        &mut self,
    ) -> Result<HomologicalStreamPortableStatus, HomologicalStreamPortableError> {
        self.token(b'{')?;
        self.key("kind")?;
        let kind = self.string("$.status.kind")?;
        self.status_kind(&kind)
    }

    fn status_kind(
        &mut self,
        kind: &str,
    ) -> Result<HomologicalStreamPortableStatus, HomologicalStreamPortableError> {
        match kind {
            "active" => {
                self.token(b'}')?;
                Ok(HomologicalStreamPortableStatus::Active)
            }
            "complete" => {
                self.token(b'}')?;
                Ok(HomologicalStreamPortableStatus::Complete)
            }
            "cut" => {
                let reason = self.next("reason", |parser| parser.cut_reason())?;
                self.token(b'}')?;
                Ok(HomologicalStreamPortableStatus::Cut(reason))
            }
            _ => Err(self.syntax("status kind must be active, complete, or cut")),
        }
    }

    fn cut_reason(&mut self) -> Result<HomologicalStreamCutReason, HomologicalStreamPortableError> {
        self.token(b'{')?;
        self.key("kind")?;
        let kind = self.string("$.status.reason.kind")?;
        self.cut_reason_kind(&kind)
    }

    fn cut_reason_kind(
        &mut self,
        kind: &str,
    ) -> Result<HomologicalStreamCutReason, HomologicalStreamPortableError> {
        match kind {
            "cancelled" => {
                self.token(b'}')?;
                Ok(HomologicalStreamCutReason::Cancelled)
            }
            "source_limit" => Ok(HomologicalStreamCutReason::SourceLimit {
                limit: self.limit_reason()?,
            }),
            "work_limit" => Ok(HomologicalStreamCutReason::WorkLimit {
                limit: self.limit_reason()?,
            }),
            _ => Err(self.syntax("unknown homological stream cut reason")),
        }
    }

    fn limit_reason(&mut self) -> Result<usize, HomologicalStreamPortableError> {
        let limit = self.next("limit", |parser| parser.number("$.status.reason.limit"))?;
        self.token(b'}')?;
        Ok(limit)
    }

    fn usize_array(
        &mut self,
        path: &str,
        limit: usize,
    ) -> Result<Vec<usize>, HomologicalStreamPortableError> {
        self.token(b'[')?;
        let mut values = Vec::new();
        self.whitespace();
        if self.peek() == Some(b']') {
            self.position += 1;
            return Ok(values);
        }
        loop {
            self.array_element(path, values.len(), limit)?;
            values.push(self.number(path)?);
            self.whitespace();
            match self.peek() {
                Some(b',') => self.position += 1,
                Some(b']') => {
                    self.position += 1;
                    return Ok(values);
                }
                _ => return Err(self.syntax("expected comma or array end")),
            }
        }
    }

    fn census_string(&mut self, path: &str) -> Result<Vec<u8>, HomologicalStreamPortableError> {
        self.json_string(path, self.limits.max_census_bytes)
    }

    fn string(&mut self, path: &str) -> Result<String, HomologicalStreamPortableError> {
        let bytes = self.json_string(path, self.limits.max_string_bytes)?;
        String::from_utf8(bytes).map_err(|_| self.syntax("string is not UTF-8"))
    }

    fn expect_string(
        &mut self,
        path: &str,
        expected: &str,
    ) -> Result<(), HomologicalStreamPortableError> {
        let found = self.string(path)?;
        if found == expected {
            Ok(())
        } else if path == "$.schema" {
            Err(HomologicalStreamPortableError::Schema { found })
        } else if path == "$.kind" {
            Err(HomologicalStreamPortableError::Kind { found })
        } else {
            Err(HomologicalStreamPortableError::Engine { found })
        }
    }

    fn json_string(
        &mut self,
        path: &str,
        limit: usize,
    ) -> Result<Vec<u8>, HomologicalStreamPortableError> {
        self.whitespace();
        if self.peek() != Some(b'"') {
            return Err(self.syntax("expected string"));
        }
        self.position += 1;
        let mut bytes = Vec::new();
        loop {
            let Some(byte) = self.string_byte()? else {
                return Ok(bytes);
            };
            bytes.push(byte);
            if bytes.len() > limit {
                return Err(HomologicalStreamPortableError::ParseLimit {
                    path: path.to_string(),
                    used: bytes.len(),
                    limit,
                });
            }
        }
    }

    fn string_byte(&mut self) -> Result<Option<u8>, HomologicalStreamPortableError> {
        let Some(byte) = self.peek() else {
            return Err(self.syntax("unterminated string"));
        };
        self.position += 1;
        match byte {
            b'"' => Ok(None),
            b'\\' => self.escaped_byte().map(Some),
            b if b.is_ascii_control() => Err(self.syntax("control byte in string")),
            b => Ok(Some(b)),
        }
    }

    fn escaped_byte(&mut self) -> Result<u8, HomologicalStreamPortableError> {
        let Some(escaped) = self.peek() else {
            return Err(self.syntax("unterminated escape"));
        };
        self.position += 1;
        match escaped {
            b'"' | b'\\' => Ok(escaped),
            _ => Err(self.syntax("only quote and backslash escapes are canonical")),
        }
    }

    fn number(&mut self, path: &str) -> Result<usize, HomologicalStreamPortableError> {
        self.whitespace();
        let start = self.position;
        while self.peek().is_some_and(|byte| byte.is_ascii_digit()) {
            self.position += 1;
        }
        let digits = self.position - start;
        if digits == 0 {
            return Err(self.syntax("expected unsigned integer"));
        }
        self.numeric_values = self.numeric_values.checked_add(1).ok_or_else(|| {
            HomologicalStreamPortableError::ParseLimit {
                path: "$".to_string(),
                used: usize::MAX,
                limit: self.limits.max_numeric_values,
            }
        })?;
        if self.numeric_values > self.limits.max_numeric_values {
            return Err(HomologicalStreamPortableError::ParseLimit {
                path: "$".to_string(),
                used: self.numeric_values,
                limit: self.limits.max_numeric_values,
            });
        }
        if digits > self.limits.max_integer_digits {
            return Err(HomologicalStreamPortableError::ParseLimit {
                path: path.to_string(),
                used: digits,
                limit: self.limits.max_integer_digits,
            });
        }
        let mut value = 0usize;
        for &byte in &self.bytes[start..self.position] {
            value = value
                .checked_mul(10)
                .and_then(|value| value.checked_add(usize::from(byte - b'0')))
                .ok_or(HomologicalStreamPortableError::CounterOverflow {
                    field: "unsigned integer",
                })?;
        }
        if digits > 1 && self.bytes[start] == b'0' {
            return Err(self.syntax("leading zero in unsigned integer"));
        }
        Ok(value)
    }

    fn number_after_key(
        &mut self,
        key: &str,
        path: &str,
    ) -> Result<usize, HomologicalStreamPortableError> {
        self.key(key)?;
        self.number(path)
    }

    fn next<T>(
        &mut self,
        key: &str,
        read: impl FnOnce(&mut Self) -> Result<T, HomologicalStreamPortableError>,
    ) -> Result<T, HomologicalStreamPortableError> {
        self.comma()?;
        self.key(key)?;
        read(self)
    }

    fn array_element(
        &mut self,
        path: &str,
        used: usize,
        limit: usize,
    ) -> Result<(), HomologicalStreamPortableError> {
        let used =
            used.checked_add(1)
                .ok_or_else(|| HomologicalStreamPortableError::ParseLimit {
                    path: path.to_string(),
                    used: usize::MAX,
                    limit,
                })?;
        self.array_elements = self.array_elements.checked_add(1).ok_or_else(|| {
            HomologicalStreamPortableError::ParseLimit {
                path: "$".to_string(),
                used: usize::MAX,
                limit: self.limits.max_array_elements,
            }
        })?;
        if self.array_elements > self.limits.max_array_elements {
            return Err(HomologicalStreamPortableError::ParseLimit {
                path: "$".to_string(),
                used: self.array_elements,
                limit: self.limits.max_array_elements,
            });
        }
        if used > limit {
            return Err(HomologicalStreamPortableError::ParseLimit {
                path: path.to_string(),
                used,
                limit,
            });
        }
        Ok(())
    }

    fn key(&mut self, expected: &str) -> Result<(), HomologicalStreamPortableError> {
        let found = self.string("key")?;
        if found == expected {
            self.token(b':')
        } else {
            Err(self.syntax("unexpected object key"))
        }
    }

    fn comma(&mut self) -> Result<(), HomologicalStreamPortableError> {
        self.whitespace();
        if self.peek() == Some(b',') {
            self.position += 1;
            Ok(())
        } else {
            Err(self.syntax("expected comma"))
        }
    }

    fn token(&mut self, expected: u8) -> Result<(), HomologicalStreamPortableError> {
        self.whitespace();
        if self.peek() == Some(expected) {
            self.position += 1;
            Ok(())
        } else {
            Err(self.syntax("unexpected JSON token"))
        }
    }

    fn whitespace(&mut self) {
        while self
            .peek()
            .is_some_and(|byte| matches!(byte, b' ' | b'\n' | b'\r' | b'\t'))
        {
            self.position += 1;
        }
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.position).copied()
    }

    fn syntax(&self, message: &str) -> HomologicalStreamPortableError {
        HomologicalStreamPortableError::Syntax {
            byte: self.position,
            message: message.to_string(),
        }
    }
}

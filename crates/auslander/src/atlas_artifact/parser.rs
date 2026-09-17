use crate::atlas::{
    CatalogAtlasLimits, CatalogAtlasWork, MultiplicityCutReason, MultiplicityLimits,
};

use super::errors::CatalogAtlasArtifactError;
use super::model::CatalogAtlasArtifactParseLimits;
use super::{
    CATALOG_ATLAS_ARTIFACT_ENGINE, CATALOG_ATLAS_ARTIFACT_KIND, CATALOG_ATLAS_ARTIFACT_SCHEMA,
};

pub(super) struct RawArtifact {
    pub(super) certificate: Vec<u8>,
    pub(super) field: u64,
    pub(super) provenance: String,
    pub(super) catalog_ids: Vec<usize>,
    pub(super) target_dimensions: Vec<usize>,
    pub(super) max_degree: usize,
    pub(super) atlas_limits: CatalogAtlasLimits,
    pub(super) multiplicity_limits: MultiplicityLimits,
    pub(super) work: CatalogAtlasWork,
    pub(super) ext_rows: Vec<RawExtRow>,
    pub(super) result_rows: Vec<RawResultRow>,
    pub(super) status: RawStatus,
    pub(super) fingerprint: String,
}

pub(super) struct RawExtRow {
    pub(super) source: usize,
    pub(super) target: usize,
    pub(super) dimensions: Vec<usize>,
}

pub(super) struct RawResultRow {
    pub(super) multiplicities: Vec<usize>,
    pub(super) self_ext: Vec<usize>,
}

pub(super) struct RawStatus {
    pub(super) kind: String,
    pub(super) reason: Option<MultiplicityCutReason>,
    pub(super) coverage: Option<usize>,
    pub(super) nodes_visited: Option<usize>,
}

impl RawArtifact {
    pub(super) fn parse(
        text: &str,
        limits: CatalogAtlasArtifactParseLimits,
    ) -> Result<Self, CatalogAtlasArtifactError> {
        let mut parser = ArtifactParser {
            bytes: text.as_bytes(),
            position: 0,
            limits,
            numeric_values: 0,
            array_elements: 0,
        };
        parser.read()
    }
}

struct ArtifactParser<'a> {
    bytes: &'a [u8],
    position: usize,
    limits: CatalogAtlasArtifactParseLimits,
    numeric_values: usize,
    array_elements: usize,
}

struct IdentityFields {
    certificate: Vec<u8>,
    field: u64,
    provenance: String,
    catalog_ids: Vec<usize>,
    target_dimensions: Vec<usize>,
}

struct DataFields {
    max_degree: usize,
    atlas_limits: CatalogAtlasLimits,
    multiplicity_limits: MultiplicityLimits,
    work: CatalogAtlasWork,
    ext_rows: Vec<RawExtRow>,
    result_rows: Vec<RawResultRow>,
    status: RawStatus,
    fingerprint: String,
}

impl ArtifactParser<'_> {
    fn read(&mut self) -> Result<RawArtifact, CatalogAtlasArtifactError> {
        self.header()?;
        let identity = self.identity_fields()?;
        let data = self.data_fields()?;
        self.finish(&data.fingerprint)?;
        Ok(RawArtifact {
            certificate: identity.certificate,
            field: identity.field,
            provenance: identity.provenance,
            catalog_ids: identity.catalog_ids,
            target_dimensions: identity.target_dimensions,
            max_degree: data.max_degree,
            atlas_limits: data.atlas_limits,
            multiplicity_limits: data.multiplicity_limits,
            work: data.work,
            ext_rows: data.ext_rows,
            result_rows: data.result_rows,
            status: data.status,
            fingerprint: data.fingerprint,
        })
    }

    fn header(&mut self) -> Result<(), CatalogAtlasArtifactError> {
        self.token(b'{')?;
        self.key("schema")?;
        self.expect_string(CATALOG_ATLAS_ARTIFACT_SCHEMA, "schema")?;
        self.next_key("kind")?;
        self.expect_string(CATALOG_ATLAS_ARTIFACT_KIND, "kind")?;
        self.next_key("engine")?;
        self.expect_string(CATALOG_ATLAS_ARTIFACT_ENGINE, "engine")
    }

    fn identity_fields(&mut self) -> Result<IdentityFields, CatalogAtlasArtifactError> {
        let certificate = self.next("certificate", Self::certificate)?;
        let field = self.next("field", |p| p.number_u64("field"))?;
        let provenance = self.next("provenance", |p| p.string("provenance"))?;
        let catalog_ids = self.next("catalog_ids", |p| {
            p.usize_array("catalog_ids", p.limits.max_catalog_entries, None)
        })?;
        let target_dimensions = self.next("target_dimensions", |p| {
            p.usize_array(
                "target_dimensions",
                p.limits.max_dimensions,
                Some(p.limits.max_dimension),
            )
        })?;
        Ok(IdentityFields {
            certificate,
            field,
            provenance,
            catalog_ids,
            target_dimensions,
        })
    }

    fn data_fields(&mut self) -> Result<DataFields, CatalogAtlasArtifactError> {
        let max_degree = self.next("max_degree", |p| p.number_usize("max_degree"))?;
        let atlas_limits = self.next("atlas_limits", ArtifactParser::atlas_limits)?;
        let multiplicity_limits =
            self.next("multiplicity_limits", ArtifactParser::multiplicity_limits)?;
        let work = self.next("work", ArtifactParser::work)?;
        let ext_rows = self.next("ext_rows", ArtifactParser::ext_rows)?;
        let result_rows = self.next("result_rows", ArtifactParser::result_rows)?;
        let status = self.next("status", ArtifactParser::status)?;
        let fingerprint = self.next("fingerprint", |p| p.string("fingerprint"))?;
        Ok(DataFields {
            max_degree,
            atlas_limits,
            multiplicity_limits,
            work,
            ext_rows,
            result_rows,
            status,
            fingerprint,
        })
    }

    fn finish(&mut self, fingerprint: &str) -> Result<(), CatalogAtlasArtifactError> {
        self.token(b'}')?;
        self.whitespace();
        if self.position != self.bytes.len() {
            return Err(self.syntax("trailing content"));
        }
        if !valid_fingerprint(fingerprint) {
            return Err(CatalogAtlasArtifactError::Syntax {
                byte: self.position,
                message: "fingerprint must contain 16 lowercase hexadecimal digits".to_string(),
            });
        }
        Ok(())
    }

    fn certificate(parser: &mut ArtifactParser<'_>) -> Result<Vec<u8>, CatalogAtlasArtifactError> {
        parser.escaped_certificate("certificate")
    }
}

impl ArtifactParser<'_> {
    fn syntax(&self, message: &str) -> CatalogAtlasArtifactError {
        CatalogAtlasArtifactError::Syntax {
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

    fn token(&mut self, expected: u8) -> Result<(), CatalogAtlasArtifactError> {
        self.whitespace();
        if self.bytes.get(self.position) != Some(&expected) {
            return Err(self.syntax(&format!("expected byte {}", expected as char)));
        }
        self.position += 1;
        Ok(())
    }

    fn next_key(&mut self, expected: &str) -> Result<(), CatalogAtlasArtifactError> {
        self.token(b',')?;
        self.key(expected)
    }

    fn key(&mut self, expected: &str) -> Result<(), CatalogAtlasArtifactError> {
        let found = self.string("object key")?;
        if found != expected {
            return Err(self.syntax(&format!("expected key {expected:?}")));
        }
        self.token(b':')
    }

    fn next<T>(
        &mut self,
        key: &str,
        read: impl FnOnce(&mut Self) -> Result<T, CatalogAtlasArtifactError>,
    ) -> Result<T, CatalogAtlasArtifactError> {
        self.next_key(key)?;
        read(self)
    }

    fn string(&mut self, path: &str) -> Result<String, CatalogAtlasArtifactError> {
        self.token(b'"')?;
        let start = self.position;
        let end = self.scan_string_end()?;
        let length = end - start;
        if length > self.limits.max_string_bytes {
            return Err(CatalogAtlasArtifactError::ParseLimit {
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

    fn expect_string(
        &mut self,
        expected: &str,
        path: &str,
    ) -> Result<(), CatalogAtlasArtifactError> {
        let found = self.string(path)?;
        if found == expected {
            Ok(())
        } else if path == "schema" {
            Err(CatalogAtlasArtifactError::Schema { found })
        } else if path == "kind" {
            Err(CatalogAtlasArtifactError::Kind { found })
        } else {
            Err(CatalogAtlasArtifactError::Engine { found })
        }
    }

    fn scan_string_end(&mut self) -> Result<usize, CatalogAtlasArtifactError> {
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

    fn number_u128(&mut self, path: &str) -> Result<u128, CatalogAtlasArtifactError> {
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
            return Err(CatalogAtlasArtifactError::ParseLimit {
                path: path.to_string(),
                used: digits,
                limit: self.limits.max_integer_digits,
            });
        }
        if digits > 1 && self.bytes[start] == b'0' {
            return Err(self.syntax("integer has a leading zero"));
        }
        if self.numeric_values == self.limits.max_numeric_values {
            return Err(CatalogAtlasArtifactError::ParseLimit {
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

    fn number_u64(&mut self, path: &str) -> Result<u64, CatalogAtlasArtifactError> {
        u64::try_from(self.number_u128(path)?).map_err(|_| self.syntax("integer exceeds u64"))
    }

    fn number_usize(&mut self, path: &str) -> Result<usize, CatalogAtlasArtifactError> {
        usize::try_from(self.number_u128(path)?).map_err(|_| self.syntax("integer exceeds usize"))
    }

    fn escaped_certificate(&mut self, path: &str) -> Result<Vec<u8>, CatalogAtlasArtifactError> {
        self.token(b'"')?;
        let mut output = Vec::new();
        loop {
            let Some(byte) = self.certificate_byte()? else {
                return Ok(output);
            };
            self.push_certificate_byte(byte, path, &mut output)?;
        }
    }

    fn certificate_byte(&mut self) -> Result<Option<u8>, CatalogAtlasArtifactError> {
        let byte = *self
            .bytes
            .get(self.position)
            .ok_or_else(|| self.syntax("unterminated certificate string"))?;
        match byte {
            b'"' => {
                self.position += 1;
                Ok(None)
            }
            b'\\' => self.escaped_certificate_byte(),
            0..=0x1f | 0x80..=u8::MAX => {
                Err(self.syntax("certificate string contains a forbidden byte"))
            }
            _ => {
                self.position += 1;
                Ok(Some(byte))
            }
        }
    }

    fn escaped_certificate_byte(&mut self) -> Result<Option<u8>, CatalogAtlasArtifactError> {
        self.position += 1;
        let escaped = *self
            .bytes
            .get(self.position)
            .ok_or_else(|| self.syntax("unterminated certificate escape"))?;
        if !matches!(escaped, b'"' | b'\\') {
            return Err(self.syntax("certificate escape must be quote or backslash"));
        }
        self.position += 1;
        Ok(Some(escaped))
    }

    fn push_certificate_byte(
        &self,
        byte: u8,
        path: &str,
        output: &mut Vec<u8>,
    ) -> Result<(), CatalogAtlasArtifactError> {
        if output.len() == self.limits.max_certificate_bytes {
            return Err(CatalogAtlasArtifactError::ParseLimit {
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
        mut next: impl FnMut(&mut Self, usize) -> Result<T, CatalogAtlasArtifactError>,
    ) -> Result<Vec<T>, CatalogAtlasArtifactError> {
        self.token(b'[')?;
        self.whitespace();
        if self.bytes.get(self.position) == Some(&b']') {
            self.position += 1;
            return Ok(Vec::new());
        }
        let mut output = Vec::new();
        loop {
            if output.len() == limit {
                return Err(CatalogAtlasArtifactError::ParseLimit {
                    path: path.to_string(),
                    used: output.len() + 1,
                    limit,
                });
            }
            if self.array_elements == self.limits.max_array_elements {
                return Err(CatalogAtlasArtifactError::ParseLimit {
                    path: "array elements".to_string(),
                    used: self.array_elements + 1,
                    limit: self.limits.max_array_elements,
                });
            }
            let index = output.len();
            output.push(next(self, index)?);
            self.array_elements += 1;
            self.whitespace();
            match self.bytes.get(self.position) {
                Some(b',') => {
                    self.position += 1;
                }
                Some(b']') => {
                    self.position += 1;
                    return Ok(output);
                }
                _ => return Err(self.syntax("expected comma or array end")),
            }
        }
    }

    fn usize_array(
        &mut self,
        path: &str,
        limit: usize,
        maximum: Option<usize>,
    ) -> Result<Vec<usize>, CatalogAtlasArtifactError> {
        self.array(path, limit, |parser, index| {
            let value = parser.number_usize(&format!("{path}[{index}]"))?;
            if let Some(maximum) = maximum
                && value > maximum
            {
                return Err(CatalogAtlasArtifactError::ParseLimit {
                    path: format!("{path}[{index}]"),
                    used: value,
                    limit: maximum,
                });
            }
            Ok(value)
        })
    }

    fn object_start(&mut self) -> Result<(), CatalogAtlasArtifactError> {
        self.token(b'{')
    }

    fn object_end(&mut self) -> Result<(), CatalogAtlasArtifactError> {
        self.token(b'}')
    }

    fn atlas_limits(&mut self) -> Result<CatalogAtlasLimits, CatalogAtlasArtifactError> {
        self.object_start()?;
        self.key("max_pairs")?;
        let max_pairs = self.number_usize("atlas_limits.max_pairs")?;
        let max_ext_cells = self.next("max_ext_cells", |p| {
            p.number_usize("atlas_limits.max_ext_cells")
        })?;
        let max_resolution_terms = self.next("max_resolution_terms", |p| {
            p.number_usize("atlas_limits.max_resolution_terms")
        })?;
        let max_materialized_summands = self.next("max_materialized_summands", |p| {
            p.number_usize("atlas_limits.max_materialized_summands")
        })?;
        let max_materialized_cells = self.next("max_materialized_cells", |p| {
            p.number_usize("atlas_limits.max_materialized_cells")
        })?;
        self.object_end()?;
        Ok(CatalogAtlasLimits {
            max_pairs,
            max_ext_cells,
            max_resolution_terms,
            max_materialized_summands,
            max_materialized_cells,
        })
    }

    fn multiplicity_limits(&mut self) -> Result<MultiplicityLimits, CatalogAtlasArtifactError> {
        self.object_start()?;
        self.key("max_solutions")?;
        let max_solutions = self.number_usize("multiplicity_limits.max_solutions")?;
        let max_nodes = self.next("max_nodes", |p| {
            p.number_usize("multiplicity_limits.max_nodes")
        })?;
        self.object_end()?;
        Ok(MultiplicityLimits {
            max_solutions,
            max_nodes,
        })
    }

    fn work(&mut self) -> Result<CatalogAtlasWork, CatalogAtlasArtifactError> {
        self.object_start()?;
        self.key("pairs")?;
        let pairs = self.number_usize("work.pairs")?;
        let ext_cells = self.next("ext_cells", |p| p.number_usize("work.ext_cells"))?;
        let resolutions = self.next("resolutions", |p| p.number_usize("work.resolutions"))?;
        let resolution_terms = self.next("resolution_terms", |p| {
            p.number_usize("work.resolution_terms")
        })?;
        let ext_tables = self.next("ext_tables", |p| p.number_usize("work.ext_tables"))?;
        self.object_end()?;
        Ok(CatalogAtlasWork {
            pairs,
            ext_cells,
            resolutions,
            resolution_terms,
            ext_tables,
        })
    }

    fn ext_rows(&mut self) -> Result<Vec<RawExtRow>, CatalogAtlasArtifactError> {
        let limit = self.limits.max_ext_rows;
        self.array("ext_rows", limit, |parser, _| {
            parser.object_start()?;
            parser.key("source")?;
            let source = parser.number_usize("ext_rows[].source")?;
            let target = parser.next("target", |p| p.number_usize("ext_rows[].target"))?;
            let dimensions = parser.next("dimensions", |p| {
                p.usize_array("ext_rows[].dimensions", p.limits.max_ext_degrees, None)
            })?;
            parser.object_end()?;
            Ok(RawExtRow {
                source,
                target,
                dimensions,
            })
        })
    }

    fn result_rows(&mut self) -> Result<Vec<RawResultRow>, CatalogAtlasArtifactError> {
        let limit = self.limits.max_result_rows;
        self.array("result_rows", limit, |parser, _| {
            parser.object_start()?;
            parser.key("multiplicities")?;
            let multiplicities = parser.usize_array(
                "result_rows[].multiplicities",
                parser.limits.max_multiplicity_values,
                None,
            )?;
            let self_ext = parser.next("self_ext", |p| {
                p.usize_array("result_rows[].self_ext", p.limits.max_ext_degrees, None)
            })?;
            parser.object_end()?;
            Ok(RawResultRow {
                multiplicities,
                self_ext,
            })
        })
    }

    fn status(&mut self) -> Result<RawStatus, CatalogAtlasArtifactError> {
        self.object_start()?;
        self.key("kind")?;
        let kind = self.string("status.kind")?;
        match kind.as_str() {
            "complete" => self.complete_status(kind),
            "cut" => self.cut_status(kind),
            _ => Err(self.syntax("status kind must be complete or cut")),
        }
    }

    fn complete_status(&mut self, kind: String) -> Result<RawStatus, CatalogAtlasArtifactError> {
        self.object_end()?;
        Ok(RawStatus {
            kind,
            reason: None,
            coverage: None,
            nodes_visited: None,
        })
    }

    fn cut_status(&mut self, kind: String) -> Result<RawStatus, CatalogAtlasArtifactError> {
        let reason = self.next("reason", ArtifactParser::cut_reason)?;
        let coverage = self.next("coverage", |p| p.number_usize("status.coverage"))?;
        let nodes_visited =
            self.next("nodes_visited", |p| p.number_usize("status.nodes_visited"))?;
        self.object_end()?;
        Ok(RawStatus {
            kind,
            reason: Some(reason),
            coverage: Some(coverage),
            nodes_visited: Some(nodes_visited),
        })
    }

    fn cut_reason(&mut self) -> Result<MultiplicityCutReason, CatalogAtlasArtifactError> {
        self.object_start()?;
        self.key("kind")?;
        let kind = self.string("status.reason.kind")?;
        let limit = self.next("limit", |p| p.number_usize("status.reason.limit"))?;
        self.object_end()?;
        match kind.as_str() {
            "solution_limit" => Ok(MultiplicityCutReason::SolutionLimit { limit }),
            "node_limit" => Ok(MultiplicityCutReason::NodeLimit { limit }),
            _ => Err(self.syntax("unknown multiplicity cut reason")),
        }
    }
}

fn valid_fingerprint(value: &str) -> bool {
    value.len() == 16
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

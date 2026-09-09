use super::errors::SelfExtLocusArtifactError;
use super::model::{
    SELF_EXT_LOCUS_ARTIFACT_KIND, SELF_EXT_LOCUS_ARTIFACT_SCHEMA, SelfExtLocusParseLimits,
};

pub(super) struct RawSelfExtLocusArtifact {
    pub(super) checkpoint: String,
    pub(super) first_degree: usize,
    pub(super) last_degree: usize,
    pub(super) vanishing_indices: Vec<usize>,
    pub(super) fingerprint: String,
}

pub(super) fn parse(
    text: &str,
    limits: SelfExtLocusParseLimits,
) -> Result<RawSelfExtLocusArtifact, SelfExtLocusArtifactError> {
    if text.len() > limits.max_input_bytes {
        return Err(SelfExtLocusArtifactError::ParseLimit {
            path: "$".to_string(),
            used: text.len(),
            limit: limits.max_input_bytes,
        });
    }
    Parser::new(text, limits).document()
}

struct Parser<'a> {
    bytes: &'a [u8],
    position: usize,
    limits: SelfExtLocusParseLimits,
}

struct RawClaim {
    checkpoint: String,
    first_degree: usize,
    last_degree: usize,
    vanishing_indices: Vec<usize>,
}

struct ObjectScan {
    depth: usize,
    in_string: bool,
    escaped: bool,
}

impl ObjectScan {
    fn new() -> Self {
        Self {
            depth: 0,
            in_string: false,
            escaped: false,
        }
    }

    fn advance(&mut self, byte: u8) -> bool {
        if self.in_string {
            self.advance_string(byte);
            return false;
        }
        match byte {
            b'"' => self.in_string = true,
            b'{' => self.depth += 1,
            b'}' if self.depth == 1 => return true,
            b'}' if self.depth > 1 => self.depth -= 1,
            _ => {}
        }
        false
    }

    fn advance_string(&mut self, byte: u8) {
        if self.escaped {
            self.escaped = false;
        } else if byte == b'\\' {
            self.escaped = true;
        } else if byte == b'"' {
            self.in_string = false;
        }
    }
}

impl<'a> Parser<'a> {
    fn new(text: &'a str, limits: SelfExtLocusParseLimits) -> Self {
        Self {
            bytes: text.as_bytes(),
            position: 0,
            limits,
        }
    }

    fn document(mut self) -> Result<RawSelfExtLocusArtifact, SelfExtLocusArtifactError> {
        self.header()?;
        let claim = self.claim()?;
        let fingerprint = self.trailer()?;
        Ok(RawSelfExtLocusArtifact {
            checkpoint: claim.checkpoint,
            first_degree: claim.first_degree,
            last_degree: claim.last_degree,
            vanishing_indices: claim.vanishing_indices,
            fingerprint,
        })
    }

    fn header(&mut self) -> Result<(), SelfExtLocusArtifactError> {
        self.token(b'{')?;
        self.key("schema")?;
        let schema = self.string()?;
        if schema != SELF_EXT_LOCUS_ARTIFACT_SCHEMA {
            return Err(SelfExtLocusArtifactError::Schema { found: schema });
        }
        self.comma_key("kind")?;
        let kind = self.string()?;
        if kind != SELF_EXT_LOCUS_ARTIFACT_KIND {
            return Err(SelfExtLocusArtifactError::Kind { found: kind });
        }
        Ok(())
    }

    fn claim(&mut self) -> Result<RawClaim, SelfExtLocusArtifactError> {
        self.comma_key("checkpoint")?;
        let checkpoint = self.checkpoint()?;
        self.comma_key("first_degree")?;
        let first_degree = self.number()?;
        self.comma_key("last_degree")?;
        let last_degree = self.number()?;
        self.comma_key("vanishing_indices")?;
        let vanishing_indices = self.indices()?;
        Ok(RawClaim {
            checkpoint,
            first_degree,
            last_degree,
            vanishing_indices,
        })
    }

    fn trailer(&mut self) -> Result<String, SelfExtLocusArtifactError> {
        self.comma_key("fingerprint")?;
        let fingerprint = self.fingerprint()?;
        self.token(b'}')?;
        self.whitespace();
        if self.position != self.bytes.len() {
            return Err(self.syntax("trailing content"));
        }
        Ok(fingerprint)
    }

    fn checkpoint(&mut self) -> Result<String, SelfExtLocusArtifactError> {
        self.whitespace();
        let start = self.position;
        if self.bytes.get(start) != Some(&b'{') {
            return Err(self.syntax("checkpoint must be an object"));
        }
        let mut scan = ObjectScan::new();
        while let Some(&byte) = self.bytes.get(self.position) {
            self.position += 1;
            if self.position - start > self.limits.checkpoint.max_input_bytes {
                return Err(SelfExtLocusArtifactError::ParseLimit {
                    path: "$.checkpoint".to_string(),
                    used: self.position - start,
                    limit: self.limits.checkpoint.max_input_bytes,
                });
            }
            if scan.advance(byte) {
                return Ok(self.checkpoint_text(start));
            }
        }
        Err(self.syntax("unterminated checkpoint object"))
    }

    fn checkpoint_text(&self, start: usize) -> String {
        std::str::from_utf8(&self.bytes[start..self.position])
            .expect("the parser input is UTF-8")
            .to_string()
    }

    fn indices(&mut self) -> Result<Vec<usize>, SelfExtLocusArtifactError> {
        self.token(b'[')?;
        self.whitespace();
        if self.bytes.get(self.position) == Some(&b']') {
            self.position += 1;
            return Ok(Vec::new());
        }
        let mut values = Vec::new();
        loop {
            if values.len() == self.limits.max_vanishing_indices {
                return Err(SelfExtLocusArtifactError::ParseLimit {
                    path: "$.vanishing_indices".to_string(),
                    used: values.len() + 1,
                    limit: self.limits.max_vanishing_indices,
                });
            }
            values.push(self.number()?);
            self.whitespace();
            match self.bytes.get(self.position) {
                Some(b',') => self.position += 1,
                Some(b']') => {
                    self.position += 1;
                    return Ok(values);
                }
                _ => return Err(self.syntax("expected comma or vanishing-indices end")),
            }
        }
    }

    fn fingerprint(&mut self) -> Result<String, SelfExtLocusArtifactError> {
        let value = self.string()?;
        if value.len() == 16
            && value
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        {
            Ok(value)
        } else {
            Err(SelfExtLocusArtifactError::FingerprintShape)
        }
    }

    fn number(&mut self) -> Result<usize, SelfExtLocusArtifactError> {
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
            return Err(SelfExtLocusArtifactError::ParseLimit {
                path: "integer".to_string(),
                used: digits,
                limit: self.limits.max_integer_digits,
            });
        }
        if digits > 1 && self.bytes[start] == b'0' {
            return Err(self.syntax("integer has a leading zero"));
        }
        std::str::from_utf8(&self.bytes[start..self.position])
            .expect("the parser input is UTF-8")
            .parse()
            .map_err(|_| self.syntax("integer exceeds usize"))
    }

    fn string(&mut self) -> Result<String, SelfExtLocusArtifactError> {
        self.token(b'"')?;
        let start = self.position;
        while let Some(&byte) = self.bytes.get(self.position) {
            if byte == b'"' {
                let len = self.position - start;
                if len > self.limits.max_string_bytes {
                    return Err(SelfExtLocusArtifactError::ParseLimit {
                        path: "string".to_string(),
                        used: len,
                        limit: self.limits.max_string_bytes,
                    });
                }
                let value = std::str::from_utf8(&self.bytes[start..self.position])
                    .expect("the parser input is UTF-8")
                    .to_string();
                self.position += 1;
                return Ok(value);
            }
            if matches!(byte, b'\\' | 0..=0x1f | 0x80..=u8::MAX) {
                return Err(self.syntax("string contains a forbidden byte"));
            }
            self.position += 1;
        }
        Err(self.syntax("unterminated string"))
    }

    fn comma_key(&mut self, expected: &str) -> Result<(), SelfExtLocusArtifactError> {
        self.token(b',')?;
        self.key(expected)
    }

    fn key(&mut self, expected: &str) -> Result<(), SelfExtLocusArtifactError> {
        let key = self.string()?;
        if key != expected {
            return Err(self.syntax(&format!("expected key {expected:?}")));
        }
        self.token(b':')
    }

    fn token(&mut self, expected: u8) -> Result<(), SelfExtLocusArtifactError> {
        self.whitespace();
        if self.bytes.get(self.position) != Some(&expected) {
            return Err(self.syntax(&format!("expected byte {}", expected as char)));
        }
        self.position += 1;
        Ok(())
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

    fn syntax(&self, message: &str) -> SelfExtLocusArtifactError {
        SelfExtLocusArtifactError::Syntax {
            byte: self.position,
            message: message.to_string(),
        }
    }
}

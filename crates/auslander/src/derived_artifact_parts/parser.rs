use super::DERIVED_ARTIFACT_SCHEMA;
use super::errors::ArtifactError;
use super::model::{ArtifactMutation, ArtifactParseLimits};
use crate::tilting_complex::ApproximationDirection;

pub(super) struct RawArtifact {
    pub(super) source: Vec<u8>,
    pub(super) mutations: Vec<ArtifactMutation>,
    pub(super) target: Vec<u8>,
    pub(super) limits: [usize; 10],
    pub(super) work: [usize; 4],
    pub(super) fingerprint: String,
}

struct RawContents {
    source: Vec<u8>,
    mutations: Vec<ArtifactMutation>,
    target: Vec<u8>,
}

impl RawArtifact {
    pub(super) fn parse(
        text: &str,
        limits: ArtifactParseLimits,
    ) -> Result<RawArtifact, ArtifactError> {
        let mut parser = ArtifactParser {
            bytes: text.as_bytes(),
            position: 0,
            limits,
        };
        let contents = parser.contents()?;
        let (limits, work, fingerprint) = parser.metadata()?;
        parser.token(b'}')?;
        parser.whitespace();
        if parser.position != parser.bytes.len() {
            return Err(parser.syntax("trailing content"));
        }
        Ok(RawArtifact {
            source: contents.source,
            mutations: contents.mutations,
            target: contents.target,
            limits,
            work,
            fingerprint,
        })
    }
}

struct ArtifactParser<'a> {
    bytes: &'a [u8],
    position: usize,
    limits: ArtifactParseLimits,
}

impl ArtifactParser<'_> {
    fn contents(&mut self) -> Result<RawContents, ArtifactError> {
        self.schema()?;
        let source = self.next("source", |parser| parser.byte_array("$.source"))?;
        let mutations = self.next("mutations", Self::mutations)?;
        let target = self.next("target", |parser| parser.byte_array("$.target"))?;
        Ok(RawContents {
            source,
            mutations,
            target,
        })
    }

    fn metadata(&mut self) -> Result<([usize; 10], [usize; 4], String), ArtifactError> {
        let limits = self.next("limits", |parser| parser.fixed_array::<10>("$.limits"))?;
        let work = self.next("work", |parser| parser.fixed_array::<4>("$.work"))?;
        let fingerprint = self.next("fingerprint", |parser| {
            let fingerprint = parser.string()?;
            if fingerprint.len() != 16
                || !fingerprint
                    .bytes()
                    .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
            {
                return Err(ArtifactError::FingerprintShape);
            }
            Ok(fingerprint)
        })?;
        Ok((limits, work, fingerprint))
    }

    fn schema(&mut self) -> Result<(), ArtifactError> {
        self.token(b'{')?;
        self.key("schema")?;
        let schema = self.string()?;
        if schema != DERIVED_ARTIFACT_SCHEMA {
            return Err(ArtifactError::Schema { found: schema });
        }
        Ok(())
    }

    fn next<T>(
        &mut self,
        key: &str,
        read: impl FnOnce(&mut Self) -> Result<T, ArtifactError>,
    ) -> Result<T, ArtifactError> {
        self.comma()?;
        self.key(key)?;
        read(self)
    }

    fn syntax(&self, message: &str) -> ArtifactError {
        ArtifactError::Syntax {
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

    fn token(&mut self, expected: u8) -> Result<(), ArtifactError> {
        self.whitespace();
        if self.bytes.get(self.position) != Some(&expected) {
            return Err(self.syntax(&format!("expected byte {}", expected as char)));
        }
        self.position += 1;
        Ok(())
    }

    fn comma(&mut self) -> Result<(), ArtifactError> {
        self.token(b',')
    }

    fn key(&mut self, expected: &str) -> Result<(), ArtifactError> {
        let key = self.string()?;
        if key != expected {
            return Err(self.syntax(&format!("expected key {expected:?}")));
        }
        self.token(b':')
    }

    fn string(&mut self) -> Result<String, ArtifactError> {
        self.token(b'"')?;
        let start = self.position;
        let end = self.scan_string_end()?;
        let value = std::str::from_utf8(&self.bytes[start..end])
            .map_err(|_| self.syntax("string is not UTF-8"))?
            .to_string();
        self.position += 1;
        Ok(value)
    }

    fn scan_string_end(&mut self) -> Result<usize, ArtifactError> {
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

    fn number(&mut self) -> Result<usize, ArtifactError> {
        self.whitespace();
        let start = self.position;
        self.scan_digits();
        self.check_digits(start)?;
        let text = std::str::from_utf8(&self.bytes[start..self.position])
            .map_err(|_| self.syntax("integer is not ASCII"))?;
        text.parse()
            .map_err(|_| self.syntax("integer exceeds usize"))
    }

    fn scan_digits(&mut self) {
        while self
            .bytes
            .get(self.position)
            .is_some_and(u8::is_ascii_digit)
        {
            self.position += 1;
        }
    }

    fn check_digits(&self, start: usize) -> Result<(), ArtifactError> {
        let digits = self.position - start;
        if digits == 0 {
            return Err(self.syntax("expected unsigned integer"));
        }
        if digits > self.limits.max_integer_digits {
            return Err(ArtifactError::ParseLimit {
                path: "integer".to_string(),
                used: digits,
                limit: self.limits.max_integer_digits,
            });
        }
        if digits > 1 && self.bytes[start] == b'0' {
            return Err(self.syntax("integer has a leading zero"));
        }
        Ok(())
    }

    fn array_start(&mut self) -> Result<bool, ArtifactError> {
        self.token(b'[')?;
        self.whitespace();
        if self.bytes.get(self.position) == Some(&b']') {
            self.position += 1;
            return Ok(false);
        }
        Ok(true)
    }

    fn array_end(&mut self, message: &str) -> Result<bool, ArtifactError> {
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
            _ => Err(self.syntax(message)),
        }
    }

    fn next_byte(&mut self, count: usize, path: &str) -> Result<u8, ArtifactError> {
        if count == self.limits.max_certificate_bytes {
            return Err(ArtifactError::ParseLimit {
                path: path.to_string(),
                used: count + 1,
                limit: self.limits.max_certificate_bytes,
            });
        }
        let value = self.number()?;
        u8::try_from(value).map_err(|_| self.syntax("byte exceeds 255"))
    }

    fn array<T>(
        &mut self,
        end_message: &str,
        mut next: impl FnMut(&mut Self, usize) -> Result<T, ArtifactError>,
    ) -> Result<Vec<T>, ArtifactError> {
        let mut output = Vec::new();
        if !self.array_start()? {
            return Ok(output);
        }
        self.fill_array(&mut output, end_message, &mut next)?;
        Ok(output)
    }

    fn fill_array<T>(
        &mut self,
        output: &mut Vec<T>,
        end_message: &str,
        next: &mut impl FnMut(&mut Self, usize) -> Result<T, ArtifactError>,
    ) -> Result<(), ArtifactError> {
        loop {
            output.push(next(self, output.len())?);
            if self.array_end(end_message)? {
                return Ok(());
            }
        }
    }

    fn byte_array(&mut self, path: &str) -> Result<Vec<u8>, ArtifactError> {
        self.array("expected comma or array end", |parser, count| {
            parser.next_byte(count, path)
        })
    }

    fn mutation_values(&mut self) -> Result<(ApproximationDirection, usize), ArtifactError> {
        let direction = mutation_direction(self.number()?)
            .ok_or_else(|| self.syntax("mutation direction must be 0 or 1"))?;
        self.comma()?;
        let summand = self.number()?;
        Ok((direction, summand))
    }

    fn mutation(&mut self) -> Result<ArtifactMutation, ArtifactError> {
        self.token(b'[')?;
        let (direction, summand) = self.mutation_values()?;
        self.token(b']')?;
        Ok(ArtifactMutation { direction, summand })
    }

    fn mutations(&mut self) -> Result<Vec<ArtifactMutation>, ArtifactError> {
        self.array("expected comma or mutation-array end", |parser, count| {
            if count == parser.limits.max_mutations {
                return Err(ArtifactError::ParseLimit {
                    path: "$.mutations".to_string(),
                    used: count + 1,
                    limit: parser.limits.max_mutations,
                });
            }
            parser.mutation()
        })
    }

    fn fixed_values<const N: usize>(&mut self) -> Result<[usize; N], ArtifactError> {
        let mut output = [0; N];
        for (index, value) in output.iter_mut().enumerate() {
            *value = self.number()?;
            if index + 1 != N {
                self.comma()?;
            }
        }
        Ok(output)
    }

    fn fixed_array<const N: usize>(&mut self, path: &str) -> Result<[usize; N], ArtifactError> {
        self.token(b'[')?;
        let output = self.fixed_values()?;
        self.token(b']').map_err(|_| ArtifactError::Syntax {
            byte: self.position,
            message: format!("{path} must contain {N} integers"),
        })?;
        Ok(output)
    }
}

fn mutation_direction(value: usize) -> Option<ApproximationDirection> {
    match value {
        0 => Some(ApproximationDirection::Left),
        1 => Some(ApproximationDirection::Right),
        _ => None,
    }
}

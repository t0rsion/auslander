use super::errors::ArtifactError;
use super::model::{ArtifactMutation, ArtifactParseLimits};
use super::{DERIVED_ARTIFACT_SCHEMA, OBSOLETE_DERIVED_ARTIFACT_SCHEMA};
use crate::portable::{Cursor, CursorLimits, PortableError, is_fingerprint};
use crate::tilting_complex::ApproximationDirection;

pub(super) struct RawArtifact {
    pub(super) source: Vec<u8>,
    pub(super) mutations: Vec<ArtifactMutation>,
    pub(super) target: Vec<u8>,
    pub(super) limits: [u64; 10],
    pub(super) work: [u64; 4],
    pub(super) fingerprint: String,
}

impl RawArtifact {
    pub(super) fn parse(
        text: &str,
        limits: ArtifactParseLimits,
    ) -> Result<RawArtifact, ArtifactError> {
        let mut c = Cursor::new(
            text,
            CursorLimits {
                input_bytes: limits.max_input_bytes,
                integer_digits: limits.max_integer_digits,
                ..CursorLimits::NONE
            },
        )?;
        c.token(b'{')?;
        c.key("schema")?;
        let schema = c.string("$.schema")?;
        if schema == OBSOLETE_DERIVED_ARTIFACT_SCHEMA {
            return Err(ArtifactError::ObsoleteSchema {
                found: schema,
                current: DERIVED_ARTIFACT_SCHEMA,
            });
        }
        if schema != DERIVED_ARTIFACT_SCHEMA {
            return Err(ArtifactError::Schema { found: schema });
        }
        let raw = Self::fields(&mut c, limits)?;
        c.token(b'}')?;
        c.end()?;
        Ok(raw)
    }

    fn fields(c: &mut Cursor, limits: ArtifactParseLimits) -> Result<Self, ArtifactError> {
        let max_bytes = limits.max_certificate_bytes;
        let source = c.next("source", |c| bytes(c, "$.source", max_bytes))?;
        let mutations = c.next("mutations", |c| {
            c.array("$.mutations", limits.max_mutations, |c, _| {
                read_mutation(c, "$.mutations[]")
            })
        })?;
        let target = c.next("target", |c| bytes(c, "$.target", max_bytes))?;
        let parse_limits = c.next("limits", |c| fixed_numbers(c, "$.limits"))?;
        let work = c.next("work", |c| fixed_numbers(c, "$.work"))?;
        let fingerprint = c.next("fingerprint", |c| c.string("$.fingerprint"))?;
        if !is_fingerprint(&fingerprint) {
            return Err(ArtifactError::FingerprintShape);
        }
        Ok(RawArtifact {
            source,
            mutations,
            target,
            limits: parse_limits,
            work,
            fingerprint,
        })
    }
}

fn bytes(c: &mut Cursor, path: &str, limit: usize) -> Result<Vec<u8>, PortableError> {
    c.array(path, limit, |c, _| {
        let value = c.u64(path)?;
        u8::try_from(value).map_err(|_| c.syntax("byte exceeds 255"))
    })
}

/// Reads one recipe step `[direction, summand]`, with direction `0` for
/// left and `1` for right. `path` names the step in error messages.
pub(crate) fn read_mutation(c: &mut Cursor, path: &str) -> Result<ArtifactMutation, PortableError> {
    c.token(b'[')?;
    let direction = match c.u64(&format!("{path}.direction"))? {
        0 => ApproximationDirection::Left,
        1 => ApproximationDirection::Right,
        _ => return Err(c.syntax("mutation direction must be 0 or 1")),
    };
    c.token(b',')?;
    let summand = c.usize(&format!("{path}.summand"))?;
    c.token(b']')?;
    Ok(ArtifactMutation { direction, summand })
}

/// Reads an array of exactly `N` ceilings or work counters. A longer array
/// is rejected at the first extra element, before it is read.
fn fixed_numbers<const N: usize>(c: &mut Cursor, path: &str) -> Result<[u64; N], PortableError> {
    c.token(b'[')?;
    let mut output = [0; N];
    for (index, value) in output.iter_mut().enumerate() {
        if index != 0 {
            c.token(b',')?;
        }
        *value = c.u64(path)?;
    }
    if !c.eat(b']') {
        return Err(c.syntax(format!("{path} must contain {N} integers")));
    }
    Ok(output)
}

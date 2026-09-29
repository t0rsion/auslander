use super::errors::SelfExtLocusArtifactError;
use super::model::{
    SELF_EXT_LOCUS_ARTIFACT_KIND, SELF_EXT_LOCUS_ARTIFACT_SCHEMA, SelfExtLocusParseLimits,
};
use crate::portable::{Cursor, CursorLimits, is_fingerprint};

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
    let mut c = Cursor::new(
        text,
        CursorLimits {
            input_bytes: limits.max_input_bytes,
            integer_digits: limits.max_integer_digits,
            string_bytes: limits.max_string_bytes,
            ..CursorLimits::NONE
        },
    )?;
    header(&mut c)?;
    let raw = claim(&mut c, &limits)?;
    c.token(b'}')?;
    c.end()?;
    Ok(raw)
}

fn header(c: &mut Cursor) -> Result<(), SelfExtLocusArtifactError> {
    c.token(b'{')?;
    c.key("schema")?;
    let schema = c.string("$.schema")?;
    if schema != SELF_EXT_LOCUS_ARTIFACT_SCHEMA {
        return Err(SelfExtLocusArtifactError::Schema { found: schema });
    }
    let kind = c.next("kind", |c| c.string("$.kind"))?;
    if kind != SELF_EXT_LOCUS_ARTIFACT_KIND {
        return Err(SelfExtLocusArtifactError::Kind { found: kind });
    }
    Ok(())
}

fn claim(
    c: &mut Cursor,
    limits: &SelfExtLocusParseLimits,
) -> Result<RawSelfExtLocusArtifact, SelfExtLocusArtifactError> {
    let checkpoint = c.next("checkpoint", |c| {
        c.raw_object("$.checkpoint", limits.checkpoint.max_input_bytes)
    })?;
    let first_degree = c.next("first_degree", |c| c.usize("$.first_degree"))?;
    let last_degree = c.next("last_degree", |c| c.usize("$.last_degree"))?;
    let vanishing_indices = c.next("vanishing_indices", |c| {
        c.numbers("$.vanishing_indices", limits.max_vanishing_indices)
    })?;
    let fingerprint = c.next("fingerprint", |c| c.string("$.fingerprint"))?;
    if !is_fingerprint(&fingerprint) {
        return Err(SelfExtLocusArtifactError::FingerprintShape);
    }
    Ok(RawSelfExtLocusArtifact {
        checkpoint: checkpoint.to_string(),
        first_degree,
        last_degree,
        vanishing_indices,
        fingerprint,
    })
}

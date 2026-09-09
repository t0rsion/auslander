use super::*;
use crate::certificate::{Certificate, Trace};

fn check(certificate: &Certificate) -> Result<VerifiedCompletion, VerifyError> {
    verify(&certificate.to_canonical_json())
}

fn empty_trace() -> Trace {
    Trace {
        start: vec![],
        steps: vec![],
    }
}

mod accepted;
mod ambiguity;
mod automaton;
mod finiteness;
mod fixtures;
mod normal_words;
mod shape;
mod trace;

//! Independent verification of completion certificates.
//!
//! The verifier accepts a certificate only when it reproduces every claim
//! itself, from the certificate and nothing else. It reuses four modules:
//! [`crate::field`] arithmetic, [`crate::quiver`] paths, the admissible
//! order [`crate::order::ORDER_ID`], and the [`crate::certificate`] data
//! model. Every replay routine, the ambiguity enumeration, and the
//! normal-word automaton are written here from the definitions, so a defect
//! in the completion engine cannot make a bad certificate pass.
//!
//! Two entry points, one verifier. [`verify`] takes untrusted bytes and
//! parses them strictly before anything else. [`verify_certificate`] takes
//! a parsed [`crate::certificate::Certificate`] and runs every check listed
//! on it. The engine calls the typed one, so building an algebra does not
//! serialize and reparse its own certificate. Transport is the only
//! difference: the checks are the same function on the same data either way.
//!
//! The implementation separates certificate shape checks, completion trace
//! replay, and automaton/finiteness checks. The public API stays here.

mod automaton;
mod common;
mod entry;
mod shape;
mod trace;
mod types;

pub use entry::{verify, verify_certificate};
pub use types::{
    CycleWitness, TermDefect, TraceSite, VerifiedCompletion, VerifyError, WitnessDefect,
};

#[cfg(test)]
mod tests;

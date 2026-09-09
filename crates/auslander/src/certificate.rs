//! Completion certificates: the data model shared by the completion engine
//! and the verifier, with canonical JSON encoding and strict decoding.
//!
//! A certificate is plain data. This module checks shape, not mathematics.
//! The verifier replays the traces. Encoding is canonical: one byte-exact
//! format, no timestamps, no machine data. Decoding is strict: duplicate
//! keys, unknown keys, missing keys, trailing commas, wrong types, string
//! escapes, numbers with leading zeros, and containers nested deeper than
//! [`MAX_JSON_DEPTH`] levels are errors. Whitespace between tokens is the
//! only freedom the parser allows.

mod decode;
mod encode;
mod model;
mod parser;

pub use model::{
    AmbiguityEntry, AmbiguityKind, AutomatonData, Certificate, FinitenessData, OriginTerm,
    QuiverData, RelationData, Trace, TraceStep,
};

/// Schema identifier stored in [`Certificate::schema`].
pub const CERT_SCHEMA: &str = "auslander-completion-certificate-v1";

/// Maximum container nesting the parser accepts. The schema needs seven
/// levels at its deepest: an arrow word inside a step of an ambiguity trace.
/// The bound is far above that and still stops stack exhaustion from
/// adversarial bytes.
pub const MAX_JSON_DEPTH: usize = 64;

/// Rejected certificate text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CertParseError {
    /// The text is not JSON in the accepted strict form; `byte` is the
    /// offset of the defect.
    Syntax { byte: usize, message: String },
    /// The JSON is well formed but does not have the certificate shape;
    /// `context` names the enclosing object or field.
    Shape { context: String, message: String },
}

display_error! { error CertParseError {
    Self::Syntax { byte, message } => "invalid certificate JSON at byte {byte}: {message}";
    Self::Shape { context, message } => "invalid certificate shape in {context}: {message}";
} }

impl Certificate {
    /// Serializes the certificate as canonical JSON. Equal certificates
    /// produce equal bytes.
    ///
    /// The format has no whitespace. Numbers are unsigned decimal integers
    /// without leading zeros. Strings are plain ASCII without escapes.
    /// Arrays keep stored order. A term `(c, w)` is the two-element array
    /// `[c, w]`; an arrow `(s, t)` is `[s, t]`. Object keys appear in this
    /// fixed order:
    ///
    /// - certificate: `schema`, `field`, `quiver`, `order`,
    ///   `input_relations`, `basis`, `origin`, `membership`, `ambiguities`,
    ///   `normal_words`, `automaton`, `finiteness`
    /// - quiver: `vertices`, `arrows`
    /// - origin term: `coeff`, `left`, `input_index`, `right`
    /// - trace: `start`, `steps`
    /// - trace step: `word`, `basis_index`, `left`, `right`, `coeff`
    /// - ambiguity: `i`, `j`, `kind`, `offset`, `trace`
    /// - automaton: `states`, `transitions`; a transition `(s, a, n)` is the
    ///   three-element array `[s, a, n]`
    /// - finiteness: exactly one key, `finite` with the literal `true`, or
    ///   `infinite` with keys `prefix`, `cycle`
    ///
    /// # Panics
    /// Panics when a string field contains a quote, a backslash, a control
    /// character, or a non-ASCII character. Certificates built by this
    /// crate only store fixed ASCII identifiers.
    pub fn to_canonical_json(&self) -> String {
        encode::certificate(self)
    }

    /// Parses a certificate from JSON text.
    ///
    /// Decoding is strict. It rejects duplicate keys, unknown keys,
    /// missing keys, trailing commas, wrong types, string escapes,
    /// non-ASCII strings, signs, floats, and numbers with leading zeros.
    /// It rejects containers nested deeper than [`MAX_JSON_DEPTH`] levels
    /// before recursing into them. It accepts the literals `true` and
    /// `false` as tokens, but the schema stores a boolean in exactly one
    /// place, `finiteness.finite`, and only as `true`. `false` anywhere is
    /// a shape error. It allows whitespace between tokens. On canonical
    /// input, `to_canonical_json` reproduces the exact bytes.
    ///
    /// This function checks shape only. It does not check the schema
    /// string, primality, or any mathematical claim. The verifier does.
    pub fn from_json(text: &str) -> Result<Certificate, CertParseError> {
        decode::certificate(&parser::parse(text)?)
    }
}

#[cfg(test)]
mod tests;

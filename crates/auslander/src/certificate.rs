//! Completion certificates: the data model shared by the completion engine
//! and the verifier, with canonical JSON encoding and strict decoding.
//!
//! A certificate is plain data. This module checks shape, not mathematics;
//! the verifier replays the traces. Encoding is canonical: one byte-exact
//! format, no timestamps, no machine data. Decoding is strict: duplicate
//! keys, unknown keys, missing keys, trailing commas, wrong types, string
//! escapes, numbers with leading zeros, and containers nested deeper than
//! [`MAX_JSON_DEPTH`] levels are errors. Whitespace between tokens is the
//! only freedom the parser allows.

use std::fmt;

/// Schema identifier stored in [`Certificate::schema`].
pub const CERT_SCHEMA: &str = "auslander-completion-certificate-v1";

/// Maximum container nesting the parser accepts. The schema needs seven
/// levels at its deepest, an arrow word inside a step of an ambiguity
/// trace, so the bound leaves wide headroom and still stops stack
/// exhaustion from adversarial bytes.
pub const MAX_JSON_DEPTH: usize = 64;

/// A relation as certificate data: terms `(coefficient, word)` with the
/// coefficient as its canonical representative in `0..p` and the word as
/// arrow indices. Terms descend strictly under the sealed order.
pub type RelationData = Vec<(u64, Vec<u32>)>;

/// The quiver as certificate data: vertex count and `(source, target)`
/// arrow pairs in [`crate::quiver::ArrowId`] order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuiverData {
    pub vertices: u32,
    pub arrows: Vec<(u32, u32)>,
}

/// One term of a provenance expression: `coeff · left · r_{input_index} · right`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OriginTerm {
    pub coeff: u64,
    pub left: Vec<u32>,
    pub input_index: usize,
    pub right: Vec<u32>,
}

/// One reduction step: the element under reduction contains `word` as
/// `left · leading(basis[basis_index]) · right`, and the step subtracts
/// `coeff · left · basis[basis_index] · right`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraceStep {
    pub word: Vec<u32>,
    pub basis_index: usize,
    pub left: Vec<u32>,
    pub right: Vec<u32>,
    pub coeff: u64,
}

/// A reduction trace: the start element and the steps that take it to zero.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Trace {
    pub start: RelationData,
    pub steps: Vec<TraceStep>,
}

/// How two leading words form an ambiguity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AmbiguityKind {
    /// A proper suffix of `leading(basis[i])` equals a proper prefix of
    /// `leading(basis[j])`.
    Overlap,
    /// `leading(basis[j])` is a proper factor of `leading(basis[i])`.
    Inclusion,
}

impl AmbiguityKind {
    /// The identifier stored in JSON: `"overlap"` or `"inclusion"`.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Overlap => "overlap",
            Self::Inclusion => "inclusion",
        }
    }
}

/// One ambiguity of the basis leading words, keyed `(i, j, kind, offset)`,
/// with a reduction trace of its composition ending at zero.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AmbiguityEntry {
    pub i: usize,
    pub j: usize,
    pub kind: AmbiguityKind,
    pub offset: usize,
    pub trace: Trace,
}

/// The normal-word automaton as certificate data. `states[v]` is the empty
/// word for each vertex `v` in vertex order; the remaining states are the
/// proper nonempty prefixes of the basis leading words, sorted
/// lexicographically, each stored as its arrow-id word. `transitions` holds
/// sparse `(state, arrow, next state)` triples sorted by state then arrow;
/// a missing pair is noncomposable or completes a leading word.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AutomatonData {
    pub states: Vec<Vec<u32>>,
    pub transitions: Vec<(usize, u32, usize)>,
}

/// The finiteness claim of the certificate. `Infinite` carries a witness:
/// `prefix` reads from the start state of its source vertex to a state on a
/// cycle, and `cycle` returns to exactly that state, so every
/// `prefix·cycle^k` is a normal word.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FinitenessData {
    Finite,
    Infinite { prefix: Vec<u32>, cycle: Vec<u32> },
}

/// A completion certificate. The engine emits it; the verifier checks it
/// from bytes. See the v0.3 design, sections 4 and 5.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Certificate {
    pub schema: String,
    pub field: u64,
    pub quiver: QuiverData,
    pub order: String,
    pub input_relations: Vec<RelationData>,
    pub basis: Vec<RelationData>,
    /// `origin[j]` expands to `basis[j]` as a two-sided combination of the
    /// input relations.
    pub origin: Vec<Vec<OriginTerm>>,
    /// `membership[i]` reduces `input_relations[i]` to zero by `basis`.
    pub membership: Vec<Trace>,
    pub ambiguities: Vec<AmbiguityEntry>,
    /// The claimed normal-word basis of the quotient, in the fixed basis
    /// order of the design, section 6. Empty when `finiteness` claims an
    /// infinite quotient.
    pub normal_words: Vec<Vec<u32>>,
    /// The normal-word automaton over the basis leading words.
    pub automaton: AutomatonData,
    /// Whether the normal-word language is finite, with a cycle witness
    /// when it is not.
    pub finiteness: FinitenessData,
}

impl Certificate {
    /// Serializes the certificate as canonical JSON. One fixed format:
    /// equal certificates produce equal bytes.
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
        let mut out = String::new();
        out.push_str("{\"schema\":");
        push_string(&mut out, &self.schema);
        out.push_str(",\"field\":");
        out.push_str(&self.field.to_string());
        out.push_str(",\"quiver\":{\"vertices\":");
        out.push_str(&self.quiver.vertices.to_string());
        out.push_str(",\"arrows\":");
        push_list(&mut out, &self.quiver.arrows, |out, &(s, t)| {
            out.push('[');
            out.push_str(&s.to_string());
            out.push(',');
            out.push_str(&t.to_string());
            out.push(']');
        });
        out.push_str("},\"order\":");
        push_string(&mut out, &self.order);
        out.push_str(",\"input_relations\":");
        push_list(&mut out, &self.input_relations, push_relation);
        out.push_str(",\"basis\":");
        push_list(&mut out, &self.basis, push_relation);
        out.push_str(",\"origin\":");
        push_list(&mut out, &self.origin, |out, terms| {
            push_list(out, terms, push_origin_term);
        });
        out.push_str(",\"membership\":");
        push_list(&mut out, &self.membership, |out, trace| {
            push_trace(out, trace);
        });
        out.push_str(",\"ambiguities\":");
        push_list(&mut out, &self.ambiguities, push_ambiguity);
        out.push_str(",\"normal_words\":");
        push_list(&mut out, &self.normal_words, |out, word| {
            push_word(out, word);
        });
        out.push_str(",\"automaton\":{\"states\":");
        push_list(&mut out, &self.automaton.states, |out, word| {
            push_word(out, word);
        });
        out.push_str(",\"transitions\":");
        push_list(
            &mut out,
            &self.automaton.transitions,
            |out, &(state, arrow, next)| {
                out.push('[');
                out.push_str(&state.to_string());
                out.push(',');
                out.push_str(&arrow.to_string());
                out.push(',');
                out.push_str(&next.to_string());
                out.push(']');
            },
        );
        out.push_str("},\"finiteness\":");
        match &self.finiteness {
            FinitenessData::Finite => out.push_str("{\"finite\":true}"),
            FinitenessData::Infinite { prefix, cycle } => {
                out.push_str("{\"infinite\":{\"prefix\":");
                push_word(&mut out, prefix);
                out.push_str(",\"cycle\":");
                push_word(&mut out, cycle);
                out.push_str("}}");
            }
        }
        out.push('}');
        out
    }

    /// Parses a certificate from JSON text.
    ///
    /// Decoding is strict. It rejects duplicate keys, unknown keys,
    /// missing keys, trailing commas, wrong types, string escapes,
    /// non-ASCII strings, signs, floats, and numbers with leading zeros.
    /// It rejects containers nested deeper than [`MAX_JSON_DEPTH`] levels
    /// before recursing into them. It accepts the literals `true` and
    /// `false` as tokens, but the schema stores a boolean in exactly one
    /// place, `finiteness.finite`, and only as `true`; `false` anywhere is
    /// a shape error. It allows whitespace between tokens; on canonical
    /// input, `to_canonical_json` reproduces the exact bytes.
    ///
    /// This function checks shape only. It does not check the schema
    /// string, primality, or any mathematical claim; the verifier does.
    pub fn from_json(text: &str) -> Result<Certificate, CertParseError> {
        decode_certificate(&parse(text)?)
    }
}

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

impl fmt::Display for CertParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Syntax { byte, message } => {
                write!(f, "invalid certificate JSON at byte {byte}: {message}")
            }
            Self::Shape { context, message } => {
                write!(f, "invalid certificate shape in {context}: {message}")
            }
        }
    }
}

impl std::error::Error for CertParseError {}

fn push_string(out: &mut String, s: &str) {
    assert!(
        s.chars()
            .all(|c| c.is_ascii() && !c.is_ascii_control() && c != '"' && c != '\\'),
        "certificate strings must be printable ASCII without quotes or backslashes"
    );
    out.push('"');
    out.push_str(s);
    out.push('"');
}

fn push_list<T>(out: &mut String, items: &[T], mut push_item: impl FnMut(&mut String, &T)) {
    out.push('[');
    for (i, item) in items.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        push_item(out, item);
    }
    out.push(']');
}

fn push_word(out: &mut String, word: &[u32]) {
    push_list(out, word, |out, a| out.push_str(&a.to_string()));
}

fn push_relation(out: &mut String, relation: &RelationData) {
    push_list(out, relation, |out, (coeff, word)| {
        out.push('[');
        out.push_str(&coeff.to_string());
        out.push(',');
        push_word(out, word);
        out.push(']');
    });
}

fn push_origin_term(out: &mut String, term: &OriginTerm) {
    out.push_str("{\"coeff\":");
    out.push_str(&term.coeff.to_string());
    out.push_str(",\"left\":");
    push_word(out, &term.left);
    out.push_str(",\"input_index\":");
    out.push_str(&term.input_index.to_string());
    out.push_str(",\"right\":");
    push_word(out, &term.right);
    out.push('}');
}

fn push_trace(out: &mut String, trace: &Trace) {
    out.push_str("{\"start\":");
    push_relation(out, &trace.start);
    out.push_str(",\"steps\":");
    push_list(out, &trace.steps, push_step);
    out.push('}');
}

fn push_step(out: &mut String, step: &TraceStep) {
    out.push_str("{\"word\":");
    push_word(out, &step.word);
    out.push_str(",\"basis_index\":");
    out.push_str(&step.basis_index.to_string());
    out.push_str(",\"left\":");
    push_word(out, &step.left);
    out.push_str(",\"right\":");
    push_word(out, &step.right);
    out.push_str(",\"coeff\":");
    out.push_str(&step.coeff.to_string());
    out.push('}');
}

fn push_ambiguity(out: &mut String, entry: &AmbiguityEntry) {
    out.push_str("{\"i\":");
    out.push_str(&entry.i.to_string());
    out.push_str(",\"j\":");
    out.push_str(&entry.j.to_string());
    out.push_str(",\"kind\":");
    push_string(out, entry.kind.as_str());
    out.push_str(",\"offset\":");
    out.push_str(&entry.offset.to_string());
    out.push_str(",\"trace\":");
    push_trace(out, &entry.trace);
    out.push('}');
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Value {
    Num(u64),
    Str(String),
    Bool(bool),
    Arr(Vec<Value>),
    Obj(Vec<(String, Value)>),
}

fn syntax(byte: usize, message: &str) -> CertParseError {
    CertParseError::Syntax {
        byte,
        message: message.to_string(),
    }
}

fn shape(context: &str, message: String) -> CertParseError {
    CertParseError::Shape {
        context: context.to_string(),
        message,
    }
}

fn parse(text: &str) -> Result<Value, CertParseError> {
    let bytes = text.as_bytes();
    let mut pos = 0;
    let value = parse_value(bytes, &mut pos, 0)?;
    skip_ws(bytes, &mut pos);
    if pos != bytes.len() {
        return Err(syntax(pos, "trailing content"));
    }
    Ok(value)
}

fn skip_ws(bytes: &[u8], pos: &mut usize) {
    while matches!(bytes.get(*pos), Some(b' ' | b'\t' | b'\n' | b'\r')) {
        *pos += 1;
    }
}

fn expect(bytes: &[u8], pos: &mut usize, ch: u8) -> Result<(), CertParseError> {
    skip_ws(bytes, pos);
    if bytes.get(*pos) == Some(&ch) {
        *pos += 1;
        Ok(())
    } else {
        Err(syntax(*pos, &format!("expected '{}'", ch as char)))
    }
}

/// `depth` counts the containers enclosing this value. A container that
/// would sit deeper than [`MAX_JSON_DEPTH`] levels is rejected before the
/// parser recurses into it.
fn parse_value(bytes: &[u8], pos: &mut usize, depth: usize) -> Result<Value, CertParseError> {
    skip_ws(bytes, pos);
    match bytes.get(*pos) {
        Some(b'{') => {
            check_depth(bytes, pos, depth)?;
            parse_obj(bytes, pos, depth + 1)
        }
        Some(b'[') => {
            check_depth(bytes, pos, depth)?;
            parse_arr(bytes, pos, depth + 1)
        }
        Some(b'"') => Ok(Value::Str(parse_string(bytes, pos)?)),
        Some(b'0'..=b'9') => parse_num(bytes, pos),
        Some(b't' | b'f') => parse_bool(bytes, pos),
        _ => Err(syntax(
            *pos,
            "expected an object, array, string, boolean, or unsigned integer",
        )),
    }
}

fn check_depth(bytes: &[u8], pos: &mut usize, depth: usize) -> Result<(), CertParseError> {
    let _ = bytes;
    if depth >= MAX_JSON_DEPTH {
        return Err(syntax(
            *pos,
            &format!("containers nest deeper than {MAX_JSON_DEPTH} levels"),
        ));
    }
    Ok(())
}

fn parse_bool(bytes: &[u8], pos: &mut usize) -> Result<Value, CertParseError> {
    for (literal, value) in [(&b"true"[..], true), (&b"false"[..], false)] {
        if bytes[*pos..].starts_with(literal) {
            *pos += literal.len();
            return Ok(Value::Bool(value));
        }
    }
    Err(syntax(*pos, "expected 'true' or 'false'"))
}

fn parse_num(bytes: &[u8], pos: &mut usize) -> Result<Value, CertParseError> {
    let start = *pos;
    while matches!(bytes.get(*pos), Some(b'0'..=b'9')) {
        *pos += 1;
    }
    let digits = &bytes[start..*pos];
    if digits.len() > 1 && digits[0] == b'0' {
        return Err(syntax(start, "number has a leading zero"));
    }
    if matches!(bytes.get(*pos), Some(b'.' | b'e' | b'E')) {
        return Err(syntax(*pos, "number must be an unsigned integer"));
    }
    std::str::from_utf8(digits)
        .expect("digits are ASCII")
        .parse()
        .map(Value::Num)
        .map_err(|_| syntax(start, "number does not fit in u64"))
}

fn parse_string(bytes: &[u8], pos: &mut usize) -> Result<String, CertParseError> {
    expect(bytes, pos, b'"')?;
    let start = *pos;
    loop {
        match bytes.get(*pos) {
            Some(b'"') => {
                let s = std::str::from_utf8(&bytes[start..*pos]).expect("checked ASCII");
                *pos += 1;
                return Ok(s.to_string());
            }
            Some(b'\\') => return Err(syntax(*pos, "escape sequences are not canonical")),
            Some(&c) if c < 0x20 => return Err(syntax(*pos, "control character in string")),
            Some(&c) if c >= 0x80 => return Err(syntax(*pos, "non-ASCII character in string")),
            Some(_) => *pos += 1,
            None => return Err(syntax(*pos, "unterminated string")),
        }
    }
}

fn parse_arr(bytes: &[u8], pos: &mut usize, depth: usize) -> Result<Value, CertParseError> {
    expect(bytes, pos, b'[')?;
    let mut items = Vec::new();
    skip_ws(bytes, pos);
    if bytes.get(*pos) == Some(&b']') {
        *pos += 1;
        return Ok(Value::Arr(items));
    }
    loop {
        items.push(parse_value(bytes, pos, depth)?);
        skip_ws(bytes, pos);
        match bytes.get(*pos) {
            Some(b',') => *pos += 1,
            Some(b']') => {
                *pos += 1;
                return Ok(Value::Arr(items));
            }
            _ => return Err(syntax(*pos, "expected ',' or ']'")),
        }
    }
}

fn parse_obj(bytes: &[u8], pos: &mut usize, depth: usize) -> Result<Value, CertParseError> {
    expect(bytes, pos, b'{')?;
    let mut pairs: Vec<(String, Value)> = Vec::new();
    let mut keys: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    skip_ws(bytes, pos);
    if bytes.get(*pos) == Some(&b'}') {
        *pos += 1;
        return Ok(Value::Obj(pairs));
    }
    loop {
        skip_ws(bytes, pos);
        let key = parse_string(bytes, pos)?;
        if !keys.insert(key.clone()) {
            return Err(syntax(*pos, &format!("duplicate key {key:?}")));
        }
        expect(bytes, pos, b':')?;
        let value = parse_value(bytes, pos, depth)?;
        pairs.push((key, value));
        skip_ws(bytes, pos);
        match bytes.get(*pos) {
            Some(b',') => *pos += 1,
            Some(b'}') => {
                *pos += 1;
                return Ok(Value::Obj(pairs));
            }
            _ => return Err(syntax(*pos, "expected ',' or '}'")),
        }
    }
}

/// The object's values in the order of `keys`. Rejects unknown keys and
/// missing keys; the parser already rejects duplicates.
fn obj_fields<'a>(
    value: &'a Value,
    context: &str,
    keys: &[&str],
) -> Result<Vec<&'a Value>, CertParseError> {
    let Value::Obj(pairs) = value else {
        return Err(shape(context, "expected an object".to_string()));
    };
    for (k, _) in pairs {
        if !keys.contains(&k.as_str()) {
            return Err(shape(context, format!("unknown key {k:?}")));
        }
    }
    keys.iter()
        .map(|key| {
            pairs
                .iter()
                .find(|(k, _)| k == key)
                .map(|(_, v)| v)
                .ok_or_else(|| shape(context, format!("missing key {key:?}")))
        })
        .collect()
}

fn as_u64(value: &Value, context: &str) -> Result<u64, CertParseError> {
    match value {
        Value::Num(n) => Ok(*n),
        _ => Err(shape(context, "expected an unsigned integer".to_string())),
    }
}

fn as_u32(value: &Value, context: &str) -> Result<u32, CertParseError> {
    u32::try_from(as_u64(value, context)?)
        .map_err(|_| shape(context, "number does not fit in u32".to_string()))
}

fn as_usize(value: &Value, context: &str) -> Result<usize, CertParseError> {
    usize::try_from(as_u64(value, context)?)
        .map_err(|_| shape(context, "number does not fit in usize".to_string()))
}

fn as_string(value: &Value, context: &str) -> Result<String, CertParseError> {
    match value {
        Value::Str(s) => Ok(s.clone()),
        _ => Err(shape(context, "expected a string".to_string())),
    }
}

fn as_arr<'a>(value: &'a Value, context: &str) -> Result<&'a [Value], CertParseError> {
    match value {
        Value::Arr(items) => Ok(items),
        _ => Err(shape(context, "expected an array".to_string())),
    }
}

fn decode_word(value: &Value, context: &str) -> Result<Vec<u32>, CertParseError> {
    as_arr(value, context)?
        .iter()
        .map(|item| as_u32(item, context))
        .collect()
}

fn decode_words(value: &Value, context: &str) -> Result<Vec<Vec<u32>>, CertParseError> {
    as_arr(value, context)?
        .iter()
        .map(|item| decode_word(item, context))
        .collect()
}

fn decode_relation(value: &Value, context: &str) -> Result<RelationData, CertParseError> {
    as_arr(value, context)?
        .iter()
        .map(|term| {
            let parts = as_arr(term, context)?;
            let [coeff, word] = parts else {
                return Err(shape(
                    context,
                    "expected a [coefficient, word] pair".to_string(),
                ));
            };
            Ok((as_u64(coeff, context)?, decode_word(word, context)?))
        })
        .collect()
}

fn decode_relations(value: &Value, context: &str) -> Result<Vec<RelationData>, CertParseError> {
    as_arr(value, context)?
        .iter()
        .map(|item| decode_relation(item, context))
        .collect()
}

fn decode_quiver(value: &Value) -> Result<QuiverData, CertParseError> {
    let fields = obj_fields(value, "quiver", &["vertices", "arrows"])?;
    let arrows = as_arr(fields[1], "quiver.arrows")?
        .iter()
        .map(|pair| {
            let parts = as_arr(pair, "quiver.arrows")?;
            let [source, target] = parts else {
                return Err(shape(
                    "quiver.arrows",
                    "expected a [source, target] pair".to_string(),
                ));
            };
            Ok((
                as_u32(source, "quiver.arrows")?,
                as_u32(target, "quiver.arrows")?,
            ))
        })
        .collect::<Result<_, _>>()?;
    Ok(QuiverData {
        vertices: as_u32(fields[0], "quiver.vertices")?,
        arrows,
    })
}

fn decode_origin_term(value: &Value) -> Result<OriginTerm, CertParseError> {
    let fields = obj_fields(
        value,
        "origin term",
        &["coeff", "left", "input_index", "right"],
    )?;
    Ok(OriginTerm {
        coeff: as_u64(fields[0], "origin term coeff")?,
        left: decode_word(fields[1], "origin term left")?,
        input_index: as_usize(fields[2], "origin term input_index")?,
        right: decode_word(fields[3], "origin term right")?,
    })
}

fn decode_step(value: &Value) -> Result<TraceStep, CertParseError> {
    let fields = obj_fields(
        value,
        "trace step",
        &["word", "basis_index", "left", "right", "coeff"],
    )?;
    Ok(TraceStep {
        word: decode_word(fields[0], "trace step word")?,
        basis_index: as_usize(fields[1], "trace step basis_index")?,
        left: decode_word(fields[2], "trace step left")?,
        right: decode_word(fields[3], "trace step right")?,
        coeff: as_u64(fields[4], "trace step coeff")?,
    })
}

fn decode_trace(value: &Value) -> Result<Trace, CertParseError> {
    let fields = obj_fields(value, "trace", &["start", "steps"])?;
    Ok(Trace {
        start: decode_relation(fields[0], "trace start")?,
        steps: as_arr(fields[1], "trace steps")?
            .iter()
            .map(decode_step)
            .collect::<Result<_, _>>()?,
    })
}

fn decode_kind(value: &Value) -> Result<AmbiguityKind, CertParseError> {
    match as_string(value, "ambiguity kind")?.as_str() {
        "overlap" => Ok(AmbiguityKind::Overlap),
        "inclusion" => Ok(AmbiguityKind::Inclusion),
        other => Err(shape(
            "ambiguity kind",
            format!("expected \"overlap\" or \"inclusion\", got {other:?}"),
        )),
    }
}

fn decode_ambiguity(value: &Value) -> Result<AmbiguityEntry, CertParseError> {
    let fields = obj_fields(value, "ambiguity", &["i", "j", "kind", "offset", "trace"])?;
    Ok(AmbiguityEntry {
        i: as_usize(fields[0], "ambiguity i")?,
        j: as_usize(fields[1], "ambiguity j")?,
        kind: decode_kind(fields[2])?,
        offset: as_usize(fields[3], "ambiguity offset")?,
        trace: decode_trace(fields[4])?,
    })
}

fn decode_automaton(value: &Value) -> Result<AutomatonData, CertParseError> {
    let fields = obj_fields(value, "automaton", &["states", "transitions"])?;
    let transitions = as_arr(fields[1], "automaton.transitions")?
        .iter()
        .map(|triple| {
            let parts = as_arr(triple, "automaton.transitions")?;
            let [state, arrow, next] = parts else {
                return Err(shape(
                    "automaton.transitions",
                    "expected a [state, arrow, next state] triple".to_string(),
                ));
            };
            Ok((
                as_usize(state, "automaton.transitions")?,
                as_u32(arrow, "automaton.transitions")?,
                as_usize(next, "automaton.transitions")?,
            ))
        })
        .collect::<Result<_, _>>()?;
    Ok(AutomatonData {
        states: decode_words(fields[0], "automaton.states")?,
        transitions,
    })
}

fn decode_finiteness(value: &Value) -> Result<FinitenessData, CertParseError> {
    let Value::Obj(pairs) = value else {
        return Err(shape("finiteness", "expected an object".to_string()));
    };
    match pairs.as_slice() {
        [(key, flag)] if key == "finite" => match flag {
            Value::Bool(true) => Ok(FinitenessData::Finite),
            _ => Err(shape(
                "finiteness",
                "the value of \"finite\" must be the literal true".to_string(),
            )),
        },
        [(key, witness)] if key == "infinite" => {
            let fields = obj_fields(witness, "finiteness.infinite", &["prefix", "cycle"])?;
            Ok(FinitenessData::Infinite {
                prefix: decode_word(fields[0], "finiteness.infinite.prefix")?,
                cycle: decode_word(fields[1], "finiteness.infinite.cycle")?,
            })
        }
        _ => Err(shape(
            "finiteness",
            "expected exactly one key, \"finite\" or \"infinite\"".to_string(),
        )),
    }
}

fn decode_certificate(value: &Value) -> Result<Certificate, CertParseError> {
    let fields = obj_fields(
        value,
        "certificate",
        &[
            "schema",
            "field",
            "quiver",
            "order",
            "input_relations",
            "basis",
            "origin",
            "membership",
            "ambiguities",
            "normal_words",
            "automaton",
            "finiteness",
        ],
    )?;
    Ok(Certificate {
        schema: as_string(fields[0], "schema")?,
        field: as_u64(fields[1], "field")?,
        quiver: decode_quiver(fields[2])?,
        order: as_string(fields[3], "order")?,
        input_relations: decode_relations(fields[4], "input_relations")?,
        basis: decode_relations(fields[5], "basis")?,
        origin: as_arr(fields[6], "origin")?
            .iter()
            .map(|terms| {
                as_arr(terms, "origin")?
                    .iter()
                    .map(decode_origin_term)
                    .collect()
            })
            .collect::<Result<_, _>>()?,
        membership: as_arr(fields[7], "membership")?
            .iter()
            .map(decode_trace)
            .collect::<Result<_, _>>()?,
        ambiguities: as_arr(fields[8], "ambiguities")?
            .iter()
            .map(decode_ambiguity)
            .collect::<Result<_, _>>()?,
        normal_words: decode_words(fields[9], "normal_words")?,
        automaton: decode_automaton(fields[10])?,
        finiteness: decode_finiteness(fields[11])?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::order::ORDER_ID;

    fn sample() -> Certificate {
        Certificate {
            schema: CERT_SCHEMA.to_string(),
            field: 2,
            quiver: QuiverData {
                vertices: 1,
                arrows: vec![(0, 0)],
            },
            order: ORDER_ID.to_string(),
            input_relations: vec![vec![(1, vec![0, 0])]],
            basis: vec![vec![(1, vec![0, 0])]],
            origin: vec![vec![OriginTerm {
                coeff: 1,
                left: vec![],
                input_index: 0,
                right: vec![],
            }]],
            membership: vec![Trace {
                start: vec![(1, vec![0, 0])],
                steps: vec![TraceStep {
                    word: vec![0, 0],
                    basis_index: 0,
                    left: vec![],
                    right: vec![],
                    coeff: 1,
                }],
            }],
            ambiguities: vec![AmbiguityEntry {
                i: 0,
                j: 0,
                kind: AmbiguityKind::Overlap,
                offset: 1,
                trace: Trace {
                    start: vec![],
                    steps: vec![],
                },
            }],
            normal_words: vec![vec![], vec![0]],
            automaton: AutomatonData {
                states: vec![vec![], vec![0]],
                transitions: vec![(0, 0, 1)],
            },
            finiteness: FinitenessData::Finite,
        }
    }

    const SAMPLE_JSON: &str = concat!(
        "{\"schema\":\"auslander-completion-certificate-v1\",\"field\":2,",
        "\"quiver\":{\"vertices\":1,\"arrows\":[[0,0]]},",
        "\"order\":\"deglex-arrowid-v1\",",
        "\"input_relations\":[[[1,[0,0]]]],",
        "\"basis\":[[[1,[0,0]]]],",
        "\"origin\":[[{\"coeff\":1,\"left\":[],\"input_index\":0,\"right\":[]}]],",
        "\"membership\":[{\"start\":[[1,[0,0]]],\"steps\":",
        "[{\"word\":[0,0],\"basis_index\":0,\"left\":[],\"right\":[],\"coeff\":1}]}],",
        "\"ambiguities\":[{\"i\":0,\"j\":0,\"kind\":\"overlap\",\"offset\":1,",
        "\"trace\":{\"start\":[],\"steps\":[]}}],",
        "\"normal_words\":[[],[0]],",
        "\"automaton\":{\"states\":[[],[0]],\"transitions\":[[0,0,1]]},",
        "\"finiteness\":{\"finite\":true}}"
    );

    #[test]
    fn canonical_json_is_byte_exact() {
        assert_eq!(sample().to_canonical_json(), SAMPLE_JSON);
    }

    #[test]
    fn json_round_trip_reproduces_the_certificate() {
        let c = sample();
        assert_eq!(Certificate::from_json(&c.to_canonical_json()), Ok(c));
    }

    #[test]
    fn canonical_text_round_trips_byte_exact() {
        let parsed = Certificate::from_json(SAMPLE_JSON).unwrap();
        assert_eq!(parsed.to_canonical_json(), SAMPLE_JSON);
    }

    #[test]
    fn whitespace_between_tokens_is_accepted() {
        let spaced = SAMPLE_JSON
            .replace("\"field\":2,", "\"field\" : 2 ,\n")
            .replace("\"normal_words\":", " \"normal_words\"\t: ");
        assert_eq!(Certificate::from_json(&spaced), Ok(sample()));
    }

    #[test]
    fn duplicate_key_rejected() {
        let text = SAMPLE_JSON.replacen("\"field\":2,", "\"field\":2,\"field\":2,", 1);
        assert!(matches!(
            Certificate::from_json(&text),
            Err(CertParseError::Syntax { .. })
        ));
    }

    #[test]
    fn unknown_key_rejected() {
        let text = SAMPLE_JSON.replacen("\"field\":2,", "\"field\":2,\"extra\":3,", 1);
        assert!(matches!(
            Certificate::from_json(&text),
            Err(CertParseError::Shape { .. })
        ));
        let nested = SAMPLE_JSON.replacen("{\"vertices\":1,", "{\"vertices\":1,\"loops\":0,", 1);
        assert!(matches!(
            Certificate::from_json(&nested),
            Err(CertParseError::Shape { .. })
        ));
    }

    #[test]
    fn missing_key_rejected() {
        let text = SAMPLE_JSON.replacen("\"order\":\"deglex-arrowid-v1\",", "", 1);
        assert!(matches!(
            Certificate::from_json(&text),
            Err(CertParseError::Shape { .. })
        ));
    }

    #[test]
    fn trailing_comma_rejected() {
        let text = SAMPLE_JSON.replacen(
            "\"normal_words\":[[],[0]],",
            "\"normal_words\":[[],[0],],",
            1,
        );
        assert!(matches!(
            Certificate::from_json(&text),
            Err(CertParseError::Syntax { .. })
        ));
    }

    #[test]
    fn wrong_type_rejected() {
        let text = SAMPLE_JSON.replacen("\"field\":2,", "\"field\":\"2\",", 1);
        assert!(matches!(
            Certificate::from_json(&text),
            Err(CertParseError::Shape { .. })
        ));
    }

    #[test]
    fn truncated_input_rejected() {
        for len in [0, 1, SAMPLE_JSON.len() / 2, SAMPLE_JSON.len() - 1] {
            assert!(
                matches!(
                    Certificate::from_json(&SAMPLE_JSON[..len]),
                    Err(CertParseError::Syntax { .. })
                ),
                "prefix of length {len}"
            );
        }
    }

    #[test]
    fn leading_zero_number_rejected() {
        let text = SAMPLE_JSON.replacen("\"field\":2,", "\"field\":02,", 1);
        assert!(matches!(
            Certificate::from_json(&text),
            Err(CertParseError::Syntax { .. })
        ));
    }

    #[test]
    fn float_and_escape_rejected() {
        let float = SAMPLE_JSON.replacen("\"field\":2,", "\"field\":2.0,", 1);
        assert!(matches!(
            Certificate::from_json(&float),
            Err(CertParseError::Syntax { .. })
        ));
        let escape = SAMPLE_JSON.replacen("\"kind\":\"overlap\"", "\"kind\":\"over\\lap\"", 1);
        assert!(matches!(
            Certificate::from_json(&escape),
            Err(CertParseError::Syntax { .. })
        ));
    }

    #[test]
    fn trailing_content_rejected() {
        let text = format!("{SAMPLE_JSON} ");
        assert_eq!(Certificate::from_json(&text), Ok(sample()));
        let text = format!("{SAMPLE_JSON}0");
        assert!(matches!(
            Certificate::from_json(&text),
            Err(CertParseError::Syntax { .. })
        ));
    }

    #[test]
    fn bad_kind_rejected() {
        let text = SAMPLE_JSON.replacen("\"kind\":\"overlap\"", "\"kind\":\"overlaps\"", 1);
        assert!(matches!(
            Certificate::from_json(&text),
            Err(CertParseError::Shape { .. })
        ));
    }

    #[test]
    fn arrow_index_above_u32_rejected() {
        let text = SAMPLE_JSON.replacen(
            "\"normal_words\":[[],[0]]",
            "\"normal_words\":[[],[4294967296]]",
            1,
        );
        assert!(matches!(
            Certificate::from_json(&text),
            Err(CertParseError::Shape { .. })
        ));
    }

    #[test]
    fn inclusion_kind_round_trips() {
        let mut c = sample();
        c.ambiguities[0].kind = AmbiguityKind::Inclusion;
        assert_eq!(Certificate::from_json(&c.to_canonical_json()), Ok(c));
    }

    #[test]
    fn infinite_finiteness_round_trips() {
        let mut c = sample();
        c.finiteness = FinitenessData::Infinite {
            prefix: vec![0],
            cycle: vec![0, 0],
        };
        let json = c.to_canonical_json();
        assert!(json.contains("\"finiteness\":{\"infinite\":{\"prefix\":[0],\"cycle\":[0,0]}}"));
        assert_eq!(Certificate::from_json(&json), Ok(c));
    }

    #[test]
    fn finiteness_with_false_rejected() {
        let text = SAMPLE_JSON.replacen("{\"finite\":true}", "{\"finite\":false}", 1);
        assert!(matches!(
            Certificate::from_json(&text),
            Err(CertParseError::Shape { .. })
        ));
    }

    #[test]
    fn false_outside_finiteness_rejected() {
        let text = SAMPLE_JSON.replacen("\"field\":2,", "\"field\":false,", 1);
        assert!(matches!(
            Certificate::from_json(&text),
            Err(CertParseError::Shape { .. })
        ));
    }

    #[test]
    fn finiteness_with_both_keys_rejected() {
        let text = SAMPLE_JSON.replacen(
            "{\"finite\":true}",
            "{\"finite\":true,\"infinite\":{\"prefix\":[],\"cycle\":[0]}}",
            1,
        );
        assert!(matches!(
            Certificate::from_json(&text),
            Err(CertParseError::Shape { .. })
        ));
    }

    #[test]
    fn malformed_transition_triple_rejected() {
        let text = SAMPLE_JSON.replacen("\"transitions\":[[0,0,1]]", "\"transitions\":[[0,0]]", 1);
        assert!(matches!(
            Certificate::from_json(&text),
            Err(CertParseError::Shape { .. })
        ));
    }

    fn nested_arrays(depth: usize) -> String {
        let mut text = String::new();
        for _ in 0..depth {
            text.push('[');
        }
        for _ in 0..depth {
            text.push(']');
        }
        text
    }

    #[test]
    fn container_depth_at_the_limit_parses() {
        // Structurally fine at depth 64; the value is no certificate, so the
        // rejection is a shape error, not a syntax error.
        assert!(matches!(
            Certificate::from_json(&nested_arrays(MAX_JSON_DEPTH)),
            Err(CertParseError::Shape { .. })
        ));
    }

    #[test]
    fn container_depth_above_the_limit_rejected() {
        assert!(matches!(
            Certificate::from_json(&nested_arrays(MAX_JSON_DEPTH + 1)),
            Err(CertParseError::Syntax { .. })
        ));
    }
}

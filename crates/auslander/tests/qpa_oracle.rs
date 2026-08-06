//! Differential harness against QPA. Design notes in `tests/qpa-oracle/README.md`.
//!
//! The oracle is `tests/qpa-oracle/qpa_expected.json` (schema v5). Only a real
//! GAP+QPA run of `generate_fixtures.g` writes it. Every fixture carries its own
//! prime field and its full presentation. The harness rebuilds each algebra from
//! that presentation through `Relation`, `Presentation`, and `Algebra::new`, so
//! the library consumes the same input QPA saw. The always-on test compares the
//! library against the committed truth, and a missing file is a hard failure.
//! `native_snapshot.json` is a drift snapshot of this library's own output, not
//! an oracle. `QPA_ORACLE_WRITE=1` rewrites the snapshot and never touches
//! `qpa_expected.json`. `QPA_ORACLE=1` invokes GAP itself and fails hard when
//! GAP or QPA is unavailable, or when any value disagrees.
//!
//! The JSON layer is hand-rolled. The schema is small and fixed, so a writer
//! built on `format!` and a strict recursive-descent reader replace a serde
//! dependency. The reader rejects unknown keys, duplicate keys, missing fields,
//! and malformed values.

use std::collections::{BTreeMap, HashMap};
use std::env;
use std::fs;
#[cfg(unix)]
use std::path::Path;
use std::path::PathBuf;
#[cfg(unix)]
use std::process::{Command, Stdio};
use std::sync::{Arc, Mutex, OnceLock};

use auslander::algebra::Algebra;
use auslander::ar::{Tau, tau};
use auslander::completion::CompletionLimits;
use auslander::decompose::{KrullSchmidtOutcome, krull_schmidt};
use auslander::ext::ext_table;
use auslander::field::{Fp, PrimeField};
use auslander::injective::injective_dimension;
use auslander::module::{Module, direct_sum};
use auslander::opposite::opposite;
use auslander::quiver::{ArrowId, Quiver};
use auslander::radical::radical;
use auslander::relation::{Presentation, Relation};
use auslander::resolution::{Bounded, projective_dimension};

const SCHEMA: &str = "auslander-qpa-oracle-v5";
const MAX_EXT_DEGREE: usize = 4;
/// Projective and injective dimensions are recorded up to these bounds. A
/// simple whose dimension exceeds the bound is stored as `{"at_least": bound
/// + 1}`, the exact payload of the `Bounded::AtLeast` the library returns for
/// the same bound. QPA's `ProjDimensionOfModule` and `InjDimensionOfModule`
/// refuse the same way and return `false`.
const PROJDIM_BOUND: usize = 6;
const INJDIM_BOUND: usize = 6;
const ORDER_ID: &str = "deglex-arrowid-v1";
const DECOMPOSITION_MODULE: &str = "radicals-of-projectives";

const ROOT_KEYS: [&str; 7] = [
    "schema",
    "convention",
    "max_ext_degree",
    "projdim_bound",
    "injdim_bound",
    "provenance",
    "fixtures",
];
const PROVENANCE_KEYS: [&str; 3] = ["gap_version", "qpa_version", "command"];
const FIXTURE_KEYS: [&str; 17] = [
    "family",
    "case",
    "field",
    "presentation_id",
    "ideal_id",
    "order",
    "quiver",
    "relations",
    "dim",
    "cartan",
    "injectives",
    "projdim",
    "injdim",
    "tau",
    "tau_injectives",
    "decomposition",
    "ext",
];

/// Every fixture the oracle file must contain, as (family, case). A document
/// that drops or renames a fixture fails the comparison.
const FIXTURE_MANIFEST: [(&str, &str); 23] = [
    ("linear-an-2", "f5"),
    ("linear-an-3", "f5"),
    ("d4-star", "f5"),
    ("dual-numbers", "f5"),
    ("truncated-poly-3", "f5"),
    ("a3-mod-ab", "f5"),
    ("kronecker-2", "f5"),
    ("radical-square-zero-cycle-3", "f5"),
    ("linear-nakayama-3-2-1", "f5"),
    ("linear-nakayama-2-2-1", "f5"),
    ("cyclic-nakayama-3-3-3", "f5"),
    ("gentle-tree", "f5"),
    ("commutative-square", "f2"),
    ("commutative-square", "f5"),
    ("preprojective-a3", "f2"),
    ("preprojective-a3", "f3"),
    ("self-overlap", "f3"),
    ("inclusion-ambiguity", "f2"),
    ("inhomogeneous", "f5"),
    ("redundant-presentation", "f5"),
    ("permuted-presentation", "f5"),
    ("characteristic-sensitive", "f2"),
    ("characteristic-sensitive", "f3"),
];

/// Minimal JSON reader for the oracle schema. Strict where corruption could
/// hide: duplicate object keys and trailing commas are parse errors. Only
/// whitespace is free-form. Numbers are integers with an optional sign, which
/// is all the schema needs; the only signed values are relation coefficients.
mod json {
    #[derive(Debug, Clone, PartialEq)]
    pub enum Value {
        Num(i64),
        Bool(bool),
        Str(String),
        Arr(Vec<Value>),
        Obj(Vec<(String, Value)>),
    }

    impl Value {
        pub fn as_usize(&self) -> Option<usize> {
            match self {
                Value::Num(n) => usize::try_from(*n).ok(),
                _ => None,
            }
        }

        pub fn as_arr(&self) -> Option<&[Value]> {
            match self {
                Value::Arr(items) => Some(items),
                _ => None,
            }
        }
    }

    pub fn parse(text: &str) -> Result<Value, String> {
        let bytes = text.as_bytes();
        let mut pos = 0;
        let value = parse_value(bytes, &mut pos)?;
        skip_ws(bytes, &mut pos);
        if pos != bytes.len() {
            return Err(format!("trailing content at byte {pos}"));
        }
        Ok(value)
    }

    fn skip_ws(bytes: &[u8], pos: &mut usize) {
        while *pos < bytes.len() && bytes[*pos].is_ascii_whitespace() {
            *pos += 1;
        }
    }

    fn expect(bytes: &[u8], pos: &mut usize, ch: u8) -> Result<(), String> {
        skip_ws(bytes, pos);
        if bytes.get(*pos) == Some(&ch) {
            *pos += 1;
            Ok(())
        } else {
            Err(format!(
                "expected '{}' at byte {}, found {:?}",
                ch as char,
                pos,
                bytes.get(*pos).map(|&b| b as char)
            ))
        }
    }

    fn parse_value(bytes: &[u8], pos: &mut usize) -> Result<Value, String> {
        skip_ws(bytes, pos);
        match bytes.get(*pos) {
            Some(b'{') => parse_obj(bytes, pos),
            Some(b'[') => parse_arr(bytes, pos),
            Some(b'"') => Ok(Value::Str(parse_str(bytes, pos)?)),
            Some(b'-' | b'0'..=b'9') => parse_num(bytes, pos),
            Some(b't' | b'f') => parse_bool(bytes, pos),
            other => Err(format!(
                "unexpected {:?} at byte {}",
                other.map(|&b| b as char),
                pos
            )),
        }
    }

    fn parse_bool(bytes: &[u8], pos: &mut usize) -> Result<Value, String> {
        for (word, value) in [("true", true), ("false", false)] {
            if bytes[*pos..].starts_with(word.as_bytes()) {
                *pos += word.len();
                return Ok(Value::Bool(value));
            }
        }
        Err(format!("bad keyword at byte {pos}"))
    }

    fn parse_num(bytes: &[u8], pos: &mut usize) -> Result<Value, String> {
        let start = *pos;
        if bytes.get(*pos) == Some(&b'-') {
            *pos += 1;
        }
        while matches!(bytes.get(*pos), Some(b'0'..=b'9')) {
            *pos += 1;
        }
        std::str::from_utf8(&bytes[start..*pos])
            .ok()
            .and_then(|s| s.parse().ok())
            .map(Value::Num)
            .ok_or_else(|| format!("bad number at byte {start}"))
    }

    fn parse_str(bytes: &[u8], pos: &mut usize) -> Result<String, String> {
        expect(bytes, pos, b'"')?;
        let mut out = String::new();
        loop {
            match bytes.get(*pos) {
                Some(b'"') => {
                    *pos += 1;
                    return Ok(out);
                }
                Some(b'\\') => {
                    *pos += 1;
                    match bytes.get(*pos) {
                        Some(b'n') => out.push('\n'),
                        Some(b't') => out.push('\t'),
                        Some(&c) => out.push(c as char),
                        None => return Err("unterminated escape".to_string()),
                    }
                    *pos += 1;
                }
                Some(&c) => {
                    out.push(c as char);
                    *pos += 1;
                }
                None => return Err("unterminated string".to_string()),
            }
        }
    }

    fn parse_arr(bytes: &[u8], pos: &mut usize) -> Result<Value, String> {
        expect(bytes, pos, b'[')?;
        let mut items = Vec::new();
        skip_ws(bytes, pos);
        if bytes.get(*pos) == Some(&b']') {
            *pos += 1;
            return Ok(Value::Arr(items));
        }
        loop {
            items.push(parse_value(bytes, pos)?);
            skip_ws(bytes, pos);
            match bytes.get(*pos) {
                Some(b',') => *pos += 1,
                Some(b']') => {
                    *pos += 1;
                    return Ok(Value::Arr(items));
                }
                other => {
                    return Err(format!(
                        "expected ',' or ']' at byte {}, found {:?}",
                        pos,
                        other.map(|&b| b as char)
                    ));
                }
            }
        }
    }

    fn parse_obj(bytes: &[u8], pos: &mut usize) -> Result<Value, String> {
        expect(bytes, pos, b'{')?;
        let mut pairs: Vec<(String, Value)> = Vec::new();
        skip_ws(bytes, pos);
        if bytes.get(*pos) == Some(&b'}') {
            *pos += 1;
            return Ok(Value::Obj(pairs));
        }
        loop {
            skip_ws(bytes, pos);
            let key = parse_str(bytes, pos)?;
            if pairs.iter().any(|(k, _)| *k == key) {
                return Err(format!("duplicate key {key:?} at byte {pos}"));
            }
            expect(bytes, pos, b':')?;
            let value = parse_value(bytes, pos)?;
            pairs.push((key, value));
            skip_ws(bytes, pos);
            match bytes.get(*pos) {
                Some(b',') => *pos += 1,
                Some(b'}') => {
                    *pos += 1;
                    return Ok(Value::Obj(pairs));
                }
                other => {
                    return Err(format!(
                        "expected ',' or '}}' at byte {}, found {:?}",
                        pos,
                        other.map(|&b| b as char)
                    ));
                }
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
enum DimOutcome {
    Finite(usize),
    AtLeast(usize),
}

#[derive(Clone, Debug, PartialEq)]
enum TauOutcome {
    Projective,
    Dimvec(Vec<usize>),
}

#[derive(Clone, Debug, PartialEq)]
struct ArrowSpec {
    name: String,
    source: u32,
    target: u32,
}

#[derive(Clone, Debug, PartialEq)]
struct QuiverSpec {
    num_vertices: u32,
    arrows: Vec<ArrowSpec>,
}

/// One relation term as written: an integer coefficient and a path of arrow
/// indices. Coefficients stay raw here; the documented mod-p reduction runs
/// when the algebra is built.
#[derive(Clone, Debug, PartialEq)]
struct TermSpec {
    coeff: i64,
    path: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq)]
struct Fixture {
    family: String,
    case: String,
    field: u64,
    presentation_id: String,
    ideal_id: String,
    quiver: QuiverSpec,
    relations: Vec<Vec<TermSpec>>,
    dim: usize,
    cartan: Vec<Vec<usize>>,
    injectives: Vec<Vec<usize>>,
    projdim: Vec<DimOutcome>,
    injdim: Vec<DimOutcome>,
    tau: Vec<TauOutcome>,
    tau_injectives: Vec<TauOutcome>,
    decomposition: Vec<(Vec<usize>, usize)>,
    ext: Vec<Vec<Vec<usize>>>,
}

/// A validated oracle document. Provenance is kept as key/value pairs so the
/// live mode's whole-document equality covers it.
#[derive(Clone, Debug, PartialEq)]
struct Document {
    left_convention: bool,
    provenance: Vec<(String, String)>,
    fixtures: Vec<Fixture>,
}

fn as_object<'a>(value: &'a json::Value, ctx: &str) -> Result<&'a [(String, json::Value)], String> {
    match value {
        json::Value::Obj(pairs) => Ok(pairs),
        other => Err(format!("{ctx}: {other:?} is not an object")),
    }
}

fn as_array<'a>(value: &'a json::Value, ctx: &str) -> Result<&'a [json::Value], String> {
    value
        .as_arr()
        .ok_or_else(|| format!("{ctx}: expected an array"))
}

fn check_keys(pairs: &[(String, json::Value)], allowed: &[&str], ctx: &str) -> Result<(), String> {
    for (key, _) in pairs {
        if !allowed.contains(&key.as_str()) {
            return Err(format!("{ctx}: unknown key {key:?}"));
        }
    }
    Ok(())
}

fn get<'a>(
    pairs: &'a [(String, json::Value)],
    key: &str,
    ctx: &str,
) -> Result<&'a json::Value, String> {
    pairs
        .iter()
        .find(|(k, _)| k == key)
        .map(|(_, v)| v)
        .ok_or_else(|| format!("{ctx}: missing {key}"))
}

fn read_str(pairs: &[(String, json::Value)], key: &str, ctx: &str) -> Result<String, String> {
    match get(pairs, key, ctx)? {
        json::Value::Str(s) if !s.is_empty() => Ok(s.clone()),
        json::Value::Str(_) => Err(format!("{ctx}: {key} is empty")),
        other => Err(format!("{ctx}: {key} is {other:?}, expected a string")),
    }
}

fn usize_value(value: &json::Value, ctx: &str) -> Result<usize, String> {
    value
        .as_usize()
        .ok_or_else(|| format!("{ctx}: {value:?} is not a non-negative integer"))
}

fn read_usize(pairs: &[(String, json::Value)], key: &str, ctx: &str) -> Result<usize, String> {
    usize_value(get(pairs, key, ctx)?, &format!("{ctx}: {key}"))
}

fn usize_row(value: &json::Value, expected_len: usize, ctx: &str) -> Result<Vec<usize>, String> {
    let items = as_array(value, ctx)?;
    if items.len() != expected_len {
        return Err(format!(
            "{ctx} has {} entries, expected {expected_len}",
            items.len()
        ));
    }
    items.iter().map(|item| usize_value(item, ctx)).collect()
}

fn read_matrix(
    value: &json::Value,
    rows: usize,
    cols: usize,
    label: &str,
    ctx: &str,
) -> Result<Vec<Vec<usize>>, String> {
    let items = as_array(value, &format!("{ctx}: {label}"))?;
    if items.len() != rows {
        return Err(format!(
            "{ctx}: {label} has {} rows, expected {rows}",
            items.len()
        ));
    }
    items
        .iter()
        .enumerate()
        .map(|(i, row)| usize_row(row, cols, &format!("{ctx}: {label} row {i}")))
        .collect()
}

fn read_outcome(value: &json::Value, bound: usize, ctx: &str) -> Result<DimOutcome, String> {
    let pairs = as_object(value, ctx)?;
    if pairs.len() != 1 {
        return Err(format!("{ctx}: expected exactly one of finite or at_least"));
    }
    let (key, inner) = &pairs[0];
    let d = usize_value(inner, ctx)?;
    match key.as_str() {
        "finite" => {
            if d > bound {
                Err(format!("{ctx}: finite value {d} exceeds bound {bound}"))
            } else {
                Ok(DimOutcome::Finite(d))
            }
        }
        "at_least" => {
            if d != bound + 1 {
                Err(format!("{ctx}: at_least is {d}, expected {}", bound + 1))
            } else {
                Ok(DimOutcome::AtLeast(d))
            }
        }
        other => Err(format!("{ctx}: unknown key {other:?}")),
    }
}

fn read_outcomes(
    value: &json::Value,
    n: usize,
    bound: usize,
    label: &str,
    ctx: &str,
) -> Result<Vec<DimOutcome>, String> {
    let items = as_array(value, &format!("{ctx}: {label}"))?;
    if items.len() != n {
        return Err(format!(
            "{ctx}: {label} has {} entries, expected {n}",
            items.len()
        ));
    }
    items
        .iter()
        .enumerate()
        .map(|(i, item)| read_outcome(item, bound, &format!("{ctx}: {label}[{i}]")))
        .collect()
}

fn read_tau_outcome(value: &json::Value, n: usize, ctx: &str) -> Result<TauOutcome, String> {
    let pairs = as_object(value, ctx)?;
    if pairs.len() != 1 {
        return Err(format!(
            "{ctx}: expected exactly one of projective or dimvec"
        ));
    }
    let (key, inner) = &pairs[0];
    match key.as_str() {
        "projective" => match inner {
            json::Value::Bool(true) => Ok(TauOutcome::Projective),
            _ => Err(format!("{ctx}: projective must be true")),
        },
        "dimvec" => Ok(TauOutcome::Dimvec(usize_row(
            inner,
            n,
            &format!("{ctx} dimvec"),
        )?)),
        other => Err(format!("{ctx}: unknown key {other:?}")),
    }
}

fn read_tau_list(
    value: &json::Value,
    n: usize,
    label: &str,
    ctx: &str,
) -> Result<Vec<TauOutcome>, String> {
    let items = as_array(value, &format!("{ctx}: {label}"))?;
    if items.len() != n {
        return Err(format!(
            "{ctx}: {label} has {} entries, expected {n}",
            items.len()
        ));
    }
    items
        .iter()
        .enumerate()
        .map(|(i, item)| read_tau_outcome(item, n, &format!("{ctx}: {label}[{i}]")))
        .collect()
}

fn read_quiver(value: &json::Value, ctx: &str) -> Result<QuiverSpec, String> {
    let qctx = format!("{ctx}: quiver");
    let pairs = as_object(value, &qctx)?;
    check_keys(pairs, &["num_vertices", "arrows"], &qctx)?;
    let num_vertices = read_usize(pairs, "num_vertices", &qctx)?;
    if num_vertices == 0 {
        return Err(format!("{qctx}: num_vertices is 0"));
    }
    let num_vertices = u32::try_from(num_vertices)
        .map_err(|_| format!("{qctx}: num_vertices does not fit u32"))?;
    let items = as_array(get(pairs, "arrows", &qctx)?, &qctx)?;
    let mut arrows: Vec<ArrowSpec> = Vec::with_capacity(items.len());
    for (i, item) in items.iter().enumerate() {
        let actx = format!("{qctx}: arrow {i}");
        let apairs = as_object(item, &actx)?;
        check_keys(apairs, &["name", "source", "target"], &actx)?;
        let name = read_str(apairs, "name", &actx)?;
        let source = read_usize(apairs, "source", &actx)?;
        let target = read_usize(apairs, "target", &actx)?;
        for (endpoint, v) in [("source", source), ("target", target)] {
            if v >= num_vertices as usize {
                return Err(format!(
                    "{actx}: {endpoint} {v} is not a vertex below {num_vertices}"
                ));
            }
        }
        if arrows.iter().any(|a| a.name == name) {
            return Err(format!("{actx}: duplicate arrow name {name:?}"));
        }
        arrows.push(ArrowSpec {
            name,
            source: source as u32,
            target: target as u32,
        });
    }
    Ok(QuiverSpec {
        num_vertices,
        arrows,
    })
}

fn read_relations(
    value: &json::Value,
    num_arrows: usize,
    ctx: &str,
) -> Result<Vec<Vec<TermSpec>>, String> {
    let rctx = format!("{ctx}: relations");
    let items = as_array(value, &rctx)?;
    let mut relations = Vec::with_capacity(items.len());
    for (i, item) in items.iter().enumerate() {
        let ictx = format!("{rctx} entry {i}");
        let pairs = as_object(item, &ictx)?;
        check_keys(pairs, &["terms"], &ictx)?;
        let term_items = as_array(get(pairs, "terms", &ictx)?, &ictx)?;
        if term_items.is_empty() {
            return Err(format!("{ictx}: terms is empty"));
        }
        let mut terms = Vec::with_capacity(term_items.len());
        for (j, term_item) in term_items.iter().enumerate() {
            let tctx = format!("{ictx} term {j}");
            let tpairs = as_object(term_item, &tctx)?;
            check_keys(tpairs, &["coeff", "path"], &tctx)?;
            let coeff = match get(tpairs, "coeff", &tctx)? {
                json::Value::Num(n) => *n,
                other => return Err(format!("{tctx}: coeff is {other:?}, expected an integer")),
            };
            let path_items = as_array(get(tpairs, "path", &tctx)?, &tctx)?;
            if path_items.is_empty() {
                return Err(format!("{tctx}: path is empty"));
            }
            let mut path = Vec::with_capacity(path_items.len());
            for item in path_items {
                let a = usize_value(item, &tctx)?;
                if a >= num_arrows {
                    return Err(format!("{tctx}: arrow index {a} is not below {num_arrows}"));
                }
                path.push(a as u32);
            }
            terms.push(TermSpec { coeff, path });
        }
        relations.push(terms);
    }
    Ok(relations)
}

fn read_decomposition(
    value: &json::Value,
    n: usize,
    ctx: &str,
) -> Result<Vec<(Vec<usize>, usize)>, String> {
    let dctx = format!("{ctx}: decomposition");
    let pairs = as_object(value, &dctx)?;
    check_keys(pairs, &["module", "summands"], &dctx)?;
    let module = read_str(pairs, "module", &dctx)?;
    if module != DECOMPOSITION_MODULE {
        return Err(format!(
            "{dctx}: module is {module:?}, expected {DECOMPOSITION_MODULE:?}"
        ));
    }
    let items = as_array(get(pairs, "summands", &dctx)?, &dctx)?;
    let mut summands: Vec<(Vec<usize>, usize)> = Vec::with_capacity(items.len());
    for (i, item) in items.iter().enumerate() {
        let sctx = format!("{dctx} summand {i}");
        let spairs = as_object(item, &sctx)?;
        check_keys(spairs, &["dimvec", "multiplicity"], &sctx)?;
        let dimvec = usize_row(get(spairs, "dimvec", &sctx)?, n, &format!("{sctx} dimvec"))?;
        let multiplicity = read_usize(spairs, "multiplicity", &sctx)?;
        if multiplicity == 0 {
            return Err(format!("{sctx}: multiplicity is 0"));
        }
        if let Some((prev, _)) = summands.last() {
            match prev.cmp(&dimvec) {
                std::cmp::Ordering::Less => {}
                std::cmp::Ordering::Equal => {
                    return Err(format!("{dctx}: summands repeat dimvec at entry {i}"));
                }
                std::cmp::Ordering::Greater => {
                    return Err(format!(
                        "{dctx}: summands are not sorted ascending at entry {i}"
                    ));
                }
            }
        }
        summands.push((dimvec, multiplicity));
    }
    Ok(summands)
}

fn read_ext(value: &json::Value, n: usize, ctx: &str) -> Result<Vec<Vec<Vec<usize>>>, String> {
    let items = as_array(value, &format!("{ctx}: ext"))?;
    if items.len() != n {
        return Err(format!("{ctx}: ext has {} rows, expected {n}", items.len()));
    }
    let mut ext = Vec::with_capacity(n);
    for (i, row) in items.iter().enumerate() {
        let cells = as_array(row, &format!("{ctx}: ext row {i}"))?;
        if cells.len() != n {
            return Err(format!(
                "{ctx}: ext row {i} has {} entries, expected {n}",
                cells.len()
            ));
        }
        let mut out_row = Vec::with_capacity(n);
        for (j, cell) in cells.iter().enumerate() {
            out_row.push(usize_row(
                cell,
                MAX_EXT_DEGREE + 1,
                &format!("{ctx}: ext[{i}][{j}]"),
            )?);
        }
        ext.push(out_row);
    }
    Ok(ext)
}

fn read_fixture(value: &json::Value, index: usize) -> Result<Fixture, String> {
    let fallback = format!("fixture {index}");
    let pairs = as_object(value, &fallback)?;
    let family = read_str(pairs, "family", &fallback)?;
    let case = read_str(pairs, "case", &fallback)?;
    let ctx = format!("{family}/{case}");
    check_keys(pairs, &FIXTURE_KEYS, &ctx)?;
    let field = read_usize(pairs, "field", &ctx)? as u64;
    PrimeField::new(field).map_err(|e| format!("{ctx}: field {field} rejected: {e}"))?;
    if case != format!("f{field}") {
        return Err(format!("{ctx}: case {case:?} does not name field {field}"));
    }
    let presentation_id = read_str(pairs, "presentation_id", &ctx)?;
    let ideal_id = read_str(pairs, "ideal_id", &ctx)?;
    let order = read_str(pairs, "order", &ctx)?;
    if order != ORDER_ID {
        return Err(format!("{ctx}: order is {order:?}, expected {ORDER_ID:?}"));
    }
    let quiver = read_quiver(get(pairs, "quiver", &ctx)?, &ctx)?;
    let relations = read_relations(get(pairs, "relations", &ctx)?, quiver.arrows.len(), &ctx)?;
    let n = quiver.num_vertices as usize;
    Ok(Fixture {
        dim: read_usize(pairs, "dim", &ctx)?,
        cartan: read_matrix(get(pairs, "cartan", &ctx)?, n, n, "cartan", &ctx)?,
        injectives: read_matrix(get(pairs, "injectives", &ctx)?, n, n, "injectives", &ctx)?,
        projdim: read_outcomes(
            get(pairs, "projdim", &ctx)?,
            n,
            PROJDIM_BOUND,
            "projdim",
            &ctx,
        )?,
        injdim: read_outcomes(get(pairs, "injdim", &ctx)?, n, INJDIM_BOUND, "injdim", &ctx)?,
        tau: read_tau_list(get(pairs, "tau", &ctx)?, n, "tau", &ctx)?,
        tau_injectives: read_tau_list(
            get(pairs, "tau_injectives", &ctx)?,
            n,
            "tau_injectives",
            &ctx,
        )?,
        decomposition: read_decomposition(get(pairs, "decomposition", &ctx)?, n, &ctx)?,
        ext: read_ext(get(pairs, "ext", &ctx)?, n, &ctx)?,
        family,
        case,
        field,
        presentation_id,
        ideal_id,
        quiver,
        relations,
    })
}

/// Two fixtures share a presentation_id if and only if their quiver and
/// relations are byte-identical (README, "Identity fields").
fn check_presentation_ids(fixtures: &[Fixture]) -> Result<(), String> {
    for (i, a) in fixtures.iter().enumerate() {
        for b in &fixtures[i + 1..] {
            let same_presentation = a.quiver == b.quiver && a.relations == b.relations;
            let same_id = a.presentation_id == b.presentation_id;
            if same_id && !same_presentation {
                return Err(format!(
                    "fixtures {}/{} and {}/{} share presentation_id {:?} but their presentations differ",
                    a.family, a.case, b.family, b.case, a.presentation_id
                ));
            }
            if !same_id && same_presentation {
                return Err(format!(
                    "fixtures {}/{} and {}/{} have identical presentations under different presentation_ids",
                    a.family, a.case, b.family, b.case
                ));
            }
        }
    }
    Ok(())
}

/// Parses and validates a v5 oracle document. Every structural defect is an
/// error: wrong schema string, unknown or missing keys, wrong pinned bounds,
/// malformed presentations, malformed typed outcomes, unsorted or unmerged
/// decomposition summands, duplicate fixtures, inconsistent presentation ids.
fn parse_document(text: &str) -> Result<Document, String> {
    let root = json::parse(text)?;
    let ctx = "document";
    let pairs = as_object(&root, ctx)?;
    check_keys(pairs, &ROOT_KEYS, ctx)?;
    let schema = read_str(pairs, "schema", ctx)?;
    if schema != SCHEMA {
        return Err(format!("{ctx}: schema is {schema:?}, expected {SCHEMA:?}"));
    }
    let left_convention = match read_str(pairs, "convention", ctx)?.as_str() {
        "right" => false,
        "left" => true,
        other => {
            return Err(format!(
                "{ctx}: convention is {other:?}, expected \"left\" or \"right\""
            ));
        }
    };
    for (key, expected) in [
        ("max_ext_degree", MAX_EXT_DEGREE),
        ("projdim_bound", PROJDIM_BOUND),
        ("injdim_bound", INJDIM_BOUND),
    ] {
        let value = read_usize(pairs, key, ctx)?;
        if value != expected {
            return Err(format!("{ctx}: {key} is {value}, expected {expected}"));
        }
    }
    let pctx = "provenance";
    let ppairs = as_object(get(pairs, "provenance", ctx)?, pctx)?;
    check_keys(ppairs, &PROVENANCE_KEYS, pctx)?;
    let provenance = PROVENANCE_KEYS
        .iter()
        .map(|key| Ok((key.to_string(), read_str(ppairs, key, pctx)?)))
        .collect::<Result<Vec<_>, String>>()?;
    let items = as_array(get(pairs, "fixtures", ctx)?, ctx)?;
    let fixtures = items
        .iter()
        .enumerate()
        .map(|(i, item)| read_fixture(item, i))
        .collect::<Result<Vec<_>, String>>()?;
    for (i, fx) in fixtures.iter().enumerate() {
        if fixtures[..i]
            .iter()
            .any(|other| other.family == fx.family && other.case == fx.case)
        {
            return Err(format!("duplicate fixture {}/{}", fx.family, fx.case));
        }
    }
    check_presentation_ids(&fixtures)?;
    Ok(Document {
        left_convention,
        provenance,
        fixtures,
    })
}

/// Everything the library computes for one fixture, in the shapes the schema
/// stores.
#[derive(Clone, Debug, PartialEq)]
struct Computed {
    dim: usize,
    cartan: Vec<Vec<usize>>,
    injectives: Vec<Vec<usize>>,
    projdim: Vec<DimOutcome>,
    injdim: Vec<DimOutcome>,
    tau: Vec<TauOutcome>,
    tau_injectives: Vec<TauOutcome>,
    decomposition: Vec<(Vec<usize>, usize)>,
    ext: Vec<Vec<Vec<usize>>>,
}

/// Builds the fixture's algebra from its recorded presentation, the same
/// input path QPA consumed. The documented coefficient rule applies first:
/// reduce each coefficient mod the fixture's field, drop terms that reduce to
/// zero, drop relations with no surviving terms.
fn build_algebra(fx: &Fixture) -> Result<Arc<Algebra>, String> {
    let field =
        PrimeField::new(fx.field).map_err(|e| format!("field {} rejected: {e}", fx.field))?;
    let arrows: Vec<(u32, u32)> = fx
        .quiver
        .arrows
        .iter()
        .map(|a| (a.source, a.target))
        .collect();
    let quiver = Quiver::new(fx.quiver.num_vertices, &arrows)
        .map_err(|e| format!("quiver rejected: {e}"))?;
    let mut relations = Vec::new();
    for (index, terms) in fx.relations.iter().enumerate() {
        let reduced: Vec<(Fp, Vec<ArrowId>)> = terms
            .iter()
            .filter_map(|term| {
                let coeff = field.elem(term.coeff);
                (!coeff.is_zero()).then(|| (coeff, term.path.iter().map(|&a| ArrowId(a)).collect()))
            })
            .collect();
        if reduced.is_empty() {
            continue;
        }
        relations.push(
            Relation::new(&quiver, field, reduced)
                .map_err(|e| format!("relation {index} rejected: {e}"))?,
        );
    }
    let presentation = Presentation::new(quiver, field, relations)
        .map_err(|e| format!("presentation rejected: {e}"))?;
    Algebra::new(presentation, &CompletionLimits::default())
        .map_err(|e| format!("algebra construction failed: {e}"))
}

fn dim_outcome(bounded: Bounded<usize>) -> DimOutcome {
    match bounded {
        Bounded::Exact(d) => DimOutcome::Finite(d),
        Bounded::AtLeast(d) => DimOutcome::AtLeast(d),
    }
}

/// `Tau::Zero` marks a projective input; the schema stores that as
/// `{"projective": true}` and a dimension vector otherwise.
fn tau_outcome(m: &Module) -> TauOutcome {
    match tau(m).expect("τ routes agree on fixtures") {
        Tau::Zero => TauOutcome::Projective,
        Tau::Module(t) => TauOutcome::Dimvec(t.dim_vector().to_vec()),
    }
}

/// The designated test module: the direct sum of the nonzero radicals of the
/// indecomposable projectives, decomposed by `krull_schmidt` and aggregated
/// into (dimvec, multiplicity) pairs sorted lexicographically ascending.
fn radical_summand_classes(algebra: &Arc<Algebra>) -> Result<Vec<(Vec<usize>, usize)>, String> {
    let n = algebra.quiver().num_vertices();
    let radicals: Vec<Module> = (0..n)
        .map(|v| radical(&Module::projective(algebra, v)).0)
        .filter(|m| !m.is_zero())
        .collect();
    if radicals.is_empty() {
        return Ok(Vec::new());
    }
    let parts: Vec<&Module> = radicals.iter().collect();
    let (total, _, _) = direct_sum(&parts);
    match krull_schmidt(&total) {
        KrullSchmidtOutcome::Classes(classes) => {
            let mut counts: BTreeMap<Vec<usize>, usize> = BTreeMap::new();
            for class in classes {
                *counts
                    .entry(class.representative.dim_vector().to_vec())
                    .or_insert(0) += class.multiplicity;
            }
            Ok(counts.into_iter().collect())
        }
        KrullSchmidtOutcome::Unknown { reason } => Err(format!(
            "Krull-Schmidt decomposition undetermined: {reason}"
        )),
    }
}

fn compute(algebra: &Arc<Algebra>) -> Result<Computed, String> {
    let n = algebra.quiver().num_vertices();
    let simples: Vec<Module> = (0..n).map(|v| Module::simple(algebra, v)).collect();
    let injective_modules: Vec<Module> = (0..n).map(|v| Module::injective(algebra, v)).collect();
    let ext = simples
        .iter()
        .map(|si| {
            simples
                .iter()
                .map(|sj| ext_table(si, sj, MAX_EXT_DEGREE).expect("simples share one algebra"))
                .collect()
        })
        .collect();
    Ok(Computed {
        dim: algebra.dim(),
        cartan: algebra.cartan_matrix(),
        injectives: injective_modules
            .iter()
            .map(|m| m.dim_vector().to_vec())
            .collect(),
        projdim: simples
            .iter()
            .map(|s| dim_outcome(projective_dimension(s, PROJDIM_BOUND)))
            .collect(),
        injdim: simples
            .iter()
            .map(|s| {
                dim_outcome(
                    injective_dimension(s, INJDIM_BOUND).expect("the opposite algebra builds"),
                )
            })
            .collect(),
        tau: simples.iter().map(tau_outcome).collect(),
        tau_injectives: injective_modules.iter().map(tau_outcome).collect(),
        decomposition: radical_summand_classes(algebra)?,
        ext,
    })
}

/// A left-convention document stores values for left modules. Left modules
/// over `A` are right modules over `A^op`, so every value is computed over
/// the opposite algebra and compared index for index.
fn build_and_compute(fx: &Fixture, left: bool) -> Result<Computed, String> {
    let algebra = build_algebra(fx)?;
    let algebra = if left {
        opposite(&algebra)
            .map_err(|e| format!("cannot build the opposite algebra: {e}"))?
            .opposite()
            .clone()
    } else {
        algebra
    };
    compute(&algebra)
}

type ComputedCache = Mutex<HashMap<String, Result<Arc<Computed>, String>>>;

/// Fixtures repeat across tests and corrupted documents keep their
/// presentations, so results are cached by field, presentation, and side.
fn computed_for(fx: &Fixture, left: bool) -> Result<Arc<Computed>, String> {
    static CACHE: OnceLock<ComputedCache> = OnceLock::new();
    let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    let key = format!("{left}|{}|{:?}|{:?}", fx.field, fx.quiver, fx.relations);
    if let Some(hit) = cache.lock().unwrap().get(&key) {
        return hit.clone();
    }
    let result = build_and_compute(fx, left).map(Arc::new);
    cache.lock().unwrap().insert(key, result.clone());
    result
}

fn compare_fixture(mismatches: &mut Vec<String>, ctx: &str, fx: &Fixture, ours: &Computed) {
    if fx.dim != ours.dim {
        mismatches.push(format!("{ctx}: dim is {}, ours is {}", fx.dim, ours.dim));
    }
    if fx.cartan != ours.cartan {
        mismatches.push(format!(
            "{ctx}: cartan is {:?}, ours is {:?}",
            fx.cartan, ours.cartan
        ));
    }
    if fx.injectives != ours.injectives {
        mismatches.push(format!(
            "{ctx}: injectives is {:?}, ours is {:?}",
            fx.injectives, ours.injectives
        ));
    }
    for (i, (theirs, our)) in fx.projdim.iter().zip(&ours.projdim).enumerate() {
        if theirs != our {
            mismatches.push(format!(
                "{ctx}: projdim(S_{i}) is {theirs:?}, ours is {our:?}"
            ));
        }
    }
    for (i, (theirs, our)) in fx.injdim.iter().zip(&ours.injdim).enumerate() {
        if theirs != our {
            mismatches.push(format!(
                "{ctx}: injdim(S_{i}) is {theirs:?}, ours is {our:?}"
            ));
        }
    }
    for (i, (theirs, our)) in fx.tau.iter().zip(&ours.tau).enumerate() {
        if theirs != our {
            mismatches.push(format!("{ctx}: tau(S_{i}) is {theirs:?}, ours is {our:?}"));
        }
    }
    for (i, (theirs, our)) in fx
        .tau_injectives
        .iter()
        .zip(&ours.tau_injectives)
        .enumerate()
    {
        if theirs != our {
            mismatches.push(format!(
                "{ctx}: tau_injectives(I_{i}) is {theirs:?}, ours is {our:?}"
            ));
        }
    }
    if fx.decomposition != ours.decomposition {
        mismatches.push(format!(
            "{ctx}: decomposition summands are {:?}, ours are {:?}",
            fx.decomposition, ours.decomposition
        ));
    }
    for (i, (their_row, our_row)) in fx.ext.iter().zip(&ours.ext).enumerate() {
        for (j, (theirs, our)) in their_row.iter().zip(our_row).enumerate() {
            if theirs != our {
                mismatches.push(format!(
                    "{ctx}: Ext(S_{i}, S_{j}) is {theirs:?}, ours is {our:?}"
                ));
            }
        }
    }
}

/// Mismatch descriptions from comparing the library against a validated
/// document. Every fixture's algebra is rebuilt from its recorded
/// presentation; a construction failure is a mismatch, not a skip. The
/// fixture set itself is pinned by `FIXTURE_MANIFEST`.
fn compare(doc: &Document) -> Vec<String> {
    let mut mismatches = Vec::new();
    for (family, case) in FIXTURE_MANIFEST {
        if !doc
            .fixtures
            .iter()
            .any(|fx| fx.family == family && fx.case == case)
        {
            mismatches.push(format!("{family}/{case}: missing from oracle file"));
        }
    }
    for fx in &doc.fixtures {
        let ctx = format!("{}/{}", fx.family, fx.case);
        if !FIXTURE_MANIFEST
            .iter()
            .any(|&(f, c)| f == fx.family && c == fx.case)
        {
            mismatches.push(format!("{ctx}: not in the fixture manifest"));
        }
        match computed_for(fx, doc.left_convention) {
            Ok(ours) => compare_fixture(&mut mismatches, &ctx, fx, &ours),
            Err(e) => mismatches.push(format!("{ctx}: {e}")),
        }
    }
    mismatches
}

fn oracle_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/qpa-oracle")
}

fn committed_text() -> String {
    let path = oracle_dir().join("qpa_expected.json");
    fs::read_to_string(&path).unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()))
}

fn committed_doc() -> Document {
    parse_document(&committed_text()).unwrap_or_else(|e| panic!("qpa_expected.json rejected: {e}"))
}

fn int_row(row: &[usize]) -> String {
    let items: Vec<String> = row.iter().map(usize::to_string).collect();
    format!("[{}]", items.join(", "))
}

fn int_matrix(mat: &[Vec<usize>]) -> String {
    let rows: Vec<String> = mat.iter().map(|r| int_row(r)).collect();
    format!("[{}]", rows.join(", "))
}

fn outcome_json(outcome: &DimOutcome) -> String {
    match outcome {
        DimOutcome::Finite(d) => format!("{{\"finite\": {d}}}"),
        DimOutcome::AtLeast(d) => format!("{{\"at_least\": {d}}}"),
    }
}

fn outcome_row(outcomes: &[DimOutcome]) -> String {
    let items: Vec<String> = outcomes.iter().map(outcome_json).collect();
    format!("[{}]", items.join(", "))
}

fn tau_json(outcome: &TauOutcome) -> String {
    match outcome {
        TauOutcome::Projective => "{\"projective\": true}".to_string(),
        TauOutcome::Dimvec(v) => format!("{{\"dimvec\": {}}}", int_row(v)),
    }
}

fn tau_row(outcomes: &[TauOutcome]) -> String {
    let items: Vec<String> = outcomes.iter().map(tau_json).collect();
    format!("[{}]", items.join(", "))
}

fn summands_json(summands: &[(Vec<usize>, usize)]) -> String {
    let items: Vec<String> = summands
        .iter()
        .map(|(dimvec, multiplicity)| {
            format!(
                "{{\"dimvec\": {}, \"multiplicity\": {multiplicity}}}",
                int_row(dimvec)
            )
        })
        .collect();
    format!("[{}]", items.join(", "))
}

fn arrow_json(arrow: &ArrowSpec) -> String {
    format!(
        "{{\"name\": \"{}\", \"source\": {}, \"target\": {}}}",
        arrow.name, arrow.source, arrow.target
    )
}

fn relation_json(terms: &[TermSpec]) -> String {
    let items: Vec<String> = terms
        .iter()
        .map(|term| {
            let path: Vec<String> = term.path.iter().map(u32::to_string).collect();
            format!(
                "{{\"coeff\": {}, \"path\": [{}]}}",
                term.coeff,
                path.join(", ")
            )
        })
        .collect();
    format!("{{\"terms\": [{}]}}", items.join(", "))
}

/// Renders a v5 document from fixture presentations plus library-computed
/// values, in the layout `generate_fixtures.g` writes. The provenance block
/// names this library, never GAP.
fn render_document(fixtures: &[(&Fixture, &Computed)], convention: &str) -> String {
    let mut out = String::new();
    out.push_str("{\n");
    out.push_str(&format!("  \"schema\": \"{SCHEMA}\",\n"));
    out.push_str(&format!("  \"convention\": \"{convention}\",\n"));
    out.push_str(&format!("  \"max_ext_degree\": {MAX_EXT_DEGREE},\n"));
    out.push_str(&format!("  \"projdim_bound\": {PROJDIM_BOUND},\n"));
    out.push_str(&format!("  \"injdim_bound\": {INJDIM_BOUND},\n"));
    out.push_str("  \"provenance\": {\n");
    out.push_str("    \"gap_version\": \"none\",\n");
    out.push_str("    \"qpa_version\": \"none\",\n");
    out.push_str(
        "    \"command\": \"QPA_ORACLE_WRITE=1 cargo test -p auslander --test qpa_oracle\"\n",
    );
    out.push_str("  },\n");
    out.push_str("  \"fixtures\": [\n");
    for (idx, (fx, ours)) in fixtures.iter().enumerate() {
        out.push_str("    {\n");
        out.push_str(&format!("      \"family\": \"{}\",\n", fx.family));
        out.push_str(&format!("      \"case\": \"{}\",\n", fx.case));
        out.push_str(&format!("      \"field\": {},\n", fx.field));
        out.push_str(&format!(
            "      \"presentation_id\": \"{}\",\n",
            fx.presentation_id
        ));
        out.push_str(&format!("      \"ideal_id\": \"{}\",\n", fx.ideal_id));
        out.push_str(&format!("      \"order\": \"{ORDER_ID}\",\n"));
        out.push_str("      \"quiver\": {\n");
        out.push_str(&format!(
            "        \"num_vertices\": {},\n",
            fx.quiver.num_vertices
        ));
        out.push_str("        \"arrows\": [\n");
        for (i, arrow) in fx.quiver.arrows.iter().enumerate() {
            let comma = if i + 1 < fx.quiver.arrows.len() {
                ","
            } else {
                ""
            };
            out.push_str(&format!("          {}{comma}\n", arrow_json(arrow)));
        }
        out.push_str("        ]\n");
        out.push_str("      },\n");
        if fx.relations.is_empty() {
            out.push_str("      \"relations\": [],\n");
        } else {
            out.push_str("      \"relations\": [\n");
            for (i, relation) in fx.relations.iter().enumerate() {
                let comma = if i + 1 < fx.relations.len() { "," } else { "" };
                out.push_str(&format!("        {}{comma}\n", relation_json(relation)));
            }
            out.push_str("      ],\n");
        }
        out.push_str(&format!("      \"dim\": {},\n", ours.dim));
        out.push_str(&format!(
            "      \"cartan\": {},\n",
            int_matrix(&ours.cartan)
        ));
        out.push_str(&format!(
            "      \"injectives\": {},\n",
            int_matrix(&ours.injectives)
        ));
        out.push_str(&format!(
            "      \"projdim\": {},\n",
            outcome_row(&ours.projdim)
        ));
        out.push_str(&format!(
            "      \"injdim\": {},\n",
            outcome_row(&ours.injdim)
        ));
        out.push_str(&format!("      \"tau\": {},\n", tau_row(&ours.tau)));
        out.push_str(&format!(
            "      \"tau_injectives\": {},\n",
            tau_row(&ours.tau_injectives)
        ));
        out.push_str(&format!(
            "      \"decomposition\": {{\"module\": \"{DECOMPOSITION_MODULE}\", \"summands\": {}}},\n",
            summands_json(&ours.decomposition)
        ));
        out.push_str("      \"ext\": [\n");
        for (i, row) in ours.ext.iter().enumerate() {
            let comma = if i + 1 < ours.ext.len() { "," } else { "" };
            out.push_str(&format!("        {}{comma}\n", int_matrix(row)));
        }
        out.push_str("      ]\n");
        let comma = if idx + 1 < fixtures.len() { "," } else { "" };
        out.push_str(&format!("    }}{comma}\n"));
    }
    out.push_str("  ]\n");
    out.push_str("}\n");
    out
}

/// Renders the document with library-computed values for every fixture of
/// `doc`, over the algebra itself or its opposite per `left`.
fn rendered_from_computed(doc: &Document, left: bool, convention: &str) -> String {
    let computed: Vec<(&Fixture, Arc<Computed>)> = doc
        .fixtures
        .iter()
        .map(|fx| {
            let value =
                computed_for(fx, left).unwrap_or_else(|e| panic!("{}/{}: {e}", fx.family, fx.case));
            (fx, value)
        })
        .collect();
    let refs: Vec<(&Fixture, &Computed)> = computed
        .iter()
        .map(|(fx, value)| (*fx, value.as_ref()))
        .collect();
    render_document(&refs, convention)
}

/// The committed independent truth: `qpa_expected.json` was produced by a real
/// GAP+QPA run of `generate_fixtures.g` (provenance in `tests/qpa-oracle/README.md`)
/// and is regenerated only by that path, never by this library.
#[test]
fn library_matches_the_committed_qpa_truth() {
    let mismatches = compare(&committed_doc());
    assert!(
        mismatches.is_empty(),
        "library disagrees with the committed QPA truth:\n{}",
        mismatches.join("\n")
    );
}

/// Self-consistency only: `native_snapshot.json` is this library's own output,
/// so agreement detects drift, not correctness (the oracle test above does
/// that). `QPA_ORACLE_WRITE=1` rewrites the snapshot after an intentional
/// change. The presentations in the snapshot are copied from the committed
/// truth; the result values are the library's.
#[test]
fn library_matches_its_native_snapshot() {
    let path = oracle_dir().join("native_snapshot.json");
    let rendered = rendered_from_computed(&committed_doc(), false, "right");
    if env::var("QPA_ORACLE_WRITE").as_deref() == Ok("1") {
        fs::write(&path, rendered)
            .unwrap_or_else(|e| panic!("cannot write {}: {e}", path.display()));
        println!("wrote {}", path.display());
        return;
    }
    let text =
        fs::read_to_string(&path).unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
    assert_eq!(
        text, rendered,
        "library output drifted from native_snapshot.json; rerun with \
         QPA_ORACLE_WRITE=1 if the change is intentional"
    );
}

/// The writer's output must pass the strict reader and compare clean, so the
/// snapshot cannot go stale against the reader.
#[test]
fn native_render_round_trips_through_the_reader() {
    let rendered = rendered_from_computed(&committed_doc(), false, "right");
    let parsed = parse_document(&rendered).expect("writer output parses");
    assert!(!parsed.left_convention);
    assert_eq!(compare(&parsed), Vec::<String>::new());
}

/// A left-convention document must compare clean against values computed
/// over the opposite algebra. The check runs on a rendered copy of our own
/// opposite-side data, the same code path a left-module GAP build would take.
#[test]
fn left_convention_documents_compare_over_the_opposite_algebra() {
    let rendered = rendered_from_computed(&committed_doc(), true, "left");
    let parsed = parse_document(&rendered).expect("left-convention document parses");
    assert!(parsed.left_convention);
    assert_eq!(compare(&parsed), Vec::<String>::new());
}

/// Metamorphic: fixtures with one ideal_id over one field generate the same
/// ideal, so the library must produce identical results for them however the
/// presentation is spelled. The commutative-square trio (plain, redundant
/// generator, permuted terms) is pinned to stay in the fixture set.
#[test]
fn fixtures_sharing_an_ideal_and_field_agree() {
    let doc = committed_doc();
    let mut groups: BTreeMap<(&str, u64), Vec<&Fixture>> = BTreeMap::new();
    for fx in &doc.fixtures {
        groups
            .entry((fx.ideal_id.as_str(), fx.field))
            .or_default()
            .push(fx);
    }
    assert_eq!(
        groups.get(&("commutative-square", 5)).map_or(0, Vec::len),
        3,
        "the commutative-square trio must stay in the fixture set"
    );
    let mut checked = 0;
    for ((ideal, field), members) in &groups {
        if members.len() < 2 {
            continue;
        }
        let first = computed_for(members[0], false)
            .unwrap_or_else(|e| panic!("{}/{}: {e}", members[0].family, members[0].case));
        for other in &members[1..] {
            let value = computed_for(other, false)
                .unwrap_or_else(|e| panic!("{}/{}: {e}", other.family, other.case));
            assert_eq!(
                first, value,
                "{}/{} and {}/{} share ideal {ideal} over F_{field} but the library disagrees",
                members[0].family, members[0].case, other.family, other.case
            );
        }
        checked += 1;
    }
    assert_eq!(checked, 3, "expected three multi-fixture ideal groups");
}

/// Metamorphic: the characteristic-sensitive pair keeps one presentation
/// while the ideal degenerates over F_2. The library must reproduce the
/// recorded agreement (dim, cartan, injectives, projdim, injdim, ext) and the
/// recorded differences (tau of S_1, tau of I_2 and I_3, the decomposition).
#[test]
fn characteristic_sensitive_pair_differs_as_recorded() {
    let doc = committed_doc();
    let find = |case: &str| {
        doc.fixtures
            .iter()
            .find(|fx| fx.family == "characteristic-sensitive" && fx.case == case)
            .unwrap_or_else(|| panic!("characteristic-sensitive/{case} missing"))
    };
    let (f2, f3) = (find("f2"), find("f3"));
    let ours2 = computed_for(f2, false).expect("characteristic-sensitive builds over F_2");
    let ours3 = computed_for(f3, false).expect("characteristic-sensitive builds over F_3");
    assert_eq!(ours2.dim, ours3.dim);
    assert_eq!(ours2.cartan, ours3.cartan);
    assert_eq!(ours2.injectives, ours3.injectives);
    assert_eq!(ours2.projdim, ours3.projdim);
    assert_eq!(ours2.injdim, ours3.injdim);
    assert_eq!(ours2.ext, ours3.ext);
    assert_eq!(
        ours2.tau, f2.tau,
        "library tau over F_2 must match the record"
    );
    assert_eq!(
        ours3.tau, f3.tau,
        "library tau over F_3 must match the record"
    );
    assert_ne!(ours2.tau[1], ours3.tau[1], "tau S_1 must differ");
    assert_eq!(ours2.tau_injectives, f2.tau_injectives);
    assert_eq!(ours3.tau_injectives, f3.tau_injectives);
    assert_ne!(
        ours2.tau_injectives[2], ours3.tau_injectives[2],
        "tau I_2 must differ"
    );
    assert_ne!(
        ours2.tau_injectives[3], ours3.tau_injectives[3],
        "tau I_3 must differ"
    );
    assert!(matches!(ours3.tau_injectives[3], TauOutcome::Projective));
    assert!(matches!(ours2.tau_injectives[3], TauOutcome::Dimvec(_)));
    assert_eq!(ours2.decomposition, f2.decomposition);
    assert_eq!(ours3.decomposition, f3.decomposition);
    assert_ne!(
        ours2.decomposition, ours3.decomposition,
        "the radical of P_0 must split only over F_2"
    );
}

/// The committed truth must carry the exact pinned schema string, so the
/// corruption test below cannot rot into replacing a string that is not
/// there.
#[test]
fn committed_truth_carries_the_pinned_schema() {
    assert!(committed_text().contains(&format!("\"schema\": \"{SCHEMA}\"")));
}

/// Locates GAP and a loadable QPA, in the order the README documents. GAP launches
/// plainly when `~/.gap/pkg/qpa` exists, because GAP auto-loads packages from
/// `~/.gap`. Otherwise the test builds a temporary GAP root whose `pkg/qpa` symlinks
/// to `$QPA_DIR`, and whose `pkg/gbnp` symlinks to `$GBNP_DIR` when that is set. QPA
/// cannot load without its gbnp dependency in some root. The GAP binary is
/// `$GAP_BIN` or `gap`. Interactive shells may alias `gap` away, but process
/// spawning here never sees shell aliases.
#[cfg(unix)]
fn gap_command(workdir: &Path) -> Command {
    let gap_bin = env::var("GAP_BIN").unwrap_or_else(|_| "gap".to_string());
    let mut cmd = Command::new(gap_bin);
    // -q quiet, -T no break loop: any GAP error exits nonzero instead of hanging.
    cmd.arg("-q").arg("-T");
    let home_qpa = env::var("HOME")
        .map(|h| PathBuf::from(h).join(".gap/pkg/qpa"))
        .ok()
        .filter(|p| p.exists());
    if home_qpa.is_none() {
        let qpa_dir = env::var("QPA_DIR").unwrap_or_else(|_| {
            panic!(
                "QPA_ORACLE=1: no ~/.gap/pkg/qpa and QPA_DIR is unset; \
                 point QPA_DIR at a QPA source tree"
            )
        });
        let root = workdir.join("gaproot");
        fs::create_dir_all(root.join("pkg")).expect("can create temporary GAP root");
        std::os::unix::fs::symlink(&qpa_dir, root.join("pkg/qpa"))
            .unwrap_or_else(|e| panic!("cannot symlink {qpa_dir} into the GAP root: {e}"));
        if let Ok(gbnp_dir) = env::var("GBNP_DIR") {
            std::os::unix::fs::symlink(&gbnp_dir, root.join("pkg/gbnp"))
                .unwrap_or_else(|e| panic!("cannot symlink {gbnp_dir} into the GAP root: {e}"));
        }
        // ";" prepends to the default roots, so stdlib still resolves.
        cmd.arg("-l").arg(format!(";{}", root.display()));
    }
    cmd.current_dir(workdir).stdin(Stdio::null());
    cmd
}

/// `QPA_ORACLE=1`: run `generate_fixtures.g` under GAP+QPA into a temp dir, then
/// require the fresh output to agree with both this library and the committed
/// `qpa_expected.json`. Every failure mode is hard: GAP missing, QPA not loading,
/// no output file, schema mismatch, value mismatch. Unix only. The GAP root is
/// assembled with symlinks, and this harness does not support GAP on Windows.
#[cfg(unix)]
#[test]
fn live_gap_run_agrees_with_library_and_committed_truth() {
    if env::var("QPA_ORACLE").as_deref() != Ok("1") {
        println!("live GAP run skipped; set QPA_ORACLE=1 to invoke GAP+QPA");
        return;
    }
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("clock after the epoch")
        .as_nanos();
    let workdir = env::temp_dir().join(format!("qpa-oracle-{}-{nanos}", std::process::id()));
    fs::create_dir(&workdir).expect("can create a fresh GAP working directory");
    let script = oracle_dir().join("generate_fixtures.g");
    let output = gap_command(&workdir)
        .arg(&script)
        .output()
        .unwrap_or_else(|e| panic!("cannot launch GAP (set GAP_BIN to the binary): {e}"));
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "GAP exited with {}; stdout:\n{stdout}\nstderr:\n{stderr}",
        output.status
    );
    let fresh_path = workdir.join("fixtures_qpa.json");
    assert!(
        fresh_path.exists(),
        "GAP ran but wrote no {}; QPA probably failed to load; stdout:\n{stdout}\nstderr:\n{stderr}",
        fresh_path.display()
    );
    let fresh_text = fs::read_to_string(&fresh_path)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", fresh_path.display()));
    let fresh = parse_document(&fresh_text)
        .unwrap_or_else(|e| panic!("fresh GAP output {} rejected: {e}", fresh_path.display()));
    let mismatches = compare(&fresh);
    assert!(
        mismatches.is_empty(),
        "fresh QPA run disagrees with the library:\n{}",
        mismatches.join("\n")
    );
    assert_eq!(
        fresh,
        committed_doc(),
        "fresh QPA run disagrees with the committed qpa_expected.json; \
         if QPA itself changed, regenerate per tests/qpa-oracle/README.md"
    );
    // The value comparison above gives readable diagnostics. The documented
    // guarantee is byte-for-byte reproducibility, so check that as well.
    assert_eq!(
        fresh_text,
        committed_text(),
        "fresh QPA run is value-equal but not byte-identical to qpa_expected.json; \
         regenerate per tests/qpa-oracle/README.md"
    );
    fs::remove_dir_all(&workdir).ok();
}

/// Corruption regressions: each mutation of the committed truth must be
/// caught, by the parser, by the strict reader, or by the comparator. Every
/// corruption target is asserted present in the committed bytes, so a test
/// cannot rot into replacing nothing.
mod corruption {
    use super::*;

    fn corrupted(from: &str, to: &str) -> String {
        let text = committed_text();
        let replaced = text.replacen(from, to, 1);
        assert_ne!(text, replaced, "corruption target {from:?} not found");
        replaced
    }

    /// The corrupted document must fail the strict reader.
    fn read_error(from: &str, to: &str) -> String {
        parse_document(&corrupted(from, to)).expect_err("the corrupted document must be rejected")
    }

    /// The corrupted document still reads; the comparator must flag it.
    fn corrupted_mismatches(from: &str, to: &str) -> Vec<String> {
        let doc = parse_document(&corrupted(from, to))
            .unwrap_or_else(|e| panic!("the corrupted document must still read: {e}"));
        compare(&doc)
    }

    #[test]
    fn parser_rejects_a_duplicated_key() {
        let text = corrupted("\"dim\": 3,", "\"dim\": 3,\n      \"dim\": 3,");
        let err = json::parse(&text).unwrap_err();
        assert!(err.contains("duplicate key \"dim\""), "{err}");
    }

    #[test]
    fn parser_rejects_a_trailing_comma() {
        let text = corrupted(
            "\"cartan\": [[1, 1], [0, 1]],",
            "\"cartan\": [[1, 1], [0, 1],],",
        );
        let err = json::parse(&text).unwrap_err();
        assert!(err.contains("unexpected"), "{err}");
    }

    /// The corrupted string is derived from the pinned SCHEMA constant, so
    /// this test tracks the real schema string instead of a stale copy.
    #[test]
    fn reader_rejects_the_previous_schema_version() {
        let from = format!("\"schema\": \"{SCHEMA}\"");
        let to = from.replace("-v5", "-v4");
        assert_ne!(from, to, "the pinned schema must carry the v5 marker");
        let err = read_error(&from, &to);
        assert!(err.contains("schema"), "{err}");
    }

    #[test]
    fn reader_rejects_a_missing_root_field() {
        let err = read_error("  \"max_ext_degree\": 4,\n", "");
        assert!(err.contains("missing max_ext_degree"), "{err}");
    }

    #[test]
    fn reader_rejects_a_changed_max_ext_degree() {
        let err = read_error("\"max_ext_degree\": 4", "\"max_ext_degree\": 3");
        assert!(err.contains("max_ext_degree is 3"), "{err}");
    }

    #[test]
    fn reader_rejects_a_changed_projdim_bound() {
        let err = read_error("\"projdim_bound\": 6", "\"projdim_bound\": 5");
        assert!(err.contains("projdim_bound is 5"), "{err}");
    }

    #[test]
    fn reader_rejects_an_unknown_top_level_key() {
        let err = read_error(
            "\"max_ext_degree\": 4,",
            "\"max_ext_degree\": 4,\n  \"surprise\": 1,",
        );
        assert!(err.contains("unknown key \"surprise\""), "{err}");
    }

    #[test]
    fn reader_rejects_an_unknown_fixture_key() {
        let err = read_error("\"dim\": 3,", "\"dim\": 3,\n      \"surprise\": 1,");
        assert!(err.contains("unknown key \"surprise\""), "{err}");
        assert!(err.contains("linear-an-2/f5"), "{err}");
    }

    #[test]
    fn reader_rejects_a_missing_fixture_field() {
        let err = read_error("      \"dim\": 3,\n", "");
        assert!(err.contains("missing dim"), "{err}");
    }

    #[test]
    fn reader_rejects_an_unknown_convention() {
        let err = read_error("\"convention\": \"right\"", "\"convention\": \"sideways\"");
        assert!(err.contains("convention"), "{err}");
    }

    #[test]
    fn reader_rejects_a_wrong_order_id() {
        let err = read_error("\"order\": \"deglex-arrowid-v1\",", "\"order\": \"lex\",");
        assert!(err.contains("order"), "{err}");
    }

    #[test]
    fn reader_rejects_provenance_with_an_unknown_key() {
        let err = read_error(
            "    \"qpa_version\": \"1.36\",\n",
            "    \"qpa_version\": \"1.36\",\n    \"surprise\": \"x\",\n",
        );
        assert!(err.contains("provenance"), "{err}");
        assert!(err.contains("surprise"), "{err}");
    }

    #[test]
    fn reader_rejects_an_empty_provenance_value() {
        let err = read_error("\"qpa_version\": \"1.36\"", "\"qpa_version\": \"\"");
        assert!(err.contains("qpa_version is empty"), "{err}");
    }

    #[test]
    fn reader_rejects_a_non_prime_field() {
        let err = read_error("\"field\": 2,", "\"field\": 4,");
        assert!(err.contains("not prime"), "{err}");
    }

    #[test]
    fn reader_rejects_a_case_that_names_another_field() {
        let err = read_error("\"field\": 3,", "\"field\": 7,");
        assert!(err.contains("does not name field 7"), "{err}");
    }

    #[test]
    fn reader_rejects_wrong_num_vertices() {
        let err = read_error("\"num_vertices\": 2,", "\"num_vertices\": 99,");
        assert!(err.contains("cartan has 2 rows, expected 99"), "{err}");
    }

    #[test]
    fn reader_rejects_an_arrow_endpoint_out_of_range() {
        let err = read_error(
            "{\"name\": \"a1\", \"source\": 0, \"target\": 1}",
            "{\"name\": \"a1\", \"source\": 0, \"target\": 9}",
        );
        assert!(err.contains("target 9 is not a vertex below 2"), "{err}");
    }

    #[test]
    fn reader_rejects_a_duplicate_arrow_name() {
        let err = read_error(
            "{\"name\": \"a2\", \"source\": 0, \"target\": 1}",
            "{\"name\": \"a1\", \"source\": 0, \"target\": 1}",
        );
        assert!(err.contains("duplicate arrow name \"a1\""), "{err}");
    }

    #[test]
    fn reader_rejects_a_relation_path_index_out_of_range() {
        let err = read_error(
            "{\"coeff\": 1, \"path\": [0, 0]}",
            "{\"coeff\": 1, \"path\": [0, 9]}",
        );
        assert!(err.contains("arrow index 9 is not below 1"), "{err}");
    }

    #[test]
    fn reader_rejects_a_relation_without_terms() {
        let err = read_error(
            "{\"terms\": [{\"coeff\": 1, \"path\": [0, 0]}]}",
            "{\"terms\": []}",
        );
        assert!(err.contains("terms is empty"), "{err}");
    }

    #[test]
    fn reader_rejects_a_truncated_tau_dimvec() {
        let err = read_error(
            "\"tau\": [{\"dimvec\": [0, 1]}",
            "\"tau\": [{\"dimvec\": [0]}",
        );
        assert!(
            err.contains("tau[0] dimvec has 1 entries, expected 2"),
            "{err}"
        );
    }

    #[test]
    fn reader_rejects_a_tau_entry_with_two_keys() {
        let err = read_error(
            "{\"projective\": true}",
            "{\"projective\": true, \"dimvec\": [0, 0]}",
        );
        assert!(err.contains("exactly one of projective or dimvec"), "{err}");
    }

    #[test]
    fn reader_rejects_projective_false() {
        let err = read_error("{\"projective\": true}", "{\"projective\": false}");
        assert!(err.contains("projective must be true"), "{err}");
    }

    #[test]
    fn reader_rejects_an_unknown_outcome_key() {
        let err = read_error("{\"finite\": 1}", "{\"bounded\": 1}");
        assert!(err.contains("unknown key \"bounded\""), "{err}");
    }

    #[test]
    fn reader_rejects_an_outcome_with_two_keys() {
        let err = read_error("{\"finite\": 1}", "{\"finite\": 1, \"at_least\": 7}");
        assert!(err.contains("exactly one of finite or at_least"), "{err}");
    }

    #[test]
    fn reader_rejects_at_least_off_the_bound() {
        let err = read_error("{\"at_least\": 7}", "{\"at_least\": 8}");
        assert!(err.contains("at_least is 8, expected 7"), "{err}");
    }

    #[test]
    fn reader_rejects_finite_beyond_the_bound() {
        let err = read_error("{\"finite\": 2}", "{\"finite\": 9}");
        assert!(err.contains("finite value 9 exceeds bound 6"), "{err}");
    }

    #[test]
    fn reader_rejects_a_wrong_decomposition_module() {
        let err = read_error(
            "\"module\": \"radicals-of-projectives\"",
            "\"module\": \"socles-of-projectives\"",
        );
        assert!(err.contains("module"), "{err}");
    }

    #[test]
    fn reader_rejects_unsorted_decomposition_summands() {
        let err = read_error(
            "\"summands\": [{\"dimvec\": [0, 0, 1], \"multiplicity\": 1}, {\"dimvec\": [0, 1, 0], \"multiplicity\": 1}]",
            "\"summands\": [{\"dimvec\": [0, 1, 0], \"multiplicity\": 1}, {\"dimvec\": [0, 0, 1], \"multiplicity\": 1}]",
        );
        assert!(err.contains("not sorted ascending"), "{err}");
    }

    #[test]
    fn reader_rejects_unmerged_decomposition_summands() {
        let err = read_error(
            "[{\"dimvec\": [0, 0, 0, 1], \"multiplicity\": 2}",
            "[{\"dimvec\": [0, 0, 0, 1], \"multiplicity\": 1}, {\"dimvec\": [0, 0, 0, 1], \"multiplicity\": 1}",
        );
        assert!(err.contains("repeat dimvec"), "{err}");
    }

    #[test]
    fn reader_rejects_a_zero_multiplicity() {
        let err = read_error("\"multiplicity\": 1}", "\"multiplicity\": 0}");
        assert!(err.contains("multiplicity is 0"), "{err}");
    }

    #[test]
    fn reader_rejects_an_unknown_summand_key() {
        let err = read_error(
            "{\"dimvec\": [0, 1], \"multiplicity\": 1}",
            "{\"dimvec\": [0, 1], \"multiplicity\": 1, \"surprise\": 1}",
        );
        assert!(err.contains("unknown key \"surprise\""), "{err}");
    }

    #[test]
    fn reader_rejects_a_truncated_ext_row() {
        let err = read_error("[[1, 0, 0, 0, 0], [0, 1, 0, 0, 0]],", "[[1, 0, 0, 0, 0]],");
        assert!(err.contains("ext row 0 has 1 entries, expected 2"), "{err}");
    }

    #[test]
    fn reader_rejects_a_truncated_ext_table() {
        let err = read_error("[0, 1, 0, 0, 0]]", "[0, 1, 0]]");
        assert!(err.contains("ext[0][1] has 3 entries, expected 5"), "{err}");
    }

    #[test]
    fn reader_rejects_duplicate_fixtures() {
        let err = read_error(
            "\"family\": \"linear-an-3\",",
            "\"family\": \"linear-an-2\",",
        );
        assert!(err.contains("duplicate fixture linear-an-2/f5"), "{err}");
    }

    #[test]
    fn reader_rejects_a_presentation_id_conflict() {
        let err = read_error(
            "\"presentation_id\": \"a3-mod-ab\",",
            "\"presentation_id\": \"a3-mod-ab-x\",",
        );
        assert!(
            err.contains("identical presentations under different presentation_ids"),
            "{err}"
        );
    }

    #[test]
    fn compare_rejects_a_renamed_fixture() {
        let mismatches = corrupted_mismatches(
            "\"family\": \"gentle-tree\",",
            "\"family\": \"bogus-algebra\",",
        );
        assert!(
            mismatches
                .iter()
                .any(|m| m.contains("not in the fixture manifest")),
            "{mismatches:?}"
        );
        assert!(
            mismatches
                .iter()
                .any(|m| m.contains("gentle-tree/f5: missing from oracle file")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_dim() {
        let mismatches = corrupted_mismatches("\"dim\": 3,", "\"dim\": 4,");
        assert!(
            mismatches.iter().any(|m| m.contains("dim is 4, ours is 3")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_cartan_value() {
        let mismatches = corrupted_mismatches(
            "\"cartan\": [[1, 1], [0, 1]],",
            "\"cartan\": [[1, 5], [0, 1]],",
        );
        assert!(
            mismatches.iter().any(|m| m.contains("cartan")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_injectives_value() {
        let mismatches = corrupted_mismatches(
            "\"injectives\": [[1, 0], [1, 1]],",
            "\"injectives\": [[1, 0], [7, 1]],",
        );
        assert!(
            mismatches.iter().any(|m| m.contains("injectives")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_projdim_value() {
        let mismatches = corrupted_mismatches(
            "\"projdim\": [{\"finite\": 1}, {\"finite\": 0}],",
            "\"projdim\": [{\"finite\": 3}, {\"finite\": 0}],",
        );
        assert!(
            mismatches.iter().any(|m| m.contains("projdim(S_0)")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_injdim_value() {
        let mismatches = corrupted_mismatches(
            "\"injdim\": [{\"finite\": 0}, {\"finite\": 1}],",
            "\"injdim\": [{\"at_least\": 7}, {\"finite\": 1}],",
        );
        assert!(
            mismatches.iter().any(|m| m.contains("injdim(S_0)")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_tau_value() {
        let mismatches = corrupted_mismatches(
            "\"tau\": [{\"dimvec\": [0, 1]}",
            "\"tau\": [{\"dimvec\": [0, 7]}",
        );
        assert!(
            mismatches.iter().any(|m| m.contains("tau(S_0)")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_tau_injectives_value() {
        let mismatches = corrupted_mismatches(
            "\"tau_injectives\": [{\"dimvec\": [0, 1]}",
            "\"tau_injectives\": [{\"dimvec\": [0, 7]}",
        );
        assert!(
            mismatches.iter().any(|m| m.contains("tau_injectives(I_0)")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_decomposition_multiplicity() {
        let mismatches = corrupted_mismatches(
            "{\"dimvec\": [0, 0, 0, 1], \"multiplicity\": 2}",
            "{\"dimvec\": [0, 0, 0, 1], \"multiplicity\": 3}",
        );
        assert!(
            mismatches.iter().any(|m| m.contains("decomposition")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_ext_value() {
        let mismatches = corrupted_mismatches(
            "[[1, 0, 0, 0, 0], [0, 1, 0, 0, 0]],",
            "[[1, 0, 0, 0, 0], [0, 7, 0, 0, 0]],",
        );
        assert!(
            mismatches.iter().any(|m| m.contains("Ext(S_")),
            "{mismatches:?}"
        );
    }

    /// The documented coefficient rule applies: a coefficient that reduces to
    /// zero drops its term. Here that empties the only relation of
    /// dual-numbers, and a loop with no relation is infinite dimensional.
    #[test]
    fn compare_rejects_a_relation_that_vanishes_mod_p() {
        let mismatches = corrupted_mismatches(
            "{\"coeff\": 1, \"path\": [0, 0]}",
            "{\"coeff\": 5, \"path\": [0, 0]}",
        );
        assert!(
            mismatches
                .iter()
                .any(|m| m.contains("infinite dimensional")),
            "{mismatches:?}"
        );
    }

    /// The other side of the rule: coefficients congruent mod the field build
    /// the same ideal, so the comparison stays clean.
    #[test]
    fn congruent_coefficients_build_the_same_ideal() {
        let doc = parse_document(&corrupted(
            "{\"coeff\": 1, \"path\": [0, 0]}",
            "{\"coeff\": 6, \"path\": [0, 0]}",
        ))
        .expect("a congruent coefficient still reads");
        assert_eq!(compare(&doc), Vec::<String>::new());
    }
}

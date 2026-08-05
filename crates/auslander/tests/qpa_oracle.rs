//! Differential harness against QPA. Design notes in `tests/qpa-oracle/README.md`.
//!
//! The oracle is `tests/qpa-oracle/qpa_expected.json`. Only a real GAP+QPA run of
//! `generate_fixtures.g` writes it. The always-on test compares the library against
//! it, and a missing file is a hard failure. `native_snapshot.json` is a drift
//! snapshot of this library's own output, not an oracle. `QPA_ORACLE_WRITE=1`
//! rewrites the snapshot and never touches `qpa_expected.json`. `QPA_ORACLE=1`
//! invokes GAP itself and fails hard when GAP or QPA is unavailable, or when any
//! value disagrees.
//!
//! The JSON layer is hand-rolled. The schema is small and fixed, so a writer built
//! on `format!` and a strict recursive-descent reader replace a serde dependency.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
#[cfg(unix)]
use std::process::{Command, Stdio};
use std::sync::Arc;

use auslander::algebra::{
    MonomialAlgebra, an_with_relations, cyclic_nakayama, dual_numbers, kronecker, linear_an,
    linear_nakayama, radical_square_zero_cycle, truncated_poly,
};
use auslander::ar::{Tau, tau};
use auslander::ext::ext_table;
use auslander::field::PrimeField;
use auslander::injective::injective_dimension;
use auslander::module::Module;
use auslander::opposite::opposite;
use auslander::quiver::{ArrowId, Quiver};
use auslander::resolution::Bounded;

const MAX_EXT_DEGREE: usize = 4;
/// Injective dimensions are recorded up to this bound. A simple whose injective
/// dimension exceeds the bound is stored as `INJ_DIM_BOUND + 1`. That value is the
/// payload of the `Bounded::AtLeast` that `injective_dimension` returns, so the
/// encoding loses nothing. QPA's `InjDimensionOfModule` refuses the same way and
/// returns `false`.
const INJ_DIM_BOUND: usize = 6;
const SCHEMA: &str = "auslander-qpa-oracle-v4";
const ROOT_KEYS: [&str; 5] = [
    "schema",
    "convention",
    "max_ext_degree",
    "injdim_bound",
    "fixtures",
];
const FIXTURE_KEYS: [&str; 8] = [
    "name",
    "num_vertices",
    "dim",
    "cartan",
    "tau",
    "tau_injectives",
    "injdim",
    "ext",
];

/// The fixture algebras, under the names used by `generate_fixtures.g`.
fn fixtures() -> Vec<(&'static str, Arc<MonomialAlgebra>)> {
    let d4 = {
        let quiver = Quiver::new(4, &[(0, 3), (1, 3), (2, 3)]).unwrap();
        MonomialAlgebra::new(quiver, Vec::new()).unwrap()
    };
    let gentle = {
        let quiver = Quiver::new(4, &[(0, 1), (1, 2), (1, 3)]).unwrap();
        MonomialAlgebra::new(quiver, vec![vec![ArrowId(0), ArrowId(1)]]).unwrap()
    };
    vec![
        ("linear_an_2", linear_an(2)),
        ("linear_an_3", linear_an(3)),
        ("d4_star", d4),
        ("dual_numbers", dual_numbers()),
        ("truncated_poly_3", truncated_poly(3).unwrap()),
        ("a3_mod_ab", an_with_relations(3, &[(0, 2)]).unwrap()),
        ("kronecker_2", kronecker(2)),
        ("radical_square_zero_cycle_3", radical_square_zero_cycle(3)),
        (
            "linear_nakayama_3_2_1",
            linear_nakayama(&[3, 2, 1]).unwrap(),
        ),
        (
            "linear_nakayama_2_2_1",
            linear_nakayama(&[2, 2, 1]).unwrap(),
        ),
        (
            "cyclic_nakayama_3_3_3",
            cyclic_nakayama(&[3, 3, 3]).unwrap(),
        ),
        ("gentle_tree", gentle),
    ]
}

struct FixtureData {
    name: &'static str,
    num_vertices: usize,
    dim: usize,
    cartan: Vec<Vec<usize>>,
    /// `tau[i]` = dimension vector of `τ S_i`, all zeros when `S_i` is
    /// projective.
    tau: Vec<Vec<usize>>,
    /// `τ` of the simples over the opposite algebra. A left-convention document
    /// records these values, because left `A`-modules are right `A^op`-modules.
    tau_op: Vec<Vec<usize>>,
    /// `tau_injectives[i]` = dimension vector of `τ I_i`, all zeros when
    /// `I_i` is projective. The injective family supplies the non-simple,
    /// multi-entry presentation cases across the suite. Individual `I_i` may
    /// still be simple or projective.
    tau_injectives: Vec<Vec<usize>>,
    /// `τ` of the injectives over the opposite algebra, for left-convention
    /// documents.
    tau_injectives_op: Vec<Vec<usize>>,
    /// `injdim[i]` = injective dimension of `S_i`, capped: `INJ_DIM_BOUND + 1`
    /// stands for "greater than the bound".
    injdim: Vec<usize>,
    /// Injective dimensions of the simples over the opposite algebra. A
    /// left-convention document records these values.
    injdim_op: Vec<usize>,
    /// `ext[i][j][k] = dim Ext^k(S_i, S_j)`, `k = 0..=MAX_EXT_DEGREE`.
    ext: Vec<Vec<Vec<usize>>>,
}

fn injdim_row(algebra: &Arc<MonomialAlgebra>, field: PrimeField) -> Vec<usize> {
    (0..algebra.quiver().num_vertices())
        .map(|v| {
            let s = Module::simple(algebra, field, v);
            match injective_dimension(&s, INJ_DIM_BOUND) {
                Bounded::Exact(d) => d,
                Bounded::AtLeast(d) => d,
            }
        })
        .collect()
}

fn tau_rows(
    algebra: &Arc<MonomialAlgebra>,
    field: PrimeField,
    module: fn(&Arc<MonomialAlgebra>, PrimeField, u32) -> Module,
) -> Vec<Vec<usize>> {
    let n = algebra.quiver().num_vertices();
    (0..n)
        .map(
            |v| match tau(&module(algebra, field, v)).expect("τ routes agree on fixtures") {
                Tau::Zero => vec![0; n as usize],
                Tau::Module(t) => t.dim_vector().to_vec(),
            },
        )
        .collect()
}

fn compute(name: &'static str, algebra: &Arc<MonomialAlgebra>, field: PrimeField) -> FixtureData {
    let n = algebra.quiver().num_vertices();
    let simples: Vec<Module> = (0..n).map(|v| Module::simple(algebra, field, v)).collect();
    let ext = simples
        .iter()
        .map(|si| {
            simples
                .iter()
                .map(|sj| {
                    ext_table(si, sj, MAX_EXT_DEGREE).expect("simples share algebra and field")
                })
                .collect()
        })
        .collect();
    let op = opposite(algebra);
    FixtureData {
        name,
        num_vertices: n as usize,
        dim: algebra.dim(),
        cartan: algebra.cartan_matrix(),
        tau: tau_rows(algebra, field, Module::simple),
        tau_op: tau_rows(op.opposite(), field, Module::simple),
        tau_injectives: tau_rows(algebra, field, Module::injective),
        tau_injectives_op: tau_rows(op.opposite(), field, Module::injective),
        injdim: injdim_row(algebra, field),
        injdim_op: injdim_row(op.opposite(), field),
        ext,
    }
}

/// The fixture data over F_5, after checking that F_2 agrees. Every stored value
/// is characteristic-free, so a disagreement is a library bug, not fixture drift.
fn compute_all() -> Vec<FixtureData> {
    let f2 = PrimeField::new(2).unwrap();
    let f5 = PrimeField::new(5).unwrap();
    fixtures()
        .into_iter()
        .map(|(name, algebra)| {
            let over_f5 = compute(name, &algebra, f5);
            let over_f2 = compute(name, &algebra, f2);
            assert_eq!(
                over_f5.ext, over_f2.ext,
                "{name}: Ext differs between F_2 and F_5"
            );
            assert_eq!(
                (&over_f5.tau, &over_f5.tau_op),
                (&over_f2.tau, &over_f2.tau_op),
                "{name}: τ differs between F_2 and F_5"
            );
            assert_eq!(
                (&over_f5.tau_injectives, &over_f5.tau_injectives_op),
                (&over_f2.tau_injectives, &over_f2.tau_injectives_op),
                "{name}: τ of injectives differs between F_2 and F_5"
            );
            assert_eq!(
                (&over_f5.injdim, &over_f5.injdim_op),
                (&over_f2.injdim, &over_f2.injdim_op),
                "{name}: injective dimensions differ between F_2 and F_5"
            );
            over_f5
        })
        .collect()
}

fn oracle_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/qpa-oracle")
}

fn int_row(row: &[usize]) -> String {
    let items: Vec<String> = row.iter().map(usize::to_string).collect();
    format!("[{}]", items.join(", "))
}

fn int_matrix(mat: &[Vec<usize>]) -> String {
    let rows: Vec<String> = mat.iter().map(|r| int_row(r)).collect();
    format!("[{}]", rows.join(", "))
}

fn render_json(data: &[FixtureData]) -> String {
    let mut out = String::new();
    out.push_str("{\n");
    out.push_str(&format!("  \"schema\": \"{SCHEMA}\",\n"));
    out.push_str("  \"convention\": \"right\",\n");
    out.push_str(&format!("  \"max_ext_degree\": {MAX_EXT_DEGREE},\n"));
    out.push_str(&format!("  \"injdim_bound\": {INJ_DIM_BOUND},\n"));
    out.push_str("  \"fixtures\": [\n");
    for (idx, fx) in data.iter().enumerate() {
        out.push_str("    {\n");
        out.push_str(&format!("      \"name\": \"{}\",\n", fx.name));
        out.push_str(&format!("      \"num_vertices\": {},\n", fx.num_vertices));
        out.push_str(&format!("      \"dim\": {},\n", fx.dim));
        out.push_str(&format!("      \"cartan\": {},\n", int_matrix(&fx.cartan)));
        out.push_str(&format!("      \"tau\": {},\n", int_matrix(&fx.tau)));
        out.push_str(&format!(
            "      \"tau_injectives\": {},\n",
            int_matrix(&fx.tau_injectives)
        ));
        out.push_str(&format!("      \"injdim\": {},\n", int_row(&fx.injdim)));
        out.push_str("      \"ext\": [\n");
        for (i, row) in fx.ext.iter().enumerate() {
            let comma = if i + 1 < fx.ext.len() { "," } else { "" };
            out.push_str(&format!("        {}{comma}\n", int_matrix(row)));
        }
        out.push_str("      ]\n");
        let comma = if idx + 1 < data.len() { "," } else { "" };
        out.push_str(&format!("    }}{comma}\n"));
    }
    out.push_str("  ]\n");
    out.push_str("}\n");
    out
}

/// Minimal JSON reader for the oracle schema. Strict where corruption could
/// hide: duplicate object keys and trailing commas are parse errors, and the
/// comparator rejects unknown keys. Only whitespace is free-form. Numbers are
/// non-negative integers, which is all the schema needs.
mod json {
    #[derive(Debug, Clone, PartialEq)]
    pub enum Value {
        Num(u64),
        Str(String),
        Arr(Vec<Value>),
        Obj(Vec<(String, Value)>),
    }

    impl Value {
        pub fn get(&self, key: &str) -> Option<&Value> {
            match self {
                Value::Obj(pairs) => pairs.iter().find(|(k, _)| k == key).map(|(_, v)| v),
                _ => None,
            }
        }

        /// The object's keys in document order; `None` for non-objects.
        pub fn keys(&self) -> Option<Vec<&str>> {
            match self {
                Value::Obj(pairs) => Some(pairs.iter().map(|(k, _)| k.as_str()).collect()),
                _ => None,
            }
        }

        pub fn as_usize(&self) -> Option<usize> {
            match self {
                Value::Num(n) => usize::try_from(*n).ok(),
                _ => None,
            }
        }

        pub fn as_str(&self) -> Option<&str> {
            match self {
                Value::Str(s) => Some(s),
                _ => None,
            }
        }

        pub fn as_arr(&self) -> Option<&[Value]> {
            match self {
                Value::Arr(items) => Some(items),
                _ => None,
            }
        }

        /// A rectangular array of arrays of integers.
        pub fn as_int_matrix(&self) -> Option<Vec<Vec<usize>>> {
            self.as_arr()?
                .iter()
                .map(|row| row.as_arr()?.iter().map(Value::as_usize).collect())
                .collect()
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
            Some(b'0'..=b'9') => parse_num(bytes, pos),
            other => Err(format!(
                "unexpected {:?} at byte {}",
                other.map(|&b| b as char),
                pos
            )),
        }
    }

    fn parse_num(bytes: &[u8], pos: &mut usize) -> Result<Value, String> {
        let start = *pos;
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

fn transpose(mat: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let cols = mat.first().map_or(0, Vec::len);
    (0..cols)
        .map(|j| mat.iter().map(|row| row[j]).collect())
        .collect()
}

/// Compares one τ matrix field (`tau` or `tau_injectives`) of a fixture.
/// `label` names the row modules in mismatch messages (`S` or `I`).
fn compare_tau_block(
    mismatches: &mut Vec<String>,
    name: &str,
    field: &str,
    label: &str,
    theirs: Option<&json::Value>,
    ours: &[Vec<usize>],
    n: usize,
) {
    match theirs.and_then(json::Value::as_int_matrix) {
        Some(their_tau) => {
            if their_tau.len() != n {
                mismatches.push(format!(
                    "{name}: {field} has {} rows, expected {n}",
                    their_tau.len()
                ));
            }
            for (i, row) in their_tau.iter().enumerate() {
                if row.len() != n {
                    mismatches.push(format!(
                        "{name}: {field} row {i} has {} columns, expected {n}",
                        row.len()
                    ));
                }
            }
            for (i, our_row) in ours.iter().enumerate() {
                if their_tau.get(i) != Some(our_row) {
                    mismatches.push(format!(
                        "{name}: {field}({label}_{i}) is {:?}, ours is {our_row:?}",
                        their_tau.get(i)
                    ));
                }
            }
        }
        None => mismatches.push(format!("{name}: unreadable {field} matrix")),
    }
}

/// Mismatch descriptions from comparing `ours` against a parsed oracle document.
/// With `"convention": "left"` the document's Cartan matrix is transposed, its
/// Ext tables have `(i, j)` swapped, and its tau rows are read as `τ` over the
/// opposite algebra before comparison. Left modules over `A` are right modules
/// over `A^op`, which flips all directed pairings and moves `τ` to `A^op`.
fn compare(ours: &[FixtureData], doc: &json::Value) -> Vec<String> {
    let mut mismatches = Vec::new();
    for key in doc.keys().unwrap_or_default() {
        if !ROOT_KEYS.contains(&key) {
            mismatches.push(format!("unknown top-level key {key:?}"));
        }
    }
    let left_convention = match doc.get("convention").and_then(json::Value::as_str) {
        Some("left") => true,
        Some("right") => false,
        other => {
            mismatches.push(format!(
                "document convention is {other:?}, expected \"left\" or \"right\""
            ));
            false
        }
    };
    let empty = Vec::new();
    let doc_fixtures = doc
        .get("fixtures")
        .and_then(json::Value::as_arr)
        .unwrap_or(&empty);
    let doc_names: Vec<&str> = doc_fixtures
        .iter()
        .filter_map(|v| v.get("name").and_then(json::Value::as_str))
        .collect();
    for (idx, name) in doc_names.iter().enumerate() {
        if doc_names[..idx].contains(name) {
            mismatches.push(format!("{name}: duplicated in oracle file"));
        }
        if !ours.iter().any(|fx| fx.name == *name) {
            mismatches.push(format!("{name}: in oracle file but not a library fixture"));
        }
    }
    if doc_names.len() != doc_fixtures.len() {
        mismatches.push("oracle file has a fixture without a readable name".to_string());
    }
    for fx in ours {
        let Some(theirs) = doc_fixtures
            .iter()
            .find(|v| v.get("name").and_then(json::Value::as_str) == Some(fx.name))
        else {
            mismatches.push(format!("{}: missing from oracle file", fx.name));
            continue;
        };
        for key in theirs.keys().unwrap_or_default() {
            if !FIXTURE_KEYS.contains(&key) {
                mismatches.push(format!("{}: unknown fixture key {key:?}", fx.name));
            }
        }
        if theirs.get("num_vertices").and_then(json::Value::as_usize) != Some(fx.num_vertices) {
            mismatches.push(format!(
                "{}: num_vertices is {:?}, ours is {}",
                fx.name,
                theirs.get("num_vertices"),
                fx.num_vertices
            ));
        }
        if theirs.get("dim").and_then(json::Value::as_usize) != Some(fx.dim) {
            mismatches.push(format!(
                "{}: dim is {:?}, ours is {}",
                fx.name,
                theirs.get("dim"),
                fx.dim
            ));
        }
        match theirs.get("cartan").and_then(json::Value::as_int_matrix) {
            Some(mut cartan) => {
                if left_convention {
                    cartan = transpose(&cartan);
                }
                if cartan != fx.cartan {
                    mismatches.push(format!(
                        "{}: Cartan is {cartan:?}, ours is {:?}",
                        fx.name, fx.cartan
                    ));
                }
            }
            None => mismatches.push(format!("{}: unreadable Cartan matrix", fx.name)),
        }
        compare_tau_block(
            &mut mismatches,
            fx.name,
            "tau",
            "S",
            theirs.get("tau"),
            if left_convention { &fx.tau_op } else { &fx.tau },
            fx.num_vertices,
        );
        compare_tau_block(
            &mut mismatches,
            fx.name,
            "tau_injectives",
            "I",
            theirs.get("tau_injectives"),
            if left_convention {
                &fx.tau_injectives_op
            } else {
                &fx.tau_injectives
            },
            fx.num_vertices,
        );
        let expected_injdim = if left_convention {
            &fx.injdim_op
        } else {
            &fx.injdim
        };
        match theirs
            .get("injdim")
            .and_then(json::Value::as_arr)
            .map(|row| row.iter().map(json::Value::as_usize).collect::<Vec<_>>())
        {
            Some(row) if row.iter().all(Option::is_some) => {
                let row: Vec<usize> = row.into_iter().map(Option::unwrap).collect();
                if row.len() != fx.num_vertices {
                    mismatches.push(format!(
                        "{}: injdim has {} entries, expected {}",
                        fx.name,
                        row.len(),
                        fx.num_vertices
                    ));
                } else if row != *expected_injdim {
                    mismatches.push(format!(
                        "{}: injdim is {row:?}, ours is {expected_injdim:?}",
                        fx.name
                    ));
                }
            }
            _ => mismatches.push(format!("{}: unreadable injdim row", fx.name)),
        }
        let tables = theirs.get("ext").and_then(json::Value::as_arr);
        let n = fx.num_vertices;
        if let Some(rows) = tables {
            if rows.len() != n {
                mismatches.push(format!(
                    "{}: ext has {} rows, expected {n}",
                    fx.name,
                    rows.len()
                ));
            }
            for (i, row) in rows.iter().enumerate() {
                let cols = row.as_arr().map_or(0, <[json::Value]>::len);
                if cols != n {
                    mismatches.push(format!(
                        "{}: ext row {i} has {cols} columns, expected {n}",
                        fx.name
                    ));
                }
            }
        } else {
            mismatches.push(format!("{}: unreadable ext tables", fx.name));
        }
        for (i, our_row) in fx.ext.iter().enumerate() {
            for (j, our_table) in our_row.iter().enumerate() {
                let (ti, tj) = if left_convention { (j, i) } else { (i, j) };
                let their_table = tables
                    .and_then(|rows| rows.get(ti))
                    .and_then(json::Value::as_arr)
                    .and_then(|row| row.get(tj))
                    .and_then(|t| {
                        t.as_arr()?
                            .iter()
                            .map(json::Value::as_usize)
                            .collect::<Option<Vec<usize>>>()
                    });
                if their_table.as_ref() != Some(our_table) {
                    mismatches.push(format!(
                        "{}: Ext(S_{i}, S_{j}) is {their_table:?}, ours is {our_table:?}",
                        fx.name
                    ));
                }
            }
        }
    }
    mismatches
}

/// Reads and parses an oracle-schema JSON file. A missing file and a parse
/// failure are both hard failures, not skips.
fn read_doc(path: &Path) -> json::Value {
    let text =
        fs::read_to_string(path).unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
    json::parse(&text).unwrap_or_else(|e| panic!("cannot parse {}: {e}", path.display()))
}

fn check_schema(path: &Path, doc: &json::Value) {
    assert_eq!(
        doc.get("schema").and_then(json::Value::as_str),
        Some(SCHEMA),
        "{}: wrong or missing schema marker",
        path.display()
    );
    assert_eq!(
        doc.get("max_ext_degree").and_then(json::Value::as_usize),
        Some(MAX_EXT_DEGREE),
        "{}: wrong or missing max_ext_degree",
        path.display()
    );
    assert_eq!(
        doc.get("injdim_bound").and_then(json::Value::as_usize),
        Some(INJ_DIM_BOUND),
        "{}: wrong or missing injdim_bound",
        path.display()
    );
    let convention = doc.get("convention").and_then(json::Value::as_str);
    assert!(
        matches!(convention, Some("left") | Some("right")),
        "{}: convention is {convention:?}, expected \"left\" or \"right\"",
        path.display()
    );
}

/// The committed independent truth: `qpa_expected.json` was produced by a real
/// GAP+QPA run of `generate_fixtures.g` (provenance in `tests/qpa-oracle/README.md`)
/// and is regenerated only by that path, never by this library.
#[test]
fn library_matches_the_committed_qpa_truth() {
    let path = oracle_dir().join("qpa_expected.json");
    let doc = read_doc(&path);
    check_schema(&path, &doc);
    let mismatches = compare(&compute_all(), &doc);
    assert!(
        mismatches.is_empty(),
        "library disagrees with the committed QPA truth:\n{}",
        mismatches.join("\n")
    );
}

/// Self-consistency only: `native_snapshot.json` is this library's own output, so
/// agreement detects drift, not correctness (the oracle test above does that).
/// `QPA_ORACLE_WRITE=1` rewrites the snapshot after an intentional change.
#[test]
fn library_matches_its_native_snapshot() {
    let path = oracle_dir().join("native_snapshot.json");
    let rendered = render_json(&compute_all());
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
    let fresh = read_doc(&fresh_path);
    check_schema(&fresh_path, &fresh);
    let mismatches = compare(&compute_all(), &fresh);
    assert!(
        mismatches.is_empty(),
        "fresh QPA run disagrees with the library:\n{}",
        mismatches.join("\n")
    );
    let committed_path = oracle_dir().join("qpa_expected.json");
    let committed = read_doc(&committed_path);
    assert_eq!(
        fresh, committed,
        "fresh QPA run disagrees with the committed qpa_expected.json; \
         if QPA itself changed, regenerate per tests/qpa-oracle/README.md"
    );
    // The value comparison above gives readable diagnostics. The documented
    // guarantee is byte-for-byte reproducibility, so check that as well.
    let fresh_text =
        fs::read_to_string(&fresh_path).expect("fresh oracle output was already read once");
    let committed_text =
        fs::read_to_string(&committed_path).expect("committed oracle was already read once");
    assert_eq!(
        fresh_text, committed_text,
        "fresh QPA run is value-equal but not byte-identical to qpa_expected.json; \
         regenerate per tests/qpa-oracle/README.md"
    );
    fs::remove_dir_all(&workdir).ok();
}

#[test]
fn oracle_json_round_trips_through_the_reader() {
    let ours = compute_all();
    let doc = json::parse(&render_json(&ours)).expect("writer output parses");
    assert_eq!(
        doc.get("schema").and_then(json::Value::as_str),
        Some(SCHEMA)
    );
    assert_eq!(
        doc.get("max_ext_degree").and_then(json::Value::as_usize),
        Some(MAX_EXT_DEGREE)
    );
    assert_eq!(compare(&ours, &doc), Vec::<String>::new());
}

/// A left-convention document must compare equal after transposition. The check
/// runs on a transposed copy of our own data, with tau over the opposite algebra,
/// so it takes the same code path that GAP output from a left-module build would
/// take.
#[test]
fn left_convention_documents_are_transposed_before_comparison() {
    let ours = compute_all();
    let mut flipped = String::from("{\"convention\": \"left\", \"fixtures\": [");
    for (idx, fx) in ours.iter().enumerate() {
        let ext_t: Vec<String> = (0..fx.num_vertices)
            .map(|i| {
                let row: Vec<String> = (0..fx.num_vertices)
                    .map(|j| int_row(&fx.ext[j][i]))
                    .collect();
                format!("[{}]", row.join(", "))
            })
            .collect();
        flipped.push_str(&format!(
            "{}{{\"name\": \"{}\", \"num_vertices\": {}, \"dim\": {}, \"cartan\": {}, \
             \"tau\": {}, \"tau_injectives\": {}, \"injdim\": {}, \"ext\": [{}]}}",
            if idx == 0 { "" } else { ", " },
            fx.name,
            fx.num_vertices,
            fx.dim,
            int_matrix(&transpose(&fx.cartan)),
            int_matrix(&fx.tau_op),
            int_matrix(&fx.tau_injectives_op),
            int_row(&fx.injdim_op),
            ext_t.join(", ")
        ));
    }
    flipped.push_str("]}");
    let doc = json::parse(&flipped).expect("flipped document parses");
    assert_eq!(compare(&ours, &doc), Vec::<String>::new());
}

/// Corruption regressions: each mutation of the committed truth must be caught.
/// A corrupted convention or num_vertices must not pass the comparator.
mod corruption {
    use super::*;

    fn committed_text() -> String {
        fs::read_to_string(oracle_dir().join("qpa_expected.json")).expect("committed truth exists")
    }

    fn corrupted(from: &str, to: &str) -> json::Value {
        let text = committed_text();
        let replaced = text.replacen(from, to, 1);
        assert_ne!(text, replaced, "corruption target {from:?} not found");
        json::parse(&replaced).expect("corrupted document still parses")
    }

    #[test]
    #[should_panic(expected = "schema")]
    fn schema_check_rejects_the_old_v2_schema_string() {
        let doc = corrupted(
            "\"schema\": \"auslander-qpa-oracle-v4\"",
            "\"schema\": \"auslander-qpa-oracle-v2\"",
        );
        check_schema(Path::new("corrupted"), &doc);
    }

    #[test]
    #[should_panic(expected = "max_ext_degree")]
    fn schema_check_rejects_a_missing_root_field() {
        let doc = corrupted("  \"max_ext_degree\": 4,\n", "");
        check_schema(Path::new("corrupted"), &doc);
    }

    #[test]
    fn compare_rejects_a_missing_fixture_field() {
        let doc = corrupted("      \"dim\": 3,\n", "");
        let mismatches = compare(&compute_all(), &doc);
        assert!(mismatches.iter().any(|m| m.contains("dim is None")));
    }

    #[test]
    fn compare_rejects_an_unknown_top_level_key() {
        let doc = corrupted(
            "\"max_ext_degree\": 4,",
            "\"max_ext_degree\": 4,\n  \"surprise\": 1,",
        );
        let mismatches = compare(&compute_all(), &doc);
        assert!(
            mismatches
                .iter()
                .any(|m| m.contains("unknown top-level key \"surprise\""))
        );
    }

    #[test]
    fn compare_rejects_an_unknown_fixture_key() {
        let doc = corrupted("\"dim\": 3,", "\"dim\": 3,\n      \"surprise\": 1,");
        let mismatches = compare(&compute_all(), &doc);
        assert!(
            mismatches
                .iter()
                .any(|m| m.contains("unknown fixture key \"surprise\""))
        );
    }

    #[test]
    fn parser_rejects_a_duplicated_key() {
        let text = committed_text().replacen("\"dim\": 3,", "\"dim\": 3,\n      \"dim\": 3,", 1);
        let err = json::parse(&text).unwrap_err();
        assert!(err.contains("duplicate key \"dim\""), "{err}");
    }

    #[test]
    fn parser_rejects_a_trailing_comma() {
        let text =
            committed_text().replacen("\"tau\": [[0, 1], [0, 0]]", "\"tau\": [[0, 1], [0, 0],]", 1);
        let err = json::parse(&text).unwrap_err();
        assert!(err.contains("unexpected"), "{err}");
    }

    #[test]
    fn compare_rejects_truncated_tau_row() {
        let doc = corrupted("\"tau\": [[0, 1], [0, 0]]", "\"tau\": [[0, 1], [0]]");
        let mismatches = compare(&compute_all(), &doc);
        assert!(mismatches.iter().any(|m| m.contains("tau row")));
    }

    #[test]
    fn compare_rejects_wrong_tau_value() {
        let doc = corrupted("\"tau\": [[0, 1], [0, 0]]", "\"tau\": [[0, 7], [0, 0]]");
        let mismatches = compare(&compute_all(), &doc);
        assert!(mismatches.iter().any(|m| m.contains("tau(S_")));
    }

    #[test]
    fn compare_rejects_truncated_tau_injectives_row() {
        let doc = corrupted(
            "\"tau_injectives\": [[0, 1], [0, 0]]",
            "\"tau_injectives\": [[0, 1], [0]]",
        );
        let mismatches = compare(&compute_all(), &doc);
        assert!(mismatches.iter().any(|m| m.contains("tau_injectives row")));
    }

    #[test]
    fn compare_rejects_wrong_tau_injectives_value() {
        let doc = corrupted(
            "\"tau_injectives\": [[0, 1], [0, 0]]",
            "\"tau_injectives\": [[0, 7], [0, 0]]",
        );
        let mismatches = compare(&compute_all(), &doc);
        assert!(mismatches.iter().any(|m| m.contains("tau_injectives(I_")));
    }

    #[test]
    #[should_panic(expected = "convention")]
    fn schema_check_rejects_unknown_convention() {
        let doc = corrupted(
            "\"convention\": \"right\"",
            "\"convention\": \"not-a-convention\"",
        );
        check_schema(Path::new("corrupted"), &doc);
    }

    #[test]
    fn compare_rejects_unknown_convention() {
        let doc = corrupted("\"convention\": \"right\"", "\"convention\": \"sideways\"");
        assert!(!compare(&compute_all(), &doc).is_empty());
    }

    #[test]
    fn compare_rejects_wrong_num_vertices() {
        let doc = corrupted("\"num_vertices\": 2,", "\"num_vertices\": 999,");
        let mismatches = compare(&compute_all(), &doc);
        assert!(mismatches.iter().any(|m| m.contains("num_vertices")));
    }

    #[test]
    fn compare_rejects_duplicated_fixture() {
        let doc = corrupted("\"name\": \"linear_an_3\"", "\"name\": \"linear_an_2\"");
        let mismatches = compare(&compute_all(), &doc);
        assert!(mismatches.iter().any(|m| m.contains("duplicated")));
    }

    #[test]
    fn compare_rejects_foreign_fixture_name() {
        let doc = corrupted("\"name\": \"gentle_tree\"", "\"name\": \"bogus_algebra\"");
        let mismatches = compare(&compute_all(), &doc);
        assert!(
            mismatches
                .iter()
                .any(|m| m.contains("not a library fixture"))
                && mismatches.iter().any(|m| m.contains("missing from oracle"))
        );
    }

    #[test]
    fn compare_rejects_truncated_ext_row() {
        let doc = corrupted("[[1, 0, 0, 0, 0], [0, 1, 0, 0, 0]],", "[[1, 0, 0, 0, 0]],");
        let mismatches = compare(&compute_all(), &doc);
        assert!(mismatches.iter().any(|m| m.contains("columns")));
    }

    #[test]
    fn compare_rejects_wrong_ext_value() {
        let doc = corrupted(
            "[[1, 0, 0, 0, 0], [0, 1, 0, 0, 0]],",
            "[[1, 0, 0, 0, 0], [0, 7, 0, 0, 0]],",
        );
        let mismatches = compare(&compute_all(), &doc);
        assert!(mismatches.iter().any(|m| m.contains("Ext")));
    }
}

//! Differential harness against QPA; design notes in `tests/qpa-oracle/README.md`.
//!
//! The oracle is `tests/qpa-oracle/qpa_expected.json`, generated only by an actual
//! GAP+QPA run of `generate_fixtures.g`; the always-on test compares the library
//! against it and a missing file is a hard failure. `native_snapshot.json` is a
//! drift snapshot of this library's own output, not an oracle; `QPA_ORACLE_WRITE=1`
//! rewrites it (and never touches `qpa_expected.json`). `QPA_ORACLE=1` invokes GAP
//! itself and fails hard when GAP or QPA is unavailable or any value disagrees.
//!
//! The JSON layer is hand-rolled: the schema is small and fixed, so a writer built
//! on `format!` and a tolerant recursive-descent reader replace a serde dependency.

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
use auslander::ext::ext_table;
use auslander::field::PrimeField;
use auslander::module::Module;
use auslander::quiver::{ArrowId, Quiver};

const MAX_EXT_DEGREE: usize = 4;
const SCHEMA: &str = "auslander-qpa-oracle-v1";

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
    /// `ext[i][j][k] = dim Ext^k(S_i, S_j)`, `k = 0..=MAX_EXT_DEGREE`.
    ext: Vec<Vec<Vec<usize>>>,
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
    FixtureData {
        name,
        num_vertices: n as usize,
        dim: algebra.dim(),
        cartan: algebra.cartan_matrix(),
        ext,
    }
}

/// The fixture data over F_5, after checking F_2 agrees; every stored value is
/// characteristic-free, so a disagreement is a library bug, not fixture drift.
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
    out.push_str("  \"fixtures\": [\n");
    for (idx, fx) in data.iter().enumerate() {
        out.push_str("    {\n");
        out.push_str(&format!("      \"name\": \"{}\",\n", fx.name));
        out.push_str(&format!("      \"num_vertices\": {},\n", fx.num_vertices));
        out.push_str(&format!("      \"dim\": {},\n", fx.dim));
        out.push_str(&format!("      \"cartan\": {},\n", int_matrix(&fx.cartan)));
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

/// Minimal JSON reader for the oracle schema. Tolerates extra whitespace, trailing
/// commas, and unknown keys; numbers are non-negative integers (all the schema needs).
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
        loop {
            skip_ws(bytes, pos);
            if bytes.get(*pos) == Some(&b']') {
                *pos += 1;
                return Ok(Value::Arr(items));
            }
            items.push(parse_value(bytes, pos)?);
            skip_ws(bytes, pos);
            if bytes.get(*pos) == Some(&b',') {
                *pos += 1;
            }
        }
    }

    fn parse_obj(bytes: &[u8], pos: &mut usize) -> Result<Value, String> {
        expect(bytes, pos, b'{')?;
        let mut pairs = Vec::new();
        loop {
            skip_ws(bytes, pos);
            if bytes.get(*pos) == Some(&b'}') {
                *pos += 1;
                return Ok(Value::Obj(pairs));
            }
            let key = parse_str(bytes, pos)?;
            expect(bytes, pos, b':')?;
            let value = parse_value(bytes, pos)?;
            pairs.push((key, value));
            skip_ws(bytes, pos);
            if bytes.get(*pos) == Some(&b',') {
                *pos += 1;
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

/// Mismatch descriptions from comparing `ours` against a parsed oracle document.
/// With `"convention": "left"` the document's Cartan matrix is transposed and its
/// Ext tables have `(i, j)` swapped before comparison (left modules over `A` are
/// right modules over `A^op`, which flips all directed pairings).
fn compare(ours: &[FixtureData], doc: &json::Value) -> Vec<String> {
    let mut mismatches = Vec::new();
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

/// Reads and parses an oracle-schema JSON file; both a missing file and a parse
/// failure are hard failures, never skips.
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

/// Locates GAP and a loadable QPA, in the order documented in the README: a plain
/// GAP launch when `~/.gap/pkg/qpa` exists (GAP auto-loads packages from `~/.gap`),
/// otherwise a temporary GAP root whose `pkg/qpa` symlinks to `$QPA_DIR` (and
/// `pkg/gbnp` to `$GBNP_DIR` when set; QPA cannot load without its gbnp
/// dependency in some root). The GAP binary is `$GAP_BIN` or `gap`; interactive
/// shells may alias `gap` away, but process spawning here never sees shell aliases.
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
/// no output file, schema mismatch, value mismatch. Unix-only: the GAP root is
/// assembled with symlinks, and GAP itself is not supported on Windows here.
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

/// A left-convention document must compare equal after transposition, checked on a
/// transposed copy of our own data, exercising the same code path the GAP output
/// would take if regenerated under a left-module build.
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
            "{}{{\"name\": \"{}\", \"num_vertices\": {}, \"dim\": {}, \"cartan\": {}, \"ext\": [{}]}}",
            if idx == 0 { "" } else { ", " },
            fx.name,
            fx.num_vertices,
            fx.dim,
            int_matrix(&transpose(&fx.cartan)),
            ext_t.join(", ")
        ));
    }
    flipped.push_str("]}");
    let doc = json::parse(&flipped).expect("flipped document parses");
    assert_eq!(compare(&ours, &doc), Vec::<String>::new());
}

/// Corruption regressions: each mutation of the committed truth must be caught.
/// The review found the original comparator accepted a corrupted convention and
/// num_vertices; these pin the strict validation.
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

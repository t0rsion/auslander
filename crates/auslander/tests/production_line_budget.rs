//! Checks the production code-line ceiling for `crates/auslander/src`.
//!
//! The scan stops at the first column-zero `#[cfg(test)]` and reports code,
//! production, and total lines. Code lines exclude blank lines and lines whose
//! first non-whitespace characters are `//`. The code count is enforced.
//!
//! Test sources, benches, bindings, and documentation are outside the scan.
//! Block comments are unsupported because the scanner is not a Rust lexer.
//! Macro expansion and `include!` content are also outside the count.
//! Moving code outside `src` lowers the count, and line-width changes are not
//! tracked.
//!
//! The ceiling is a constant so the test works in `cargo package`. A second
//! check rejects top-level items after the first test module.

use std::fs;
use std::path::{Path, PathBuf};

/// This file, named in failure messages.
const SELF: &str = "crates/auslander/tests/production_line_budget.rs";

/// The production code-line ceiling.
const PRODUCTION_CODE_CEILING: usize = 42336;

/// The column-zero marker that ends a production region.
const MARKER: &str = "#[cfg(test)]";

/// Returns production `.rs` files under `src`, sorted by path.
fn source_files() -> Vec<PathBuf> {
    let mut out = Vec::new();
    collect(&Path::new(env!("CARGO_MANIFEST_DIR")).join("src"), &mut out);
    out.sort();
    out
}

fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect(&path, out);
        } else if path.extension().and_then(|e| e.to_str()) == Some("rs") && !is_test_source(&path)
        {
            out.push(path);
        }
    }
}

fn is_test_source(path: &Path) -> bool {
    path.file_name()
        .is_some_and(|name| name == "tests.rs" || name.to_string_lossy().ends_with("_tests.rs"))
        || path.components().any(|part| part.as_os_str() == "tests")
}

/// Returns code, production, and total line counts for one file body.
///
/// The production region includes its marker and covers the whole body when
/// no marker exists.
fn count(body: &str) -> (usize, usize, usize) {
    let lines: Vec<&str> = body.lines().collect();
    let total = lines.len();
    let production = lines
        .iter()
        .position(|line| line.starts_with(MARKER))
        .map_or(total, |index| index + 1);
    let code = lines[..production]
        .iter()
        .filter(|line| {
            let text = line.trim_start();
            !text.is_empty() && !text.starts_with("//")
        })
        .count();
    (code, production, total)
}

/// Consumes one line inside an active test module.
fn consume_test_body(line: &str, in_test_module: &mut bool) -> bool {
    if !*in_test_module {
        return false;
    }
    if line.starts_with('}') {
        *in_test_module = false;
    }
    true
}

fn ignored_after_marker(line: &str) -> bool {
    let trimmed = line.trim();
    trimmed.is_empty() || trimmed.starts_with("//") || line.starts_with(char::is_whitespace)
}

fn consume_expected_module(
    line: &str,
    expecting_module: &mut bool,
    in_test_module: &mut bool,
) -> bool {
    if !*expecting_module {
        return false;
    }
    if line.starts_with("#[") {
        return true;
    }
    if line.starts_with("mod ") || line.starts_with("pub mod ") {
        *expecting_module = false;
        *in_test_module = line.ends_with('{');
        return true;
    }
    false
}

/// Returns top-level lines after the first test module.
///
/// The textual check follows rustfmt's column-zero module layout. It does not
/// parse nested braces or distinguish production code placed inside `mod tests`.
fn items_after_tests(body: &str) -> Vec<(usize, String)> {
    let mut out = Vec::new();
    let mut seen_marker = false;
    let mut expecting_module = false;
    let mut in_test_module = false;
    for (index, line) in body.lines().enumerate() {
        if consume_test_body(line, &mut in_test_module) {
            continue;
        }
        if line.starts_with(MARKER) {
            seen_marker = true;
            expecting_module = true;
            continue;
        }
        if !seen_marker {
            continue;
        }
        if ignored_after_marker(line) {
            continue;
        }
        if consume_expected_module(line, &mut expecting_module, &mut in_test_module) {
            continue;
        }
        out.push((index + 1, line.to_string()));
    }
    out
}

/// One measured file: code lines, production lines, total lines, path.
struct Measured {
    code: usize,
    production: usize,
    total: usize,
    path: PathBuf,
}

/// Measures source files, largest code count first.
fn measured() -> Vec<Measured> {
    let mut rows: Vec<Measured> = source_files()
        .into_iter()
        .filter_map(|path| {
            let body = fs::read_to_string(&path).ok()?;
            let (code, production, total) = count(&body);
            Some(Measured {
                code,
                production,
                total,
                path,
            })
        })
        .collect();
    rows.sort_by(|a, b| b.code.cmp(&a.code).then_with(|| a.path.cmp(&b.path)));
    rows
}

#[test]
fn production_code_lines_stay_at_or_below_the_ceiling() {
    let rows = measured();
    assert!(
        rows.len() > 20,
        "the scan found only {} source files, so it is not reaching src; fix \
         the scan before trusting the count",
        rows.len()
    );
    let code: usize = rows.iter().map(|r| r.code).sum();
    let production: usize = rows.iter().map(|r| r.production).sum();
    let total: usize = rows.iter().map(|r| r.total).sum();
    let worst: Vec<String> = rows
        .iter()
        .take(10)
        .map(|r| {
            format!(
                "    {:6} code, {:6} production, {:6} total  {}",
                r.code,
                r.production,
                r.total,
                r.path
                    .file_name()
                    .unwrap_or(r.path.as_os_str())
                    .to_string_lossy()
            )
        })
        .collect();
    assert!(
        code <= PRODUCTION_CODE_CEILING,
        "production is {code} code lines across {} files, {} over the \
         ceiling of {PRODUCTION_CODE_CEILING}. Diagnostics for this tree, not \
         enforced: {production} production lines, {total} total lines across \
         src.\n\nRemove \
         duplicate or unnecessary production code before changing it in \
         {SELF}. Deleting comments does not help: the enforced count already \
         excludes them. Start with the largest files:\n{}",
        rows.len(),
        code - PRODUCTION_CODE_CEILING,
        worst.join("\n")
    );
}

#[test]
fn no_source_file_puts_a_top_level_item_after_its_test_modules() {
    let files = source_files();
    assert!(
        files.len() > 20,
        "the scan found only {} source files, so it is not reaching src",
        files.len()
    );
    let mut found = Vec::new();
    for path in &files {
        let Ok(body) = fs::read_to_string(path) else {
            continue;
        };
        for (line, text) in items_after_tests(&body) {
            found.push(format!("{}:{line}: {text}", path.display()));
        }
    }
    assert!(
        found.is_empty(),
        "these top-level items sit below the first {MARKER}, where the line \
         budget does not count them:\n{}\n\nMove each one above the first test \
         module so it is charged, or delete it. Test code belongs inside a \
         {MARKER} module.",
        found.join("\n")
    );
}

#[test]
fn the_count_stops_at_the_first_column_zero_test_marker() {
    let body = "fn a() {}\nfn b() {}\n#[cfg(test)]\nmod tests {\n    fn c() {}\n}\n";
    assert_eq!(count(body), (3, 3, 6));
}

#[test]
fn an_indented_test_marker_does_not_stop_the_count() {
    let body = "mod inner {\n    #[cfg(test)]\n    mod tests {}\n}\n";
    assert_eq!(count(body), (4, 4, 4));
}

#[test]
fn a_file_without_a_test_marker_counts_whole() {
    let body = "fn a() {}\nfn b() {}\n";
    assert_eq!(count(body), (2, 2, 2));
}

#[test]
fn split_test_sources_are_not_production_files() {
    assert!(is_test_source(Path::new("src/module/tests.rs")));
    assert!(is_test_source(Path::new("src/module/portable_tests.rs")));
    assert!(is_test_source(Path::new("src/module/tests/fixtures.rs")));
    assert!(!is_test_source(Path::new("src/module/test_support.rs")));
}

#[test]
fn blank_lines_and_every_comment_form_are_left_out_of_the_code_count() {
    let body = "//! Module doc.\n\n/// Item doc.\npub fn a() {}\n    // Indented note.\n";
    assert_eq!(count(body), (1, 5, 5));
}

#[test]
fn a_trailing_comment_still_counts_as_a_code_line() {
    let body = "let x = 1; // note\n";
    assert_eq!(count(body), (1, 1, 1));
}

#[test]
fn a_function_after_the_test_module_is_reported() {
    let body = "#[cfg(test)]\nmod tests {\n    fn t() {}\n}\n\npub fn hidden() {}\n";
    let found = items_after_tests(body);
    assert_eq!(found.len(), 1, "expected one item, got {found:?}");
    assert_eq!(found[0], (6, "pub fn hidden() {}".to_string()));
}

#[test]
fn a_second_test_module_after_the_first_is_not_reported() {
    let body = "#[cfg(test)]\nmod first {\n    fn t() {}\n}\n\n#[cfg(test)]\nmod second {\n    fn u() {}\n}\n";
    assert!(items_after_tests(body).is_empty());
}

#[test]
fn comments_and_blank_lines_after_the_test_module_are_not_reported() {
    let body = "#[cfg(test)]\nmod tests {\n    fn t() {}\n}\n\n// A closing note.\n";
    assert!(items_after_tests(body).is_empty());
}

#[test]
fn production_code_above_the_marker_is_counted_and_not_reported() {
    let body = "pub fn a() {}\n#[cfg(test)]\nmod tests {\n}\n";
    assert_eq!(count(body), (2, 2, 4));
    assert!(items_after_tests(body).is_empty());
}

//! The v0.7 production line ceiling for `crates/auslander/src`.
//!
//! The ceiling records the tree after the v0.7 deletion and duplicate-logic
//! pass. It rejects later production growth before the release is rebuilt.
//! One scan of every `src/**/*.rs` produces three numbers:
//!
//! - Production region: every physical line through and including the first
//!   column-zero `#[cfg(test)]`, or the whole file when it has no such marker.
//! - Production lines: the physical lines of that region.
//! - Code lines: the production lines that are neither blank nor a comment.
//!
//! Code lines are the enforced number. Production lines and total lines print
//! on failure as diagnostics. Tests, benches, bindings, and documentation are
//! outside the scan, so they cannot offset production growth.
//!
//! Comments are excluded, so deleting documentation cannot pass the ceiling.
//!
//! A line counts as a comment when its first non-whitespace characters are
//! `//`, which covers `//`, `///`, and `//!`. A trailing comment after code
//! is not stripped, so `let x = 1; // note` counts as one code line. Block
//! comments are not handled: no file under `src` contains `/*` today, and
//! handling them would need a real lexer.
//!
//! The ceiling is a constant, not a git query, because the test also runs
//! inside `cargo package`. The scan starts at `CARGO_MANIFEST_DIR` for the
//! same reason.
//!
//! Only `crates/auslander/src` counts. Code moved to `crates/auslander-py/src`,
//! to a new crate, to `benches`, or into a file pulled in with `include!`
//! keeps working and stops being charged. Macro expansion is free: a
//! `macro_rules!` that generates twenty impls counts as its definition.
//! Neither is detected here. Line width is unwatched: the crate has no
//! `rustfmt.toml`, so `max_width` is the default 100, and a committed
//! `rustfmt.toml` that raises it would lower every count at once.
//!
//! A second gate rejects production items placed below the first test module,
//! where the line scan would otherwise miss them.

use std::fs;
use std::path::{Path, PathBuf};

/// This file, named in failure messages so a reader can find the constants.
const SELF: &str = "crates/auslander/tests/production_line_budget.rs";

/// The v0.7 release production code line count under `crates/auslander/src`.
///
/// Copied from this test's scanner after the release deletion pass.
const V07_CODE_CEILING: usize = 20697;

/// The attribute that ends the production part of a file, at column zero only.
const MARKER: &str = "#[cfg(test)]";

/// Every `.rs` file under the crate's `src`, sorted by path.
///
/// The walk is recursive, so a module moved into a subdirectory keeps counting.
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
        } else if path.extension().and_then(|e| e.to_str()) == Some("rs") {
            out.push(path);
        }
    }
}

/// The code, production, and total line counts of one file body.
///
/// The production region stops at the first line that starts with
/// `#[cfg(test)]` at column zero and includes that line. A body with no such
/// line counts whole. Code lines are the production lines that hold something
/// other than whitespace and do not start with `//` after optional whitespace.
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

/// Column-zero lines after the first `#[cfg(test)]` that are not part of a test
/// module, as line number and text.
///
/// The line counter charges nothing below the first marker, so anything here is
/// production the budget does not see. The scan is textual. After the first
/// marker it expects the rustfmt layout: attributes at column zero, then
/// `mod tests {` at column zero, then an indented body, then `}` at column zero.
/// Blank lines and `//` comments are allowed anywhere. Every other column-zero
/// line outside a test module is reported.
///
/// What it does not catch: a test module written with its closing brace
/// indented, since the scan takes the first column-zero `}` as the end of the
/// module; a raw string inside a test module whose content starts a line with
/// `}`, for the same reason; production code parked inside `mod tests` itself,
/// which the compiler keeps out of the library but the scan cannot see; and any
/// production code above the first marker, which is the normal case and is
/// counted rather than reported.
fn items_after_tests(body: &str) -> Vec<(usize, String)> {
    let mut out = Vec::new();
    let mut seen_marker = false;
    let mut expecting_module = false;
    let mut in_test_module = false;
    for (index, line) in body.lines().enumerate() {
        if in_test_module {
            if line.starts_with('}') {
                in_test_module = false;
            }
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
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with("//") {
            continue;
        }
        // An indented line at this point belongs to an item the scan did not
        // open, so it cannot be the top-level item this gate looks for.
        if line.starts_with(char::is_whitespace) {
            continue;
        }
        if expecting_module {
            if line.starts_with("#[") {
                continue;
            }
            if line.starts_with("mod ") || line.starts_with("pub mod ") {
                expecting_module = false;
                in_test_module = line.ends_with('{');
                continue;
            }
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

/// Every source file measured, largest code count first.
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
fn production_code_lines_stay_at_or_below_the_v07_ceiling() {
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
        code <= V07_CODE_CEILING,
        "production is {code} code lines across {} files, {} over the v0.7 \
         ceiling of {V07_CODE_CEILING}. Diagnostics for this tree, not \
         enforced: {production} production lines, {total} total lines across \
         src.\n\nThe ceiling records the completed v0.7 deletion pass. Remove \
         duplicate or unnecessary production code before changing it in \
         {SELF}. Deleting comments does not help: the enforced count already \
         excludes them. Start with the largest files:\n{}",
        rows.len(),
        code - V07_CODE_CEILING,
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

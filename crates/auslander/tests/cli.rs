//! Fresh-process tests for help, usage errors, atlas summaries, and
//! `auslander classify gentle`.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use auslander::control::ComputationControl;
use auslander::derived_classification::{ClassificationLimits, classify_derived};
use auslander::field::PrimeField;
use auslander::gentle::connected_gentle_algebras;

fn auslander(arguments: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_auslander"))
        .args(arguments)
        .output()
        .unwrap()
}

fn stdout(output: &Output) -> String {
    String::from_utf8(output.stdout.clone()).unwrap()
}

fn committed_atlas() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("artifacts/research/derived-atlas-f2-n3.json")
}

fn scratch(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!("auslander-cli-{}-{name}", std::process::id()))
}

/// Asserts a usage error: exit status 2, the message, and the help hint.
fn assert_usage(arguments: &[&str], message: &str, help: &str) {
    let output = auslander(arguments);
    assert_eq!(output.status.code(), Some(2), "{arguments:?}");
    assert!(output.stdout.is_empty());
    let expected = format!("auslander: {message}\nRun `auslander {help}--help` for usage.\n");
    assert_eq!(String::from_utf8(output.stderr).unwrap(), expected);
}

#[test]
fn every_command_prints_its_help() {
    let cases: [(&[&str], &str); 7] = [
        (&["--help"], "usage: auslander <command> [options]\n"),
        (&["help"], "usage: auslander <command> [options]\n"),
        (&["inspect", "--help"], "usage: auslander inspect FILE\n"),
        (&["verify", "-h"], "usage: auslander verify FILE\n"),
        (
            &["canonicalize", "--help"],
            "usage: auslander canonicalize FILE\n",
        ),
        (
            &["fingerprint", "--help"],
            "usage: auslander fingerprint FILE\n",
        ),
        (
            &["classify", "gentle", "--vertices", "2", "--help"],
            "usage: auslander classify gentle --vertices N [options]\n",
        ),
    ];
    for (arguments, first) in cases {
        let output = auslander(arguments);
        assert!(output.status.success(), "{arguments:?}");
        assert!(stdout(&output).starts_with(first), "{arguments:?}");
        assert!(output.stderr.is_empty());
    }
}

#[test]
fn a_usage_error_prints_one_message_and_a_help_hint() {
    let missing = "/nonexistent/auslander-cli.json";
    let read = format!("cannot read {missing:?}: No such file or directory (os error 2)");
    let classify = ["classify", "gentle"];
    assert_usage(&[], "missing command", "");
    assert_usage(&["check"], "unknown command \"check\"", "");
    assert_usage(&["verify"], "missing FILE", "verify ");
    assert_usage(&["verify", missing], &read, "verify ");
    assert_usage(&["inspect", "--all", "x"], "too many arguments", "inspect ");
    assert_usage(&["verify", "--all"], "unknown option \"--all\"", "verify ");
    assert_usage(
        &["classify"],
        "missing family \"gentle\"",
        "classify gentle ",
    );
    assert_usage(
        &["classify", "tree"],
        "unknown family \"tree\"",
        "classify gentle ",
    );
    assert_usage(&classify, "--vertices is required", "classify gentle ");
    let cases = [
        (
            &["--vertices", "x"][..],
            "--vertices takes a nonnegative integer, found \"x\"",
        ),
        (
            &["--vertices", "-1"],
            "--vertices takes a nonnegative integer, found \"-1\"",
        ),
        (&["--vertices", "0"], "--vertices must be at least 1"),
        (
            &["--vertices", "2", "--field", "4"],
            "--field: modulus 4 is not prime",
        ),
        (
            &["--vertices", "2", "--walk", "8"],
            "unknown option \"--walk\"",
        ),
        (
            &["--vertices", "2", "--vertices", "3"],
            "--vertices is given twice",
        ),
        (&["--vertices"], "--vertices takes a value"),
    ];
    for (options, message) in cases {
        let arguments: Vec<&str> = classify.iter().chain(options).copied().collect();
        assert_usage(&arguments, message, "classify gentle ");
    }
}

#[test]
fn inspect_lists_the_first_ten_classes_of_an_atlas() {
    let output = auslander(&["inspect", committed_atlas().to_str().unwrap()]);
    assert!(output.status.success());
    let text = stdout(&output);
    let lines: Vec<&str> = text.lines().collect();
    let start = lines
        .iter()
        .position(|line| line.starts_with("walks "))
        .unwrap();
    assert_eq!(lines[start + 1], "class 0 members [0]");
    assert_eq!(lines[start + 3], "class 2 members [2, 5]");
    assert!(lines[start + 10].starts_with("class 9 members "));
    assert_eq!(lines[start + 11], "... 30 more classes");
    assert!(lines[start + 12].starts_with("fingerprint "));
    assert!(lines.contains(&"classes 40"));
    assert!(lines.contains(&"status complete"));
}

#[test]
fn verify_marks_the_walk_stops_of_an_open_pair_as_recorded() {
    let family = connected_gentle_algebras(2, PrimeField::new(2).unwrap()).unwrap();
    let limits = ClassificationLimits::with_walk_vertices(1);
    let result = classify_derived(&family, &limits, &ComputationControl::new()).unwrap();
    let path = scratch("open-atlas.json");
    std::fs::write(&path, result.to_artifact().unwrap().to_canonical_json()).unwrap();
    let output = auslander(&["verify", path.to_str().unwrap()]);
    std::fs::remove_file(&path).unwrap();
    assert!(output.status.success());
    let text = stdout(&output);
    let pair = text.lines().find(|line| line.starts_with("pair ")).unwrap();
    let stop = "VertexLimit { stored: 1, limit: 1 }";
    let expected = format!("pair 0 3 walks [0, 1] recorded stops (not replayed) [{stop}, {stop}]");
    assert_eq!(pair, expected);
}

#[test]
fn classify_gentle_writes_a_verified_atlas_and_a_record() {
    let (atlas, record) = (scratch("atlas.json"), scratch("record.json"));
    let output = auslander(&[
        "classify",
        "gentle",
        "--vertices",
        "2",
        "--output",
        atlas.to_str().unwrap(),
        "--record",
        record.to_str().unwrap(),
    ]);
    assert!(output.status.success());
    let text = stdout(&output);
    let mut lines = text.lines();
    assert!(
        lines
            .next()
            .unwrap()
            .starts_with("n  members  classes  merged")
    );
    let rows: Vec<Vec<&str>> = lines
        .by_ref()
        .take(2)
        .map(|line| line.split_whitespace().collect())
        .collect();
    assert_eq!(rows[0][..6], ["1", "2", "2", "0", "1", "0"]);
    assert_eq!(rows[1][..6], ["2", "9", "8", "1", "28", "0"]);
    assert!(text.contains("\natlas: "));
    let record_text = std::fs::read_to_string(&record).unwrap();
    assert!(record_text.starts_with(
        "{\"schema\":\"derived-classification-study-v1\",\"field\":2,\"max_vertices\":2,"
    ));
    let verify = auslander(&["verify", atlas.to_str().unwrap()]);
    let verify = stdout(&verify);
    assert!(verify.starts_with("verified derived-atlas-v1 "));
    assert!(verify.contains("\nmembers 11\nclasses 10\n"));
    assert!(verify.contains("\nclass 9 members "));
    assert!(!verify.contains("more classes"));
    std::fs::remove_file(atlas).unwrap();
    std::fs::remove_file(record).unwrap();
}

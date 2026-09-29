//! The file commands `inspect`, `verify`, `canonicalize`, and `fingerprint`.

use auslander::artifact::{
    ArtifactKind, ArtifactLimits, ArtifactReport, ArtifactVerification, VerifiedArtifact,
    VerifiedArtifactValue, inspect_artifact, verify_artifact,
};
use auslander::control::ComputationControl;
use auslander::derived_classification::DerivedAtlasArtifact;

use crate::{Failure, is_help};

/// The classes and the unresolved pairs an atlas summary lists.
const LISTED: usize = 10;

const INSPECT: &str = "\
usage: auslander inspect FILE

Parses one portable value and prints its schema, kind, summary, and stored
fingerprint. Runs no replay and does not check the fingerprint. For a
derived atlas, also prints the walk count, the first 10 classes, and the
first 10 unresolved pairs with the recorded stops of their walks.
";

const VERIFY: &str = "\
usage: auslander verify FILE

Replays one portable value under the default verifier ceilings. The first
line is the status, the kind, and the fingerprint. The summary lines of
`auslander inspect` follow. A rejected value, or a replay that a verifier
limit stops, prints one error line and exits with status 1. Replay of a
derived atlas does not rerun its walks, so a walk stop stays a recorded
claim.
";

const CANONICALIZE: &str = "\
usage: auslander canonicalize FILE

Replays one portable value as `auslander verify` does, then prints its
canonical JSON.
";

const FINGERPRINT: &str = "\
usage: auslander fingerprint FILE

Replays one portable value as `auslander verify` does, then prints its
fingerprint.
";

const COMMANDS: [(&str, &str); 4] = [
    ("inspect", INSPECT),
    ("verify", VERIFY),
    ("canonicalize", CANONICALIZE),
    ("fingerprint", FINGERPRINT),
];

/// Runs the file command `name` on `arguments`.
pub(crate) fn run(name: &str, arguments: &[String]) -> Result<(), Failure> {
    let Some(&(command, help)) = COMMANDS.iter().find(|(known, _)| *known == name) else {
        return Err(Failure::usage("", format!("unknown command {name:?}")));
    };
    let Some(path) = path(command, arguments)? else {
        print!("{help}");
        return Ok(());
    };
    let text = std::fs::read_to_string(path)
        .map_err(|error| Failure::usage(command, format!("cannot read {path:?}: {error}")))?;
    if command == "inspect" {
        inspect(&text)
    } else {
        replay(command, &text)
    }
}

/// The FILE argument of `command`, or `None` when the arguments ask for
/// help.
fn path<'a>(command: &'static str, arguments: &'a [String]) -> Result<Option<&'a str>, Failure> {
    match arguments {
        [flag] if is_help(flag) => Ok(None),
        [flag] if flag.starts_with('-') => {
            Err(Failure::usage(command, format!("unknown option {flag:?}")))
        }
        [path] => Ok(Some(path)),
        [] => Err(Failure::usage(command, "missing FILE")),
        _ => Err(Failure::usage(command, "too many arguments")),
    }
}

fn replay(command: &str, text: &str) -> Result<(), Failure> {
    let value = verified(text)?;
    let report = value.report();
    match command {
        "verify" => {
            let (status, kind) = (value.status().as_str(), report.kind().name());
            println!("{status} {kind} {}", report.fingerprint());
            print_summary(report);
            if let VerifiedArtifactValue::DerivedAtlas(atlas) = value.value() {
                print_atlas(atlas.artifact());
            }
        }
        "canonicalize" => println!("{}", report.canonical_json()),
        _ => println!("{}", report.fingerprint()),
    }
    Ok(())
}

fn inspect(text: &str) -> Result<(), Failure> {
    let limits = ArtifactLimits::default();
    let report = inspect_artifact(text, &limits).map_err(Failure::failed)?;
    let kind = report.kind();
    println!("schema {}", kind.schema());
    if let Some(payload) = kind.payload_kind() {
        println!("kind {payload}");
    }
    print_summary(&report);
    if kind == ArtifactKind::DerivedAtlas {
        let parse = limits.derived_atlas.parse;
        print_atlas(&DerivedAtlasArtifact::from_json(text, parse).map_err(Failure::failed)?);
    }
    println!("fingerprint {}", report.fingerprint());
    Ok(())
}

/// Replays `text` under the default limits of every kind.
pub(crate) fn verified(text: &str) -> Result<VerifiedArtifact, Failure> {
    let limits = ArtifactLimits::default();
    match verify_artifact(text, &limits, &ComputationControl::new()).map_err(Failure::failed)? {
        ArtifactVerification::Verified(value) => Ok(*value),
        ArtifactVerification::Stopped { cut, .. } => Err(Failure::Failed(format!(
            "artifact verification stopped: {cut:?}"
        ))),
    }
}

fn print_summary(report: &ArtifactReport) {
    for (label, value) in report.summary() {
        println!("{label} {value}");
    }
}

/// Prints the walk count, then the first [`LISTED`] classes and unresolved
/// pairs of `atlas`. A longer list ends with the count it leaves out.
///
/// A pair line marks its walk stops as not replayed: replay checks the
/// member and the merges of a walk, never its stop.
fn print_atlas(atlas: &DerivedAtlasArtifact) {
    println!("walks {}", atlas.walks().len());
    let classes = atlas.classes().iter().enumerate();
    print_listed(
        classes.map(|(index, class)| format!("class {index} members {:?}", class.members())),
        "classes",
    );
    let pairs = atlas.unresolved().iter().map(|pair| {
        let (left, right) = pair.classes();
        let stops: Vec<_> = pair
            .walks()
            .iter()
            .map(|&w| atlas.walks()[w].stop())
            .collect();
        let walks = pair.walks();
        format!("pair {left} {right} walks {walks:?} recorded stops (not replayed) {stops:?}")
    });
    print_listed(pairs, "unresolved pairs");
}

fn print_listed(lines: impl ExactSizeIterator<Item = String>, noun: &str) {
    let total = lines.len();
    for line in lines.take(LISTED) {
        println!("{line}");
    }
    if total > LISTED {
        println!("... {} more {noun}", total - LISTED);
    }
}

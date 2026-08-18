//! Tombstones for retired claims.
//!
//! Three review rounds of v0.5 found no code defect and eleven prose defects:
//! comments asserting a check the code does not perform, a theorem that is not
//! the one used, and measurements from a superseded design. Every one passed
//! the whole test suite, clippy, and rustdoc. In a crate whose product is
//! certified correctness, prose that overstates a guarantee is a defect, and
//! until this file it had no gate.
//!
//! Each entry below is a string that was true once and is false now. The test
//! fails if any reappears outside its allowlist. That catches the two ways
//! these defects arose: a stale number copied forward into a new document, and
//! a block edit that rewrote the head of a paragraph and left its tail
//! contradicting the new text.
//!
//! Adding a tombstone is part of retiring a claim. When a measurement or an
//! API changes, delete the old statement and record it here, so the next
//! attempt to restate it fails loudly instead of shipping.
//!
//! Two limits, both real. The gate cannot check mathematical prose. And it
//! matches LITERAL strings, so a paraphrase of a retired claim passes: a
//! module doc referring to the deleted `Tau::Zero` as "the `Zero` conventions"
//! survived this gate and was caught by a human reading the file. Treat a
//! green run as evidence that known wording did not come back, never as
//! evidence that the prose is true.

use std::fs;
use std::path::{Path, PathBuf};

/// Where a tombstone applies.
#[derive(PartialEq)]
enum Scope {
    /// Anywhere the gate scans. Use for a CLAIM, which is false wherever it is
    /// stated.
    Everywhere,
    /// Rust sources only. Use for a retired NAME: prose that records what was
    /// removed has to name it, while code that still references it is stale.
    CodeOnly,
}

/// A retired claim, with the paths allowed to still contain it.
struct Tombstone {
    /// The literal text that must not reappear.
    text: &'static str,
    /// Why it was retired, printed on failure so the reader does not have to
    /// reconstruct it.
    reason: &'static str,
    /// Whether prose may still mention this, for instance in a removal notice.
    scope: Scope,
    /// Path suffixes permitted to contain `text`. A changelog records history
    /// and legitimately keeps old claims; this file quotes them by definition.
    allowed: &'static [&'static str],
}

const SELF: &str = "tests/prose.rs";

const TOMBSTONES: &[Tombstone] = &[
    Tombstone {
        text: "95.0 ms",
        reason: "measured the assembled-module tau route, which no longer \
                 exists, and predates the identity-keyed cache",
        scope: Scope::Everywhere,
        allowed: &[SELF, "CHANGELOG.md"],
    },
    Tombstone {
        text: "2.77 ms",
        reason: "same superseded measurement as 95.0 ms",
        scope: Scope::Everywhere,
        allowed: &[SELF, "CHANGELOG.md"],
    },
    Tombstone {
        text: "the cache answers from the index alone",
        reason: "TauCache keys on nominal module identity, never on an index. \
                 An index-keyed cache returned another module's translate",
        scope: Scope::Everywhere,
        allowed: &[SELF],
    },
    Tombstone {
        text: "The release is additive",
        reason: "v0.5 removes Algebra::from_monomial, the Tau enum, and three \
                 witness types, and changes Python's Module.tau()",
        scope: Scope::Everywhere,
        // v0.4 WAS additive, and its design doc says so truthfully.
        allowed: &[SELF, "docs/v0.4-design.md"],
    },
    Tombstone {
        text: "3707228",
        reason: "work-unit counts moved when the rates gained the size factor \
                 e; D_4 charges a different count now",
        scope: Scope::Everywhere,
        allowed: &[SELF, "CHANGELOG.md"],
    },
    Tombstone {
        text: "131312",
        reason: "superseded A_3 work-unit count",
        scope: Scope::Everywhere,
        allowed: &[SELF, "CHANGELOG.md"],
    },
    Tombstone {
        text: "131 s at 64",
        reason: "measured the Kronecker walk under a work-unit rate charged by \
                 call, which the size factor replaced",
        scope: Scope::Everywhere,
        allowed: &[SELF, "CHANGELOG.md"],
    },
    Tombstone {
        text: "75.4 s",
        reason: "same superseded Kronecker measurement as the 131 s series",
        scope: Scope::Everywhere,
        allowed: &[SELF, "CHANGELOG.md"],
    },
    Tombstone {
        text: "86 percent",
        reason: "a cost-majority claim about tau that additivity does not \
                 prove and no current measurement supports",
        scope: Scope::Everywhere,
        allowed: &[SELF, "CHANGELOG.md"],
    },
    Tombstone {
        text: "HomVanishingWitness",
        reason: "deleted: a vanishing claim carries no positive witness data, \
                 so private construction of TauRigidModule is the proof token",
        scope: Scope::CodeOnly,
        allowed: &[SELF, "CHANGELOG.md"],
    },
    Tombstone {
        text: "Tau::Zero",
        reason: "the Tau enum is deleted; tau returns the zero module, which \
                 keeps its algebra",
        scope: Scope::CodeOnly,
        allowed: &[
            SELF,
            "CHANGELOG.md",
            "docs/v0.2-plan.md",
            "docs/v0.4-design.md",
        ],
    },
    Tombstone {
        text: "1.77 s to 1.99 s",
        reason: "measured the exhaustive acceptance block while it still ran \
                 the D_4 and A_3 one-tilting sweeps, which are cut",
        scope: Scope::Everywhere,
        allowed: &[SELF],
    },
    Tombstone {
        text: "ClassicalOneTiltingModule",
        reason: "cut before v0.5.0: it verified one supplied module and \
                 enumerated nothing, so it carried none of the release theme. \
                 Tilting returns with the checked complex layer",
        scope: Scope::CodeOnly,
        allowed: &[SELF, "CHANGELOG.md"],
    },
    Tombstone {
        text: "right_approximation",
        reason: "cut with the tilting module: left mutation is the only \
                 production caller of the approximation layer and uses the \
                 left side alone",
        scope: Scope::CodeOnly,
        allowed: &[SELF, "CHANGELOG.md"],
    },
    Tombstone {
        text: "MinimalRightApproximation",
        reason: "the witness type of the removed right_approximation",
        scope: Scope::CodeOnly,
        allowed: &[SELF, "CHANGELOG.md"],
    },
    Tombstone {
        text: "Algebra::from_monomial",
        reason: "deleted: a monomial ideal reaches Algebra as an ordinary \
                 Presentation",
        scope: Scope::CodeOnly,
        allowed: &[
            SELF,
            "CHANGELOG.md",
            "docs/migrating-to-0.3.md",
            "docs/v0.3-design.md",
        ],
    },
];

/// Every tracked source and documentation file this gate scans.
fn scanned_files() -> Vec<PathBuf> {
    // Two layouts have to work. In the workspace the crate sits at
    // `crates/auslander`, and the sweep reaches the bindings and the prose at
    // the workspace root. Inside an extracted `cargo package` tarball the
    // layout is flat: the manifest directory holds `src` and `tests`, there is
    // no workspace above it, and `docs` and `ROADMAP.md` are not shipped.
    // Scanning from the manifest directory covers both, and the workspace
    // paths are added only when they exist.
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR")).to_path_buf();
    let mut out = Vec::new();
    for dir in ["src", "tests", "benches"] {
        collect(&crate_dir.join(dir), &mut out);
    }
    if let Some(root) = crate_dir.parent().and_then(Path::parent) {
        for dir in [root.join("crates/auslander-py/src"), root.join("docs")] {
            collect(&dir, &mut out);
        }
        for file in ["README.md", "ROADMAP.md", "crates/auslander-py/README.md"] {
            let path = root.join(file);
            if path.is_file() {
                out.push(path);
            }
        }
    }
    let crate_readme = crate_dir.join("README.md");
    if crate_readme.is_file() {
        out.push(crate_readme);
    }
    out.sort();
    out.dedup();
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
        } else if matches!(
            path.extension().and_then(|e| e.to_str()),
            Some("rs") | Some("md")
        ) {
            out.push(path);
        }
    }
}

/// Whether `path` ends with any allowlisted suffix, compared with forward
/// slashes so the table reads the same on every platform.
fn allowed(path: &Path, suffixes: &[&str]) -> bool {
    let text = path.to_string_lossy().replace('\\', "/");
    suffixes.iter().any(|s| text.ends_with(s))
}

/// Every tombstone `body` violates at `path`, as printable lines.
///
/// The whole matcher lives here so the gate's own test can drive it with a
/// synthetic path instead of asserting something that is true by construction.
fn violations(path: &Path, body: &str) -> Vec<String> {
    let is_rust = path.extension().and_then(|e| e.to_str()) == Some("rs");
    let mut out = Vec::new();
    for stone in TOMBSTONES {
        if stone.scope == Scope::CodeOnly && !is_rust {
            continue;
        }
        if allowed(path, stone.allowed) {
            continue;
        }
        for (n, line) in body.lines().enumerate() {
            if line.contains(stone.text) {
                out.push(format!(
                    "{}:{}: retired claim {:?}\n    retired because {}",
                    path.display(),
                    n + 1,
                    stone.text,
                    stone.reason
                ));
            }
        }
    }
    out
}

#[test]
fn no_retired_claim_reappears() {
    let files = scanned_files();
    assert!(
        files.len() > 20,
        "the scan found only {} files, so it is not reaching the sources",
        files.len()
    );
    let mut failures = Vec::new();
    for path in &files {
        let Ok(body) = fs::read_to_string(path) else {
            continue;
        };
        failures.extend(violations(path, &body));
    }
    assert!(
        failures.is_empty(),
        "retired claims reappeared:\n{}\n\nEither the claim is true again, in \
         which case remove its tombstone in {SELF} and say why, or the text is \
         stale and should be corrected.",
        failures.join("\n")
    );
}

/// Every tombstone fires through the checker.
///
/// Each entry runs through `violations` at a synthetic path that no allowlist
/// covers, which is the property that matters: the gate catches the string
/// where it should not appear. Scanning the real tree cannot test that. This
/// file holds every tombstone in its own table, so such a scan always finds
/// them and never fails.
#[test]
fn every_tombstone_is_caught_by_the_checker() {
    for stone in TOMBSTONES {
        // A `.rs` path, so both scopes apply, under no allowlisted suffix.
        let fake = PathBuf::from("/synthetic/not-allowlisted/probe.rs");
        let body = format!("prefix {} suffix", stone.text);
        let hits = violations(&fake, &body);
        assert!(
            hits.iter().any(|h| h.contains(stone.text)),
            "tombstone {:?} did not fire through the checker, so it guards \
             nothing",
            stone.text
        );
    }
}

/// A body with no retired claim produces no violation, so the gate is not
/// failing on everything.
#[test]
fn clean_prose_produces_no_violation() {
    let fake = PathBuf::from("/synthetic/not-allowlisted/probe.rs");
    let body = "The cache keys on nominal module identity. Counts are exact.";
    assert!(violations(&fake, body).is_empty());
}

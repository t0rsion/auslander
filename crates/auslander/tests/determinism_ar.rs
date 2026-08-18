//! v0.4 determinism gates for the AR layer (design section 14).
//!
//! In-process: Ext spaces recomputed on separately built identical
//! algebras carry byte-identical bases and representatives. Fresh-process:
//! two spawned children agree on a fingerprint covering the flat Ext
//! complement bases of fixed fixture triples, the chosen AR class
//! coordinates of two modules, and the normalized AR-quiver renderings of
//! one Nakayama and one Dynkin fixture. Golden: the committed renderings
//! under tests/golden-ar/ match byte for byte; regenerate them only after
//! a deliberate format change with
//! `GOLDEN_AR_WRITE=1 cargo test -p auslander --test determinism_ar`.
//!
//! The normalized rendering is a deterministic plain-text format: one line
//! per vertex `v<id> dim=<dim_vector> res=<residue_degree> proj=<bool>
//! inj=<bool>` with the dimension vector comma-joined, one line per arrow
//! `a<source>-><target> base=<n> src=<n> tgt=<n>`, in stored order, LF
//! line endings.

use std::env;
use std::fmt::Write as _;
use std::path::Path;
use std::time::Duration;

use auslander::algebra::{commutative_square, linear_an, truncated_poly};
use auslander::almost_split::{AlmostSplitOutcome, almost_split};
use auslander::arquiver::{ArQuiver, ar_quiver};
use auslander::ext::ExtSpace;
use auslander::indec::IndecomposableModule;
use auslander::module::Module;

mod common;

use common::{f2, f5};

fn normalized_rendering(quiver: &ArQuiver) -> String {
    let mut out = String::new();
    for vertex in quiver.vertices() {
        let dims: Vec<String> = vertex
            .module()
            .module()
            .dim_vector()
            .iter()
            .map(|d| d.to_string())
            .collect();
        writeln!(
            out,
            "v{} dim={} res={} proj={} inj={}",
            vertex.id(),
            dims.join(","),
            vertex.residue_degree(),
            vertex.projective(),
            vertex.injective()
        )
        .unwrap();
    }
    for arrow in quiver.arrows() {
        writeln!(
            out,
            "a{}->{} base={} src={} tgt={}",
            arrow.source(),
            arrow.target(),
            arrow.base_dim(),
            arrow.over_source_residue(),
            arrow.over_target_residue()
        )
        .unwrap();
    }
    out
}

/// The chosen AR class coordinates rendered through `Fp`'s derived Debug.
/// Elements are always reduced, so the rendering is canonical.
fn chosen_class_coords_text(m: &Module) -> String {
    let ind = IndecomposableModule::new(m).unwrap();
    match almost_split(&ind).unwrap() {
        AlmostSplitOutcome::Sequence(sequence) => {
            format!("{:?}", sequence.chosen_ar_class().coordinates())
        }
        AlmostSplitOutcome::Projective => panic!("the fingerprint modules are not projective"),
    }
}

/// The determinism payload: every part is rebuilt from freshly constructed
/// algebras, so two processes agree exactly when every stored matrix,
/// chosen class, and quiver ordering is deterministic.
fn fingerprint_payload() -> String {
    let mut out = String::new();
    let square = commutative_square(f5());
    let simples: Vec<Module> = (0..4).map(|v| Module::simple(&square, v)).collect();
    for (i, j, k) in [(0usize, 1usize, 1usize), (0, 3, 2)] {
        let space = ExtSpace::new(&simples[i], &simples[j], k).unwrap();
        writeln!(
            out,
            "ext:square:{i}:{j}:{k}:{:?}",
            space.complement_basis().entries_u64()
        )
        .unwrap();
    }
    let x3 = truncated_poly(3, f2()).unwrap();
    let s = Module::simple(&x3, 0);
    for k in [1usize, 2] {
        let space = ExtSpace::new(&s, &s, k).unwrap();
        writeln!(
            out,
            "ext:x3:{k}:{:?}",
            space.complement_basis().entries_u64()
        )
        .unwrap();
    }
    writeln!(out, "ar-class:x3-s:{}", chosen_class_coords_text(&s)).unwrap();
    let a3 = linear_an(3, f5());
    writeln!(
        out,
        "ar-class:a3-s1:{}",
        chosen_class_coords_text(&Module::simple(&a3, 1))
    )
    .unwrap();
    out.push_str("ar-quiver:truncated-poly-3-f2\n");
    out.push_str(&normalized_rendering(&ar_quiver(&x3).unwrap()));
    out.push_str("ar-quiver:linear-a3-f5\n");
    out.push_str(&normalized_rendering(&ar_quiver(&a3).unwrap()));
    out
}

const CHILD_ENV: &str = "AUSLANDER_AR_DETERMINISM_CHILD";
const MARKER: &str = "ar-fingerprint:";
/// The child builds two AR quivers, which takes under a second here. The bound
/// exists to turn a hang into a test failure.
const CHILD_TIMEOUT: Duration = Duration::from_secs(120);

fn fingerprint(payload: &str) -> String {
    common::fingerprint(MARKER, payload)
}

#[test]
fn ext_spaces_on_separately_built_identical_algebras_carry_identical_bases() {
    // Each builder constructs its algebra from scratch, so the two spaces
    // share no Arc. The comparison is on raw entries: the deterministic
    // construction must reproduce every stored matrix byte for byte.
    let builders: Vec<Box<dyn Fn() -> ExtSpace>> = vec![
        Box::new(|| {
            let a = linear_an(3, f5());
            ExtSpace::new(&Module::simple(&a, 0), &Module::simple(&a, 1), 1).unwrap()
        }),
        Box::new(|| {
            let a = commutative_square(f5());
            ExtSpace::new(&Module::simple(&a, 0), &Module::simple(&a, 1), 1).unwrap()
        }),
        Box::new(|| {
            let a = commutative_square(f5());
            ExtSpace::new(&Module::simple(&a, 0), &Module::simple(&a, 3), 2).unwrap()
        }),
    ];
    for build in &builders {
        let first = build();
        let second = build();
        assert!(first.dim() > 0, "the fixture triples are nonzero");
        assert_eq!(
            first.cocycle_basis().entries_u64(),
            second.cocycle_basis().entries_u64()
        );
        assert_eq!(
            first.coboundary_basis().entries_u64(),
            second.coboundary_basis().entries_u64()
        );
        assert_eq!(
            first.complement_basis().entries_u64(),
            second.complement_basis().entries_u64()
        );
        let nv = first.source().algebra().quiver().num_vertices();
        for (f, g) in first.representatives().iter().zip(second.representatives()) {
            for v in 0..nv {
                assert_eq!(f.map_at(v).entries_u64(), g.map_at(v).entries_u64());
            }
        }
    }
}

/// Runs only when spawned by the fresh-process gate below; a plain test
/// run passes it vacuously.
#[test]
fn ar_determinism_child_prints_fingerprint() {
    if env::var(CHILD_ENV).is_err() {
        return;
    }
    println!("{}", fingerprint(&fingerprint_payload()));
}

/// Spawns the current test binary on the child test alone and returns the
/// fingerprint line it printed.
fn child_fingerprint() -> String {
    let stdout = common::child_test_stdout(
        "ar_determinism_child_prints_fingerprint",
        CHILD_ENV,
        CHILD_TIMEOUT,
    );
    common::marked_line(&stdout, MARKER)
}

#[test]
fn ar_fingerprint_identical_across_two_fresh_processes() {
    let first = child_fingerprint();
    let second = child_fingerprint();
    assert_eq!(first, second, "fresh processes disagree on the AR layer");
    assert_eq!(
        first,
        fingerprint(&fingerprint_payload()),
        "child processes disagree with this process"
    );
}

fn check_golden(name: &str, committed: &[u8], rendering: &str) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/golden-ar")
        .join(name);
    if common::rewrite_golden("GOLDEN_AR_WRITE", &path, rendering.as_bytes()) {
        return;
    }
    assert_eq!(
        rendering.as_bytes(),
        committed,
        "the AR-quiver rendering for {name} differs from the committed golden file"
    );
}

#[test]
fn truncated_poly_3_f2_rendering_matches_the_golden_file() {
    let algebra = truncated_poly(3, f2()).unwrap();
    check_golden(
        "truncated-poly-3-f2.txt",
        include_bytes!("golden-ar/truncated-poly-3-f2.txt"),
        &normalized_rendering(&ar_quiver(&algebra).unwrap()),
    );
}

#[test]
fn linear_a3_f5_rendering_matches_the_golden_file() {
    let algebra = linear_an(3, f5());
    check_golden(
        "linear-a3-f5.txt",
        include_bytes!("golden-ar/linear-a3-f5.txt"),
        &normalized_rendering(&ar_quiver(&algebra).unwrap()),
    );
}

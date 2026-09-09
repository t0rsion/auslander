/// The committed independent truth: `qpa_expected.json` was produced by a real
/// GAP+QPA run of `generate_fixtures.g` (provenance in `tests/qpa-oracle/README.md`)
/// and is regenerated only by that path, never by this library.
#[test]
fn library_matches_the_committed_qpa_truth() {
    let mismatches = compare_at(&committed_doc(), SttDepth::Slots);
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
    let rendered = rendered_from_computed(&committed_doc());
    if common::rewrite_golden("QPA_ORACLE_WRITE", &path, rendered.as_bytes()) {
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
    let rendered = rendered_from_computed(&committed_doc());
    let parsed = parse_document(&rendered, SNAPSHOT_SCHEMA).expect("writer output parses");
    assert!(!parsed.left_convention);
}

/// The fixture over the opposite presentation: every arrow swaps source and
/// target and every relation term reverses its path. Vertex ids and the arrow
/// order are kept, so an `ArrowId` still names the same arrow, and reversal is
/// injective, so two presentations stay distinct exactly when they were.
/// Relation uniformity and the length-at-least-2 requirement survive it.
fn opposed_presentation(fx: &Fixture) -> Fixture {
    let arrows = fx
        .quiver
        .arrows
        .iter()
        .map(|a| ArrowSpec {
            name: a.name.clone(),
            source: a.target,
            target: a.source,
        })
        .collect();
    let relations = fx
        .relations
        .iter()
        .map(|terms| {
            terms
                .iter()
                .map(|term| TermSpec {
                    coeff: term.coeff,
                    path: term.path.iter().rev().copied().collect(),
                })
                .collect()
        })
        .collect();
    Fixture {
        quiver: QuiverSpec {
            num_vertices: fx.quiver.num_vertices,
            arrows,
        },
        relations,
        ..fx.clone()
    }
}

/// The committed values in the shape the writer takes, so a rendered document
/// carries QPA's numbers rather than this library's.
fn committed_values(fx: &Fixture) -> Computed {
    Computed {
        dim: fx.dim,
        cartan: fx.cartan.clone(),
        injectives: fx.injectives.clone(),
        projdim: fx.projdim.clone(),
        injdim: fx.injdim.clone(),
        tau: fx.tau.clone(),
        tau_injectives: fx.tau_injectives.clone(),
        decomposition: fx.decomposition.clone(),
        ext: fx.ext.clone(),
        designated: fx.designated.clone(),
        ar_sequences: fx.ar_sequences.clone(),
        irreducible_maps: fx.irreducible_maps.clone(),
        ext_algebra: fx.ext_algebra.clone(),
        yoneda_products: fx.yoneda_products.clone(),
        stable_hom: fx.stable_hom.clone(),
        tau_rigid: fx.tau_rigid.clone(),
        rigid: fx.rigid.clone(),
        tau_period: fx.tau_period.clone(),
    }
}

/// The left branch against the committed QPA truth, not against itself.
///
/// A left-convention document over `kQ^op/I^op` asserts values for left modules
/// there. Left modules over `kQ^op/I^op` are right modules over
/// `(kQ^op/I^op)^op = kQ/I`, the algebra QPA measured, so every committed value
/// transfers to the opposed presentation unchanged. The harness takes that
/// second opposite itself in `build_and_compute`, so `compare` runs the whole
/// left path and checks it against independent truth.
#[test]
fn left_convention_documents_compare_over_the_opposite_algebra() {
    let doc = committed_doc();
    let opposed: Vec<Fixture> = doc.fixtures.iter().map(opposed_presentation).collect();
    let values: Vec<Computed> = doc.fixtures.iter().map(committed_values).collect();
    let refs: Vec<(&Fixture, &Computed)> = opposed.iter().zip(&values).collect();
    let rendered = render_document(&refs, "left");
    let parsed =
        parse_document(&rendered, SNAPSHOT_SCHEMA).expect("left-convention document parses");
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
/// recorded agreement (dim, cartan, injectives, projdim, injdim, ext,
/// ext_algebra, rigid) and the recorded differences (tau of S_1, tau of I_2
/// and I_3, the decomposition, the AR sequences, the irreducible maps, stable
/// Hom, one Yoneda product rank, the tau period of S_1, and tau-rigidity of
/// I_3).
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
    assert_eq!(ours2.ext_algebra, ours3.ext_algebra);
    assert_eq!(ours2.rigid, ours3.rigid);
    assert_ne!(ours2.ar_sequences, ours3.ar_sequences);
    assert_ne!(ours2.irreducible_maps, ours3.irreducible_maps);
    assert_ne!(ours2.stable_hom, ours3.stable_hom);
    // The three sharpest differences, all recorded in the oracle README.
    // The designated list is S_0..S_3, then P_0..P_3, then I_0..I_3, so
    // index 1 is S_1 and index 11 is I_3.
    let product = |ours: &Computed| {
        ours.yoneda_products
            .iter()
            .find(|y| (y.i, y.j, y.k) == (0, 2, 3))
            .expect("the triple (S_0, S_2, S_3) has nonzero factors over both fields")
            .yoneda_map_rank
    };
    assert_eq!(product(&ours2), 0, "the product must die over F_2");
    assert_eq!(product(&ours3), 1, "the product must survive over F_3");
    assert_eq!(ours2.tau_period[1], TauPeriod::Period(2));
    assert_eq!(ours3.tau_period[1], TauPeriod::NoneUpTo(6));
    assert!(!ours2.tau_rigid[11], "I_3 is not tau-rigid over F_2");
    assert!(ours3.tau_rigid[11], "I_3 is tau-rigid over F_3");
}

/// The committed truth must carry the exact pinned schema string, so the
/// corruption test below cannot rot into replacing a string that is not
/// there.
#[test]
fn committed_truth_carries_the_pinned_schema() {
    assert!(committed_text().contains(&format!("\"schema\": \"{SCHEMA}\"")));
}

/// `kronecker-2` is tau-tilting infinite, and the oracle records that GAP's
/// AR-quiver walk did not close on it. The library must not close either: both
/// catalog constructors reject the algebra, and a bounded mutation-graph walk
/// returns a typed truncation instead of a pair list. That is the library's
/// truncation cross-checked against GAP's, not a restatement of it.
///
/// The ceiling is the design's 16 vertices. The cost of failing grows steeply
/// with that ceiling, since the preprojective ray carries ever larger modules.
/// The earlier figures measured a work-unit rate this code no longer uses and
/// are not restated.
#[test]
fn kronecker_2_truncates_on_both_sides() {
    let doc = committed_doc();
    let fx = doc
        .fixtures
        .iter()
        .find(|fx| fx.family == "kronecker-2")
        .expect("the oracle carries kronecker-2");
    let stt = fx.stt.as_ref().expect("the oracle is at schema v9");
    assert!(
        matches!(stt.indecomposables, Closure::NotClosed { .. }),
        "the oracle must record that GAP's walk did not close on kronecker-2"
    );
    let algebra = build_algebra(fx).expect("kronecker-2 builds");
    assert!(IndecomposableCatalog::nakayama(&algebra).is_err());
    assert!(IndecomposableCatalog::dynkin(&algebra).is_err());
    let limits = MutationGraphLimits {
        max_vertices: 16,
        ..MutationGraphLimits::default()
    };
    let outcome = support_tau_tilting_graph(&algebra, &limits).expect("the walk runs");
    let incomplete = outcome
        .incomplete()
        .expect("a tau-tilting infinite algebra must not close");
    assert!(
        incomplete.verify_parts(),
        "the certified part of the truncated walk must recheck"
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
    // -q quiet, -T no break loop: a GAP error quits the run instead of waiting
    // for input. The exit code still carries nothing, so the live test reads
    // the sentinel and the output file instead.
    // -m 1g asks for a large initial workspace. GAP 4.16dev segfaults on the v6
    // workload without it, and the flag changes no output value.
    cmd.arg("-q").arg("-T").arg("-m").arg("1g");
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
        // A leading ";" appends the root to the defaults, so stdlib still
        // resolves.
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
    // The exit code carries nothing: `gap -q -T` with closed stdin exits 0
    // after an uncaught error, measured for a division by zero, an unbound
    // variable and a QPA "no method found". The two signals that do carry are
    // the sentinel, printed as the last stdout line after the write, and the
    // output file, written in one final statement.
    assert_eq!(
        stdout.lines().next_back(),
        Some(GENERATOR_SENTINEL),
        "GAP did not print {GENERATOR_SENTINEL} as its last stdout line, so the run \
         aborted; stdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let fresh_path = workdir.join(GENERATOR_OUTPUT);
    assert!(
        fresh_path.exists(),
        "GAP ran but wrote no {}; QPA probably failed to load; stdout:\n{stdout}\nstderr:\n{stderr}",
        fresh_path.display()
    );
    let fresh_text = fs::read_to_string(&fresh_path)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", fresh_path.display()));
    let fresh = parse_document(&fresh_text, SCHEMA)
        .unwrap_or_else(|e| panic!("fresh GAP output {} rejected: {e}", fresh_path.display()));
    let mismatches = compare_at(&fresh, SttDepth::Slots);
    assert!(
        mismatches.is_empty(),
        "fresh QPA run disagrees with the library:\n{}",
        mismatches.join("\n")
    );
    // The check above is the one that carries the mathematics: a real GAP,
    // whatever its version, recomputed these values and agrees with the
    // library. It runs unconditionally.
    //
    // The document comparison below is a different claim, reproducibility of
    // the committed FILE, and it holds only within one GAP version. GAP 4.16dev
    // and the Ubuntu distro package produce documents that differ while both
    // agree with the library, so comparing them byte for byte would fail on a
    // true result. The committed document records the version it came from, so
    // compare only when the fresh run matches it.
    let fresh_gap = provenance_of(&fresh, "gap_version");
    let committed = committed_doc();
    let committed_gap = provenance_of(&committed, "gap_version");
    if fresh_gap != committed_gap {
        eprintln!(
            "live oracle: GAP {fresh_gap} agrees with the library, and the committed document \
             was generated on GAP {committed_gap}. Document comparison skipped: it is defined \
             only within one GAP version. To make this environment the reference, regenerate \
             per tests/qpa-oracle/README.md."
        );
        fs::remove_dir_all(&workdir).ok();
        return;
    }
    assert_eq!(
        fresh, committed,
        "fresh QPA run disagrees with the committed qpa_expected.json on the same GAP version; \
         if QPA itself changed, regenerate per tests/qpa-oracle/README.md"
    );
    // The value comparison above gives readable diagnostics. The guarantee is
    // byte-for-byte reproducibility on the recorded GAP version, so check that
    // as well.
    assert_eq!(
        fresh_text,
        committed_text(),
        "fresh QPA run is value-equal but not byte-identical to qpa_expected.json; \
         regenerate per tests/qpa-oracle/README.md"
    );
    fs::remove_dir_all(&workdir).ok();
}

/// The provenance value `key` records, or `"unrecorded"` when the document
/// carries no such key. Used to compare the GAP version a document came from.
fn provenance_of(doc: &Document, key: &str) -> String {
    doc.provenance
        .iter()
        .find(|(k, _)| k == key)
        .map(|(_, v)| v.clone())
        .unwrap_or_else(|| "unrecorded".to_string())
}

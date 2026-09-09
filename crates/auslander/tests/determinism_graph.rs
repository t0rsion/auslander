//! Fresh-process determinism tests for the support tau-tilting graph.
//!
//! Fresh-process: two spawned children each walk the closed graph of four
//! fixtures and print one fingerprint over the concatenated renderings; the
//! two lines must agree with each other and with this process. Golden: the
//! committed renderings under tests/golden-graph/ match byte for byte;
//! regenerate them only after a deliberate format change with
//! `GOLDEN_GRAPH_WRITE=1 cargo test -p auslander --test determinism_graph`.
//!
//! One core is fine now, and was not before. When `available_parallelism()`
//! returns 1, under `taskset -c 2 cargo test` or on a single-core machine,
//! libtest prints the test name before the test runs instead of after, so a
//! child's `println!` continues that line rather than starting one. A
//! start-anchored search for the marker then found nothing, and every
//! fresh-process gate here, in `determinism_ar.rs` and in
//! `determinism_cert.rs` failed for a reason unrelated to determinism.
//! `common::marked_line` now finds its marker anywhere in a line, which cannot
//! turn a failure into a false pass, and all three gates pass under
//! `taskset -c 2`.
//!
//! Only a `ClosedSupportTauTiltingGraph` is rendered, so every rendering here
//! is of a graph that already passed `ClosureWitness::verify`. A truncated
//! walk has no rendering and fails the test that asked for one.
//!
//! Every test here is always-on. CI runs `cargo test --workspace` and never
//! `--ignored`, so an ignored gate over the closed graph would run on no
//! machine but a developer's. The D_4 walks are the cost, and their closure
//! recheck is the slower half of each walk.
//!
//! # What the rendering covers
//!
//! Every value stored in the graph's witnesses reaches the rendering, either
//! as a printed field or through one of the digests below. Design section 14
//! promises determinism for every stored witness, so a projection that reads
//! only the indices and the dimension vectors is not enough: a witness can
//! change while its projection does not. Over F_5 you can scale a stored
//! forward isomorphism by 2 and its backward partner by 3, and the composite
//! stays an identity, so the witness still verifies and the summand bijection
//! is untouched.
//! `scaling_an_endpoint_isomorphism_over_f5_changes_the_rendering` is that
//! perturbation, and it is what proves the digests reach the stored maps.
//!
//! Three rules make a digest injective enough that one change cannot cancel
//! another out. Every value goes in under a domain tag, so bytes hashed as a
//! forward isomorphism cannot collide with the same bytes hashed as a backward
//! one. Every value goes in with its length, so a concatenation admits one
//! partition only. Matrices and coordinate vectors go in as decimal text
//! through `DenseMat::entries_u64`, so no byte order enters. `Payload` is the
//! builder that applies all three.
//!
//! Three things stay out, and the third is a real gap. The algebra is the
//! fixture's input rather than a product of the walk, and
//! `tests/determinism_cert.rs` gates its completion certificate. Values a
//! witness recomputes on demand, such as `FacWitness::image_dims` and
//! `TauRigidModule::vanishing_pairs`, are functions of data the rendering
//! already covers. And `EndoAlgebra` stores working data for its locality
//! decision that has no accessor: the flattened basis, the coordinate columns,
//! the multiplication tables, the radical complement, the quotient map, and
//! the center with its Frobenius fixed space. The rendering takes the four
//! numbers and two flags that decision reports, plus the algebra basis and the
//! radical basis it runs on, so a drift in the unreachable rows is caught only
//! when it moves one of those. Closing that gap needs a new accessor in
//! `src/endo.rs`.
//!
//! # The format
//!
//! The normalized rendering is a deterministic plain-text format with LF line
//! endings. The first line is the work units the walk charged:
//!
//! ```text
//! units=<count>
//! ```
//!
//! Then one line per vertex, in discovery order:
//!
//! ```text
//! v<index> dim=<summands> proj=<support> slots=<records> mod=<digest> \
//! tau=<digest>
//! ```
//!
//! `<summands>` is the dimension vector of each module summand in stored
//! order, entries joined by commas and summands joined by `|`. `<support>` is
//! the sorted projective-support vertices, joined by commas. `<records>` is
//! one record per module-summand slot in slot order, joined by commas:
//! `e<index>` names the edge the left mutation at that slot stored, and
//! `f<count>:<digest>` marks the `Fac` branch, which admits no left mutation,
//! with the number of maps in the witness and a digest of the whole witness.
//! `mod` digests the certified decomposition of `M`: the assembled module, each
//! summand, and each summand's endomorphism algebra. `tau` digests the
//! tau-rigid data: the summand labels, the summands, and their certified AR
//! translates.
//!
//! Then one line per edge, in stored order:
//!
//! ```text
//! e<index> <source>:<slot>-><target> shape=<shape> exchanged=<dims> \
//! target=<dims> bij=<map> seq=<digest> iso=<digest> mut=<digest> \
//! acp=<digest> add=<digest> approx=<digest>
//! ```
//!
//! `<shape>` is `proj:<vertex>` when the slot moves to the projective support
//! and `module:<multiplicity>` when the cokernel enters the module part.
//! `<dims>` is the dimension vector of the exchanged summand `X_j` and then of
//! the target module part. `<map>` is the summand bijection of the endpoint
//! isomorphism witness, which binds the mutation's own target to the pair
//! stored at `<target>`. The six digests split the edge's stored data by owner,
//! so a diff names the store that moved:
//!
//! - `seq` digests the approximation map `f` and the cokernel map `g`.
//! - `iso` digests the endpoint witness: the bijection, every forward
//!   isomorphism, and every backward isomorphism.
//! - `mut` digests the mutation's own target pair and the witness modules:
//!   the exchanged summand, both module parts with their projective supports,
//!   the replacement, and the obstruction that separates the endpoints.
//! - `acp` digests the almost complete pair: its decomposition, its tau-rigid
//!   data, and its omitted vertex.
//! - `add` digests the two `add` closure witnesses, source then target, each
//!   with `T`, the summands of both sides, and every match's index, forward
//!   map, and backward map.
//! - `approx` digests the approximation past its map: the add-generators with
//!   their endomorphism algebras, the slot list, the block inclusions and
//!   projections, the factorization coordinates, the kernel basis, and the
//!   radical coordinates.
//!
//! An empty field renders as `-`: `dim` and `slots` at the pair `(0, A)`,
//! `proj` wherever the module part supports every vertex, and `bij` on an edge
//! into `(0, A)`.
//!
//! A digest is FNV-1a over a `Payload`, as 16 lowercase hex digits. The digest
//! names no entry, so a diff says which vertex, slot, or edge moved and not
//! how. To see how, print the store the field names at that index.
//!
//! Nothing host-dependent enters a rendering. Work units are charged by call
//! and by module size, so the count is the same in every profile and on every
//! platform, and there is no elapsed time anywhere in the format.

use std::env;
use std::iter;
use std::path::Path;
use std::time::Duration;

use auslander::field::Fp;
use auslander::hom::{Morphism, identity};
use auslander::linalg::DenseMat;

mod common;
#[path = "determinism_graph/fixtures.rs"]
mod fixtures;
#[path = "determinism_graph/payload.rs"]
mod payload;
#[path = "determinism_graph/rendering.rs"]
mod rendering;

use common::f5;
use fixtures::{d4, fingerprint_payload, rendering, walk};
use payload::endpoint_digest;

const CHILD_ENV: &str = "AUSLANDER_GRAPH_DETERMINISM_CHILD";
const MARKER: &str = "graph-fingerprint:";
/// The child walks four graphs, rechecks each closure, and renders every
/// stored witness, which took 0.277 s at the median and 0.379 s at the maximum
/// over nine dev-profile runs here. The bound exists to turn a hang into a test
/// failure.
const CHILD_TIMEOUT: Duration = Duration::from_secs(300);

fn fingerprint(payload: &str) -> String {
    common::fingerprint(MARKER, payload)
}

/// Runs only when spawned by the fresh-process gate below; a plain test run
/// passes it vacuously.
#[test]
fn graph_determinism_child_prints_fingerprint() {
    if env::var(CHILD_ENV).is_err() {
        return;
    }
    println!("{}", fingerprint(&fingerprint_payload()));
}

/// Spawns the current test binary on the child test alone and returns the
/// fingerprint line it printed.
fn child_fingerprint() -> String {
    let stdout = common::child_test_stdout(
        "graph_determinism_child_prints_fingerprint",
        CHILD_ENV,
        CHILD_TIMEOUT,
    );
    common::marked_line(&stdout, MARKER)
}

#[test]
fn graph_fingerprint_identical_across_two_fresh_processes() {
    let first = child_fingerprint();
    let second = child_fingerprint();
    assert_eq!(
        first, second,
        "fresh processes disagree on the support tau-tilting graph"
    );
    assert_eq!(
        first,
        fingerprint(&fingerprint_payload()),
        "child processes disagree with this process"
    );
}

fn check_golden(name: &str, committed: &[u8]) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/golden-graph")
        .join(name);
    let rendering = rendering(name);
    if common::rewrite_golden("GOLDEN_GRAPH_WRITE", &path, rendering.as_bytes()) {
        return;
    }
    assert_eq!(
        rendering.as_bytes(),
        committed,
        "the graph rendering for {name} differs from the committed golden file"
    );
}

#[test]
fn d4_f2_rendering_matches_the_golden_file() {
    check_golden("d4-f2.txt", include_bytes!("golden-graph/d4-f2.txt"));
}

#[test]
fn d4_f5_rendering_matches_the_golden_file() {
    check_golden("d4-f5.txt", include_bytes!("golden-graph/d4-f5.txt"));
}

#[test]
fn linear_a3_f5_rendering_matches_the_golden_file() {
    check_golden(
        "linear-a3-f5.txt",
        include_bytes!("golden-graph/linear-a3-f5.txt"),
    );
}

#[test]
fn radical_square_zero_cycle_3_f2_rendering_matches_the_golden_file() {
    check_golden(
        "radical-square-zero-cycle-3-f2.txt",
        include_bytes!("golden-graph/radical-square-zero-cycle-3-f2.txt"),
    );
}

/// The two D_4 renderings agree once their digests are cut.
///
/// The graph of a hereditary algebra of Dynkin type does not depend on the
/// field, so the vertex, slot, and edge structure over F_2 must equal the one
/// over F_5 line for line. Digests are cut rather than compared: they cover
/// stored matrices, and a matrix over F_2 need not read the same as its
/// partner over F_5. This is a cross-check on the two goldens, not a
/// determinism gate: it would still pass if both files drifted together.
#[test]
fn the_two_d4_renderings_differ_only_in_their_matrix_digests() {
    let over_f2: Vec<String> = rendering("d4-f2.txt")
        .lines()
        .map(without_digests)
        .collect();
    let over_f5: Vec<String> = rendering("d4-f5.txt")
        .lines()
        .map(without_digests)
        .collect();
    assert_eq!(over_f2.len(), over_f5.len());
    for (a, b) in iter::zip(&over_f2, &over_f5) {
        assert_eq!(a, b, "the two D_4 renderings differ outside their digests");
    }
}

/// `line` with its digests dropped, tokens joined by single spaces.
///
/// A digest is the only token of exactly 16 hex characters: every other token
/// is a keyword or a small decimal number.
fn without_digests(line: &str) -> String {
    line.split([' ', ',', ':', '='])
        .filter(|token| token.len() != 16 || !token.chars().all(|c| c.is_ascii_hexdigit()))
        .collect::<Vec<_>>()
        .join(" ")
}

/// `f` with every entry multiplied by `c`, which keeps every commuting square.
fn scaled(f: &Morphism, c: Fp) -> Morphism {
    let field = f.source().field();
    let maps: Vec<DenseMat> = (0..f.source().algebra().quiver().num_vertices())
        .map(|v| {
            let m = f.map_at(v);
            let rows: Vec<Vec<Fp>> = (0..m.rows())
                .map(|r| {
                    (0..m.cols())
                        .map(|col| field.mul(c, m.get(r, col)))
                        .collect()
                })
                .collect();
            if rows.is_empty() {
                DenseMat::zero(0, m.cols())
            } else {
                DenseMat::from_rows(&rows)
            }
        })
        .collect();
    Morphism::new(f.source(), f.target(), maps).expect("scaling keeps A-linearity")
}

/// Scaling a stored endpoint isomorphism by 2 and its inverse by 3 over F_5
/// moves the rendering, though the witness still verifies.
///
/// This is the gate biting on a value the rendering used to omit. The witness
/// stores a summand bijection, a forward isomorphism per summand, and a
/// backward one; the old format recorded the bijection alone. Since 2 times 3
/// is 1 in F_5, both composites stay identities, so the scaled maps pass every
/// check `SupportPairIsoWitness::verify` runs, and the bijection is untouched.
/// Under the old format the rendering was byte identical. Under this one the
/// `iso` digest moves.
///
/// The limit: `SupportPairIsoWitness` has private fields and one constructor,
/// `pair_iso`, so the test cannot build a perturbed witness and hand it to
/// `verify`. It feeds the perturbed maps to the same `endpoint_digest` the
/// rendering calls, and it reruns the two checks `verify` performs on them.
#[test]
fn scaling_an_endpoint_isomorphism_over_f5_changes_the_rendering() {
    let graph = walk(&d4(f5()));
    let field = f5();
    let witness = graph
        .mutations()
        .iter()
        .map(|edge| edge.endpoint())
        .find(|endpoint| !endpoint.forward().is_empty())
        .expect("an edge out of a nonzero pair carries a nonempty endpoint isomorphism");

    let forward: Vec<Morphism> = witness
        .forward()
        .iter()
        .map(|f| scaled(f, field.elem(2)))
        .collect();
    let backward: Vec<Morphism> = witness
        .backward()
        .iter()
        .map(|g| scaled(g, field.elem(3)))
        .collect();

    assert!(
        iter::zip(&forward, witness.forward()).any(|(scaled, stored)| scaled != stored),
        "the perturbation left every stored forward isomorphism where it was"
    );
    for (f, g) in iter::zip(&forward, &backward) {
        let round = f.then(g).expect("the scaled maps still compose");
        let round_back = g.then(f).expect("the scaled maps still compose back");
        assert_eq!(round, identity(f.source()), "2 times 3 is 1 in F_5");
        assert_eq!(round_back, identity(g.source()), "2 times 3 is 1 in F_5");
    }

    assert_ne!(
        endpoint_digest(witness.bijection(), witness.forward(), witness.backward()),
        endpoint_digest(witness.bijection(), &forward, &backward),
        "the rendering misses the stored isomorphisms of the endpoint witness"
    );
}

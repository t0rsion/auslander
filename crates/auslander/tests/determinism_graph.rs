//! v0.5 determinism gates for the support tau-tilting graph (design section
//! 14).
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
//! Every test here is always-on, and nothing sits behind `#[ignore]`. CI runs
//! `cargo test --workspace` and never `--ignored`, so an ignored gate over the
//! closed graph would run on no machine but a developer's. Measured in the dev
//! profile on the development host over nine runs of this binary only, against
//! nine interleaved runs of the binary as it stood before the rendering
//! reached every stored witness:
//!
//! ```text
//!                          median   maximum   median before   maximum before
//! default parallelism      0.70 s   0.80 s    0.60 s          0.70 s
//! --test-threads=1         1.22 s   1.33 s    0.83 s          1.02 s
//! ```
//!
//! The D_4 walks are the cost, and their closure recheck is the slower half of
//! each walk; `taugraph` carries the recheck intervals. Each fixture is walked
//! once per process, and three processes walk them: this one and the two
//! children. One such pass went from 0.220 s to 0.277 s at the median, so the
//! wider rendering costs about 0.06 s per pass. The host throws intermittent
//! machine-check errors, which is why these are medians over nine runs and not
//! single readings.
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

use std::fmt::Write as _;
use std::path::Path;
use std::sync::{Arc, OnceLock};
use std::time::Duration;
use std::{env, iter};

use auslander::algebra::{Algebra, linear_an, path_algebra, radical_square_zero_cycle};
use auslander::approx::MinimalLeftApproximation;
use auslander::basic::{AddClosureWitness, BasicDecomposition, SupportPairObstruction};
use auslander::dynkin::{DynkinType, dynkin_quiver};
use auslander::endo::EndoAlgebra;
use auslander::field::{Fp, PrimeField};
use auslander::hom::{Morphism, identity};
use auslander::homspace::HomSpace;
use auslander::indec::IndecomposableModule;
use auslander::linalg::DenseMat;
use auslander::module::Module;
use auslander::mutation::{ExchangeShape, FacWitness, Mutation};
use auslander::quiver::ArrowId;
use auslander::supporttau::{AlmostCompletePair, SupportTauTiltingPair};
use auslander::taugraph::{
    ClosedSupportTauTiltingGraph, MutationGraphLimits, SlotRecord, SupportTauTiltingGraphOutcome,
    support_tau_tilting_graph,
};
use auslander::taurigid::TauRigidModule;

mod common;

use common::{f2, f5};

/// The zero-ideal path algebra of D_4 as `dynkin_quiver` orients it: vertex 0
/// is the center, arrows `0 -> 1`, `0 -> 2`, `0 -> 3`.
fn d4(field: PrimeField) -> Arc<Algebra> {
    path_algebra(
        dynkin_quiver(DynkinType::D(4)).expect("D_4 has a quiver"),
        field,
    )
    .expect("the zero ideal over an acyclic quiver completes")
}

fn walk(algebra: &Arc<Algebra>) -> ClosedSupportTauTiltingGraph {
    let outcome = support_tau_tilting_graph(algebra, &MutationGraphLimits::default())
        .expect("the fixture walks without a defect");
    match outcome {
        SupportTauTiltingGraphOutcome::Closed(graph) => graph,
        SupportTauTiltingGraphOutcome::Incomplete(graph) => {
            panic!("the walk stopped short: {}", graph.reason())
        }
    }
}

/// A tagged, length-prefixed text buffer, hashed into one digest.
///
/// Every value enters under a domain tag and with the byte length of its body,
/// so bytes hashed as a forward isomorphism cannot collide with the same bytes
/// hashed as a backward one, and a concatenation admits one partition only.
/// Field elements enter as decimal text through `DenseMat::entries_u64`, so no
/// byte order enters.
struct Payload(String);

impl Payload {
    fn new() -> Payload {
        Payload(String::new())
    }

    /// Appends `tag`, the byte length of `body`, and `body`.
    fn field(&mut self, tag: &str, body: &str) {
        write!(self.0, "{tag}({}){body}", body.len()).unwrap();
    }

    /// Appends a payload built by `fill` under `tag`.
    fn group(&mut self, tag: &str, fill: impl FnOnce(&mut Payload)) {
        let mut inner = Payload::new();
        fill(&mut inner);
        self.field(tag, &inner.0);
    }

    fn number(&mut self, tag: &str, value: u64) {
        self.field(tag, &value.to_string());
    }

    fn flag(&mut self, tag: &str, value: bool) {
        self.field(tag, if value { "1" } else { "0" });
    }

    /// Appends the element count and then each value as decimal text.
    fn numbers(&mut self, tag: &str, values: impl IntoIterator<Item = u64>) {
        let mut body = String::new();
        let mut count = 0u64;
        for value in values {
            write!(body, "{value},").unwrap();
            count += 1;
        }
        self.field(tag, &format!("{count}:{body}"));
    }

    fn sizes(&mut self, tag: &str, values: impl IntoIterator<Item = usize>) {
        self.numbers(tag, values.into_iter().map(|v| v as u64));
    }

    fn vertices(&mut self, tag: &str, values: &[u32]) {
        self.numbers(tag, values.iter().copied().map(u64::from));
    }

    /// Appends the shape and then the entries, row by row.
    ///
    /// The shape goes in first, so a zero row and a missing row differ.
    fn matrix(&mut self, tag: &str, m: &DenseMat) {
        self.group(tag, |p| {
            p.number("rows", m.rows() as u64);
            p.number("cols", m.cols() as u64);
            for row in m.entries_u64() {
                p.numbers("row", row);
            }
        });
    }

    /// Appends a coordinate vector, routed through a one-row `DenseMat` for
    /// the same decimal text every matrix gets.
    fn coords(&mut self, tag: &str, values: &[Fp]) {
        let decimals = if values.is_empty() {
            Vec::new()
        } else {
            DenseMat::from_rows(&[values.to_vec()])
                .entries_u64()
                .remove(0)
        };
        self.numbers(tag, decimals);
    }

    /// Appends a module: its dimension vector and its action on every arrow.
    fn module(&mut self, tag: &str, m: &Module) {
        self.group(tag, |p| {
            p.sizes("dim", m.dim_vector().iter().copied());
            for a in 0..m.algebra().quiver().num_arrows() {
                p.matrix("arrow", m.map(ArrowId(a as u32)));
            }
        });
    }

    fn modules<'a>(&mut self, tag: &str, ms: impl IntoIterator<Item = &'a Module>) {
        self.group(tag, |p| {
            let mut count = 0u64;
            for m in ms {
                p.module("m", m);
                count += 1;
            }
            p.number("count", count);
        });
    }

    /// Appends a morphism: both endpoint modules and its matrix at every
    /// vertex.
    ///
    /// The endpoints go in whole rather than as dimension vectors, so a
    /// morphism pins the modules it runs between even where nothing else in
    /// the payload names them. The approximation's `B` and the cokernel `Y`
    /// reach the rendering only this way.
    fn morphism(&mut self, tag: &str, f: &Morphism) {
        self.group(tag, |p| {
            p.module("source", f.source());
            p.module("target", f.target());
            for v in 0..f.source().algebra().quiver().num_vertices() {
                p.matrix("at", f.map_at(v));
            }
        });
    }

    fn morphisms<'a>(&mut self, tag: &str, fs: impl IntoIterator<Item = &'a Morphism>) {
        self.group(tag, |p| {
            let mut count = 0u64;
            for f in fs {
                p.morphism("f", f);
                count += 1;
            }
            p.number("count", count);
        });
    }

    /// Appends an endomorphism algebra: the dimensions it reports, the
    /// identity coordinates, the radical basis, and the algebra basis.
    fn endo(&mut self, tag: &str, e: &EndoAlgebra) {
        self.group(tag, |p| {
            p.number("dim", e.dim() as u64);
            p.number("radical_dim", e.radical_dim() as u64);
            p.number("quotient_dim", e.quotient_dim() as u64);
            p.number("factors", e.semisimple_factor_count() as u64);
            p.flag("local", e.is_local());
            p.flag("quotient_commutative", e.quotient_is_commutative());
            p.coords("one", e.one());
            p.matrix("radical", e.radical_basis());
            p.morphisms("basis", e.basis());
        });
    }

    fn indecomposable(&mut self, tag: &str, x: &IndecomposableModule) {
        self.group(tag, |p| {
            p.module("module", x.module());
            p.endo("endo", x.endo());
        });
    }

    fn decomposition(&mut self, tag: &str, d: &BasicDecomposition) {
        self.group(tag, |p| {
            p.module("module", d.module());
            p.number("count", d.summands().len() as u64);
            for x in d.summands() {
                p.indecomposable("summand", x);
            }
        });
    }

    /// Appends the tau-rigid data: the caller's summand labels, the summands,
    /// and the certified AR translates.
    fn rigid(&mut self, tag: &str, r: &TauRigidModule) {
        self.group(tag, |p| {
            p.number("count", r.summands().len() as u64);
            for (label, m) in r.summands() {
                p.number("label", *label as u64);
                p.module("summand", m);
            }
            p.modules("translates", r.translates());
        });
    }

    fn pair(&mut self, tag: &str, pair: &SupportTauTiltingPair) {
        self.group(tag, |p| {
            p.decomposition("module", pair.module());
            p.vertices("projective", pair.projective().vertices());
            p.rigid("rigid", pair.rigid());
        });
    }

    fn almost_complete(&mut self, tag: &str, pair: &AlmostCompletePair) {
        self.group(tag, |p| {
            p.decomposition("module", pair.module());
            p.vertices("projective", pair.projective().vertices());
            match pair.omitted_vertex() {
                Some(v) => p.number("omitted", u64::from(v)),
                None => p.field("omitted", "-"),
            }
            p.rigid("rigid", pair.rigid());
        });
    }

    /// Appends an `add` closure witness: both sides with their summands, and
    /// every match with its index and its two maps.
    fn add_closure(&mut self, tag: &str, w: &AddClosureWitness) {
        self.group(tag, |p| {
            p.module("module", w.module());
            p.modules("summands", w.summands());
            p.module("target", w.target());
            p.modules("target_summands", w.target_summands());
            p.number("matches", w.matches().len() as u64);
            for entry in w.matches() {
                p.number("target_index", entry.target_index() as u64);
                p.morphism("forward", entry.forward());
                p.morphism("backward", entry.backward());
            }
        });
    }

    fn obstruction(&mut self, tag: &str, o: &SupportPairObstruction) {
        self.group(tag, |p| match o {
            SupportPairObstruction::ProjectiveSupport { first, second } => {
                p.field("kind", "projective-support");
                p.vertices("first", first);
                p.vertices("second", second);
            }
            SupportPairObstruction::SummandCount { first, second } => {
                p.field("kind", "summand-count");
                p.number("first", *first as u64);
                p.number("second", *second as u64);
            }
            SupportPairObstruction::UnmatchedSummand { index, dim_vector } => {
                p.field("kind", "unmatched-summand");
                p.number("index", *index as u64);
                p.sizes("dim", dim_vector.iter().copied());
            }
        });
    }

    /// Appends the approximation past its map.
    ///
    /// The factorization coordinates are stored per add-generator and per
    /// basis map of `Hom(X, N_i)`, and the count of the second index has no
    /// accessor, so this rebuilds that Hom space to walk it. That is the only
    /// Hom system the rendering builds.
    fn approximation(&mut self, tag: &str, a: &MinimalLeftApproximation) {
        self.group(tag, |p| {
            p.number("summands", a.summands().len() as u64);
            for n in a.summands() {
                p.indecomposable("summand", n);
            }
            p.sizes("slots", a.slots().iter().copied());
            p.morphisms("inclusions", a.inclusions());
            p.morphisms("projections", a.projections());
            for (i, n) in a.summands().iter().enumerate() {
                let space = HomSpace::new(a.map().source(), n.module())
                    .expect("the approximation and its add-generator share one algebra");
                p.number("factorizations", space.dim() as u64);
                for j in 0..space.dim() {
                    p.coords("factorization", a.factorization(i, j));
                }
            }
            p.matrix("kernel", a.kernel_basis());
            p.number("radical_rows", a.kernel_basis().rows() as u64);
            for row in 0..a.kernel_basis().rows() {
                p.coords("radical", a.radical_coordinates(row));
            }
        });
    }

    fn fac(&mut self, tag: &str, w: &FacWitness) {
        self.group(tag, |p| {
            p.module("module", w.module());
            p.modules("summands", w.summands());
            p.module("slot_summand", w.summand());
            p.morphisms("maps", w.maps());
        });
    }

    /// Appends a pair isomorphism: the bijection, then the forward maps and
    /// the backward maps under separate tags.
    fn pair_iso(
        &mut self,
        tag: &str,
        bijection: &[usize],
        forward: &[Morphism],
        backward: &[Morphism],
    ) {
        self.group(tag, |p| {
            p.sizes("bijection", bijection.iter().copied());
            p.morphisms("forward", forward);
            p.morphisms("backward", backward);
        });
    }
}

/// FNV-1a over the payload `fill` builds, as 16 lowercase hex digits.
fn digest(fill: impl FnOnce(&mut Payload)) -> String {
    let mut payload = Payload::new();
    fill(&mut payload);
    format!("{:016x}", common::fnv1a(payload.0.as_bytes()))
}

/// The `iso` field of an edge, over the three stores of the endpoint witness.
///
/// Taking the three slices rather than the witness lets
/// `scaling_an_endpoint_isomorphism_over_f5_changes_the_rendering` feed
/// perturbed maps through the same code the rendering uses.
fn endpoint_digest(bijection: &[usize], forward: &[Morphism], backward: &[Morphism]) -> String {
    digest(|p| p.pair_iso("endpoint", bijection, forward, backward))
}

/// `dims` joined by commas, or `-` when it is empty.
fn joined(dims: &[usize]) -> String {
    if dims.is_empty() {
        return "-".to_string();
    }
    dims.iter()
        .map(usize::to_string)
        .collect::<Vec<_>>()
        .join(",")
}

fn vertex_dims(summands: &[Vec<usize>]) -> String {
    if summands.is_empty() {
        return "-".to_string();
    }
    summands
        .iter()
        .map(|dims| joined(dims))
        .collect::<Vec<_>>()
        .join("|")
}

fn support(vertices: &[u32]) -> String {
    if vertices.is_empty() {
        return "-".to_string();
    }
    vertices
        .iter()
        .map(u32::to_string)
        .collect::<Vec<_>>()
        .join(",")
}

fn slot_records(records: &[SlotRecord]) -> String {
    if records.is_empty() {
        return "-".to_string();
    }
    records
        .iter()
        .map(|record| match record {
            SlotRecord::LeftMutation { mutation } => format!("e{mutation}"),
            SlotRecord::NoLeftMutation(witness) => format!(
                "f{}:{}",
                witness.maps().len(),
                digest(|p| p.fac("fac", witness))
            ),
        })
        .collect::<Vec<_>>()
        .join(",")
}

fn shape(shape: &ExchangeShape) -> String {
    match shape {
        ExchangeShape::MovesToProjective { vertex } => format!("proj:{vertex}"),
        ExchangeShape::ReplacedByModule { multiplicity } => format!("module:{multiplicity}"),
    }
}

fn bijection(bijection: &[usize]) -> String {
    if bijection.is_empty() {
        return "-".to_string();
    }
    bijection
        .iter()
        .map(usize::to_string)
        .collect::<Vec<_>>()
        .join(",")
}

/// The `mut` field: the mutation's own target pair and the modules the witness
/// stores around it.
fn mutation_digest(mutation: &Mutation) -> String {
    let witness = mutation.witness();
    digest(|p| {
        p.number("slot", mutation.slot() as u64);
        p.pair("target_pair", mutation.target());
        p.number("witness_slot", witness.slot() as u64);
        p.module("exchanged", witness.exchanged());
        p.module("source_module", witness.source_module());
        p.vertices("source_projective", witness.source_projective());
        p.module("target_module", witness.target_module());
        p.vertices("target_projective", witness.target_projective());
        match witness.replacement() {
            Some(m) => p.module("replacement", m),
            None => p.field("replacement", "-"),
        }
        p.obstruction("distinct", witness.distinct());
    })
}

/// The normalized rendering of `graph`, in the format the module doc states.
fn normalized_rendering(graph: &ClosedSupportTauTiltingGraph) -> String {
    let mut out = String::new();
    writeln!(out, "units={}", graph.work_units()).unwrap();
    for (index, vertex) in graph.vertices().iter().enumerate() {
        writeln!(
            out,
            "v{index} dim={} proj={} slots={} mod={} tau={}",
            vertex_dims(&vertex.pair().module().dim_vectors()),
            support(vertex.pair().projective().vertices()),
            slot_records(vertex.slots()),
            digest(|p| p.decomposition("pair_module", vertex.pair().module())),
            digest(|p| p.rigid("pair_rigid", vertex.pair().rigid())),
        )
        .unwrap();
    }
    for (index, edge) in graph.mutations().iter().enumerate() {
        let witness = edge.mutation().witness();
        let endpoint = edge.endpoint();
        writeln!(
            out,
            "e{index} {}:{}->{} shape={} exchanged={} target={} bij={} seq={} iso={} mut={} \
             acp={} add={} approx={}",
            edge.source(),
            edge.slot(),
            edge.target(),
            shape(edge.mutation().shape()),
            joined(witness.exchanged().dim_vector()),
            joined(witness.target_module().dim_vector()),
            bijection(endpoint.bijection()),
            digest(|p| {
                p.morphism("approximation", witness.approximation().map());
                p.morphism("exchange", witness.exchange());
            }),
            endpoint_digest(
                endpoint.bijection(),
                endpoint.forward(),
                endpoint.backward()
            ),
            mutation_digest(edge.mutation()),
            digest(|p| p.almost_complete("almost_complete", witness.almost_complete())),
            digest(|p| {
                p.add_closure("source_extension", witness.source_extension());
                p.add_closure("target_extension", witness.target_extension());
            }),
            digest(|p| p.approximation("approximation", witness.approximation())),
        )
        .unwrap();
    }
    out
}

/// The four fixtures, each with the file name of its golden.
///
/// D_4 over both fields is what design section 14 names. A_3 and the
/// radical-square-zero 3-cycle come along because they cost little next to
/// D_4 and cover two shapes D_4 does not: a graph on a linear quiver, and one
/// on a quiver with a cycle whose algebra is not hereditary.
///
/// D_4 is the largest fixture. D_5 charges 68381219 work units, past the
/// 50 million default, so it walks only under raised limits. One dev-profile
/// walk of it here took 1.21 s.
fn fixtures() -> Vec<(&'static str, Arc<Algebra>)> {
    vec![
        ("d4-f2.txt", d4(f2())),
        ("d4-f5.txt", d4(f5())),
        ("linear-a3-f5.txt", linear_an(3, f5())),
        (
            "radical-square-zero-cycle-3-f2.txt",
            radical_square_zero_cycle(3, f2()),
        ),
    ]
}

/// The rendering of every fixture, walked once per process.
///
/// The golden tests and the fingerprint read the same values, so one run of
/// this binary walks each fixture once, whichever of its tests run.
fn renderings() -> &'static [(&'static str, String)] {
    static CACHE: OnceLock<Vec<(&'static str, String)>> = OnceLock::new();
    CACHE.get_or_init(|| {
        fixtures()
            .into_iter()
            .map(|(name, algebra)| (name, normalized_rendering(&walk(&algebra))))
            .collect()
    })
}

fn rendering(name: &str) -> &'static str {
    renderings()
        .iter()
        .find(|(fixture, _)| *fixture == name)
        .map(|(_, text)| text.as_str())
        .unwrap_or_else(|| panic!("{name} is not a fixture"))
}

/// The determinism payload: every fixture rendering under its name.
///
/// Two processes agree exactly when the walk order, the vertex indices, the
/// slot branches, the edge order, and every stored witness are deterministic.
fn fingerprint_payload() -> String {
    let mut out = String::new();
    for (name, text) in renderings() {
        writeln!(out, "graph:{name}").unwrap();
        out.push_str(text);
    }
    out
}

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

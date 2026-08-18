//! v0.5 acceptance matrix for the tau-tilting layer (design sections 10, 11,
//! 15).
//!
//! Every number here is derived in the comment above the assertion. Three
//! derivations carry the rest:
//!
//! - Semisimple on `n` vertices has `2^n` pairs. Every module is semisimple
//!   and projective, so `tau = 0`, every subset of the simples is tau-rigid,
//!   and `|M| + |P| = n` forces `P` to be the complementary vertex set.
//! - Over a hereditary algebra of Dynkin type the pairs with `|M| = k` are the
//!   tilting modules of the full subquiver on a `k`-subset of the vertices.
//!   The number of tilting modules of type `T` is the positive Catalan number
//!   `prod_i (e_i + h - 1) / (e_i + 1)`, taken over the exponents `e_i` of `T`
//!   with `h` its Coxeter number. That count is 2 for `A_2`, 5 for `A_3`, and
//!   20 for `D_4`. Summing over subsets gives the histograms and the totals 5,
//!   14, and 50.
//! - On the two Nakayama fixtures the indecomposables and `tau` are short
//!   enough to list, so the pair sets are counted by hand in `catalog_fixtures`.
//!
//! Tier split, design section 11. Measured on this branch in the dev profile
//! (`opt-level = 2`) on the development host, this binary only:
//!
//! ```text
//! always-on block, default parallelism      0.12 s to 0.16 s over three runs
//! always-on block, --test-threads=1         0.18 s to 0.24 s over five runs
//! exhaustive block, --ignored               0.74 s to 0.94 s over three runs
//! ```
//!
//! Ranges, not medians, because the host runs other work. The per-block
//! breakdown that once stood here was measured before the tau cache was keyed
//! by module identity and is not restated: a stale number reads as a current
//! one.
//!
//! The design puts the D_4 walk in the always-on block. It does not fit: a
//! D_4 walk and its closure recheck cost more over two fields than the whole
//! always-on budget above, and the recheck is the slower half. The per-walk
//! figures that once stood here predate the closure gate and the identity-keyed
//! cache; `taugraph` carries the current recheck intervals. D_4 keeps its
//! always-on catalog route and moves its walk to `#[ignore]`, together with
//! the 16-vertex Kronecker walk. Nothing is dropped; the heavy cases run
//! under `cargo test -- --ignored`.
//!
//! What "tampered" means here. Every witness type has private fields and no
//! public mutator, so an integration test cannot corrupt a stored witness. It
//! can only hand a checking constructor input that fails the condition, which
//! is what `the_checking_constructors_reject_input_that_fails_a_condition`
//! does. Field-level tampering is the in-module corpus of design section 15.

use std::collections::BTreeSet;
use std::sync::{Arc, OnceLock};

use auslander::algebra::{
    Algebra, kronecker, linear_an, linear_nakayama, path_algebra as kq, radical_square_zero_cycle,
    truncated_poly,
};
use auslander::approx::{ApproxError, left_approximation};
use auslander::arquiver::{CatalogProvenance, IndecomposableCatalog};
use auslander::basic::{
    AddClosureWitness, BasicDecomposition, ProjectiveSupport, SupportPairIsoOutcome, pair_iso,
};
use auslander::dynkin::{DynkinError, DynkinType, EuclideanType, dynkin_quiver};
use auslander::enumerate::EnumerateError;
use auslander::field::PrimeField;
use auslander::module::{Module, direct_sum};
use auslander::mutation::{ExchangeShape, MutationError, SlotOutcome, mutate_at};
use auslander::quiver::Quiver;
use auslander::supporttau::{
    AlmostCompleteClassification, AlmostCompletePair, CatalogEnumeration, PairRejection,
    SupportTauTiltingClassification, SupportTauTiltingPair, enumerate_over_catalog,
};
use auslander::taugraph::{
    ClosedSupportTauTiltingGraph, GraphLimit, IncompleteReason, IncompleteSupportTauTiltingGraph,
    MutationGraphLimits, SlotRecord, SupportTauTiltingGraphOutcome, support_tau_tilting_graph,
};
use auslander::taurigid::{TauRigidityOutcome, is_tau_rigid};

mod common;

use common::{f2, f5};

fn fields() -> [PrimeField; 2] {
    [f2(), f5()]
}

fn path_algebra(quiver: Quiver, field: PrimeField) -> Arc<Algebra> {
    kq(quiver, field).expect("the zero ideal over an acyclic quiver completes")
}

/// The semisimple algebra on `n` vertices: `n` vertices, no arrows.
fn semisimple(n: u32, field: PrimeField) -> Arc<Algebra> {
    path_algebra(
        Quiver::new(n, &[]).expect("no arrow is out of range"),
        field,
    )
}

/// The zero-ideal path algebra of D_4 as `dynkin_quiver` orients it: vertex 0
/// is the center, arrows `0 -> 1`, `0 -> 2`, `0 -> 3`.
fn d4(field: PrimeField) -> Arc<Algebra> {
    path_algebra(
        dynkin_quiver(DynkinType::D(4)).expect("D_4 has a quiver"),
        field,
    )
}

/// One algebra with an exhaustive catalog, the derived pair count, and the
/// derived histogram by `|M|`.
///
/// Both routes run over the `algebra` value stored here, because `pair_iso`
/// requires one `Arc<Algebra>` across all four of its arguments.
struct Fixture {
    /// Stable across fields, so a test can pick one algebra out of the cache.
    id: &'static str,
    /// `id` with the field, for assertion messages.
    name: String,
    algebra: Arc<Algebra>,
    catalog: IndecomposableCatalog,
    provenance: CatalogProvenance,
    pairs: usize,
    histogram: Vec<usize>,
    /// Whether the always-on tier walks the mutation graph over this algebra.
    /// See the tier table in the module documentation.
    walk_always_on: bool,
}

/// The nine catalog fixtures over one field, with the counts derived here.
fn catalog_fixtures(field: PrimeField) -> Vec<Fixture> {
    let p = field.modulus();
    let mut out = Vec::new();
    let mut push = |id: &'static str,
                    algebra: Arc<Algebra>,
                    catalog: IndecomposableCatalog,
                    provenance: CatalogProvenance,
                    pairs: usize,
                    histogram: Vec<usize>,
                    walk_always_on: bool| {
        out.push(Fixture {
            id,
            name: format!("{id} over F_{p}"),
            algebra,
            catalog,
            provenance,
            pairs,
            histogram,
            walk_always_on,
        });
    };

    // Semisimple on n vertices: the indecomposables are the n simples, tau is
    // zero on all of them, so every subset is tau-rigid and P is forced to be
    // the complement. Pairs 2^n, histogram the binomial row.
    for (id, n, pairs, histogram, walk) in [
        ("semisimple(2)", 2u32, 4usize, vec![1usize, 2, 1], true),
        ("semisimple(3)", 3, 8, vec![1, 3, 3, 1], true),
        ("semisimple(4)", 4, 16, vec![1, 4, 6, 4, 1], true),
    ] {
        let algebra = semisimple(n, field);
        let catalog = IndecomposableCatalog::nakayama(&algebra).expect("no arrow means Nakayama");
        push(
            id,
            algebra,
            catalog,
            CatalogProvenance::Nakayama,
            pairs,
            histogram,
            walk,
        );
    }

    // A_2: the pentagon, listed pair by pair in
    // `the_a2_pentagon_matches_the_hand_computation`. Histogram [1, 2, 2]: the
    // empty pair, the two supports of size one, and the two tilting modules
    // P_0 + P_1 and P_0 + S_0.
    let a2 = linear_an(2, field);
    let catalog = IndecomposableCatalog::dynkin(&a2).expect("A_2 is Dynkin");
    push(
        "linear_an(2)",
        a2,
        catalog,
        CatalogProvenance::DynkinZeroIdeal,
        5,
        vec![1, 2, 2],
        true,
    );

    // A_3, hereditary, so the pairs with |M| = k are the tilting modules of
    // the full subquiver on a k-subset of {0, 1, 2} with arrows 0 -> 1 -> 2.
    // k = 0: 1. k = 1: three A_1 subquivers, 1 each, so 3. k = 2: {0,1} and
    // {1,2} are A_2 with 2 each, {0,2} is A_1 + A_1 with 1, so 5. k = 3: the
    // positive Catalan number of A_3, (4/2)(5/3)(6/4) = 5. Total 14, the
    // Catalan number C_4.
    let a3 = linear_an(3, field);
    let catalog = IndecomposableCatalog::dynkin(&a3).expect("A_3 is Dynkin");
    push(
        "linear_an(3)",
        a3,
        catalog,
        CatalogProvenance::DynkinZeroIdeal,
        14,
        vec![1, 3, 5, 5],
        true,
    );

    // k[x]/(x^3), one vertex, so |M| + |P| = 1. The indecomposables are
    // k[x]/(x), k[x]/(x^2) and A itself. The algebra is self-injective with
    // Omega(k[x]/(x^l)) = k[x]/(x^{3-l}), so tau = Omega^2 fixes the two
    // non-projectives and each of them has a nonzero map to itself. Only
    // M = A is tau-rigid, so the pairs are (A, 0) and (0, A).
    let tp = truncated_poly(3, field).expect("x^3 is admissible");
    let catalog = IndecomposableCatalog::nakayama(&tp).expect("one loop is Nakayama");
    push(
        "truncated_poly(3)",
        tp,
        catalog,
        CatalogProvenance::Nakayama,
        2,
        vec![1, 1],
        true,
    );

    // The 3-cycle with rad^2 = 0. Indecomposables S_0, S_1, S_2 and P_0, P_1,
    // P_2, where P_i has dimension 1 at i and 1 at i+1. The algebra is
    // self-injective with I_i = P_{i-1}, so tau = nu Omega^2 sends S_i to
    // S_{i+1} and kills every P_i. Writing A for the simple indices in M and B
    // for the projective ones, M is tau-rigid exactly when j in A forces j+1
    // outside A and outside B, and supp M = A + B + (B+1). Counting (A, B, V)
    // with V inside the complement of supp M and |V| = 3 - |M|:
    // |M| = 0 gives 1; |M| = 1 gives 3, since only a simple leaves room for
    // two support vertices; |M| = 2 gives 6, namely S_j with P_j or with
    // P_{j+2} over three j; |M| = 3 gives 4, namely S_j + P_j + P_{j+2} over
    // three j, plus A itself. Total 14.
    let cycle = radical_square_zero_cycle(3, field);
    let catalog = IndecomposableCatalog::nakayama(&cycle).expect("a cycle is Nakayama");
    push(
        "radical_square_zero_cycle(3)",
        cycle,
        catalog,
        CatalogProvenance::Nakayama,
        14,
        vec![1, 3, 6, 4],
        true,
    );

    // Linear Nakayama [2, 2, 1] on 0 -> 1 -> 2: P_0 = [1,1,0], P_1 = [0,1,1],
    // P_2 = S_2, and the five indecomposables are S_0, P_0, S_1, P_1, S_2. The
    // injectives are I_0 = S_0, I_1 = P_0, I_2 = P_1, so tau S_0 = S_1 and
    // tau S_1 = S_2, and tau kills the three projectives. Tau-rigidity reads
    // "S_0 in M forbids S_1 and P_1" and "S_1 in M forbids S_2". Counting with
    // |V| = 3 - |M| inside the complement of supp M: |M| = 0 gives 1;
    // |M| = 1 gives 3, the three simples; |M| = 2 gives 5, namely S_0+P_0,
    // S_0+S_2, P_0+S_1, S_1+P_1, P_1+S_2; |M| = 3 gives 3, namely S_0+P_0+S_2,
    // P_0+S_1+P_1, P_0+P_1+S_2. Total 12.
    let nakayama = linear_nakayama(&[2, 2, 1], field).expect("[2, 2, 1] is a Kupisch series");
    let catalog = IndecomposableCatalog::nakayama(&nakayama).expect("a linear quiver is Nakayama");
    push(
        "linear_nakayama([2, 2, 1])",
        nakayama,
        catalog,
        CatalogProvenance::Nakayama,
        12,
        vec![1, 3, 5, 3],
        true,
    );

    // D_4, hereditary, center 0 and leaves 1, 2, 3, counted by subquiver as
    // A_3 was. k = 0: 1. k = 1: four A_1, so 4. k = 2: the three subsets
    // holding the center are A_2 with 2 each, the three leaf pairs are
    // A_1 + A_1 with 1 each, so 9. k = 3: the three subsets holding the center
    // are A_3 with 5 each, the leaf triple is A_1^3 with 1, so 16. k = 4: the
    // positive Catalan number of D_4, (6/2)(8/4)(8/4)(10/6) = 20. Total 50.
    let d4 = d4(field);
    let catalog = IndecomposableCatalog::dynkin(&d4).expect("D_4 is Dynkin");
    push(
        "dynkin_quiver(D(4))",
        d4,
        catalog,
        CatalogProvenance::DynkinZeroIdeal,
        50,
        vec![1, 4, 9, 16, 20],
        false,
    );

    out
}

/// One fixture with the routes the always-on tier runs over it.
struct Computed {
    fixture: Fixture,
    listed: CatalogEnumeration,
    /// `None` when the walk over this algebra belongs to the exhaustive tier.
    graph: Option<ClosedSupportTauTiltingGraph>,
}

/// The nine fixtures over both fields, with the catalog route run once and the
/// mutation walk run once where the always-on tier covers it.
///
/// Ten tests read this list. The walks and the enumerations are the largest
/// single cost of the always-on block, so they run once for the whole binary
/// rather than once per test.
fn computed() -> &'static [Computed] {
    static CACHE: OnceLock<Vec<Computed>> = OnceLock::new();
    CACHE.get_or_init(|| {
        let mut out = Vec::new();
        for field in fields() {
            for fixture in catalog_fixtures(field) {
                let listed = enumerate_over_catalog(&fixture.catalog)
                    .expect("an exhaustive catalog enumerates without a defect");
                let graph = fixture.walk_always_on.then(|| walk(&fixture.algebra));
                out.push(Computed {
                    fixture,
                    listed,
                    graph,
                });
            }
        }
        out
    })
}

/// The cached entries the always-on tier walks, one per field.
fn walked() -> impl Iterator<Item = (&'static Fixture, &'static ClosedSupportTauTiltingGraph)> {
    computed()
        .iter()
        .filter_map(|entry| Some((&entry.fixture, entry.graph.as_ref()?)))
}

/// The cached entries of one fixture, one per field.
fn cached(id: &'static str) -> impl Iterator<Item = &'static Computed> {
    computed()
        .iter()
        .filter(move |entry| entry.fixture.id == id)
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

/// Whether the two pairs are isomorphic, with the stored witness rechecked.
///
/// `pair_iso` has no `Unknown` outcome: both inputs are certified basic pairs
/// and the radical criterion is total between certified indecomposables.
fn same_pair(a: &SupportTauTiltingPair, b: &SupportTauTiltingPair) -> bool {
    match pair_iso(a.module(), &a.projective(), b.module(), &b.projective())
        .expect("both pairs are over one algebra value")
    {
        SupportPairIsoOutcome::Isomorphic(witness) => {
            assert!(
                witness.verify(),
                "an isomorphism witness failed its recheck"
            );
            true
        }
        SupportPairIsoOutcome::NotIsomorphic(_) => false,
    }
}

/// Asserts that each pair of one list has exactly one partner in the other,
/// in both directions.
///
/// Exactly one, not at least one, so the assertion also carries the
/// distinctness of both lists.
fn assert_same_pair_set(
    name: &str,
    graph: &ClosedSupportTauTiltingGraph,
    listed: &CatalogEnumeration,
) {
    let from_graph: Vec<&SupportTauTiltingPair> = graph.pairs().collect();
    let from_catalog: Vec<&SupportTauTiltingPair> = listed.pairs().iter().collect();
    assert_eq!(from_graph.len(), from_catalog.len(), "{name}: list lengths");
    for a in &from_graph {
        let hits = from_catalog.iter().filter(|b| same_pair(a, b)).count();
        assert_eq!(
            hits,
            1,
            "{name}: graph pair {:?} has {hits} partners in the catalog list",
            key(a)
        );
    }
    for b in &from_catalog {
        let hits = from_graph.iter().filter(|a| same_pair(b, a)).count();
        assert_eq!(
            hits,
            1,
            "{name}: catalog pair {:?} has {hits} partners in the graph",
            key(b)
        );
    }
}

/// The sorted module dimension vectors and the projective support, which name
/// a pair uniquely on the A_2 fixture.
fn key(pair: &SupportTauTiltingPair) -> (Vec<Vec<usize>>, Vec<u32>) {
    let mut dims = pair.module().dim_vectors();
    dims.sort();
    (dims, pair.projective().vertices().to_vec())
}

fn decomposition(m: &Module) -> BasicDecomposition {
    BasicDecomposition::new(m).expect("the fixture modules are basic and certified")
}

fn support(algebra: &Arc<Algebra>, vertices: &[u32]) -> ProjectiveSupport {
    ProjectiveSupport::new(algebra, vertices).expect("the vertices are in range")
}

fn sum(parts: &[&Module]) -> Module {
    direct_sum(parts).0
}

/// The pair counts and histograms of design section 10, each derived in
/// `catalog_fixtures`.
///
/// Three sources agree on them: the derivation in the comment, the catalog
/// route here, and the mutation graph in
/// `the_mutation_graph_reproduces_the_derived_counts`.
#[test]
fn the_catalog_route_reproduces_the_derived_counts() {
    for entry in computed() {
        let fixture = &entry.fixture;
        assert_eq!(
            entry.listed.len(),
            fixture.pairs,
            "{}: pair count",
            fixture.name
        );
        assert_eq!(
            entry.listed.histogram(),
            fixture.histogram,
            "{}: histogram by |M|",
            fixture.name
        );
        assert_eq!(
            entry.listed.provenance(),
            fixture.provenance,
            "{}: completeness provenance",
            fixture.name
        );
        assert_eq!(
            entry.listed.catalog_len(),
            fixture.catalog.len(),
            "{}: catalog size",
            fixture.name
        );
        // The walk visits the tau-rigid subsets and tests each remaining
        // catalog entry once per visit, so it never visits fewer subsets than
        // it lists pairs.
        assert!(
            entry.listed.nodes_visited() >= entry.listed.len(),
            "{}: nodes visited",
            fixture.name
        );
        // |M| + |P| = n on every listed pair.
        let n = fixture.histogram.len() - 1;
        for pair in entry.listed.pairs() {
            assert_eq!(pair.summand_count(), n, "{}: |M| + |P|", fixture.name);
        }
    }
}

/// The closed mutation graph reports the same counts as the catalog route and
/// the derivation.
///
/// The two routes share no code. The graph rests on AIR Theorem 2.18 and
/// Theorem 2.35(b), the catalog route on Gabriel's theorem or the Nakayama
/// classification.
#[test]
fn the_mutation_graph_reproduces_the_derived_counts() {
    for (fixture, graph) in walked() {
        assert_eq!(graph.len(), fixture.pairs, "{}: pair count", fixture.name);
        assert_eq!(
            graph.histogram(),
            fixture.histogram,
            "{}: histogram by |M|",
            fixture.name
        );
        // Every slot of a closed graph is decided, by obligation 4 of the
        // closure witness.
        for vertex in graph.vertices() {
            assert_eq!(
                vertex.slots().len(),
                vertex.pair().module().len(),
                "{}: undecided slot",
                fixture.name
            );
        }
    }
}

/// Every closed graph rechecks its own completeness certificate.
///
/// `ClosureWitness::verify` reruns all seven obligations of design section 8,
/// including the connectivity recheck, which is recomputed from the edge list
/// rather than inferred from the walk that built it.
#[test]
fn every_closed_graph_rechecks_its_closure_witness() {
    for (fixture, graph) in walked() {
        assert!(
            graph.verify(),
            "{}: the closure witness failed",
            fixture.name
        );
        assert_eq!(graph.witness().vertices().len(), graph.len());
        // Slot accounting: every module slot of every vertex is either a
        // recorded left-mutation edge or a Fac witness, and no slot is both.
        let slots: usize = graph
            .vertices()
            .iter()
            .map(|vertex| vertex.pair().module().len())
            .sum();
        let fac = graph
            .vertices()
            .iter()
            .flat_map(|vertex| vertex.slots())
            .filter(|record| record.fac_witness().is_some())
            .count();
        assert_eq!(
            slots,
            graph.mutations().len() + fac,
            "{}: slots against edges plus Fac witnesses",
            fixture.name
        );
    }
}

/// Cross-route agreement, asserted in both directions.
#[test]
fn the_two_routes_list_the_same_pairs() {
    for entry in computed() {
        let Some(graph) = entry.graph.as_ref() else {
            continue;
        };
        assert_same_pair_set(&entry.fixture.name, graph, &entry.listed);
    }
}

/// What the A_2 walk must produce at slot `(pair, summand)`.
enum Slot {
    /// No left mutation: `X_j` lies in `Fac(M/X_j)`.
    Fac,
    /// A left mutation onto the pair with this key, of this shape.
    To((Vec<Vec<usize>>, Vec<u32>), ExchangeShape),
}

/// The A_2 pentagon, computed by hand and checked slot by slot.
///
/// `A = kQ` for `Q: 0 -> 1`, so `P_0 = [1, 1]`, `P_1 = S_1 = [0, 1]`, and
/// `S_0 = [1, 0]`. The five pairs:
///
/// - `(P_0 + P_1, 0)`, the regular module.
/// - `(P_0 + S_0, 0)`, the other tilting module.
/// - `(S_1, {0})`, since `Hom(P_0, S_1) = (S_1)_0 = 0`.
/// - `(S_0, {1})`, since `Hom(P_1, S_0) = (S_0)_1 = 0`.
/// - `(0, {0, 1})`.
///
/// The six module slots, each decided by the `Fac` test of design section 8:
///
/// - `(P_0 + P_1, 0)` at `P_1`: `Fac(P_0) = {P_0, S_0, 0}` misses `S_1`, so
///   the left mutation exists. The minimal left `add(P_0)`-approximation of
///   `S_1` is the socle inclusion `S_1 -> P_0` with cokernel `S_0`, giving
///   `(P_0 + S_0, 0)`.
/// - `(P_0 + P_1, 0)` at `P_0`: `Fac(P_1) = {S_1, 0}` misses `P_0`, and
///   `Hom(P_0, P_1) = (P_1)_0 = 0`, so the approximation is `P_0 -> 0`, the
///   support loses vertex 0, and the target is `(S_1, {0})`.
/// - `(P_0 + S_0, 0)` at `S_0`: `S_0 = P_0 / rad P_0` lies in `Fac(P_0)`, so
///   this is the one slot with a `FacWitness` and no outgoing edge.
/// - `(P_0 + S_0, 0)` at `P_0`: `Fac(S_0) = {S_0, 0}` misses `P_0`. The
///   minimal left `add(S_0)`-approximation of `P_0` is the top projection, so
///   the cokernel is zero, the support loses vertex 1, and the target is
///   `(S_0, {1})`.
/// - `(S_1, {0})` at `S_1` and `(S_0, {1})` at `S_0`: `M / X_j = 0` and
///   `Fac(0) = {0}`, so both approximations are `X_j -> 0` and both targets
///   are `(0, {0, 1})`.
/// - `(0, {0, 1})` has no module slot.
///
/// Five edges on five vertices, and the undirected graph is the pentagon.
#[test]
fn the_a2_pentagon_matches_the_hand_computation() {
    let regular = (vec![vec![0usize, 1], vec![1, 1]], Vec::new());
    let other_tilting = (vec![vec![1usize, 0], vec![1, 1]], Vec::new());
    let s1_pair = (vec![vec![0usize, 1]], vec![0u32]);
    let s0_pair = (vec![vec![1usize, 0]], vec![1u32]);
    let zero_pair = (Vec::new(), vec![0u32, 1]);

    for entry in cached("linear_an(2)") {
        let graph = entry.graph.as_ref().expect("A_2 is in the always-on tier");
        assert_eq!(graph.len(), 5);
        assert_eq!(graph.mutations().len(), 5);

        let keys: BTreeSet<(Vec<Vec<usize>>, Vec<u32>)> = graph.pairs().map(key).collect();
        assert_eq!(
            keys,
            BTreeSet::from([
                regular.clone(),
                other_tilting.clone(),
                s1_pair.clone(),
                s0_pair.clone(),
                zero_pair.clone(),
            ])
        );

        // The walk starts at (A, 0), so vertex 0 is the regular pair and no
        // edge points back into it.
        assert_eq!(key(graph.vertices()[0].pair()), regular);
        assert!(graph.mutations().iter().all(|edge| edge.target() != 0));

        let mut fac_slots = 0;
        for vertex in graph.vertices() {
            let here = key(vertex.pair());
            for (j, record) in vertex.slots().iter().enumerate() {
                let summand = vertex.pair().module().summands()[j].module().dim_vector();
                let expected = match (&here, summand) {
                    (k, [0, 1]) if *k == regular => Slot::To(
                        other_tilting.clone(),
                        ExchangeShape::ReplacedByModule { multiplicity: 1 },
                    ),
                    (k, [1, 1]) if *k == regular => Slot::To(
                        s1_pair.clone(),
                        ExchangeShape::MovesToProjective { vertex: 0 },
                    ),
                    (k, [1, 0]) if *k == other_tilting => Slot::Fac,
                    (k, [1, 1]) if *k == other_tilting => Slot::To(
                        s0_pair.clone(),
                        ExchangeShape::MovesToProjective { vertex: 1 },
                    ),
                    (k, [0, 1]) if *k == s1_pair => Slot::To(
                        zero_pair.clone(),
                        ExchangeShape::MovesToProjective { vertex: 1 },
                    ),
                    (k, [1, 0]) if *k == s0_pair => Slot::To(
                        zero_pair.clone(),
                        ExchangeShape::MovesToProjective { vertex: 0 },
                    ),
                    (k, dims) => panic!("A_2 has no slot {dims:?} at {k:?}"),
                };
                match (record, expected) {
                    (SlotRecord::NoLeftMutation(fac), Slot::Fac) => {
                        fac_slots += 1;
                        assert!(fac.verify(), "the Fac witness failed its recheck");
                        // U = M / X_j is P_0 and X_j is its top S_0.
                        assert_eq!(fac.module().dim_vector(), [1, 1]);
                        assert_eq!(fac.summand().dim_vector(), [1, 0]);
                        assert_eq!(fac.image_dims(), [1, 0]);
                    }
                    (SlotRecord::LeftMutation { mutation }, Slot::To(target, shape)) => {
                        let edge = &graph.mutations()[*mutation];
                        assert_eq!(edge.slot(), j);
                        assert_eq!(key(graph.vertices()[edge.target()].pair()), target);
                        assert_eq!(*edge.mutation().shape(), shape);
                        assert!(edge.mutation().verify());
                        assert!(edge.endpoint().verify());
                    }
                    (record, _) => panic!("A_2 slot {j} of {here:?} came back as {record:?}"),
                }
            }
        }
        // Exactly one slot of the pentagon is a right mutation.
        assert_eq!(fac_slots, 1);
    }
}

/// Every witness the release adds verifies on a fixture where it holds.
///
/// One test rather than seven, because the objects all come from one A_2 pair
/// and one A_2 walk, and splitting them would rebuild the same data.
#[test]
fn every_witness_type_verifies_on_a2() {
    let algebra = linear_an(2, f5());
    let p0 = Module::projective(&algebra, 0);
    let p1 = Module::projective(&algebra, 1);
    let s0 = Module::simple(&algebra, 0);

    // SupportTauTiltingPair: (P_0 + S_0, 0), the second tilting module.
    let pair = SupportTauTiltingPair::new(decomposition(&sum(&[&p0, &s0])), support(&algebra, &[]))
        .expect("the parts share one algebra")
        .expect("P_0 + S_0 is a tau-tilting module");
    assert!(pair.verify());
    assert!(pair.is_tau_tilting());
    assert_eq!(pair.summand_count(), 2);
    assert!(pair.projective().is_empty());
    assert!(pair.rigid().verify());

    // AlmostCompletePair: drop S_0, so |M| + |P| = 1 = n - 1.
    let almost = AlmostCompletePair::new(decomposition(&p0), support(&algebra, &[]))
        .expect("the parts share one algebra")
        .expect("P_0 alone is tau-rigid");
    assert!(almost.verify());
    assert_eq!(almost.summand_count(), 1);
    assert_eq!(almost.omitted_vertex(), None);
    assert!(almost.rigid().verify());

    // CatalogEnumeration over the same algebra.
    let catalog = IndecomposableCatalog::dynkin(&algebra).expect("A_2 is Dynkin");
    let listed = enumerate_over_catalog(&catalog).expect("A_2 enumerates");
    assert!(listed.verify());
    assert_eq!(listed.len(), 5);

    // MinimalLeftApproximation: S_1 = P_1 into add(P_0). Hom(S_1, P_0) is one
    // dimensional, the socle inclusion. End(P_0) = e_0 A e_0 = k and the map
    // End(P_0) -> Hom(S_1, P_0) is injective, so K_f is zero and lies inside
    // rad End(P_0) for free.
    let left = left_approximation(&p1, std::slice::from_ref(&p0)).expect("P_0 is indecomposable");
    assert!(left.verify());
    assert_eq!(left.multiplicity(0), 1);
    assert_eq!(left.map().source().dim_vector(), [0, 1]);
    assert_eq!(left.map().target().dim_vector(), [1, 1]);
    assert_eq!(left.kernel_basis().rows(), 0);

    // MutationWitness and FacWitness, from the two slots of (P_0 + S_0, 0).
    let mut shapes = Vec::new();
    let mut fac_seen = 0;
    for slot in 0..pair.module().len() {
        match mutate_at(&pair, slot).expect("the slot is a module summand") {
            SlotOutcome::LeftMutation(mutation) => {
                assert!(mutation.verify());
                assert!(mutation.witness().verify());
                assert_eq!(mutation.witness().slot(), slot);
                assert!(mutation.witness().source_extension().verify());
                assert!(mutation.witness().target_extension().verify());
                assert!(mutation.witness().approximation().verify());
                assert!(mutation.witness().almost_complete().verify());
                assert!(mutation.target().verify());
                shapes.push(mutation.shape().clone());
            }
            SlotOutcome::NoLeftMutation(fac) => {
                fac_seen += 1;
                assert!(fac.verify());
            }
        }
    }
    // Slot P_0 moves vertex 1 into the projective support; slot S_0 is the
    // right-mutation slot of the pentagon.
    assert_eq!(shapes, vec![ExchangeShape::MovesToProjective { vertex: 1 }]);
    assert_eq!(fac_seen, 1);

    // ClosureWitness, over the same algebra.
    let graph = walk(&algebra);
    assert!(graph.witness().verify());
    assert_eq!(graph.witness().vertices().len(), 5);
    assert_eq!(graph.witness().mutations().len(), 5);

    // AddClosureWitness on its own: P_0 lies in add(P_0 + S_0), P_1 does not.
    let target = decomposition(&sum(&[&p0, &s0]));
    let inside = AddClosureWitness::new(&decomposition(&p0), &target)
        .expect("one algebra")
        .expect("P_0 is a summand of T");
    assert!(inside.verify());
    assert!(
        AddClosureWitness::new(&decomposition(&p1), &target)
            .expect("one algebra")
            .is_none(),
        "P_1 is isomorphic to no summand of P_0 + S_0"
    );
}

/// The checking constructors reject input that fails a condition, and the
/// negative witnesses they hand back verify.
///
/// This is the public half of the mutation corpus of design section 15.
/// Witness fields are private, so the corpus that corrupts a stored witness
/// runs in-module; here the tampering is in the input.
#[test]
fn the_checking_constructors_reject_input_that_fails_a_condition() {
    let a2 = linear_an(2, f5());
    let p0 = Module::projective(&a2, 0);
    let p1 = Module::projective(&a2, 1);
    let s0 = Module::simple(&a2, 0);

    // Condition 2, Hom(P, M) = 0. Taking M = P_0 with the projective support
    // {0} keeps |M| + |P| = 2, but Hom(P_0, P_0) is one dimensional.
    match SupportTauTiltingPair::classify(decomposition(&p0), support(&a2, &[0]))
        .expect("the parts share one algebra")
    {
        SupportTauTiltingClassification::Rejected(PairRejection::HomFromProjectiveNonzero {
            vertex,
            dim,
        }) => {
            // dim Hom(P_0, P_0) = dim (P_0)_0 = 1.
            assert_eq!((vertex, dim), (0, 1));
        }
        other => panic!("expected condition 2, got {:?}", other.rejection()),
    }

    // Condition 3. k[x]/(x^3) is self-injective with tau = Omega^2 fixing the
    // simple, so Hom(S, tau S) = End(S) is one dimensional.
    let tp = truncated_poly(3, f5()).expect("x^3 is admissible");
    let simple = Module::simple(&tp, 0);
    match SupportTauTiltingPair::classify(decomposition(&simple), support(&tp, &[]))
        .expect("the parts share one algebra")
    {
        SupportTauTiltingClassification::Rejected(PairRejection::NotTauRigid(witness)) => {
            assert!(witness.verify());
            assert_eq!(witness.translate().dim_vector(), [1]);
            assert_eq!(witness.morphism().source().dim_vector(), [1]);
        }
        other => panic!("expected condition 3, got {:?}", other.rejection()),
    }
    match is_tau_rigid(&simple).expect("the simple is a module over its own algebra") {
        TauRigidityOutcome::NotTauRigid(witness) => assert!(witness.verify()),
        TauRigidityOutcome::TauRigid(_) => panic!("k[x]/(x^3) has no tau-rigid simple"),
    }

    // Condition 4. P_0 alone is a legitimate almost complete pair on A_2, and
    // the same input misses the support tau-tilting count by one.
    match SupportTauTiltingPair::classify(decomposition(&p0), support(&a2, &[]))
        .expect("the parts share one algebra")
    {
        SupportTauTiltingClassification::Rejected(PairRejection::SummandCount {
            module,
            projective,
            expected,
        }) => assert_eq!((module, projective, expected), (1, 0, 2)),
        other => panic!("expected condition 4, got {:?}", other.rejection()),
    }
    // The count runs the other way for the almost complete type.
    match AlmostCompletePair::classify(decomposition(&sum(&[&p0, &s0])), support(&a2, &[]))
        .expect("the parts share one algebra")
    {
        AlmostCompleteClassification::Rejected(PairRejection::SummandCount {
            module,
            projective,
            expected,
        }) => assert_eq!((module, projective, expected), (2, 0, 1)),
        other => panic!("expected condition 4, got {:?}", other.rejection()),
    }

    // The approximation layer refuses a decomposable add-generator and a
    // repeated one.
    match left_approximation(&s0, &[sum(&[&p0, &p1])]).unwrap_err() {
        ApproxError::SummandNotIndecomposable { index, .. } => assert_eq!(index, 0),
        other => panic!("expected a rejected add-generator, got {other}"),
    }
    match left_approximation(&s0, &[p0.clone(), p0.clone()]).unwrap_err() {
        ApproxError::RepeatedSummand { first, second } => assert_eq!((first, second), (0, 1)),
        other => panic!("expected a repeated add-generator, got {other}"),
    }

    // Mutation addresses module summands only, so slot 2 of a two-summand pair
    // is out of range rather than a projective slot.
    let pair = SupportTauTiltingPair::new(decomposition(&sum(&[&p0, &s0])), support(&a2, &[]))
        .expect("one algebra")
        .expect("P_0 + S_0 is a tau-tilting module");
    match mutate_at(&pair, 2).unwrap_err() {
        MutationError::SlotOutOfRange { slot, summands } => assert_eq!((slot, summands), (2, 2)),
        other => panic!("expected a slot out of range, got {other}"),
    }
}

/// Rechecks a truncated Kronecker walk: the typed reason, the diagnostics, and
/// the certification of every part that was reached.
fn assert_kronecker_truncation(partial: &IncompleteSupportTauTiltingGraph, max_vertices: usize) {
    let diagnostics = match partial.reason() {
        IncompleteReason::BudgetExhausted(diagnostics) => diagnostics,
        IncompleteReason::CertificationBlocked(blocker) => {
            panic!("the Kronecker walk should exhaust a budget, not block: {blocker}")
        }
    };
    assert_eq!(diagnostics.limit(), GraphLimit::Vertices);
    assert_eq!(diagnostics.vertices_found(), max_vertices);
    assert_eq!(partial.vertices_found().len(), max_vertices);
    assert!(diagnostics.work_units() > 0);
    assert_eq!(partial.work_units(), diagnostics.work_units());
    // The part that was reached is still certified, vertex by vertex and edge
    // by edge.
    assert!(partial.verify_parts());
    for vertex in partial.vertices_found() {
        assert!(vertex.pair().verify());
        // Kronecker has two vertices, so |M| + |P| = 2 on every pair.
        assert_eq!(vertex.pair().summand_count(), 2);
    }
    for edge in partial.verified_mutations() {
        assert!(edge.mutation().verify());
        assert!(edge.endpoint().verify());
    }
}

/// The Kronecker algebra is tau-tilting infinite, so the walk truncates and
/// says so in the type.
///
/// The design records the shape of the truncation: the descending walk runs
/// down the preprojective ray and reaches no preinjective vertex, so the
/// vertices found are a biased sample. Nothing here reads them as a list of
/// pairs, and `IncompleteSupportTauTiltingGraph` has no `pairs` accessor to
/// read them with.
///
/// The budget is 8 vertices rather than the 16 of design section 11. The
/// preprojective ray grows, so vertex 16 carries much larger modules than
/// vertex 8. Measured on this branch over two fields: this test runs in 0.04 s
/// to 0.05 s, while `the_kronecker_walk_at_sixteen_vertices_truncates` runs
/// the design's case at 1.18 s, which does not fit the always-on block.
#[test]
fn the_kronecker_walk_truncates_with_a_typed_reason() {
    let limits = MutationGraphLimits {
        max_vertices: 8,
        ..MutationGraphLimits::default()
    };
    for field in fields() {
        let algebra = kronecker(2, field);
        let outcome = support_tau_tilting_graph(&algebra, &limits)
            .expect("a budget stop is an outcome, not an error");
        assert!(!outcome.is_closed());
        assert!(outcome.closed().is_none(), "no completeness claim");
        let partial = outcome
            .incomplete()
            .expect("the walk cannot close on a tau-tilting infinite algebra");
        assert_kronecker_truncation(partial, 8);
    }
}

/// Neither catalog constructor accepts the Kronecker algebra, and each says
/// why in its own error type.
///
/// The quiver is two vertices with two parallel arrows and a zero ideal, so
/// vertex 0 has two outgoing arrows and is not Nakayama, and the underlying
/// graph is the Euclidean diagram A~_1, not a Dynkin diagram.
#[test]
fn both_catalog_constructors_reject_the_kronecker_algebra() {
    for field in fields() {
        let algebra = kronecker(2, field);
        assert_eq!(
            IndecomposableCatalog::nakayama(&algebra).unwrap_err(),
            EnumerateError::NotNakayama {
                vertex: 0,
                incoming: 0,
                outgoing: 2,
            }
        );
        assert_eq!(
            IndecomposableCatalog::dynkin(&algebra).unwrap_err(),
            DynkinError::NotDynkin {
                euclidean: Some(EuclideanType::A(1)),
            }
        );
    }
}

/// Work-unit ceilings, which are deterministic and profile-independent.
///
/// The ceilings are snapshots, not derivations. Measured on this branch: A_2
/// 6668 units, A_3 145712, D_4 3951020. Each ceiling is the next power of two
/// at or above twice the measurement. The assertion is that the count is
/// reproducible, so a change in the call sequence of the walk shows up here
/// instead of as a slower test.
///
/// The counts rose from 1416, 12895, and 140428 when every rate gained the
/// size factor `e`, the unknown count of `Hom(M, M)`. See
/// [`ClosedSupportTauTiltingGraph::work_units`]: the old rates charged one
/// unit per Hom system whatever its size, which did not brake a tau-tilting
/// infinite walk.
#[test]
fn the_walk_stays_under_its_work_unit_ceilings() {
    for (id, ceiling) in [("linear_an(2)", 16_384u64), ("linear_an(3)", 524_288)] {
        let mut counts = Vec::new();
        for entry in cached(id) {
            let graph = entry
                .graph
                .as_ref()
                .expect("the fixture is in the walk tier");
            assert!(
                graph.work_units() <= ceiling,
                "{}: {} work units, ceiling {ceiling}",
                entry.fixture.name,
                graph.work_units()
            );
            counts.push(graph.work_units());
        }
        // The model charges by call, so the count does not depend on the field.
        assert_eq!(counts[0], counts[1], "{id}: work units across fields");
    }
}

/// Exhaustive tier: the full D_4 cross-check, the largest case in the file.
///
/// The walk and its closure recheck together cost more than the always-on
/// budget, so that block keeps only the D_4 catalog route. This adds the walk,
/// the closure recheck, the cross-route agreement over all 50 pairs, and the
/// work-unit ceiling. Measured on this branch at 0.42 s to 0.64 s over two
/// fields, with the recheck the slower half.
#[test]
#[ignore = "exhaustive tier: the D_4 walk, closure recheck, and 50-pair cross-route"]
fn the_two_routes_agree_on_d4() {
    for entry in cached("dynkin_quiver(D(4))") {
        let fixture = &entry.fixture;
        let graph = walk(&fixture.algebra);
        assert_eq!(graph.len(), 50, "{}: pair count", fixture.name);
        assert_eq!(graph.histogram(), vec![1, 4, 9, 16, 20], "{}", fixture.name);
        assert!(graph.verify(), "{}: closure witness", fixture.name);
        // Snapshot ceiling, as in `the_walk_stays_under_its_work_unit_ceilings`.
        assert!(graph.work_units() <= 8_388_608, "{}", fixture.name);
        assert_same_pair_set(&fixture.name, &graph, &entry.listed);
    }
}

/// Exhaustive tier: `CatalogEnumeration::verify` on every fixture.
///
/// The recheck reverifies each listed pair and then compares every surviving
/// fingerprint bucket with `pair_iso`, which is quadratic in the list. On D_4
/// that is 50 pairs and 2500 comparisons.
#[test]
#[ignore = "exhaustive tier: the per-pair recheck of all nine catalog lists"]
fn every_catalog_list_rechecks() {
    for entry in computed() {
        assert!(
            entry.listed.verify(),
            "{}: the catalog list failed its recheck",
            entry.fixture.name
        );
    }
}

/// Exhaustive tier: the Kronecker budget of design section 11.
///
/// The always-on version stops at 8 vertices. This one stops at the 16 the
/// design names. Measured on this branch at 1.18 s over two fields, against
/// 0.04 s to 0.05 s for the 8-vertex version.
#[test]
#[ignore = "exhaustive tier: the 16-vertex Kronecker truncation of design section 11"]
fn the_kronecker_walk_at_sixteen_vertices_truncates() {
    let limits = MutationGraphLimits {
        max_vertices: 16,
        ..MutationGraphLimits::default()
    };
    for field in fields() {
        let outcome = support_tau_tilting_graph(&kronecker(2, field), &limits)
            .expect("a budget stop is an outcome, not an error");
        assert!(outcome.closed().is_none(), "no completeness claim");
        assert_kronecker_truncation(
            outcome
                .incomplete()
                .expect("the walk cannot close on a tau-tilting infinite algebra"),
            16,
        );
    }
}

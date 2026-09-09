use std::sync::{Arc, OnceLock};

use auslander::algebra::{
    Algebra, linear_an, linear_nakayama, path_algebra as kq, radical_square_zero_cycle,
    truncated_poly,
};
use auslander::arquiver::{CatalogProvenance, IndecomposableCatalog};
use auslander::dynkin::{DynkinType, dynkin_quiver};
use auslander::field::PrimeField;
use auslander::quiver::Quiver;
use auslander::supporttau::{CatalogEnumeration, enumerate_over_catalog};
use auslander::taugraph::{
    ClosedSupportTauTiltingGraph, MutationGraphLimits, SupportTauTiltingGraphOutcome,
    support_tau_tilting_graph,
};

use super::common::{f2, f5};

pub(crate) fn fields() -> [PrimeField; 2] {
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
pub(crate) struct Fixture {
    /// Stable across fields, so a test can pick one algebra out of the cache.
    pub(crate) id: &'static str,
    /// `id` with the field, for assertion messages.
    pub(crate) name: String,
    pub(crate) algebra: Arc<Algebra>,
    pub(crate) catalog: IndecomposableCatalog,
    pub(crate) provenance: CatalogProvenance,
    pub(crate) pairs: usize,
    pub(crate) histogram: Vec<usize>,
    /// Whether the always-on tier walks the mutation graph over this algebra.
    pub(crate) walk_always_on: bool,
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
pub(crate) struct Computed {
    pub(crate) fixture: Fixture,
    pub(crate) listed: CatalogEnumeration,
    /// `None` when the walk over this algebra belongs to the exhaustive tier.
    pub(crate) graph: Option<ClosedSupportTauTiltingGraph>,
}

/// The nine fixtures over both fields, with the catalog route run once and the
/// mutation walk run once where the always-on tier covers it.
///
/// Ten tests read this list. The walks and the enumerations are the largest
/// single cost of the always-on block, so they run once for the whole binary
/// rather than once per test.
pub(crate) fn computed() -> &'static [Computed] {
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
pub(crate) fn walked()
-> impl Iterator<Item = (&'static Fixture, &'static ClosedSupportTauTiltingGraph)> {
    computed()
        .iter()
        .filter_map(|entry| Some((&entry.fixture, entry.graph.as_ref()?)))
}

/// The cached entries of one fixture, one per field.
pub(crate) fn cached(id: &'static str) -> impl Iterator<Item = &'static Computed> {
    computed()
        .iter()
        .filter(move |entry| entry.fixture.id == id)
}

pub(crate) fn walk(algebra: &Arc<Algebra>) -> ClosedSupportTauTiltingGraph {
    let outcome = support_tau_tilting_graph(algebra, &MutationGraphLimits::default())
        .expect("the fixture walks without a defect");
    match outcome {
        SupportTauTiltingGraphOutcome::Closed(graph) => graph,
        SupportTauTiltingGraphOutcome::Incomplete(graph) => {
            panic!("the walk stopped short: {}", graph.reason())
        }
    }
}

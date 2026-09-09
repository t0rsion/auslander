use std::fmt::Write as _;
use std::sync::{Arc, OnceLock};

use auslander::algebra::{Algebra, linear_an, path_algebra, radical_square_zero_cycle};
use auslander::dynkin::{DynkinType, dynkin_quiver};
use auslander::field::PrimeField;
use auslander::taugraph::{
    ClosedSupportTauTiltingGraph, MutationGraphLimits, SupportTauTiltingGraphOutcome,
    support_tau_tilting_graph,
};

use super::common::{f2, f5};
use super::rendering::normalized_rendering;

/// The zero-ideal path algebra of D_4 as `dynkin_quiver` orients it: vertex 0
/// is the center, arrows `0 -> 1`, `0 -> 2`, `0 -> 3`.
pub(crate) fn d4(field: PrimeField) -> Arc<Algebra> {
    path_algebra(
        dynkin_quiver(DynkinType::D(4)).expect("D_4 has a quiver"),
        field,
    )
    .expect("the zero ideal over an acyclic quiver completes")
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
pub(crate) fn renderings() -> &'static [(&'static str, String)] {
    static CACHE: OnceLock<Vec<(&'static str, String)>> = OnceLock::new();
    CACHE.get_or_init(|| {
        fixtures()
            .into_iter()
            .map(|(name, algebra)| (name, normalized_rendering(&walk(&algebra))))
            .collect()
    })
}

pub(crate) fn rendering(name: &str) -> &'static str {
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
pub(crate) fn fingerprint_payload() -> String {
    let mut out = String::new();
    for (name, text) in renderings() {
        writeln!(out, "graph:{name}").unwrap();
        out.push_str(text);
    }
    out
}

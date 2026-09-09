use super::super::*;
use super::common::*;

use crate::algebra::kronecker;
use crate::arquiver::IndecomposableCatalog;
use crate::supporttau::{SupportTauTiltingPair, enumerate_over_catalog};

/// The Kronecker walk's mutations recheck.
///
/// Ignored: rechecking the 16 mutations costs 183 ms in the dev profile,
/// which is the exhaustive tier of `docs/support-tau-tilting.md` section 11. The
/// always-on `the_kronecker_walk_truncates_with_a_typed_budget` rechecks
/// the vertices.
#[test]
#[ignore = "exhaustive tier of docs/support-tau-tilting.md section 11"]
fn the_kronecker_mutations_recheck() {
    let limits = MutationGraphLimits {
        max_vertices: 16,
        ..MutationGraphLimits::default()
    };
    let outcome = support_tau_tilting_graph(&kronecker(2, f2()), &limits)
        .expect("the Kronecker walk runs without a defect");
    let graph = outcome.incomplete().expect("the walk stopped short");
    assert!(graph.verify_parts());
}

/// The D_4 closure witness rechecks, and the D_4 walk agrees with the
/// catalog route.
///
/// Ignored: the walk, the gate's recheck, the second recheck here, and the
/// catalog route cost more than a tenth of a second per field in the dev
/// profile, which is the exhaustive tier of `docs/support-tau-tilting.md` section
/// 11 rather than the always-on tier.
#[test]
#[ignore = "exhaustive tier of docs/support-tau-tilting.md section 11"]
fn the_d4_closure_witness_and_the_catalog_route_agree() {
    for field in fields() {
        let algebra = d4(field);
        let graph = walk(&algebra);
        assert!(graph.verify());
        let catalog = IndecomposableCatalog::dynkin(&algebra).expect("D_4 is Dynkin");
        let enumeration = enumerate_over_catalog(&catalog).expect("the catalog route runs");
        let walked: Vec<&SupportTauTiltingPair> = graph.pairs().collect();
        let listed: Vec<&SupportTauTiltingPair> = enumeration.pairs().iter().collect();
        assert!(same_pair_set(&walked, &listed));
        assert!(same_pair_set(&listed, &walked));
    }
}

use auslander::arquiver::{ArQuiverError, ArrowValuation, ar_quiver};
use auslander::dynkin::DynkinError;
use auslander::enumerate::EnumerateError;
use auslander::gentle::GentleError;

use crate::common::{
    catalog_sequence, catalog_witness, duality_sequence, duality_witness, preprojective_a3,
};

use super::support::{middle_classes, tier2_ar};

// The cross-check gate of design section 12: for every non-projective
// catalog vertex M, the Krull-Schmidt multiplicities of the middle term of
// its almost-split sequence equal the over_source_residue values of the
// arrows into M.
#[test]
fn middle_term_multiplicities_match_the_arrows_into_each_vertex() {
    for (name, _, quiver) in tier2_ar() {
        let dims: Vec<Vec<usize>> = quiver
            .vertices()
            .iter()
            .map(|v| v.module().module().dim_vector().to_vec())
            .collect();
        // Dimension vectors identify catalog entries on these domains, so
        // Krull-Schmidt classes match arrows by dimension vector alone.
        for (a, da) in dims.iter().enumerate() {
            for db in dims.iter().skip(a + 1) {
                assert_ne!(da, db, "{name}: catalog dimension vectors are distinct");
            }
        }
        let mut checked = 0usize;
        for vertex in quiver.vertices() {
            if vertex.projective() {
                continue;
            }
            let sequence = duality_sequence(vertex.module());
            let mut expected: Vec<(Vec<usize>, usize)> = quiver
                .arrows()
                .iter()
                .filter(|arrow| arrow.target() == vertex.id())
                .map(|arrow| (dims[arrow.source()].clone(), arrow.over_source_residue()))
                .collect();
            expected.sort();
            assert_eq!(
                middle_classes(sequence.sequence().middle()),
                expected,
                "{name}: middle term of vertex {} ({:?})",
                vertex.id(),
                dims[vertex.id()]
            );
            checked += 1;
        }
        assert!(
            checked > 0,
            "{name}: the domain has non-projective vertices"
        );
    }
}

#[test]
fn the_catalog_route_agrees_with_the_duality_route_on_every_vertex() {
    for (name, _, quiver) in tier2_ar() {
        let catalog = quiver.catalog();
        for vertex in quiver.vertices() {
            if vertex.projective() {
                continue;
            }
            let duality = duality_sequence(vertex.module());
            let via = catalog_sequence(vertex.module(), catalog);
            assert_eq!(
                duality.sequence().middle().dim_vector(),
                via.sequence().middle().dim_vector(),
                "{name}: middle terms of vertex {}",
                vertex.id()
            );
            // tau is deterministic, so both routes compute identical Ext
            // bases and class coordinates transport verbatim.
            let transported = duality
                .chosen_ar_class()
                .space()
                .class_from_coordinates(via.chosen_ar_class().coordinates())
                .unwrap();
            assert!(
                transported.equals(duality.chosen_ar_class()).unwrap(),
                "{name}: chosen classes of vertex {}",
                vertex.id()
            );
            let witness = catalog_witness(&via);
            assert!(
                witness.verify(
                    vertex.module(),
                    catalog,
                    via.sequence(),
                    via.chosen_ar_class()
                ),
                "{name}: catalog witness of vertex {}",
                vertex.id()
            );
            let dual_witness = duality_witness(&duality);
            assert!(
                dual_witness.verify(
                    vertex.module(),
                    duality.sequence(),
                    duality.chosen_ar_class()
                ),
                "{name}: duality witness of vertex {}",
                vertex.id()
            );
        }
    }
}

// Every indecomposable in these catalog domains has
// End(M)/rad End(M) = k, so every residue degree is 1 and every arrow
// valuation is plain.
#[test]
fn every_arrow_valuation_on_the_catalog_domains_is_plain() {
    for (name, _, quiver) in tier2_ar() {
        for vertex in quiver.vertices() {
            assert_eq!(
                vertex.residue_degree(),
                1,
                "{name}: residue degree of vertex {}",
                vertex.id()
            );
        }
        for arrow in quiver.arrows() {
            assert_eq!(
                arrow.valuation(),
                ArrowValuation::Plain(arrow.base_dim()),
                "{name}: valuation of arrow {} -> {}",
                arrow.source(),
                arrow.target()
            );
        }
    }
}

// Tier separation of design section 18: the preprojective algebra of A_3
// is representation finite, but this release certifies no catalog for it,
// so tier 1 covers it (the almost_split tests above) while the AR quiver
// dispatch rejects it with both reasons.
#[test]
fn preprojective_a3_runs_tier_1_only_and_ar_quiver_carries_both_rejections() {
    let algebra = preprojective_a3();
    match ar_quiver(&algebra).unwrap_err() {
        ArQuiverError::UnsupportedDomain {
            dynkin,
            nakayama,
            gentle,
        } => {
            // The completed reduced Groebner basis has five elements: the
            // three input relations plus the two productive completions
            // a.b.bbar and b.bbar.abar of acceptance_nonmonomial.rs.
            assert_eq!(dynkin, DynkinError::NonzeroIdeal { relations: 5 });
            // Vertex 1 carries the arrows b and abar out and a and bbar in.
            assert_eq!(
                nakayama,
                EnumerateError::NotNakayama {
                    vertex: 1,
                    incoming: 2,
                    outgoing: 2,
                }
            );
            assert_eq!(
                gentle,
                GentleError::NonMonomial {
                    relation: 1,
                    terms: 2,
                }
            );
        }
        other => panic!("expected UnsupportedDomain, got {other:?}"),
    }
}

use std::sync::Arc;

use super::*;
use crate::algebra::{monomial_algebra, path_algebra};
use crate::field::PrimeField;
use crate::monomial::MonomialIdeal;
use crate::quiver::{ArrowId, Quiver};

fn f5() -> PrimeField {
    PrimeField::new(5).unwrap()
}

fn branch(relations: Vec<Vec<ArrowId>>) -> Arc<crate::algebra::Algebra> {
    let quiver = Quiver::new(4, &[(0, 1), (1, 2), (1, 3)]).unwrap();
    let ideal = MonomialIdeal::new(quiver, relations).unwrap();
    monomial_algebra(&ideal, f5()).unwrap()
}

fn incoming_branch(relations: Vec<Vec<ArrowId>>) -> Arc<crate::algebra::Algebra> {
    let quiver = Quiver::new(4, &[(0, 2), (1, 2), (2, 3)]).unwrap();
    let ideal = MonomialIdeal::new(quiver, relations).unwrap();
    monomial_algebra(&ideal, f5()).unwrap()
}

#[test]
fn branch_strings_use_each_valid_endpoint_pair_once() {
    let algebra = branch(vec![vec![ArrowId(0), ArrowId(1)]]);
    let strings = gentle_tree_strings(&algebra).unwrap();
    let endpoints: Vec<(u32, u32)> = strings
        .iter()
        .map(|string| (string.start(), string.end()))
        .collect();
    assert_eq!(
        endpoints,
        vec![
            (0, 0),
            (0, 1),
            (0, 3),
            (1, 1),
            (1, 2),
            (1, 3),
            (2, 2),
            (2, 3),
            (3, 3),
        ]
    );
    let branch_string = strings
        .iter()
        .find(|string| string.end() == 3 && string.start() == 2)
        .unwrap();
    assert_eq!(
        branch_string.letters(),
        [
            GentleLetter::inverse(ArrowId(1)),
            GentleLetter::direct(ArrowId(2))
        ]
    );
}

#[test]
fn branch_modules_are_certified_and_have_row_vector_maps() {
    let algebra = branch(vec![vec![ArrowId(0), ArrowId(1)]]);
    let listed = gentle_tree_indecomposables(&algebra).unwrap();
    assert_eq!(listed.len(), 9);
    assert!(
        listed.iter().all(|(_, certificate)| {
            *certificate == crate::decompose::Certificate::Indecomposable
        })
    );
    let branch_module = &listed[7].0;
    assert_eq!(branch_module.dim_vector(), [0, 1, 1, 1]);
    assert_eq!(branch_module.map(ArrowId(1)).entries_u64(), vec![vec![1]]);
    assert_eq!(branch_module.map(ArrowId(2)).entries_u64(), vec![vec![1]]);
}

#[test]
fn the_release_example_has_eight_string_modules() {
    let quiver = Quiver::new(4, &[(0, 1), (1, 2), (3, 2)]).unwrap();
    let ideal = MonomialIdeal::new(quiver, vec![vec![ArrowId(0), ArrowId(1)]]).unwrap();
    let algebra = monomial_algebra(&ideal, f5()).unwrap();
    let strings = gentle_tree_strings(&algebra).unwrap();
    assert_eq!(strings.len(), 8);
    assert!(
        !strings
            .iter()
            .any(|string| string.start() == 0 && string.end() == 2)
    );
    assert!(
        strings
            .iter()
            .any(|string| string.start() == 1 && string.end() == 3)
    );
    let modules = gentle_tree_indecomposables(&algebra).unwrap();
    assert_eq!(modules.len(), 8);
    assert!(
        modules.iter().all(|(_, certificate)| {
            *certificate == crate::decompose::Certificate::Indecomposable
        })
    );
}

#[test]
fn the_release_example_catalog_runs_hom_and_ar_layers() {
    let quiver = Quiver::new(4, &[(0, 1), (1, 2), (3, 2)]).unwrap();
    let ideal = MonomialIdeal::new(quiver, vec![vec![ArrowId(0), ArrowId(1)]]).unwrap();
    let algebra = monomial_algebra(&ideal, f5()).unwrap();
    let catalog = crate::arquiver::IndecomposableCatalog::gentle_tree(&algebra).unwrap();
    for source in catalog.entries() {
        for target in catalog.entries() {
            crate::hom::hom_dim(source.module(), target.module()).unwrap();
        }
    }
    let ar = crate::arquiver::ar_quiver_from_catalog(&catalog).unwrap();
    assert_eq!(
        ar.catalog().provenance(),
        crate::arquiver::CatalogProvenance::GentleTree
    );
    assert_eq!(ar.vertices().len(), 8);
    assert!(
        ar.vertices()
            .iter()
            .all(|vertex| vertex.residue_degree() == 1)
    );
    let automatic = crate::arquiver::ar_quiver(&algebra).unwrap();
    assert_eq!(
        automatic.catalog().provenance(),
        crate::arquiver::CatalogProvenance::GentleTree
    );
}

#[test]
fn the_release_example_selects_gentle_catalog_for_support_tau() {
    let quiver = Quiver::new(4, &[(0, 1), (1, 2), (3, 2)]).unwrap();
    let ideal = MonomialIdeal::new(quiver, vec![vec![ArrowId(0), ArrowId(1)]]).unwrap();
    let algebra = monomial_algebra(&ideal, f5()).unwrap();
    let enumeration = crate::supporttau::enumerate_over_algebra(&algebra).unwrap();
    assert_eq!(
        enumeration.provenance(),
        crate::arquiver::CatalogProvenance::GentleTree
    );
    assert_eq!(enumeration.catalog_len(), 8);
    assert!(!enumeration.is_empty());
    assert!(enumeration.verify());
}

#[test]
fn a_line_with_a_zero_relation_has_the_nakayama_string_classes() {
    let quiver = Quiver::new(3, &[(0, 1), (1, 2)]).unwrap();
    let ideal = MonomialIdeal::new(quiver, vec![vec![ArrowId(0), ArrowId(1)]]).unwrap();
    let algebra = monomial_algebra(&ideal, f5()).unwrap();
    let strings = gentle_tree_strings(&algebra).unwrap();
    assert_eq!(strings.len(), 5);
    assert!(
        !strings
            .iter()
            .any(|string| string.start() == 0 && string.end() == 2)
    );
    let gentle = crate::arquiver::IndecomposableCatalog::gentle_tree(&algebra).unwrap();
    let nakayama = crate::arquiver::IndecomposableCatalog::nakayama(&algebra).unwrap();
    for source in gentle.entries() {
        assert!(nakayama.entries().iter().any(|target| {
            matches!(
                crate::iso::is_isomorphic(source.module(), target.module()),
                Ok(crate::iso::IsoOutcome::Isomorphic(_))
            )
        }));
    }
}

#[test]
fn validation_reads_the_reduced_relation_length() {
    let algebra = crate::algebra::an_with_relations(4, &[(0, 3)], f5()).unwrap();
    assert_eq!(
        gentle_tree_strings(&algebra).unwrap_err(),
        GentleError::NonQuadratic {
            relation: 0,
            length: 3,
        }
    );
}

#[test]
fn loops_parallel_edges_disconnected_graphs_and_cycles_are_rejected() {
    let looped = crate::algebra::dual_numbers(f5());
    assert!(matches!(
        gentle_tree_strings(&looped),
        Err(GentleError::Loop {
            arrow: ArrowId(0),
            vertex: 0
        })
    ));
    let parallel = crate::algebra::kronecker(2, f5());
    assert!(matches!(
        gentle_tree_strings(&parallel),
        Err(GentleError::MultipleEdges { .. })
    ));
    let disconnected = path_algebra(Quiver::new(2, &[]).unwrap(), f5()).unwrap();
    assert!(matches!(
        gentle_tree_strings(&disconnected),
        Err(GentleError::Disconnected { .. })
    ));
    let cycle = crate::algebra::radical_square_zero_cycle(3, f5());
    assert!(matches!(
        gentle_tree_strings(&cycle),
        Err(GentleError::Cycle { .. })
    ));
}

#[test]
fn continuation_conditions_reject_two_permitted_or_forbidden_choices() {
    let permitted = branch(Vec::new());
    assert_eq!(
        gentle_tree_strings(&permitted).unwrap_err(),
        GentleError::MultiplePermittedSuccessors {
            arrow: ArrowId(0),
            count: 2,
        }
    );
    let forbidden = branch(vec![
        vec![ArrowId(0), ArrowId(1)],
        vec![ArrowId(0), ArrowId(2)],
    ]);
    assert_eq!(
        gentle_tree_strings(&forbidden).unwrap_err(),
        GentleError::MultipleForbiddenSuccessors {
            arrow: ArrowId(0),
            count: 2,
        }
    );
    let permitted_predecessors = incoming_branch(Vec::new());
    assert_eq!(
        gentle_tree_strings(&permitted_predecessors).unwrap_err(),
        GentleError::MultiplePermittedPredecessors {
            arrow: ArrowId(2),
            count: 2,
        }
    );
    let forbidden_predecessors = incoming_branch(vec![
        vec![ArrowId(0), ArrowId(2)],
        vec![ArrowId(1), ArrowId(2)],
    ]);
    assert_eq!(
        gentle_tree_strings(&forbidden_predecessors).unwrap_err(),
        GentleError::MultipleForbiddenPredecessors {
            arrow: ArrowId(2),
            count: 2,
        }
    );
}

#[test]
fn degree_conditions_reject_three_arrows_at_one_vertex() {
    let quiver = Quiver::new(4, &[(0, 1), (0, 2), (0, 3)]).unwrap();
    let algebra = path_algebra(quiver, f5()).unwrap();
    assert_eq!(
        gentle_tree_strings(&algebra).unwrap_err(),
        GentleError::OutgoingDegree {
            vertex: 0,
            count: 3,
        }
    );
}

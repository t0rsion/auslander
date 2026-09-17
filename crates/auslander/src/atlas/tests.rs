use std::sync::Arc;

use super::*;
use crate::algebra::{linear_an, truncated_poly};
use crate::arquiver::IndecomposableCatalog;
use crate::ext::ext_table;
use crate::field::PrimeField;

fn atlas_with_limits(limits: CatalogAtlasLimits) -> CatalogAtlas {
    build_atlas(limits).unwrap()
}

fn build_atlas(limits: CatalogAtlasLimits) -> Result<CatalogAtlas, CatalogAtlasError> {
    let algebra = truncated_poly(3, PrimeField::new(5).unwrap()).unwrap();
    let catalog = Arc::new(IndecomposableCatalog::nakayama(&algebra).unwrap());
    CatalogAtlas::compute(catalog, 3, limits)
}

fn default_atlas() -> CatalogAtlas {
    atlas_with_limits(CatalogAtlasLimits::default())
}

#[test]
fn ordered_tables_share_source_resolutions_and_match_generic_ext() {
    let atlas = default_atlas();
    assert_eq!(atlas.catalog().len(), 3);
    assert_eq!(atlas.ext_table().rows().len(), 9);
    assert_eq!(atlas.ext_table().max_degree(), 3);
    assert_eq!(atlas.work().pairs, 9);
    assert_eq!(atlas.work().ext_cells, 36);
    assert_eq!(atlas.work().resolutions, 3);
    assert!(atlas.verify());
    for source in 0..3 {
        for target in 0..3 {
            let expected = ext_table(
                atlas.catalog().entries()[source].module(),
                atlas.catalog().entries()[target].module(),
                3,
            )
            .unwrap();
            assert_eq!(
                atlas.ext_dimensions(source, target),
                Some(expected.as_slice())
            );
            assert_eq!(
                atlas.ext_table().row(source, target).unwrap().source(),
                source
            );
            assert_eq!(
                atlas.ext_table().row(source, target).unwrap().target(),
                target
            );
        }
    }
}

#[test]
fn truncated_poly_dimension_four_has_all_multiplicity_solutions() {
    let atlas = default_atlas();
    let outcome = atlas
        .enumerate_multiplicities(
            &[4],
            MultiplicityLimits {
                max_solutions: usize::MAX,
                max_nodes: 1_000,
            },
        )
        .unwrap();
    assert!(outcome.is_complete());
    assert!(Arc::ptr_eq(outcome.catalog(), atlas.catalog()));
    assert_eq!(outcome.target_dimensions(), &[4]);
    assert_eq!(
        outcome.solutions(),
        &[vec![0, 2, 0], vec![1, 0, 1], vec![2, 1, 0], vec![4, 0, 0],]
    );
    for multiplicities in outcome.solutions() {
        assert_eq!(atlas.materialize(multiplicities).unwrap().total_dim(), 4);
    }
}

#[test]
fn self_ext_scores_match_generic_ext_of_materialized_sums() {
    let atlas = default_atlas();
    for multiplicities in [vec![0, 2, 0], vec![1, 0, 1], vec![2, 1, 0], vec![4, 0, 0]] {
        let module = atlas.materialize(&multiplicities).unwrap();
        let expected = ext_table(&module, &module, 3).unwrap();
        assert_eq!(
            atlas.self_ext_scores(&multiplicities, 0, 3).unwrap(),
            expected
        );
    }
    assert_eq!(
        atlas.ext_scores(&[1, 0, 1], &[0, 2, 0], 1, 3).unwrap(),
        (1..=3)
            .map(|degree| {
                let left = atlas.materialize(&[1, 0, 1]).unwrap();
                let right = atlas.materialize(&[0, 2, 0]).unwrap();
                ext_table(&left, &right, degree).unwrap()[degree]
            })
            .collect::<Vec<_>>()
    );
}

#[test]
fn multiplicity_cuts_are_typed_and_zero_dimension_materializes_zero() {
    let atlas = default_atlas();
    let cut = atlas
        .enumerate_multiplicities(
            &[4],
            MultiplicityLimits {
                max_solutions: 1,
                max_nodes: 1_000,
            },
        )
        .unwrap();
    let MultiplicityOutcome::Cut(cut) = cut else {
        panic!("four solutions should exceed a one-row limit");
    };
    assert_eq!(cut.solutions(), &[vec![0, 2, 0]]);
    assert_eq!(
        cut.reason(),
        MultiplicityCutReason::SolutionLimit { limit: 1 }
    );
    assert!(Arc::ptr_eq(cut.catalog(), atlas.catalog()));
    assert_eq!(cut.target_dimensions(), &[4]);

    let node_cut = atlas
        .enumerate_multiplicities(
            &[4],
            MultiplicityLimits {
                max_solutions: usize::MAX,
                max_nodes: 1,
            },
        )
        .unwrap();
    assert!(matches!(
        node_cut,
        MultiplicityOutcome::Cut(MultiplicityCut { .. })
    ));
    assert_eq!(
        node_cut.cut().unwrap().reason(),
        MultiplicityCutReason::NodeLimit { limit: 1 }
    );

    let zero = atlas
        .enumerate_multiplicities(&[0], MultiplicityLimits::default())
        .unwrap();
    assert!(zero.is_complete());
    assert_eq!(zero.solutions(), &[vec![0, 0, 0]]);
    assert!(Arc::ptr_eq(zero.catalog(), atlas.catalog()));
    assert_eq!(zero.target_dimensions(), &[0]);
    let module = atlas.materialize(&[0, 0, 0]).unwrap();
    assert!(module.is_zero());
}

#[test]
fn checked_limits_and_overflows_reject_before_unbounded_work() {
    let base = CatalogAtlasLimits::default();
    assert!(matches!(
        build_atlas(CatalogAtlasLimits {
            max_pairs: 8,
            ..base
        }),
        Err(CatalogAtlasError::PairLimit {
            requested: 9,
            limit: 8
        })
    ));
    assert!(matches!(
        build_atlas(CatalogAtlasLimits {
            max_ext_cells: 35,
            ..base
        }),
        Err(CatalogAtlasError::ExtCellLimit {
            requested: 36,
            limit: 35
        })
    ));
    assert!(matches!(
        build_atlas(CatalogAtlasLimits {
            max_resolution_terms: 14,
            ..base
        }),
        Err(CatalogAtlasError::ResolutionTermLimit {
            requested: 15,
            limit: 14
        })
    ));
    assert!(matches!(
        CatalogAtlas::compute(
            Arc::new(
                IndecomposableCatalog::nakayama(
                    &truncated_poly(3, PrimeField::new(5).unwrap()).unwrap()
                )
                .unwrap()
            ),
            usize::MAX,
            base,
        ),
        Err(CatalogAtlasError::DegreeOverflow { degree: usize::MAX })
    ));

    let atlas = atlas_with_limits(CatalogAtlasLimits {
        max_materialized_summands: 1,
        ..base
    });
    assert!(matches!(
        atlas.materialize(&[usize::MAX, 0, 0]),
        Err(AtlasMaterializeError::SummandLimit {
            requested: usize::MAX,
            limit: 1
        })
    ));
    assert!(matches!(
        atlas.materialize(&[2, 0, 0]),
        Err(AtlasMaterializeError::SummandLimit {
            requested: 2,
            limit: 1
        })
    ));
    assert!(matches!(
        atlas.self_ext_scores(&[0, 0, usize::MAX], 0, 0),
        Err(AtlasScoreError::ProductOverflow { degree: 0, .. })
    ));
    assert!(!atlas.self_ext_vanishes(&[0, 0, usize::MAX], 0, 0).unwrap());
}

#[test]
fn materialization_checks_cells_before_building_the_sum() {
    let base = CatalogAtlasLimits::default();
    let limited = atlas_with_limits(CatalogAtlasLimits {
        max_materialized_cells: 0,
        ..base
    });
    assert!(matches!(
        limited.materialize(&[1, 0, 0]),
        Err(AtlasMaterializeError::CellLimit { limit: 0, .. })
    ));

    let overflow = atlas_with_limits(CatalogAtlasLimits {
        max_materialized_summands: usize::MAX,
        max_materialized_cells: usize::MAX,
        ..base
    });
    assert!(matches!(
        overflow.materialize(&[usize::MAX, 0, 0]),
        Err(AtlasMaterializeError::CellProductOverflow {
            rows: usize::MAX,
            columns: usize::MAX
        })
    ));

    let algebra = linear_an(2, PrimeField::new(5).unwrap());
    let catalog = Arc::new(IndecomposableCatalog::dynkin(&algebra).unwrap());
    let index = catalog
        .entries()
        .iter()
        .position(|entry| entry.module().dim_vector() == [1, 1])
        .expect("A2 has an indecomposable of dimension [1, 1]");
    let mut multiplicities = vec![0; catalog.len()];
    multiplicities[index] = usize::MAX;
    let atlas = CatalogAtlas::compute(
        catalog,
        0,
        CatalogAtlasLimits {
            max_materialized_summands: usize::MAX,
            max_materialized_cells: usize::MAX,
            ..base
        },
    )
    .unwrap();
    assert!(matches!(
        atlas.materialize(&multiplicities),
        Err(AtlasMaterializeError::TotalDimensionOverflow)
    ));
}

#[test]
fn arrow_free_large_sum_uses_the_summand_ceiling_without_witness_matrices() {
    let algebra = linear_an(1, PrimeField::new(5).unwrap());
    let catalog = Arc::new(IndecomposableCatalog::dynkin(&algebra).unwrap());
    let atlas = CatalogAtlas::compute(
        catalog,
        0,
        CatalogAtlasLimits {
            max_materialized_summands: 100_000,
            max_materialized_cells: 0,
            ..CatalogAtlasLimits::default()
        },
    )
    .unwrap();
    let module = atlas.materialize(&[100_000]).unwrap();
    assert_eq!(module.dim_vector(), &[100_000]);
}

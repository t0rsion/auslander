use super::*;
use crate::algebra::dual_numbers;
use crate::batch::{HomologicalBatch, HomologicalBatchLimits};
use crate::control::ComputationControl;
use crate::field::PrimeField;
use crate::module::Module;

fn limits(max_live_sources: usize) -> HomologicalBatchStreamLimits {
    HomologicalBatchStreamLimits {
        max_live_sources,
        max_pairs: 100,
        max_ext_cells: 500,
    }
}

fn modules() -> Vec<Module> {
    let algebra = dual_numbers(PrimeField::new(5).unwrap());
    vec![
        Module::simple(&algebra, 0),
        Module::projective(&algebra, 0),
        Module::simple(&algebra, 0),
    ]
}

fn collect_rows(
    stream: &mut HomologicalSelfPairStream<std::vec::IntoIter<Module>>,
) -> (Vec<HomologicalBatchStreamRow>, HomologicalBatchStreamWork) {
    let mut rows = Vec::new();
    loop {
        match stream.next_chunk() {
            HomologicalBatchStreamStep::Chunk(chunk) => {
                assert!(chunk.verify());
                rows.extend(chunk.rows().iter().cloned());
            }
            HomologicalBatchStreamStep::Complete { work, .. } => return (rows, work),
            HomologicalBatchStreamStep::Cut { .. } | HomologicalBatchStreamStep::Failed { .. } => {
                panic!("stream did not complete")
            }
        }
    }
}

#[test]
fn chunks_match_singleton_and_all_at_once_batches() {
    let modules = modules();
    let expected =
        HomologicalBatch::self_pairs(modules.clone(), 3, HomologicalBatchLimits::default())
            .unwrap();
    let expected_rows: Vec<_> = expected
        .pairs()
        .iter()
        .enumerate()
        .map(|(index, pair)| {
            (
                index,
                pair.hom_dim(),
                pair.stable_hom_dim(),
                pair.ext_dimensions().to_vec(),
                expected.resolution(index).unwrap().end,
            )
        })
        .collect();
    for chunk_size in [1, 2, 8] {
        let mut stream = stream_self_pairs(modules.clone(), 3, limits(chunk_size), None).unwrap();
        let (rows, work) = collect_rows(&mut stream);
        assert_eq!(rows.len(), expected_rows.len());
        for (row, (index, hom_dim, stable_dim, ext, end)) in rows.iter().zip(&expected_rows) {
            assert_eq!(row.source(), *index);
            assert_eq!(row.target(), *index);
            assert_eq!(row.hom_dim(), *hom_dim);
            assert_eq!(row.stable_hom_dim(), *stable_dim);
            assert_eq!(row.ext_dimensions(), ext);
            assert_eq!(row.resolution_end(), *end);
        }
        assert_eq!(work.resolutions, expected.work().resolutions);
        assert_eq!(work.target_covers, expected.work().target_covers);
        assert_eq!(work.hom_spaces, expected.work().hom_spaces);
        assert_eq!(
            work.projective_factor_spaces,
            expected.work().projective_factor_spaces
        );
        assert_eq!(work.ext_tables, expected.work().ext_tables);
        assert!(work.peak_live_sources <= chunk_size);
        assert!(matches!(
            stream.status(),
            HomologicalBatchStreamStatus::Complete
        ));
    }
}

#[test]
fn cancellation_stops_only_at_chunk_boundaries() {
    let control = ComputationControl::new();
    let mut stream = stream_self_pairs(modules(), 2, limits(2), Some(&control)).unwrap();
    let HomologicalBatchStreamStep::Chunk(first) = stream.next_chunk() else {
        panic!("the first chunk must complete");
    };
    assert_eq!(first.first_source(), 0);
    control.cancel();
    let HomologicalBatchStreamStep::Cut {
        next_source,
        reason: HomologicalBatchStreamCutReason::Cancelled,
        work,
    } = stream.next_chunk()
    else {
        panic!("cancellation must cut the next boundary");
    };
    assert_eq!(next_source, first.source_count());
    assert_eq!(work.sources, first.source_count());
    assert!(matches!(
        stream.status(),
        HomologicalBatchStreamStatus::Cut(HomologicalBatchStreamCutReason::Cancelled)
    ));
}

#[test]
fn distinct_algebras_are_a_typed_failed_chunk() {
    let field = PrimeField::new(5).unwrap();
    let left = dual_numbers(field);
    let right = dual_numbers(field);
    let modules = vec![Module::simple(&left, 0), Module::simple(&right, 0)];
    let mut stream = stream_self_pairs(modules, 1, limits(2), None).unwrap();
    let HomologicalBatchStreamStep::Failed {
        source,
        error,
        work,
    } = stream.next_chunk()
    else {
        panic!("different algebras must fail the chunk");
    };
    assert_eq!(source, 0);
    assert_eq!(work.sources, 0);
    assert!(matches!(
        error,
        HomologicalBatchStreamError::DifferentAlgebra { source: 1 }
    ));
}

#[test]
fn cancellation_before_first_chunk_does_not_pull_input() {
    let control = ComputationControl::new();
    control.cancel();
    let mut stream = stream_self_pairs(modules(), 1, limits(2), Some(&control)).unwrap();
    let HomologicalBatchStreamStep::Cut {
        next_source, work, ..
    } = stream.next_chunk()
    else {
        panic!("pre-cancelled stream must cut");
    };
    assert_eq!(next_source, 0);
    assert_eq!(work, HomologicalBatchStreamWork::default());
}

#[test]
fn distinct_algebras_fail_across_singleton_chunks() {
    let field = PrimeField::new(5).unwrap();
    let left = dual_numbers(field);
    let right = dual_numbers(field);
    let modules = vec![Module::simple(&left, 0), Module::simple(&right, 0)];
    let mut stream = stream_self_pairs(modules, 1, limits(1), None).unwrap();
    assert!(matches!(
        stream.next_chunk(),
        HomologicalBatchStreamStep::Chunk(_)
    ));
    assert!(matches!(
        stream.next_chunk(),
        HomologicalBatchStreamStep::Failed {
            source: 1,
            error: HomologicalBatchStreamError::DifferentAlgebra { source: 1 },
            ..
        }
    ));
}

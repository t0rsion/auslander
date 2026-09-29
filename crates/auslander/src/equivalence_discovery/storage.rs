use super::{DiscoveryLimits, DiscoveryStop};
use crate::quiver::ArrowId;
use crate::tilting_complex::CertifiedSiltingComplex;

pub(super) fn complex_terms(value: &CertifiedSiltingComplex) -> usize {
    value
        .candidate()
        .summands()
        .iter()
        .map(|summand| summand.complex().len())
        .sum()
}

pub(super) fn matrix_entries(value: &CertifiedSiltingComplex) -> usize {
    value
        .candidate()
        .summands()
        .iter()
        .map(|summand| {
            let complex = summand.complex();
            let actions: usize = complex
                .terms()
                .iter()
                .map(|term| {
                    (0..term.algebra().quiver().num_arrows())
                        .map(|arrow| {
                            let map = term.map(ArrowId(arrow as u32));
                            map.rows() * map.cols()
                        })
                        .sum::<usize>()
                })
                .sum();
            let differentials: usize = complex
                .differentials()
                .iter()
                .map(|differential| {
                    (0..complex.terms()[0].algebra().quiver().num_vertices())
                        .map(|vertex| {
                            let map = differential.map_at(vertex);
                            map.rows() * map.cols()
                        })
                        .sum::<usize>()
                })
                .sum();
            actions + differentials
        })
        .sum()
}

/// The storage stop for a new vertex. A sum that overflows `u64` exceeds
/// every limit.
pub(super) fn storage_stop(
    stored_vertices: usize,
    stored_terms: usize,
    stored_entries: usize,
    requested_terms: usize,
    requested_entries: usize,
    limits: DiscoveryLimits,
) -> Option<DiscoveryStop> {
    let exceeds = |stored: usize, requested: usize, limit| {
        (stored as u64)
            .checked_add(requested as u64)
            .is_none_or(|total| total > limit)
    };
    if stored_vertices as u64 >= limits.max_vertices {
        Some(DiscoveryStop::VertexLimit {
            stored: stored_vertices as u64,
            limit: limits.max_vertices,
        })
    } else if exceeds(stored_terms, requested_terms, limits.max_total_terms) {
        Some(DiscoveryStop::TermLimit {
            stored: stored_terms as u64,
            requested: requested_terms as u64,
            limit: limits.max_total_terms,
        })
    } else if exceeds(stored_entries, requested_entries, limits.max_matrix_entries) {
        Some(DiscoveryStop::MatrixLimit {
            stored: stored_entries as u64,
            requested: requested_entries as u64,
            limit: limits.max_matrix_entries,
        })
    } else {
        None
    }
}

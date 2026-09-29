use crate::atlas::{
    CatalogAtlasLimits, CatalogAtlasWork, MultiplicityCutReason, MultiplicityLimits,
};
use crate::portable::{push_number_object, push_tagged_numbers};

use super::model::CatalogAtlasArtifactStatus;

pub(super) fn push_atlas_limits(output: &mut String, limits: CatalogAtlasLimits) {
    push_number_object(
        output,
        &[
            ("max_pairs", limits.max_pairs),
            ("max_ext_cells", limits.max_ext_cells),
            ("max_resolution_terms", limits.max_resolution_terms),
            (
                "max_materialized_summands",
                limits.max_materialized_summands,
            ),
            ("max_materialized_cells", limits.max_materialized_cells),
        ],
    );
}

pub(super) fn push_multiplicity_limits(output: &mut String, limits: MultiplicityLimits) {
    push_number_object(
        output,
        &[
            ("max_solutions", limits.max_solutions),
            ("max_nodes", limits.max_nodes),
        ],
    );
}

pub(super) fn push_work(output: &mut String, work: CatalogAtlasWork) {
    push_number_object(
        output,
        &[
            ("pairs", work.pairs),
            ("ext_cells", work.ext_cells),
            ("resolutions", work.resolutions),
            ("resolution_terms", work.resolution_terms),
            ("ext_tables", work.ext_tables),
        ],
    );
}

pub(super) fn push_status(output: &mut String, status: &CatalogAtlasArtifactStatus) {
    match status {
        CatalogAtlasArtifactStatus::Complete => output.push_str("{\"kind\":\"complete\"}"),
        CatalogAtlasArtifactStatus::Cut {
            reason,
            coverage,
            nodes_visited,
        } => {
            output.push_str("{\"kind\":\"cut\",\"reason\":");
            push_cut_reason(output, *reason);
            output.push_str(",\"coverage\":");
            output.push_str(&coverage.to_string());
            output.push_str(",\"nodes_visited\":");
            output.push_str(&nodes_visited.to_string());
            output.push('}');
        }
    }
}

fn push_cut_reason(output: &mut String, reason: MultiplicityCutReason) {
    let (kind, limit) = match reason {
        MultiplicityCutReason::SolutionLimit { limit } => ("solution_limit", limit),
        MultiplicityCutReason::NodeLimit { limit } => ("node_limit", limit),
    };
    push_tagged_numbers(output, kind, &[("limit", limit)]);
}

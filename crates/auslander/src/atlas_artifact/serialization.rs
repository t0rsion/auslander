use std::fmt::Display;

use crate::atlas::{
    CatalogAtlasLimits, CatalogAtlasWork, MultiplicityCutReason, MultiplicityLimits,
};

use super::model::CatalogAtlasArtifactStatus;

pub(super) fn push_escaped_string(output: &mut String, bytes: &[u8]) {
    for &byte in bytes {
        match byte {
            b'"' => output.push_str("\\\""),
            b'\\' => output.push_str("\\\\"),
            _ => output.push(byte as char),
        }
    }
}

pub(super) fn push_usizes<T: Display>(output: &mut String, values: &[T]) {
    output.push('[');
    for (index, value) in values.iter().enumerate() {
        if index != 0 {
            output.push(',');
        }
        output.push_str(&value.to_string());
    }
    output.push(']');
}

pub(super) fn push_atlas_limits(output: &mut String, limits: CatalogAtlasLimits) {
    output.push_str("{\"max_pairs\":");
    output.push_str(&limits.max_pairs.to_string());
    output.push_str(",\"max_ext_cells\":");
    output.push_str(&limits.max_ext_cells.to_string());
    output.push_str(",\"max_resolution_terms\":");
    output.push_str(&limits.max_resolution_terms.to_string());
    output.push_str(",\"max_materialized_summands\":");
    output.push_str(&limits.max_materialized_summands.to_string());
    output.push_str(",\"max_materialized_cells\":");
    output.push_str(&limits.max_materialized_cells.to_string());
    output.push('}');
}

pub(super) fn push_multiplicity_limits(output: &mut String, limits: MultiplicityLimits) {
    output.push_str("{\"max_solutions\":");
    output.push_str(&limits.max_solutions.to_string());
    output.push_str(",\"max_nodes\":");
    output.push_str(&limits.max_nodes.to_string());
    output.push('}');
}

pub(super) fn push_work(output: &mut String, work: CatalogAtlasWork) {
    output.push_str("{\"pairs\":");
    output.push_str(&work.pairs.to_string());
    output.push_str(",\"ext_cells\":");
    output.push_str(&work.ext_cells.to_string());
    output.push_str(",\"resolutions\":");
    output.push_str(&work.resolutions.to_string());
    output.push_str(",\"resolution_terms\":");
    output.push_str(&work.resolution_terms.to_string());
    output.push_str(",\"ext_tables\":");
    output.push_str(&work.ext_tables.to_string());
    output.push('}');
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
    output.push('{');
    output.push_str("\"kind\":\"");
    match reason {
        MultiplicityCutReason::SolutionLimit { .. } => output.push_str("solution_limit"),
        MultiplicityCutReason::NodeLimit { .. } => output.push_str("node_limit"),
    }
    output.push_str("\",\"limit\":");
    let limit = match reason {
        MultiplicityCutReason::SolutionLimit { limit }
        | MultiplicityCutReason::NodeLimit { limit } => limit,
    };
    output.push_str(&limit.to_string());
    output.push('}');
}

pub(super) fn fingerprint(text: &str) -> String {
    let mut value = 0xcbf29ce484222325u64;
    for byte in text.bytes() {
        value ^= u64::from(byte);
        value = value.wrapping_mul(0x100000001b3);
    }
    format!("{value:016x}")
}

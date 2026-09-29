use super::portable::HomologicalStreamPortable;
use super::portable_types::{
    HomologicalStreamConfig, HomologicalStreamCutReason, HomologicalStreamPortableStatus,
};
use super::{HomologicalBatchStreamRow, HomologicalBatchStreamWork};
use crate::portable::{
    open_header, push_ascii, push_escaped, push_list, push_number_object, push_numbers,
    push_tagged_numbers,
};

pub(super) fn canonical_without_fingerprint(portable: &HomologicalStreamPortable) -> String {
    let mut output = open_header([
        super::HOMOLOGICAL_STREAM_PORTABLE_SCHEMA,
        super::HOMOLOGICAL_STREAM_PORTABLE_KIND,
        super::HOMOLOGICAL_STREAM_ENGINE_ID,
    ]);
    output.push_str(",\"census\":");
    push_escaped(&mut output, portable.census.as_bytes());
    output.push_str(",\"census_fingerprint\":");
    push_ascii(&mut output, &portable.census_fingerprint);
    output.push_str(",\"max_degree\":");
    output.push_str(&portable.max_degree.to_string());
    output.push_str(",\"config\":");
    push_config(&mut output, portable.config);
    output.push_str(",\"next_source\":");
    output.push_str(&portable.next_source.to_string());
    output.push_str(",\"rows\":");
    push_list(&mut output, &portable.rows, push_row);
    output.push_str(",\"work\":");
    push_work(&mut output, portable.work);
    output.push_str(",\"chunk_sizes\":");
    push_numbers(&mut output, &portable.chunk_sizes);
    output.push_str(",\"status\":");
    push_status(&mut output, &portable.status);
    output
}

fn push_config(output: &mut String, config: HomologicalStreamConfig) {
    let limits = config.chunk_limits;
    output.push_str("{\"chunk_limits\":");
    push_number_object(
        output,
        &[
            ("max_live_sources", limits.max_live_sources),
            ("max_pairs", limits.max_pairs),
            ("max_ext_cells", limits.max_ext_cells),
        ],
    );
    output.push_str(",\"budget\":");
    push_number_object(
        output,
        &[
            ("max_sources", config.budget.max_sources),
            ("max_work_units", config.budget.max_work_units),
        ],
    );
    output.push('}');
}

fn push_row(output: &mut String, row: &HomologicalBatchStreamRow) {
    output.push_str("{\"source\":");
    output.push_str(&row.source().to_string());
    output.push_str(",\"target\":");
    output.push_str(&row.target().to_string());
    output.push_str(",\"hom_dim\":");
    output.push_str(&row.hom_dim().to_string());
    output.push_str(",\"stable_hom_dim\":");
    output.push_str(&row.stable_hom_dim().to_string());
    output.push_str(",\"ext_dimensions\":");
    push_numbers(output, row.ext_dimensions());
    output.push_str(",\"resolution_end\":");
    push_resolution_end(output, row.resolution_end());
    output.push('}');
}

fn push_resolution_end(output: &mut String, end: crate::resolution::ResolutionEnd) {
    match end {
        crate::resolution::ResolutionEnd::Finite => output.push_str("{\"kind\":\"finite\"}"),
        crate::resolution::ResolutionEnd::Cut { at } => {
            push_tagged_numbers(output, "cut", &[("at", at)]);
        }
    }
}

fn push_work(output: &mut String, work: HomologicalBatchStreamWork) {
    push_number_object(
        output,
        &[
            ("chunks", work.chunks),
            ("sources", work.sources),
            ("resolutions", work.resolutions),
            ("target_covers", work.target_covers),
            ("hom_spaces", work.hom_spaces),
            ("projective_factor_spaces", work.projective_factor_spaces),
            ("ext_tables", work.ext_tables),
            ("peak_live_sources", work.peak_live_sources),
        ],
    );
}

fn push_status(output: &mut String, status: &HomologicalStreamPortableStatus) {
    match status {
        HomologicalStreamPortableStatus::Active => output.push_str("{\"kind\":\"active\"}"),
        HomologicalStreamPortableStatus::Complete => output.push_str("{\"kind\":\"complete\"}"),
        HomologicalStreamPortableStatus::Cut(reason) => {
            output.push_str("{\"kind\":\"cut\",\"reason\":");
            push_cut_reason(output, *reason);
            output.push('}');
        }
    }
}

fn push_cut_reason(output: &mut String, reason: HomologicalStreamCutReason) {
    match reason {
        HomologicalStreamCutReason::Cancelled => output.push_str("{\"kind\":\"cancelled\"}"),
        HomologicalStreamCutReason::SourceLimit { limit } => {
            push_tagged_numbers(output, "source_limit", &[("limit", limit)]);
        }
        HomologicalStreamCutReason::WorkLimit { limit } => {
            push_tagged_numbers(output, "work_limit", &[("limit", limit)]);
        }
    }
}

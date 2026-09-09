use super::portable::HomologicalStreamPortable;
use super::portable_types::{
    HomologicalStreamConfig, HomologicalStreamCutReason, HomologicalStreamPortableStatus,
};
use super::{HomologicalBatchStreamRow, HomologicalBatchStreamWork};

pub(super) fn canonical_without_fingerprint(portable: &HomologicalStreamPortable) -> String {
    let mut output = String::new();
    output.push_str("{\"schema\":\"");
    output.push_str(super::HOMOLOGICAL_STREAM_PORTABLE_SCHEMA);
    output.push_str("\",\"kind\":\"");
    output.push_str(super::HOMOLOGICAL_STREAM_PORTABLE_KIND);
    output.push_str("\",\"engine\":\"");
    output.push_str(super::HOMOLOGICAL_STREAM_ENGINE_ID);
    output.push_str("\",\"census\":\"");
    push_escaped(&mut output, portable.census.as_bytes());
    output.push_str("\",\"census_fingerprint\":\"");
    output.push_str(&portable.census_fingerprint);
    output.push_str("\",\"max_degree\":");
    output.push_str(&portable.max_degree.to_string());
    output.push_str(",\"config\":");
    push_config(&mut output, portable.config);
    output.push_str(",\"next_source\":");
    output.push_str(&portable.next_source.to_string());
    output.push_str(",\"rows\":[");
    for (index, row) in portable.rows.iter().enumerate() {
        if index != 0 {
            output.push(',');
        }
        push_row(&mut output, row);
    }
    output.push_str("],\"work\":");
    push_work(&mut output, portable.work);
    output.push_str(",\"chunk_sizes\":[");
    for (index, size) in portable.chunk_sizes.iter().enumerate() {
        if index != 0 {
            output.push(',');
        }
        output.push_str(&size.to_string());
    }
    output.push(']');
    output.push_str(",\"status\":");
    push_status(&mut output, &portable.status);
    output
}

pub(super) fn fingerprint(text: &str) -> String {
    let mut value = 0xcbf29ce484222325u64;
    for byte in text.bytes() {
        value ^= u64::from(byte);
        value = value.wrapping_mul(0x100000001b3);
    }
    format!("{value:016x}")
}

fn push_escaped(output: &mut String, bytes: &[u8]) {
    for &byte in bytes {
        match byte {
            b'"' => output.push_str("\\\""),
            b'\\' => output.push_str("\\\\"),
            _ => output.push(byte as char),
        }
    }
}

fn push_config(output: &mut String, config: HomologicalStreamConfig) {
    output.push_str("{\"chunk_limits\":{\"max_live_sources\":");
    output.push_str(&config.chunk_limits.max_live_sources.to_string());
    output.push_str(",\"max_pairs\":");
    output.push_str(&config.chunk_limits.max_pairs.to_string());
    output.push_str(",\"max_ext_cells\":");
    output.push_str(&config.chunk_limits.max_ext_cells.to_string());
    output.push_str("},\"budget\":{\"max_sources\":");
    output.push_str(&config.budget.max_sources.to_string());
    output.push_str(",\"max_work_units\":");
    output.push_str(&config.budget.max_work_units.to_string());
    output.push_str("}}");
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
    output.push_str(",\"ext_dimensions\":[");
    for (index, value) in row.ext_dimensions().iter().enumerate() {
        if index != 0 {
            output.push(',');
        }
        output.push_str(&value.to_string());
    }
    output.push_str("],\"resolution_end\":");
    push_resolution_end(output, row.resolution_end());
    output.push('}');
}

fn push_resolution_end(output: &mut String, end: crate::resolution::ResolutionEnd) {
    match end {
        crate::resolution::ResolutionEnd::Finite => output.push_str("{\"kind\":\"finite\"}"),
        crate::resolution::ResolutionEnd::Cut { at } => {
            output.push_str("{\"kind\":\"cut\",\"at\":");
            output.push_str(&at.to_string());
            output.push('}');
        }
    }
}

fn push_work(output: &mut String, work: HomologicalBatchStreamWork) {
    output.push_str("{\"chunks\":");
    output.push_str(&work.chunks.to_string());
    output.push_str(",\"sources\":");
    output.push_str(&work.sources.to_string());
    output.push_str(",\"resolutions\":");
    output.push_str(&work.resolutions.to_string());
    output.push_str(",\"target_covers\":");
    output.push_str(&work.target_covers.to_string());
    output.push_str(",\"hom_spaces\":");
    output.push_str(&work.hom_spaces.to_string());
    output.push_str(",\"projective_factor_spaces\":");
    output.push_str(&work.projective_factor_spaces.to_string());
    output.push_str(",\"ext_tables\":");
    output.push_str(&work.ext_tables.to_string());
    output.push_str(",\"peak_live_sources\":");
    output.push_str(&work.peak_live_sources.to_string());
    output.push('}');
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
            output.push_str("{\"kind\":\"source_limit\",\"limit\":");
            output.push_str(&limit.to_string());
            output.push('}');
        }
        HomologicalStreamCutReason::WorkLimit { limit } => {
            output.push_str("{\"kind\":\"work_limit\",\"limit\":");
            output.push_str(&limit.to_string());
            output.push('}');
        }
    }
}

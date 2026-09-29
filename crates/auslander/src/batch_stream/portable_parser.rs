use super::portable_types::{
    HomologicalStreamBudget, HomologicalStreamConfig, HomologicalStreamCutReason,
    HomologicalStreamParseLimits, HomologicalStreamPortableError, HomologicalStreamPortableStatus,
};
use super::{HomologicalBatchStreamLimits, HomologicalBatchStreamRow, HomologicalBatchStreamWork};
use crate::portable::{Cursor, CursorLimits};
use crate::resolution::ResolutionEnd;

type StreamParse<T> = Result<T, HomologicalStreamPortableError>;

pub(super) struct RawHomologicalStream {
    pub census: String,
    pub census_fingerprint: String,
    pub max_degree: usize,
    pub config: HomologicalStreamConfig,
    pub next_source: usize,
    pub rows: Vec<HomologicalBatchStreamRow>,
    pub work: HomologicalBatchStreamWork,
    pub chunk_sizes: Vec<usize>,
    pub status: HomologicalStreamPortableStatus,
    pub fingerprint: String,
}

pub(super) fn parse(
    text: &str,
    limits: HomologicalStreamParseLimits,
) -> StreamParse<RawHomologicalStream> {
    let mut c = Cursor::new(
        text,
        CursorLimits {
            input_bytes: limits.max_input_bytes,
            integer_digits: limits.max_integer_digits,
            string_bytes: limits.max_string_bytes,
            numeric_values: limits.max_numeric_values,
            array_elements: limits.max_array_elements,
        },
    )?;
    preamble(&mut c)?;
    let census = c.next("census", |c| {
        c.escaped_string("$.census", limits.max_census_bytes)
    })?;
    let census_fingerprint = c.next("census_fingerprint", |c| c.string("$.census_fingerprint"))?;
    let raw = fields(&mut c, &limits, census, census_fingerprint)?;
    c.token(b'}')?;
    c.end()?;
    Ok(raw)
}

fn preamble(c: &mut Cursor) -> StreamParse<()> {
    c.token(b'{')?;
    let expected = [
        super::HOMOLOGICAL_STREAM_PORTABLE_SCHEMA,
        super::HOMOLOGICAL_STREAM_PORTABLE_KIND,
        super::HOMOLOGICAL_STREAM_ENGINE_ID,
    ];
    c.header("$.", expected)
}

fn fields(
    c: &mut Cursor,
    limits: &HomologicalStreamParseLimits,
    census: String,
    census_fingerprint: String,
) -> StreamParse<RawHomologicalStream> {
    let max_degree = c.next("max_degree", |c| c.usize("$.max_degree"))?;
    let config = c.next("config", config)?;
    let next_source = c.next("next_source", |c| c.usize("$.next_source"))?;
    let rows = c.next("rows", |c| {
        c.array("$.rows", limits.max_rows, |c, index| row(c, index, limits))
    })?;
    let work = c.next("work", work)?;
    let chunk_sizes = c.next("chunk_sizes", |c| c.numbers("$.chunk_sizes", rows.len()))?;
    let status = c.next("status", status)?;
    let fingerprint = c.next("fingerprint", |c| c.string("$.fingerprint"))?;
    Ok(RawHomologicalStream {
        census,
        census_fingerprint,
        max_degree,
        config,
        next_source,
        rows,
        work,
        chunk_sizes,
        status,
        fingerprint,
    })
}

fn config(c: &mut Cursor) -> StreamParse<HomologicalStreamConfig> {
    c.token(b'{')?;
    c.key("chunk_limits")?;
    let [max_live_sources, max_pairs, max_ext_cells] = c.uint_object(
        "$.config.chunk_limits",
        ["max_live_sources", "max_pairs", "max_ext_cells"],
    )?;
    let [max_sources, max_work_units] = c.next("budget", |c| {
        c.uint_object("$.config.budget", ["max_sources", "max_work_units"])
    })?;
    c.token(b'}')?;
    Ok(HomologicalStreamConfig {
        chunk_limits: HomologicalBatchStreamLimits {
            max_live_sources,
            max_pairs,
            max_ext_cells,
        },
        budget: HomologicalStreamBudget {
            max_sources,
            max_work_units,
        },
    })
}

fn row(
    c: &mut Cursor,
    index: usize,
    limits: &HomologicalStreamParseLimits,
) -> StreamParse<HomologicalBatchStreamRow> {
    let path = format!("$.rows[{index}]");
    c.token(b'{')?;
    let [source, target, hom_dim, stable_hom_dim] =
        c.uint_fields(&path, ["source", "target", "hom_dim", "stable_hom_dim"])?;
    let ext_dimensions = c.next("ext_dimensions", |c| {
        c.numbers(&format!("{path}.ext_dimensions"), limits.max_ext_dimensions)
    })?;
    let resolution_end = c.next("resolution_end", |c| resolution_end(c, &path))?;
    c.token(b'}')?;
    Ok(HomologicalBatchStreamRow::from_parts(
        source,
        target,
        hom_dim,
        stable_hom_dim,
        ext_dimensions,
        resolution_end,
    ))
}

fn resolution_end(c: &mut Cursor, path: &str) -> StreamParse<ResolutionEnd> {
    c.token(b'{')?;
    c.key("kind")?;
    let end = match c.string(&format!("{path}.resolution_end.kind"))?.as_str() {
        "finite" => ResolutionEnd::Finite,
        "cut" => ResolutionEnd::Cut {
            at: c.next("at", |c| c.usize(&format!("{path}.resolution_end.at")))?,
        },
        _ => return Err(c.syntax("resolution end kind must be finite or cut").into()),
    };
    c.token(b'}')?;
    Ok(end)
}

fn work(c: &mut Cursor) -> StreamParse<HomologicalBatchStreamWork> {
    let [
        chunks,
        sources,
        resolutions,
        target_covers,
        hom_spaces,
        projective_factor_spaces,
        ext_tables,
        peak_live_sources,
    ] = c.uint_object(
        "$.work",
        [
            "chunks",
            "sources",
            "resolutions",
            "target_covers",
            "hom_spaces",
            "projective_factor_spaces",
            "ext_tables",
            "peak_live_sources",
        ],
    )?;
    Ok(HomologicalBatchStreamWork {
        chunks,
        sources,
        resolutions,
        target_covers,
        hom_spaces,
        projective_factor_spaces,
        ext_tables,
        peak_live_sources,
    })
}

fn status(c: &mut Cursor) -> StreamParse<HomologicalStreamPortableStatus> {
    c.token(b'{')?;
    c.key("kind")?;
    let status = match c.string("$.status.kind")?.as_str() {
        "active" => HomologicalStreamPortableStatus::Active,
        "complete" => HomologicalStreamPortableStatus::Complete,
        "cut" => HomologicalStreamPortableStatus::Cut(c.next("reason", cut_reason)?),
        _ => {
            return Err(c
                .syntax("status kind must be active, complete, or cut")
                .into());
        }
    };
    c.token(b'}')?;
    Ok(status)
}

fn cut_reason(c: &mut Cursor) -> StreamParse<HomologicalStreamCutReason> {
    c.token(b'{')?;
    c.key("kind")?;
    let limited: Option<fn(u64) -> HomologicalStreamCutReason> =
        match c.string("$.status.reason.kind")?.as_str() {
            "cancelled" => None,
            "source_limit" => Some(|limit| HomologicalStreamCutReason::SourceLimit { limit }),
            "work_limit" => Some(|limit| HomologicalStreamCutReason::WorkLimit { limit }),
            _ => return Err(c.syntax("unknown homological stream cut reason").into()),
        };
    let reason = limited.map_or(Ok(HomologicalStreamCutReason::Cancelled), |limited| {
        c.next("limit", |c| c.u64("$.status.reason.limit"))
            .map(limited)
    })?;
    c.token(b'}')?;
    Ok(reason)
}

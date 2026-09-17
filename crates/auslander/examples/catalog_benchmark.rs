use std::env;
use std::fmt::Write;
use std::hint::black_box;
use std::sync::Arc;
use std::time::Instant;

use auslander::algebra::{linear_nakayama, monomial_algebra};
use auslander::arquiver::{CatalogProvenance, IndecomposableCatalog};
use auslander::atlas::{CatalogAtlas, CatalogAtlasLimits, MultiplicityLimits, MultiplicityOutcome};
use auslander::atlas_artifact::{
    CatalogAtlasArtifact, CatalogAtlasArtifactParseLimits, CatalogAtlasArtifactVerifyLimits,
};
use auslander::census::{Census, CensusLimits, CensusOutcome, CensusRetention};
use auslander::ext::ext_table;
use auslander::field::PrimeField;
use auslander::monomial::MonomialIdeal;
use auslander::quiver::{ArrowId, Quiver};

const FIELD: u64 = 2;
const MAX_DEGREE: usize = 2;
const DEFAULT_ITERATIONS: usize = 3;

#[derive(Clone, Copy)]
enum CaseKind {
    NakayamaA3,
    GentleBranch,
    NakayamaA4Medium,
}

#[derive(Clone, Copy)]
struct CaseSpec {
    name: &'static str,
    kind: CaseKind,
    dimensions: &'static [usize],
    catalog_entries: usize,
    raw_space_size: u128,
    raw_classes: usize,
}

const CASES: [CaseSpec; 3] = [
    CaseSpec {
        name: "nakayama-a3",
        kind: CaseKind::NakayamaA3,
        dimensions: &[1, 1, 1],
        catalog_entries: 6,
        raw_space_size: 4,
        raw_classes: 4,
    },
    CaseSpec {
        name: "gentle-tree-branch-ab0",
        kind: CaseKind::GentleBranch,
        dimensions: &[1, 1, 1, 1],
        catalog_entries: 8,
        raw_space_size: 8,
        raw_classes: 6,
    },
    CaseSpec {
        name: "nakayama-a4-medium",
        kind: CaseKind::NakayamaA4Medium,
        dimensions: &[1, 2, 2, 1],
        catalog_entries: 10,
        raw_space_size: 256,
        raw_classes: 18,
    },
];

#[derive(Clone, Debug, PartialEq, Eq)]
struct QueryResult {
    multiplicities: Vec<Vec<usize>>,
    score_checksum: Vec<u128>,
}

struct Timings {
    algebra_ns: u128,
    catalog_ns: u128,
    raw_setup_ns: u128,
    atlas_setup_ns: u128,
    atlas_query_ns: u128,
    atlas_materialize_ns: u128,
    score_verify_ns: u128,
    atlas_verify_ns: u128,
    raw_run_ns: u128,
    raw_verify_ns: u128,
    artifact_build_ns: u128,
    artifact_serialize_ns: u128,
    artifact_parse_ns: u128,
    artifact_verify_ns: u128,
}

struct ArtifactRecord {
    bytes: usize,
    result_rows: usize,
    fingerprint: String,
    complete: bool,
    verified: bool,
}

struct RunRecord {
    spec: CaseSpec,
    iterations: usize,
    catalog: Arc<IndecomposableCatalog>,
    atlas: CatalogAtlas,
    solutions: Vec<Vec<usize>>,
    materialized: Vec<auslander::module::Module>,
    query_score_checksum_total: Vec<u128>,
    materialized_summands: usize,
    materialized_dimension_checksum: usize,
    score_matching: bool,
    atlas_verified: bool,
    raw_verified: bool,
    artifact: ArtifactRecord,
    raw: auslander::census::CensusResult,
    timings: Timings,
    peak_rss_kib: Option<u64>,
}

fn required_argument(arguments: &mut impl Iterator<Item = String>, flag: &str) -> String {
    arguments
        .next()
        .unwrap_or_else(|| panic!("{flag} needs a value"))
}

fn parse_iterations(value: String) -> usize {
    let iterations = value
        .parse()
        .unwrap_or_else(|_| panic!("--iterations needs a positive integer"));
    assert!(iterations > 0, "--iterations needs a positive integer");
    iterations
}

fn parse_case(value: String) -> &'static str {
    if value == "all" {
        return "all";
    }
    CASES
        .iter()
        .find(|case| case.name == value)
        .map(|case| case.name)
        .unwrap_or_else(|| panic!("unknown benchmark case: {value}"))
}

fn print_usage() -> ! {
    println!(
        "usage: cargo run -p auslander --example catalog_benchmark -- [--iterations N] [--case NAME]"
    );
    println!("NAME is all, nakayama-a3, gentle-tree-branch-ab0, or nakayama-a4-medium");
    std::process::exit(0);
}

fn parse_argument(
    argument: String,
    arguments: &mut impl Iterator<Item = String>,
    iterations: &mut usize,
    selected: &mut Option<&'static str>,
) {
    match argument.as_str() {
        "--iterations" => {
            *iterations = parse_iterations(required_argument(arguments, "--iterations"))
        }
        "--case" => *selected = Some(parse_case(required_argument(arguments, "--case"))),
        "--help" => print_usage(),
        _ => panic!("unknown argument: {argument}"),
    }
}

fn parse_options() -> (usize, Option<&'static str>) {
    let mut iterations = DEFAULT_ITERATIONS;
    let mut selected = None;
    let mut arguments = env::args().skip(1);
    while let Some(argument) = arguments.next() {
        parse_argument(argument, &mut arguments, &mut iterations, &mut selected);
    }
    (iterations, selected)
}

fn selected_cases(selected: Option<&str>) -> impl Iterator<Item = CaseSpec> {
    CASES
        .into_iter()
        .filter(move |case| selected.is_none_or(|name| name == "all" || name == case.name))
}

fn build_algebra(kind: CaseKind) -> Arc<auslander::algebra::Algebra> {
    let field = PrimeField::new(FIELD).expect("the benchmark field is prime");
    match kind {
        CaseKind::NakayamaA3 => linear_nakayama(&[3, 2, 1], field).expect("valid Nakayama series"),
        CaseKind::NakayamaA4Medium => {
            linear_nakayama(&[4, 3, 2, 1], field).expect("valid Nakayama series")
        }
        CaseKind::GentleBranch => {
            let quiver = Quiver::new(4, &[(0, 1), (1, 2), (3, 2)]).expect("valid tree quiver");
            let ideal = MonomialIdeal::new(quiver, vec![vec![ArrowId(0), ArrowId(1)]])
                .expect("valid quadratic relation");
            monomial_algebra(&ideal, field).expect("finite gentle-tree algebra")
        }
    }
}

fn build_catalog(
    kind: CaseKind,
    algebra: &Arc<auslander::algebra::Algebra>,
) -> IndecomposableCatalog {
    match kind {
        CaseKind::NakayamaA3 | CaseKind::NakayamaA4Medium => {
            IndecomposableCatalog::nakayama(algebra).expect("the case is Nakayama")
        }
        CaseKind::GentleBranch => {
            IndecomposableCatalog::gentle_tree(algebra).expect("the case is a gentle tree")
        }
    }
}

fn atlas_limits() -> CatalogAtlasLimits {
    CatalogAtlasLimits::default()
}

fn multiplicity_limits() -> MultiplicityLimits {
    MultiplicityLimits::default()
}

fn raw_limits(raw_space_size: u128) -> CensusLimits {
    CensusLimits {
        retention: CensusRetention::RepresentativesOnly,
        max_candidates: usize::try_from(raw_space_size).expect("raw benchmark fits usize"),
        ..CensusLimits::default()
    }
}

fn complete_query(atlas: &CatalogAtlas, dimensions: &[usize]) -> QueryResult {
    let outcome = atlas
        .enumerate_multiplicities(dimensions, multiplicity_limits())
        .expect("valid benchmark dimension vector");
    assert!(
        matches!(outcome, MultiplicityOutcome::Complete(_)),
        "benchmark multiplicity enumeration must complete"
    );
    let multiplicities = outcome.solutions().to_vec();
    let mut score_checksum = vec![0u128; MAX_DEGREE + 1];
    for vector in &multiplicities {
        let scores = atlas
            .self_ext_scores(vector, 0, MAX_DEGREE)
            .expect("scores stay inside the atlas bound");
        for (total, score) in score_checksum.iter_mut().zip(scores) {
            *total += score as u128;
        }
    }
    QueryResult {
        multiplicities,
        score_checksum,
    }
}

struct QueryRun {
    solutions: Vec<Vec<usize>>,
    score_checksum_total: Vec<u128>,
    elapsed_ns: u128,
}

fn run_queries(atlas: &CatalogAtlas, dimensions: &[usize], iterations: usize) -> QueryRun {
    let query_start = Instant::now();
    let mut first_query: Option<QueryResult> = None;
    let mut score_checksum_total = vec![0u128; MAX_DEGREE + 1];
    for _ in 0..iterations {
        let query = complete_query(atlas, dimensions);
        if let Some(first) = &first_query {
            assert_eq!(
                first, &query,
                "repeated atlas queries must be deterministic"
            );
        } else {
            first_query = Some(query.clone());
        }
        for (total, score) in score_checksum_total.iter_mut().zip(query.score_checksum) {
            *total += score;
        }
    }
    QueryRun {
        solutions: first_query.expect("at least one query ran").multiplicities,
        score_checksum_total,
        elapsed_ns: query_start.elapsed().as_nanos(),
    }
}

fn materialize_all(
    atlas: &CatalogAtlas,
    solutions: &[Vec<usize>],
) -> (Vec<auslander::module::Module>, usize, usize) {
    let mut modules = Vec::with_capacity(solutions.len());
    let mut summands = 0usize;
    let mut dimension_checksum = 0usize;
    for vector in solutions {
        summands += vector.iter().sum::<usize>();
        let module = atlas
            .materialize(vector)
            .expect("benchmark sum fits limits");
        dimension_checksum += module.total_dim();
        modules.push(module);
    }
    (modules, summands, dimension_checksum)
}

fn verify_scores(
    atlas: &CatalogAtlas,
    solutions: &[Vec<usize>],
    modules: &[auslander::module::Module],
) -> bool {
    solutions.iter().zip(modules).all(|(vector, module)| {
        let cached = atlas
            .self_ext_scores(vector, 0, MAX_DEGREE)
            .expect("scores stay inside the atlas bound");
        let generic = ext_table(module, module, MAX_DEGREE).expect("generic Ext completes");
        cached == generic
    })
}

struct ArtifactRun {
    record: ArtifactRecord,
    build_ns: u128,
    serialize_ns: u128,
    parse_ns: u128,
    verify_ns: u128,
}

fn replay_artifact(atlas: &CatalogAtlas, dimensions: &[usize]) -> ArtifactRun {
    let build_start = Instant::now();
    let artifact = CatalogAtlasArtifact::from_verified(atlas, dimensions, multiplicity_limits())
        .expect("the benchmark atlas must produce an artifact");
    let build_ns = build_start.elapsed().as_nanos();

    let serialize_start = Instant::now();
    let text = artifact.to_canonical_json();
    let serialize_ns = serialize_start.elapsed().as_nanos();

    let parse_start = Instant::now();
    let parsed = CatalogAtlasArtifact::from_json(&text, CatalogAtlasArtifactParseLimits::default())
        .expect("the benchmark artifact must parse");
    let parse_ns = parse_start.elapsed().as_nanos();

    let verify_start = Instant::now();
    let verified = parsed
        .verify(CatalogAtlasArtifactVerifyLimits::default())
        .expect("the benchmark artifact must verify");
    let verify_ns = verify_start.elapsed().as_nanos();

    assert_eq!(parsed, artifact, "artifact parsing must preserve its claim");
    assert!(
        parsed.status().is_complete(),
        "the fixed artifact must be complete"
    );
    assert_eq!(verified.artifact(), &parsed);
    assert_eq!(verified.atlas().work(), atlas.work());
    assert_eq!(verified.atlas().max_degree(), atlas.max_degree());

    ArtifactRun {
        record: ArtifactRecord {
            bytes: text.len(),
            result_rows: parsed.result_rows().len(),
            fingerprint: parsed.fingerprint().to_string(),
            complete: parsed.status().is_complete(),
            verified: true,
        },
        build_ns,
        serialize_ns,
        parse_ns,
        verify_ns,
    }
}

fn run_raw_census(
    census: &Census,
    raw_space_size: u128,
) -> (auslander::census::CensusResult, u128) {
    let raw_run_start = Instant::now();
    let raw = match census.run_with(raw_limits(raw_space_size), None) {
        CensusOutcome::Complete(result) => result,
        CensusOutcome::Cut(cut) => panic!("raw census cut: {}", cut.reason()),
        CensusOutcome::Failed(failed) => panic!("raw census failed: {}", failed.error()),
    };
    (raw, raw_run_start.elapsed().as_nanos())
}

fn run_case(spec: CaseSpec, iterations: usize) -> RunRecord {
    let algebra_start = Instant::now();
    let algebra = build_algebra(spec.kind);
    let algebra_ns = algebra_start.elapsed().as_nanos();

    let catalog_start = Instant::now();
    let catalog = Arc::new(build_catalog(spec.kind, &algebra));
    let catalog_ns = catalog_start.elapsed().as_nanos();
    assert_eq!(catalog.len(), spec.catalog_entries);

    let raw_setup_start = Instant::now();
    let census = Census::new(&algebra, spec.dimensions.to_vec()).expect("valid census domain");
    let raw_setup_ns = raw_setup_start.elapsed().as_nanos();
    assert_eq!(census.domain().raw_space_size(), spec.raw_space_size);

    let atlas_start = Instant::now();
    let atlas = CatalogAtlas::compute(catalog.clone(), MAX_DEGREE, atlas_limits())
        .expect("benchmark atlas fits default limits");
    let atlas_setup_ns = atlas_start.elapsed().as_nanos();

    let query = run_queries(&atlas, spec.dimensions, iterations);
    let solutions = query.solutions;

    let materialize_start = Instant::now();
    let (materialized, materialized_summands, materialized_dimension_checksum) =
        materialize_all(&atlas, &solutions);
    let atlas_materialize_ns = materialize_start.elapsed().as_nanos();

    let score_verify_start = Instant::now();
    let score_matching = verify_scores(&atlas, &solutions, &materialized);
    let score_verify_ns = score_verify_start.elapsed().as_nanos();
    assert!(score_matching, "cached and generic Ext scores must match");

    let atlas_verify_start = Instant::now();
    let atlas_verified = atlas.verify();
    let atlas_verify_ns = atlas_verify_start.elapsed().as_nanos();
    assert!(atlas_verified, "the atlas must replay its own stored data");

    let artifact = replay_artifact(&atlas, spec.dimensions);

    let (raw, raw_run_ns) = run_raw_census(&census, spec.raw_space_size);
    assert_eq!(raw.representatives().len(), spec.raw_classes);
    assert_eq!(raw.representatives().len(), solutions.len());

    let raw_verify_start = Instant::now();
    let raw_verified = raw.verify();
    let raw_verify_ns = raw_verify_start.elapsed().as_nanos();
    assert!(raw_verified, "the raw census must replay its stored result");

    RunRecord {
        spec,
        iterations,
        catalog,
        atlas,
        solutions,
        materialized,
        query_score_checksum_total: query.score_checksum_total,
        materialized_summands,
        materialized_dimension_checksum,
        score_matching,
        atlas_verified,
        raw_verified,
        artifact: artifact.record,
        raw,
        timings: Timings {
            algebra_ns,
            catalog_ns,
            raw_setup_ns,
            atlas_setup_ns,
            atlas_query_ns: query.elapsed_ns,
            atlas_materialize_ns,
            score_verify_ns,
            atlas_verify_ns,
            raw_run_ns,
            raw_verify_ns,
            artifact_build_ns: artifact.build_ns,
            artifact_serialize_ns: artifact.serialize_ns,
            artifact_parse_ns: artifact.parse_ns,
            artifact_verify_ns: artifact.verify_ns,
        },
        peak_rss_kib: peak_rss_kib(),
    }
}

fn provenance_name(provenance: CatalogProvenance) -> &'static str {
    match provenance {
        CatalogProvenance::Nakayama => "nakayama",
        CatalogProvenance::DynkinZeroIdeal => "dynkin-zero-ideal",
        CatalogProvenance::GentleTree => "gentle_tree",
    }
}

fn json_usize_slice(values: &[usize]) -> String {
    let mut output = String::from("[");
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            output.push(',');
        }
        write!(output, "{value}").expect("writing to a String cannot fail");
    }
    output.push(']');
    output
}

fn json_u128_slice(values: &[u128]) -> String {
    let mut output = String::from("[");
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            output.push(',');
        }
        write!(output, "{value}").expect("writing to a String cannot fail");
    }
    output.push(']');
    output
}

fn json_record(record: &RunRecord) -> String {
    let work = record.atlas.work();
    let raw = &record.raw;
    let limits = record.atlas.limits();
    let raw_limits = raw.limits();
    let multiplicity_limits = multiplicity_limits();
    let memory = record
        .peak_rss_kib
        .map_or_else(|| "null".to_string(), |value| value.to_string());
    let artifact_replay_ns = record.timings.artifact_parse_ns + record.timings.artifact_verify_ns;
    format!(
        concat!(
            "{{\"schema\":\"catalog-benchmark-v2\",",
            "\"case\":\"{}\",\"field\":{},\"dimensions\":{},\"max_degree\":{},",
            "\"iterations\":{},\"catalog\":{{\"provenance\":\"{}\",\"entries\":{}}},",
            "\"raw\":{{\"coordinates\":{},\"space\":{},\"candidates\":{},",
            "\"accepted_modules\":{},\"rejected_candidates\":{},\"representatives\":{},",
            "\"isomorphism_checks\":{},\"work_units\":{}}},",
            "\"atlas_work\":{{\"pairs\":{},\"ext_cells\":{},\"resolutions\":{},",
            "\"resolution_terms\":{},\"ext_tables\":{}}},",
            "\"queries\":{{\"calls\":{},\"solutions_per_call\":{},\"score_checksum_total\":{}}},",
            "\"materialization\":{{\"solutions\":{},\"summands\":{},\"dimension_checksum\":{}}},",
            "\"verification\":{{\"atlas\":{},\"raw\":{},\"scores\":{},",
            "\"counts\":{},\"artifact\":{}}},",
            "\"limits\":{{\"atlas_pairs\":{},\"atlas_ext_cells\":{},",
            "\"atlas_resolution_terms\":{},\"atlas_materialized_summands\":{},",
            "\"atlas_materialized_cells\":{},",
            "\"multiplicity_solutions\":{},\"multiplicity_nodes\":{},",
            "\"raw_candidates\":{},\"raw_representatives\":{},\"raw_assignments\":{},",
            "\"raw_isomorphism_checks\":{},\"raw_work_units\":{}}},",
            "\"timings_ns\":{{\"algebra\":{},\"catalog\":{},\"raw_setup\":{},",
            "\"atlas_setup\":{},\"atlas_query\":{},\"atlas_materialize\":{},",
            "\"score_verify\":{},\"atlas_verify\":{},\"raw_run\":{},\"raw_verify\":{},",
            "\"artifact_build\":{},\"artifact_serialize\":{},",
            "\"artifact_parse\":{},\"artifact_verify\":{},",
            "\"atlas_setup_total\":{},\"raw_total\":{}}},",
            "\"artifact_replay\":{{\"status\":\"verified\",\"complete\":{},",
            "\"verified\":{},\"bytes\":{},\"result_rows\":{},",
            "\"fingerprint\":\"{}\",",
            "\"timings_ns\":{{\"build\":{},\"serialize\":{},\"parse\":{},",
            "\"verify\":{},\"total\":{}}}}},",
            "\"memory_peak_kib\":{}}}"
        ),
        record.spec.name,
        FIELD,
        json_usize_slice(record.spec.dimensions),
        MAX_DEGREE,
        record.iterations,
        provenance_name(record.catalog.provenance()),
        record.catalog.len(),
        raw.domain().coordinate_count(),
        raw.domain().raw_space_size(),
        raw.candidates(),
        raw.accepted_modules(),
        raw.rejected_candidates(),
        raw.representatives().len(),
        raw.isomorphism_checks(),
        raw.work_units(),
        work.pairs,
        work.ext_cells,
        work.resolutions,
        work.resolution_terms,
        work.ext_tables,
        record.iterations,
        record.solutions.len(),
        json_u128_slice(&record.query_score_checksum_total),
        record.materialized.len(),
        record.materialized_summands,
        record.materialized_dimension_checksum,
        record.atlas_verified,
        record.raw_verified,
        record.score_matching,
        raw.representatives().len() == record.solutions.len(),
        record.artifact.verified,
        limits.max_pairs,
        limits.max_ext_cells,
        limits.max_resolution_terms,
        limits.max_materialized_summands,
        limits.max_materialized_cells,
        multiplicity_limits.max_solutions,
        multiplicity_limits.max_nodes,
        raw_limits.max_candidates,
        raw_limits.max_representatives,
        raw_limits.max_assignments,
        raw_limits.max_isomorphism_checks,
        raw_limits.max_work_units,
        record.timings.algebra_ns,
        record.timings.catalog_ns,
        record.timings.raw_setup_ns,
        record.timings.atlas_setup_ns,
        record.timings.atlas_query_ns,
        record.timings.atlas_materialize_ns,
        record.timings.score_verify_ns,
        record.timings.atlas_verify_ns,
        record.timings.raw_run_ns,
        record.timings.raw_verify_ns,
        record.timings.artifact_build_ns,
        record.timings.artifact_serialize_ns,
        record.timings.artifact_parse_ns,
        record.timings.artifact_verify_ns,
        record.timings.algebra_ns + record.timings.catalog_ns + record.timings.atlas_setup_ns,
        record.timings.raw_setup_ns + record.timings.raw_run_ns + record.timings.raw_verify_ns,
        record.artifact.complete,
        record.artifact.verified,
        record.artifact.bytes,
        record.artifact.result_rows,
        record.artifact.fingerprint,
        record.timings.artifact_build_ns,
        record.timings.artifact_serialize_ns,
        record.timings.artifact_parse_ns,
        record.timings.artifact_verify_ns,
        artifact_replay_ns,
        memory,
    )
}

fn peak_rss_kib() -> Option<u64> {
    #[cfg(target_os = "linux")]
    {
        let status = std::fs::read_to_string("/proc/self/status").ok()?;
        status.lines().find_map(|line| {
            line.strip_prefix("VmHWM:")
                .and_then(|value| value.split_whitespace().next())
                .and_then(|value| value.parse().ok())
        })
    }
    #[cfg(not(target_os = "linux"))]
    {
        None
    }
}

fn main() {
    let (iterations, selected) = parse_options();
    for spec in selected_cases(selected) {
        let record = run_case(spec, iterations);
        println!("{}", json_record(&record));
        black_box(&record.materialized);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn catalog_counts_match_complete_raw_censuses_and_scores() {
        for spec in CASES {
            let algebra = build_algebra(spec.kind);
            let catalog = Arc::new(build_catalog(spec.kind, &algebra));
            assert_eq!(catalog.len(), spec.catalog_entries);
            let atlas = CatalogAtlas::compute(catalog, MAX_DEGREE, atlas_limits()).unwrap();
            let query = complete_query(&atlas, spec.dimensions);
            let census = Census::new(&algebra, spec.dimensions.to_vec()).unwrap();
            assert_eq!(census.domain().raw_space_size(), spec.raw_space_size);
            let raw = match census.run_with(raw_limits(spec.raw_space_size), None) {
                CensusOutcome::Complete(result) => result,
                _ => panic!("the fixed census case must complete"),
            };
            assert!(raw.verify());
            assert_eq!(raw.representatives().len(), spec.raw_classes);
            assert_eq!(raw.representatives().len(), query.multiplicities.len());
            let (modules, _, _) = materialize_all(&atlas, &query.multiplicities);
            assert!(verify_scores(&atlas, &query.multiplicities, &modules));
            assert!(atlas.verify());
            let artifact = replay_artifact(&atlas, spec.dimensions);
            assert!(artifact.record.complete && artifact.record.verified);
        }
    }
}

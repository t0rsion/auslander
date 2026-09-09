use std::env;
use std::fs;

use auslander::algebra::commutative_square;
use auslander::census::{Census, CensusLimits, CensusOutcome, CensusRetention};
use auslander::ext::ext_table;
use auslander::field::PrimeField;

const SCHEMA: &str = "auslander-qpa-census-oracle-v1";
const FAMILY: &str = "commutative-square";
const FIELD: u64 = 2;
const ORDER: &str = "deglex-arrowid-v1";
const MAX_EXT: usize = 3;
const GENERATED_OUTPUT: &str = "qpa_census_generated.json";
const SENTINEL: &str = "qpa-census-oracle-generator-ok";
const DOMAIN_IDS: [&str; 2] = ["d1111", "d2112"];

#[derive(Clone, Debug, PartialEq, Eq)]
struct Accepted {
    cursor: u128,
    coordinates: Vec<u64>,
    class: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Representative {
    cursor: u128,
    coordinates: Vec<u64>,
    self_ext: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Domain {
    id: String,
    dimensions: Vec<usize>,
    raw_space_size: u128,
    coordinate_count: usize,
    candidates: usize,
    accepted_modules: usize,
    rejected_candidates: usize,
    isomorphism_checks: usize,
    accepted: Vec<Accepted>,
    rejected: Vec<u128>,
    representatives: Vec<Representative>,
    ext1_free: Vec<usize>,
    ext1_to_3_free: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq)]
struct Document {
    family: String,
    field: u64,
    presentation_id: String,
    ideal_id: String,
    order: String,
    quiver: super::QuiverSpec,
    relations: Vec<Vec<super::TermSpec>>,
    provenance: Vec<(String, String)>,
    domains: Vec<Domain>,
}

fn expected_path() -> std::path::PathBuf {
    super::oracle_dir().join("qpa_census_expected.json")
}

fn expected_text() -> String {
    let path = expected_path();
    fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("cannot read {}: {error}", path.display()))
}

fn cursor(value: &super::json::Value, context: &str) -> Result<u128, String> {
    match value {
        super::json::Value::Num(value) if *value >= 0 => Ok(*value as u128),
        _ => Err(format!("{context}: expected a non-negative integer")),
    }
}

fn coordinate_row(
    value: &super::json::Value,
    expected: usize,
    context: &str,
) -> Result<Vec<u64>, String> {
    super::usize_row(value, expected, context)
        .map(|row| row.into_iter().map(|value| value as u64).collect())
}

fn parse_accepted(
    value: &super::json::Value,
    coordinate_count: usize,
    context: &str,
) -> Result<Vec<Accepted>, String> {
    let entries = super::as_array(value, context)?;
    entries
        .iter()
        .enumerate()
        .map(|(index, value)| {
            let entry_context = format!("{context} entry {index}");
            let pairs = super::as_object(value, &entry_context)?;
            super::check_keys(pairs, &["cursor", "coordinates", "class"], &entry_context)?;
            Ok(Accepted {
                cursor: cursor(super::get(pairs, "cursor", &entry_context)?, &entry_context)?,
                coordinates: coordinate_row(
                    super::get(pairs, "coordinates", &entry_context)?,
                    coordinate_count,
                    &entry_context,
                )?,
                class: super::read_usize(pairs, "class", &entry_context)?,
            })
        })
        .collect()
}

fn parse_representatives(
    value: &super::json::Value,
    coordinate_count: usize,
    context: &str,
) -> Result<Vec<Representative>, String> {
    let entries = super::as_array(value, context)?;
    entries
        .iter()
        .enumerate()
        .map(|(index, value)| {
            let entry_context = format!("{context} entry {index}");
            let pairs = super::as_object(value, &entry_context)?;
            super::check_keys(
                pairs,
                &["cursor", "coordinates", "self_ext"],
                &entry_context,
            )?;
            Ok(Representative {
                cursor: cursor(super::get(pairs, "cursor", &entry_context)?, &entry_context)?,
                coordinates: coordinate_row(
                    super::get(pairs, "coordinates", &entry_context)?,
                    coordinate_count,
                    &entry_context,
                )?,
                self_ext: super::usize_row(
                    super::get(pairs, "self_ext", &entry_context)?,
                    MAX_EXT + 1,
                    &entry_context,
                )?,
            })
        })
        .collect()
}

fn parse_rejected(value: &super::json::Value, context: &str) -> Result<Vec<u128>, String> {
    super::as_array(value, context)?
        .iter()
        .enumerate()
        .map(|(index, value)| cursor(value, &format!("{context} entry {index}")))
        .collect()
}

struct DomainMetadata {
    id: String,
    dimensions: Vec<usize>,
    raw_space_size: u128,
    coordinate_count: usize,
    candidates: usize,
    accepted_modules: usize,
    rejected_candidates: usize,
    isomorphism_checks: usize,
}

struct DomainRecords {
    accepted: Vec<Accepted>,
    rejected: Vec<u128>,
    representatives: Vec<Representative>,
    ext1_free: Vec<usize>,
    ext1_to_3_free: Vec<usize>,
}

fn read_cursor_field(
    pairs: &[(String, super::json::Value)],
    key: &str,
    context: &str,
) -> Result<u128, String> {
    cursor(super::get(pairs, key, context)?, context)
}

fn read_domain_metadata(
    pairs: &[(String, super::json::Value)],
    context: &str,
) -> Result<DomainMetadata, String> {
    Ok(DomainMetadata {
        id: super::read_str(pairs, "id", context)?,
        dimensions: super::usize_row(
            super::get(pairs, "dimensions", context)?,
            4,
            &format!("{context}: dimensions"),
        )?,
        raw_space_size: read_cursor_field(pairs, "raw_space_size", context)?,
        coordinate_count: super::read_usize(pairs, "coordinate_count", context)?,
        candidates: super::read_usize(pairs, "candidates", context)?,
        accepted_modules: super::read_usize(pairs, "accepted_modules", context)?,
        rejected_candidates: super::read_usize(pairs, "rejected_candidates", context)?,
        isomorphism_checks: super::read_usize(pairs, "isomorphism_checks", context)?,
    })
}

fn parse_field<T>(
    pairs: &[(String, super::json::Value)],
    key: &str,
    context: &str,
    parser: impl FnOnce(&super::json::Value, &str) -> Result<T, String>,
) -> Result<T, String> {
    let value = super::get(pairs, key, context)?;
    parser(value, &format!("{context}: {key}"))
}

fn parse_domain_records(
    pairs: &[(String, super::json::Value)],
    coordinate_count: usize,
    context: &str,
) -> Result<DomainRecords, String> {
    let accepted = parse_field(pairs, "accepted", context, |value, field| {
        parse_accepted(value, coordinate_count, field)
    })?;
    let rejected = parse_field(pairs, "rejected", context, parse_rejected)?;
    let representatives = parse_field(pairs, "representatives", context, |value, field| {
        parse_representatives(value, coordinate_count, field)
    })?;
    let ext1_free = parse_field(pairs, "ext1_free", context, parse_indices)?;
    let ext1_to_3_free = parse_field(pairs, "ext1_to_3_free", context, parse_indices)?;
    Ok(DomainRecords {
        accepted,
        rejected,
        representatives,
        ext1_free,
        ext1_to_3_free,
    })
}

fn parse_domain(value: &super::json::Value, index: usize) -> Result<Domain, String> {
    let context = format!("domain {index}");
    let pairs = super::as_object(value, &context)?;
    super::check_keys(
        pairs,
        &[
            "id",
            "dimensions",
            "raw_space_size",
            "coordinate_count",
            "candidates",
            "accepted_modules",
            "rejected_candidates",
            "isomorphism_checks",
            "accepted",
            "rejected",
            "representatives",
            "ext1_free",
            "ext1_to_3_free",
        ],
        &context,
    )?;
    let metadata = read_domain_metadata(pairs, &context)?;
    let records = parse_domain_records(pairs, metadata.coordinate_count, &context)?;
    let domain = Domain {
        id: metadata.id,
        dimensions: metadata.dimensions,
        raw_space_size: metadata.raw_space_size,
        coordinate_count: metadata.coordinate_count,
        candidates: metadata.candidates,
        accepted_modules: metadata.accepted_modules,
        rejected_candidates: metadata.rejected_candidates,
        isomorphism_checks: metadata.isomorphism_checks,
        accepted: records.accepted,
        rejected: records.rejected,
        representatives: records.representatives,
        ext1_free: records.ext1_free,
        ext1_to_3_free: records.ext1_to_3_free,
    };
    validate_domain(&domain)?;
    Ok(domain)
}

fn parse_indices(value: &super::json::Value, context: &str) -> Result<Vec<usize>, String> {
    let values = super::as_array(value, context)?;
    let output = values
        .iter()
        .enumerate()
        .map(|(index, value)| super::usize_value(value, &format!("{context} entry {index}")))
        .collect::<Result<Vec<_>, _>>()?;
    if output.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(format!("{context}: indices are not strictly increasing"));
    }
    Ok(output)
}

fn digits(mut cursor: u128, count: usize) -> Vec<u64> {
    let mut output = vec![0; count];
    for value in output.iter_mut().rev() {
        *value = (cursor % u128::from(FIELD)) as u64;
        cursor /= u128::from(FIELD);
    }
    output
}

fn coordinate_count(dimensions: &[usize]) -> usize {
    dimensions[0] * dimensions[1]
        + dimensions[1] * dimensions[3]
        + dimensions[0] * dimensions[2]
        + dimensions[2] * dimensions[3]
}

fn parse_document_header(
    pairs: &[(String, super::json::Value)],
) -> Result<(String, u64, String, String, String), String> {
    let schema = super::read_str(pairs, "schema", "root")?;
    if schema != SCHEMA {
        return Err(format!("root: schema {schema:?}, expected {SCHEMA:?}"));
    }
    let convention = super::read_str(pairs, "convention", "root")?;
    if convention != "right" {
        return Err(format!(
            "root: convention {convention:?}, expected \"right\""
        ));
    }
    let family = super::read_str(pairs, "family", "root")?;
    let field = super::read_usize(pairs, "field", "root")? as u64;
    let presentation_id = super::read_str(pairs, "presentation_id", "root")?;
    let ideal_id = super::read_str(pairs, "ideal_id", "root")?;
    let order = super::read_str(pairs, "order", "root")?;
    Ok((family, field, presentation_id, ideal_id, order))
}

fn parse_document_presentation(
    pairs: &[(String, super::json::Value)],
) -> Result<(super::QuiverSpec, Vec<Vec<super::TermSpec>>), String> {
    let quiver = super::read_quiver(super::get(pairs, "quiver", "root")?, "root")?;
    let relations = super::read_relations(
        super::get(pairs, "relations", "root")?,
        quiver.arrows.len(),
        "root",
    )?;
    Ok((quiver, relations))
}

fn parse_document_domains(value: &super::json::Value) -> Result<Vec<Domain>, String> {
    super::as_array(value, "root: domains")?
        .iter()
        .enumerate()
        .map(|(index, value)| parse_domain(value, index))
        .collect::<Result<Vec<_>, _>>()
}

fn parse_document(text: &str) -> Result<Document, String> {
    let value = super::json::parse(text)?;
    let pairs = super::as_object(&value, "root")?;
    super::check_keys(
        pairs,
        &[
            "schema",
            "convention",
            "family",
            "field",
            "presentation_id",
            "ideal_id",
            "order",
            "quiver",
            "relations",
            "provenance",
            "domains",
        ],
        "root",
    )?;
    let (family, field, presentation_id, ideal_id, order) = parse_document_header(pairs)?;
    let (quiver, relations) = parse_document_presentation(pairs)?;
    let provenance = parse_field(pairs, "provenance", "root", |value, _| {
        parse_provenance(value)
    })?;
    let domains = parse_field(pairs, "domains", "root", |value, _| {
        parse_document_domains(value)
    })?;
    let document = Document {
        family,
        field,
        presentation_id,
        ideal_id,
        order,
        quiver,
        relations,
        provenance,
        domains,
    };
    validate_document(&document)?;
    Ok(document)
}

fn parse_provenance(value: &super::json::Value) -> Result<Vec<(String, String)>, String> {
    let pairs = super::as_object(value, "root: provenance")?;
    super::check_keys(
        pairs,
        &["gap_version", "qpa_version", "command"],
        "provenance",
    )?;
    ["gap_version", "qpa_version", "command"]
        .into_iter()
        .map(|key| Ok((key.to_string(), super::read_str(pairs, key, "provenance")?)))
        .collect()
}

fn expected_document() -> Document {
    parse_document(&expected_text())
        .unwrap_or_else(|error| panic!("census oracle rejected: {error}"))
}

fn without_provenance(document: &Document) -> Document {
    let mut value = document.clone();
    value.provenance.clear();
    value
}

fn census_for(dimensions: &[usize]) -> auslander::census::CensusResult {
    let algebra = commutative_square(PrimeField::new(FIELD).expect("F_2 is prime"));
    let outcome = Census::new(&algebra, dimensions.to_vec())
        .expect("census dimensions define a census domain")
        .run_with(
            CensusLimits {
                retention: CensusRetention::AllAssignments,
                max_candidates: 256,
                max_representatives: 100,
                max_assignments: 256,
                max_isomorphism_checks: 10_000,
                max_work_units: 100_000,
            },
            None,
        );
    match outcome {
        CensusOutcome::Complete(result) => result,
        CensusOutcome::Cut(cut) => panic!("census cut: {}", cut.reason()),
        CensusOutcome::Failed(failed) => panic!("census failed: {}", failed.error()),
    }
}

fn actual_partition(result: &auslander::census::CensusResult) -> Vec<Accepted> {
    let representatives =
        result
            .representatives()
            .iter()
            .enumerate()
            .map(|(class, representative)| Accepted {
                cursor: representative.cursor(),
                coordinates: representative.coordinates().to_vec(),
                class,
            });
    let assignments = result.assignments().iter().map(|assignment| Accepted {
        cursor: assignment.cursor(),
        coordinates: assignment.coordinates().to_vec(),
        class: assignment.representative(),
    });
    let mut output = representatives.chain(assignments).collect::<Vec<_>>();
    output.sort_by_key(|entry| entry.cursor);
    output
}

fn compare_domain_counts(
    expected: &Domain,
    result: &auslander::census::CensusResult,
) -> Vec<String> {
    let mut mismatches = Vec::new();
    let context = expected.id.as_str();
    if result.domain().raw_space_size() != expected.raw_space_size {
        mismatches.push(format!("{context}: raw_space_size"));
    }
    if result.domain().coordinate_count() != expected.coordinate_count {
        mismatches.push(format!("{context}: coordinate_count"));
    }
    if result.candidates() != expected.candidates {
        mismatches.push(format!("{context}: candidates"));
    }
    if result.accepted_modules() != expected.accepted_modules {
        mismatches.push(format!("{context}: accepted_modules"));
    }
    if result.rejected_candidates() != expected.rejected_candidates {
        mismatches.push(format!("{context}: rejected_candidates"));
    }
    if result.isomorphism_checks() != expected.isomorphism_checks {
        mismatches.push(format!("{context}: isomorphism_checks"));
    }
    mismatches
}

fn compare_domain_partition(
    expected: &Domain,
    result: &auslander::census::CensusResult,
    actual_partition: &[Accepted],
) -> Vec<String> {
    let mut mismatches = Vec::new();
    let context = expected.id.as_str();
    let actual_representatives = result
        .representatives()
        .iter()
        .map(|representative| {
            (
                representative.cursor(),
                representative.coordinates().to_vec(),
            )
        })
        .collect::<Vec<_>>();
    let expected_representatives = expected
        .representatives
        .iter()
        .map(|representative| (representative.cursor, representative.coordinates.clone()))
        .collect::<Vec<_>>();
    if actual_representatives != expected_representatives {
        mismatches.push(format!("{context}: representatives"));
    }
    if actual_partition != expected.accepted.as_slice() {
        mismatches.push(format!("{context}: accepted partition"));
    }
    let actual_rejected = (0..result.domain().raw_space_size())
        .filter(|cursor| !actual_partition.iter().any(|entry| entry.cursor == *cursor))
        .collect::<Vec<_>>();
    if actual_rejected != expected.rejected {
        mismatches.push(format!("{context}: rejected partition"));
    }
    mismatches
}

fn compare_domain_ext(expected: &Domain, result: &auslander::census::CensusResult) -> Vec<String> {
    let mut mismatches = Vec::new();
    let context = expected.id.as_str();
    let actual_ext = result
        .representatives()
        .iter()
        .map(|representative| {
            ext_table(representative.module(), representative.module(), MAX_EXT).unwrap()
        })
        .collect::<Vec<_>>();
    let expected_ext = expected
        .representatives
        .iter()
        .map(|representative| representative.self_ext.clone())
        .collect::<Vec<_>>();
    if actual_ext != expected_ext {
        mismatches.push(format!("{context}: self_ext"));
    }
    let actual_ext1_free = actual_ext
        .iter()
        .enumerate()
        .filter_map(|(index, ext)| (ext[1] == 0).then_some(index))
        .collect::<Vec<_>>();
    let actual_ext1_to_3_free = actual_ext
        .iter()
        .enumerate()
        .filter_map(|(index, ext)| ext[1..].iter().all(|&value| value == 0).then_some(index))
        .collect::<Vec<_>>();
    if actual_ext1_free != expected.ext1_free {
        mismatches.push(format!("{context}: ext1_free"));
    }
    if actual_ext1_to_3_free != expected.ext1_to_3_free {
        mismatches.push(format!("{context}: ext1_to_3_free"));
    }
    mismatches
}

fn compare_domain(expected: &Domain) -> Vec<String> {
    let result = census_for(&expected.dimensions);
    let actual_partition = actual_partition(&result);
    let mut mismatches = compare_domain_counts(expected, &result);
    mismatches.extend(compare_domain_partition(
        expected,
        &result,
        &actual_partition,
    ));
    mismatches.extend(compare_domain_ext(expected, &result));
    mismatches
}

fn compare_document(document: &Document) -> Vec<String> {
    document.domains.iter().flat_map(compare_domain).collect()
}

fn replace_once(text: &str, from: &str, to: &str) -> String {
    assert_eq!(
        text.matches(from).count(),
        1,
        "corruption target is not unique: {from}"
    );
    text.replacen(from, to, 1)
}

include!("census_validation.rs");
include!("census_tests.rs");

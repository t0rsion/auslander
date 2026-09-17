use std::fs;
use std::sync::Arc;

use auslander::algebra::{Algebra, monomial_algebra};
use auslander::almost_split::{AlmostSplitOutcome, almost_split};
use auslander::arquiver::{CatalogProvenance, IndecomposableCatalog, ar_quiver_from_catalog};
use auslander::decompose::decompose;
use auslander::ext::ext_table;
use auslander::field::PrimeField;
use auslander::gentle::gentle_tree_strings;
use auslander::hom::hom_dim;
use auslander::module::Module;
use auslander::monomial::MonomialIdeal;
use auslander::quiver::{ArrowId, Quiver};

use super::json;

const SCHEMA: &str = "auslander-catalog-qpa-v1";
const GENERATOR_OUTPUT: &str = "catalog_qpa_generated.json";
const GENERATOR_SENTINEL: &str = "qpa-catalog-oracle-generator-ok";
const MAX_EXT: usize = 3;

#[derive(Clone, Debug, PartialEq)]
struct Presentation {
    num_vertices: u32,
    arrows: Vec<(u32, u32)>,
    relations: Vec<Vec<ArrowId>>,
}

#[derive(Clone, Debug, PartialEq)]
struct ModuleRecord {
    dimvec: Vec<usize>,
    maps: Vec<Vec<Vec<usize>>>,
}

#[derive(Clone, Debug, PartialEq)]
struct ArRecord {
    projective: bool,
    tau: Option<Vec<usize>>,
    middle_dimvec: Option<Vec<usize>>,
    middle: Vec<(Vec<usize>, usize)>,
    middle_summands: usize,
}

#[derive(Clone, Debug, PartialEq)]
struct Fixture {
    field: u64,
    algebra_dim: usize,
    count: usize,
    max_length: usize,
    checked_length: usize,
    strings: Vec<String>,
    modules: Vec<ModuleRecord>,
    hom: Vec<Vec<usize>>,
    ext: Vec<Vec<Vec<usize>>>,
    ar: Vec<ArRecord>,
    irr_in: Vec<Vec<Vec<usize>>>,
    irr_out: Vec<Vec<Vec<usize>>>,
}

#[derive(Clone, Debug, PartialEq)]
struct Document {
    presentation: Presentation,
    fixtures: Vec<Fixture>,
}

fn object(value: &json::Value) -> &[(String, json::Value)] {
    match value {
        json::Value::Obj(pairs) => pairs,
        other => panic!("expected object, found {other:?}"),
    }
}

fn array(value: &json::Value) -> &[json::Value] {
    value
        .as_arr()
        .unwrap_or_else(|| panic!("expected array, found {value:?}"))
}

fn member<'a>(pairs: &'a [(String, json::Value)], key: &str) -> &'a json::Value {
    pairs
        .iter()
        .find(|(name, _)| name == key)
        .map(|(_, value)| value)
        .unwrap_or_else(|| panic!("missing catalog oracle key {key:?}"))
}

fn keys(pairs: &[(String, json::Value)], expected: &[&str]) {
    assert_eq!(
        pairs.len(),
        expected.len(),
        "catalog oracle key set changed"
    );
    for key in expected {
        assert!(
            pairs.iter().any(|(name, _)| name == key),
            "catalog oracle key {key:?} is missing"
        );
    }
}

fn integer(value: &json::Value) -> i64 {
    match value {
        json::Value::Num(number) => *number,
        other => panic!("expected integer, found {other:?}"),
    }
}

fn usize_value(value: &json::Value) -> usize {
    usize::try_from(integer(value)).expect("catalog oracle integer is nonnegative")
}

fn string(value: &json::Value) -> String {
    match value {
        json::Value::Str(value) => value.clone(),
        other => panic!("expected string, found {other:?}"),
    }
}

fn row(value: &json::Value) -> Vec<usize> {
    array(value).iter().map(usize_value).collect()
}

fn matrix(value: &json::Value) -> Vec<Vec<usize>> {
    array(value).iter().map(row).collect()
}

fn tensor(value: &json::Value) -> Vec<Vec<Vec<usize>>> {
    array(value).iter().map(matrix).collect()
}

fn parse_presentation(root: &[(String, json::Value)]) -> Presentation {
    let q = object(member(root, "quiver"));
    keys(q, &["num_vertices", "arrows"]);
    let arrows = array(member(q, "arrows"))
        .iter()
        .map(|value| {
            let values = array(value);
            assert_eq!(values.len(), 3, "catalog oracle arrow has three fields");
            let name = string(&values[2]);
            assert!(!name.is_empty(), "catalog oracle arrow name is empty");
            (
                usize_value(&values[0]) as u32,
                usize_value(&values[1]) as u32,
            )
        })
        .collect();
    let relations = array(member(root, "relations"))
        .iter()
        .map(|value| {
            let terms = array(value);
            assert_eq!(terms.len(), 1, "catalog oracle relation is not monomial");
            let term = array(&terms[0]);
            assert_eq!(term.len(), 2, "catalog oracle relation term has two fields");
            assert_eq!(integer(&term[0]), 1, "catalog oracle relation is not monic");
            row(&term[1])
                .into_iter()
                .map(|arrow| ArrowId(arrow as u32))
                .collect()
        })
        .collect();
    Presentation {
        num_vertices: usize_value(member(q, "num_vertices")) as u32,
        arrows,
        relations,
    }
}

fn parse_module(value: &json::Value) -> ModuleRecord {
    let pairs = object(value);
    keys(pairs, &["dimvec", "maps"]);
    ModuleRecord {
        dimvec: row(member(pairs, "dimvec")),
        maps: tensor(member(pairs, "maps")),
    }
}

fn parse_weighted(value: &json::Value) -> Vec<(Vec<usize>, usize)> {
    array(value)
        .iter()
        .map(|entry| {
            let pairs = object(entry);
            keys(pairs, &["dimvec", "multiplicity"]);
            (
                row(member(pairs, "dimvec")),
                usize_value(member(pairs, "multiplicity")),
            )
        })
        .collect()
}

fn parse_ar(value: &json::Value) -> ArRecord {
    let pairs = object(value);
    let projective = match member(pairs, "projective") {
        json::Value::Bool(value) => *value,
        other => panic!("catalog oracle projective flag is not boolean: {other:?}"),
    };
    if projective {
        keys(pairs, &["projective"]);
        return ArRecord {
            projective,
            tau: None,
            middle_dimvec: None,
            middle: Vec::new(),
            middle_summands: 0,
        };
    }
    keys(
        pairs,
        &[
            "projective",
            "tau",
            "middle_dimvec",
            "middle",
            "middle_summands",
        ],
    );
    ArRecord {
        projective,
        tau: Some(row(member(pairs, "tau"))),
        middle_dimvec: Some(row(member(pairs, "middle_dimvec"))),
        middle: parse_weighted(member(pairs, "middle")),
        middle_summands: usize_value(member(pairs, "middle_summands")),
    }
}

fn parse_fixture(value: &json::Value) -> Fixture {
    let pairs = object(value);
    keys(
        pairs,
        &[
            "field",
            "algebra_dim",
            "count",
            "max_length",
            "checked_length",
            "strings",
            "modules",
            "hom",
            "ext",
            "ar",
            "irr_in",
            "irr_out",
        ],
    );
    Fixture {
        field: usize_value(member(pairs, "field")) as u64,
        algebra_dim: usize_value(member(pairs, "algebra_dim")),
        count: usize_value(member(pairs, "count")),
        max_length: usize_value(member(pairs, "max_length")),
        checked_length: usize_value(member(pairs, "checked_length")),
        strings: array(member(pairs, "strings")).iter().map(string).collect(),
        modules: array(member(pairs, "modules"))
            .iter()
            .map(parse_module)
            .collect(),
        hom: matrix(member(pairs, "hom")),
        ext: tensor(member(pairs, "ext")),
        ar: array(member(pairs, "ar")).iter().map(parse_ar).collect(),
        irr_in: tensor(member(pairs, "irr_in")),
        irr_out: tensor(member(pairs, "irr_out")),
    }
}

fn parse_document(text: &str) -> Document {
    let value = json::parse(text).expect("catalog QPA oracle is valid JSON");
    let root = object(&value);
    keys(
        root,
        &[
            "schema",
            "convention",
            "max_ext_degree",
            "quiver",
            "relations",
            "fixtures",
            "provenance",
        ],
    );
    assert_eq!(string(member(root, "schema")), SCHEMA);
    assert_eq!(string(member(root, "convention")), "right");
    assert_eq!(usize_value(member(root, "max_ext_degree")), MAX_EXT);
    let provenance = object(member(root, "provenance"));
    keys(provenance, &["gap_version", "qpa_version", "command"]);
    for key in ["gap_version", "qpa_version", "command"] {
        assert!(!string(member(provenance, key)).is_empty());
    }
    assert!(string(member(provenance, "command")).contains("generate_catalog_fixtures.g"));
    Document {
        presentation: parse_presentation(root),
        fixtures: array(member(root, "fixtures"))
            .iter()
            .map(parse_fixture)
            .collect(),
    }
}

fn read_committed() -> Document {
    let path = super::oracle_dir().join("catalog_qpa_expected.json");
    let text =
        fs::read_to_string(&path).unwrap_or_else(|error| panic!("cannot read {path:?}: {error}"));
    parse_document(&text)
}

fn expected_presentation() -> Presentation {
    Presentation {
        num_vertices: 4,
        arrows: vec![(0, 1), (1, 2), (3, 2)],
        relations: vec![vec![ArrowId(0), ArrowId(1)]],
    }
}

fn build_algebra(presentation: &Presentation, field: u64) -> Arc<Algebra> {
    let quiver = Quiver::new(presentation.num_vertices, &presentation.arrows).unwrap();
    let ideal = MonomialIdeal::new(quiver, presentation.relations.clone()).unwrap();
    monomial_algebra(&ideal, PrimeField::new(field).unwrap()).unwrap()
}

fn module_maps(module: &Module) -> Vec<Vec<Vec<usize>>> {
    (0..module.algebra().quiver().num_arrows())
        .map(|arrow| {
            let matrix = module
                .map(ArrowId(arrow as u32))
                .entries_u64()
                .into_iter()
                .map(|values| values.into_iter().map(|value| value as usize).collect())
                .collect::<Vec<Vec<usize>>>();
            if matrix.is_empty() || matrix[0].is_empty() {
                vec![vec![0]]
            } else {
                matrix
            }
        })
        .collect()
}

fn expected_entry(catalog: &IndecomposableCatalog, record: &ModuleRecord) -> usize {
    let mut matches = catalog.entries().iter().enumerate().filter(|(_, entry)| {
        entry.module().dim_vector() == record.dimvec.as_slice()
            && module_maps(entry.module()) == record.maps
    });
    let index = matches
        .next()
        .map(|(index, _)| index)
        .unwrap_or_else(|| panic!("QPA module {:?} is absent from the catalog", record.dimvec));
    assert!(
        matches.next().is_none(),
        "QPA module occurs twice in the catalog"
    );
    index
}

fn weighted_dimensions(module: &Module) -> Vec<(Vec<usize>, usize)> {
    let decomposition = decompose(module);
    let mut out = Vec::new();
    for summand in decomposition.summands() {
        let dimvec = summand.dim_vector().to_vec();
        match out.iter_mut().find(|(known, _)| *known == dimvec) {
            Some((_, multiplicity)) => *multiplicity += 1,
            None => out.push((dimvec, 1)),
        }
    }
    out.sort();
    out
}

fn expected_vertices(
    ar: &auslander::arquiver::ArQuiver,
    catalog: &IndecomposableCatalog,
    fixture: &Fixture,
    indices: &[usize],
) -> Vec<usize> {
    fixture
        .modules
        .iter()
        .enumerate()
        .map(|(qpa_index, record)| {
            let catalog_index = expected_entry(catalog, record);
            assert_eq!(indices[qpa_index], catalog_index);
            ar
                .vertices()
                .iter()
                .position(|vertex| vertex.id() == catalog_index)
                .expect("AR quiver omits a catalog entry")
        })
        .collect()
}

fn check_ar(
    ar: &auslander::arquiver::ArQuiver,
    catalog: &IndecomposableCatalog,
    fixture: &Fixture,
    indices: &[usize],
    vertices: &[usize],
) {
    for (qpa_index, record) in fixture.ar.iter().enumerate() {
        let vertex = &ar.vertices()[vertices[qpa_index]];
        assert_eq!(vertex.projective(), record.projective);
        let outcome = almost_split(&catalog.entries()[indices[qpa_index]]).unwrap();
        match (&outcome, record.projective) {
            (AlmostSplitOutcome::Projective, true) => {}
            (AlmostSplitOutcome::Projective, false) => panic!("QPA sequence is nonprojective"),
            (AlmostSplitOutcome::Sequence(_), true) => panic!("QPA sequence is projective"),
            (AlmostSplitOutcome::Sequence(sequence), false) => {
                assert_eq!(
                    sequence.sequence().sub().dim_vector(),
                    record.tau.as_ref().unwrap()
                );
                assert_eq!(
                    sequence.sequence().middle().dim_vector(),
                    record.middle_dimvec.as_ref().unwrap()
                );
                assert_eq!(
                    weighted_dimensions(sequence.sequence().middle()),
                    record.middle
                );
                assert_eq!(
                    record.middle_summands,
                    record.middle.iter().map(|(_, count)| count).sum()
                );
            }
        }
    }
}

fn arrow_endpoints(
    ar: &auslander::arquiver::ArQuiver,
    vertex: usize,
    incoming: bool,
) -> Vec<Vec<usize>> {
    let mut endpoints = ar
        .arrows()
        .iter()
        .filter_map(|arrow| {
            let matches = if incoming {
                arrow.target() == vertex
            } else {
                arrow.source() == vertex
            };
            matches.then(|| {
                let endpoint = if incoming {
                    arrow.source()
                } else {
                    arrow.target()
                };
                ar.vertices()[endpoint]
                    .module()
                    .module()
                    .dim_vector()
                    .to_vec()
            })
        })
        .collect::<Vec<_>>();
    endpoints.sort();
    endpoints
}

fn check_fixture(document: &Document, fixture: &Fixture) {
    let algebra = build_algebra(&document.presentation, fixture.field);
    assert_eq!(algebra.dim(), fixture.algebra_dim);
    let strings = gentle_tree_strings(&algebra).unwrap();
    assert_eq!(strings.len(), fixture.count);
    assert_eq!(strings.len(), fixture.strings.len());
    assert!(fixture.checked_length > fixture.max_length);
    assert_eq!(
        strings.iter().map(|string| string.vertices().len()).max(),
        Some(fixture.max_length)
    );

    let catalog = IndecomposableCatalog::gentle_tree(&algebra).unwrap();
    assert_eq!(catalog.provenance(), CatalogProvenance::GentleTree);
    assert_eq!(catalog.len(), fixture.count);
    let indices: Vec<usize> = fixture
        .modules
        .iter()
        .map(|record| expected_entry(&catalog, record))
        .collect();
    for (record, &index) in fixture.modules.iter().zip(&indices) {
        assert_eq!(module_maps(catalog.entries()[index].module()), record.maps);
    }
    for (source, &source_index) in indices.iter().enumerate() {
        for (target, &target_index) in indices.iter().enumerate() {
            let source_module = catalog.entries()[source_index].module();
            let target_module = catalog.entries()[target_index].module();
            assert_eq!(
                hom_dim(source_module, target_module).unwrap(),
                fixture.hom[source][target]
            );
            assert_eq!(
                ext_table(source_module, target_module, MAX_EXT).unwrap(),
                (0..=MAX_EXT)
                    .map(|degree| fixture.ext[degree][source][target])
                    .collect::<Vec<_>>()
            );
        }
    }

    let ar = ar_quiver_from_catalog(&catalog).unwrap();
    let vertices = expected_vertices(&ar, &catalog, fixture, &indices);
    check_ar(&ar, &catalog, fixture, &indices, &vertices);
    for (qpa_index, &vertex) in vertices.iter().enumerate() {
        assert_eq!(
            arrow_endpoints(&ar, vertex, true),
            fixture.irr_in[qpa_index]
        );
        assert_eq!(
            arrow_endpoints(&ar, vertex, false),
            fixture.irr_out[qpa_index]
        );
    }
}

#[test]
fn catalog_qpa_oracle_matches_the_gentle_catalog() {
    let document = read_committed();
    assert_eq!(document.presentation, expected_presentation());
    assert_eq!(document.fixtures.len(), 2);
    assert_eq!(
        document
            .fixtures
            .iter()
            .map(|fixture| fixture.field)
            .collect::<Vec<_>>(),
        vec![2, 5]
    );
    for fixture in &document.fixtures {
        assert_eq!(
            fixture.strings,
            vec![
                "(1,-1)".to_string(),
                "(2,-1)".to_string(),
                "(3,-1)".to_string(),
                "(4,-1)".to_string(),
                "A".to_string(),
                "B".to_string(),
                "Bc".to_string(),
                "C".to_string(),
            ]
        );
        check_fixture(&document, fixture);
    }
}

#[cfg(unix)]
#[test]
fn catalog_live_gap_run_agrees_with_committed_truth() {
    if std::env::var("QPA_ORACLE").as_deref() != Ok("1") {
        println!("live catalog QPA run skipped; set QPA_ORACLE=1 to invoke GAP+QPA");
        return;
    }
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("clock after the epoch")
        .as_nanos();
    let workdir =
        std::env::temp_dir().join(format!("qpa-catalog-oracle-{}-{nanos}", std::process::id()));
    fs::create_dir(&workdir).expect("can create a fresh catalog GAP directory");
    let script = super::oracle_dir().join("generate_catalog_fixtures.g");
    let output = super::gap_command(&workdir)
        .arg(&script)
        .output()
        .unwrap_or_else(|error| panic!("cannot launch GAP: {error}"));
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    // GAP can exit zero after an uncaught error, so the final sentinel and
    // generated document are the completion signals.
    assert_eq!(
        stdout.lines().next_back(),
        Some(GENERATOR_SENTINEL),
        "catalog QPA generator did not finish; stdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let generated = workdir.join(GENERATOR_OUTPUT);
    let generated_text = fs::read_to_string(&generated)
        .unwrap_or_else(|error| panic!("cannot read {}: {error}", generated.display()));
    let fresh = parse_document(&generated_text);
    let committed = read_committed();
    assert_eq!(
        fresh, committed,
        "fresh catalog QPA values differ from committed truth"
    );
    for fixture in &fresh.fixtures {
        check_fixture(&fresh, fixture);
    }
    fs::remove_dir_all(&workdir).expect("can remove the completed catalog GAP directory");
}

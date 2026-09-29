//! `auslander classify gentle`: the derived classification of the connected
//! gentle algebras with at most `N` vertices, its study record, and its
//! atlas.
//!
//! Derived equivalence keeps the vertex count, so each `n <= N` is one family
//! from `connected_gentle_algebras(n, field)`. The invariant stage runs once
//! more on its own to time it. Every result is verified before a file is
//! written.

use std::fmt::Write;
use std::str::FromStr;
use std::sync::Arc;
use std::time::Instant;

use auslander::algebra::Algebra;
use auslander::control::ComputationControl;
use auslander::derived_classification::{
    ClassificationLimits, DerivedClassification, classify_derived,
};
use auslander::derived_invariant::{DerivedInvariantKind, DerivedInvariants, InvariantReading};
use auslander::field::PrimeField;
use auslander::gentle::connected_gentle_algebras;

use crate::{Failure, is_help};

const COMMAND: &str = "classify gentle";

const HELP: &str = "\
usage: auslander classify gentle --vertices N [options]

Classifies the connected gentle algebras with at most N vertices over GF(p)
up to derived equivalence. Each vertex count n <= N is one family. Prints
one table row per family. Every result is verified before a file is
written.

options:
  --vertices N           the largest vertex count, at least 1 (required)
  --field P              the prime p, below 2^31 (default 2)
  --walk-vertices W      the most complexes stored per mutation walk
                         (default 8). The mutation, term, and matrix-entry
                         limits are 4, 32, and 2048 times W.
  --through-silting      also store silting complexes that are not tilting
                         as walk vertices. Targets come from tilting
                         vertices only.
  --hochschild-degree D  compute dim HH^0 through dim HH^D (default 2)
  --output FILE          classify every member with at most N vertices
                         again, as one family, and write its verified
                         derived-atlas-v1 artifact to FILE
  --record FILE          write the derived-classification-study-v1 record,
                         with wall times, to FILE
  -h, --help             print this help

Exits with status 1 when a classification fails or does not verify.
";

/// The flags that take a value, in help order.
const VALUE_FLAGS: [&str; 6] = [
    "--vertices",
    "--field",
    "--walk-vertices",
    "--hochschild-degree",
    "--output",
    "--record",
];

struct Options {
    vertices: u32,
    field: PrimeField,
    walk_vertices: u64,
    through_silting: bool,
    hochschild_degree: usize,
    output: Option<String>,
    record: Option<String>,
}

/// One family: the classification and the measured wall times.
struct Run {
    vertices: u32,
    result: DerivedClassification,
    verified: bool,
    nanos: [u128; 4],
}

fn usage(message: impl Into<String>) -> Failure {
    Failure::usage(COMMAND, message)
}

/// Runs `auslander classify` with the arguments after `classify`.
pub(crate) fn run(arguments: &[String]) -> Result<(), Failure> {
    let Some(options) = parse(arguments)? else {
        print!("{HELP}");
        return Ok(());
    };
    let limits = limits(&options);
    let runs = (1..=options.vertices)
        .map(|vertices| run_family(vertices, options.field, &limits))
        .collect::<Result<Vec<Run>, Failure>>()?;
    print_table(&runs);
    if let Some(run) = runs.iter().find(|run| !run.verified) {
        let n = run.vertices;
        return Err(Failure::Failed(format!(
            "the classification of the {n}-vertex family failed verification"
        )));
    }
    if let Some(path) = &options.record {
        write(path, &record_json(&options, &limits, &runs))?;
        println!("record: {path}");
    }
    match &options.output {
        Some(path) => write_atlas(path, &options, &limits),
        None => Ok(()),
    }
}

/// The parsed options, or `None` when the arguments ask for help.
fn parse(arguments: &[String]) -> Result<Option<Options>, Failure> {
    match arguments.split_first() {
        Some((family, rest)) if family == "gentle" => flags(rest)?.map(options).transpose(),
        Some((flag, _)) if is_help(flag) => Ok(None),
        Some((family, _)) => Err(usage(format!("unknown family {family:?}"))),
        None => Err(usage("missing family \"gentle\"")),
    }
}

/// The flag values in the order of [`VALUE_FLAGS`], and the silting switch.
struct Flags<'a> {
    values: [Option<&'a str>; 6],
    through_silting: bool,
}

/// The flags of `arguments`, or `None` when they ask for help.
fn flags(arguments: &[String]) -> Result<Option<Flags<'_>>, Failure> {
    let mut flags = Flags {
        values: [None; 6],
        through_silting: false,
    };
    let mut rest = arguments.iter();
    while let Some(argument) = rest.next() {
        if is_help(argument) {
            return Ok(None);
        } else if argument == "--through-silting" {
            flags.through_silting = true;
            continue;
        }
        let Some(index) = VALUE_FLAGS.iter().position(|flag| flag == argument) else {
            return Err(usage(format!("unknown option {argument:?}")));
        };
        let value = rest.next();
        let value = value.ok_or_else(|| usage(format!("{argument} takes a value")))?;
        if flags.values[index].replace(value).is_some() {
            return Err(usage(format!("{argument} is given twice")));
        }
    }
    Ok(Some(flags))
}

fn options(flags: Flags<'_>) -> Result<Options, Failure> {
    let [vertices, field, walk, degree, output, record] = flags.values;
    let vertices: u32 = number("--vertices", vertices, None)?;
    if vertices == 0 {
        return Err(usage("--vertices must be at least 1"));
    }
    let p = number("--field", field, Some(2))?;
    let field = PrimeField::new(p).map_err(|error| usage(format!("--field: {error}")))?;
    Ok(Options {
        vertices,
        field,
        walk_vertices: number("--walk-vertices", walk, Some(8))?,
        through_silting: flags.through_silting,
        hochschild_degree: number("--hochschild-degree", degree, Some(2))?,
        output: output.map(str::to_string),
        record: record.map(str::to_string),
    })
}

/// The value of `flag`, or `default` when it is absent.
fn number<T: FromStr>(flag: &str, text: Option<&str>, default: Option<T>) -> Result<T, Failure> {
    match (text, default) {
        (Some(text), _) => text.parse().map_err(|_| {
            usage(format!(
                "{flag} takes a nonnegative integer, found {text:?}"
            ))
        }),
        (None, Some(value)) => Ok(value),
        (None, None) => Err(usage(format!("{flag} is required"))),
    }
}

fn limits(options: &Options) -> ClassificationLimits {
    let mut limits = ClassificationLimits::with_walk_vertices(options.walk_vertices);
    limits.invariants.hochschild_degree = options.hochschild_degree;
    limits.discovery.through_silting = options.through_silting;
    limits
}

fn gentle(vertices: u32, field: PrimeField) -> Result<Vec<Arc<Algebra>>, Failure> {
    connected_gentle_algebras(vertices, field).map_err(Failure::failed)
}

fn run_family(
    vertices: u32,
    field: PrimeField,
    limits: &ClassificationLimits,
) -> Result<Run, Failure> {
    let control = ComputationControl::new();
    let clock = Instant::now();
    let family = gentle(vertices, field)?;
    let enumerate = clock.elapsed().as_nanos();
    let clock = Instant::now();
    for algebra in &family {
        DerivedInvariants::compute(algebra, limits.invariants, &control)
            .map_err(Failure::failed)?;
    }
    let invariants = clock.elapsed().as_nanos();
    let clock = Instant::now();
    let result = classify_derived(&family, limits, &control).map_err(Failure::failed)?;
    let classify = clock.elapsed().as_nanos();
    let clock = Instant::now();
    let verified = result.verify();
    let verify = clock.elapsed().as_nanos();
    Ok(Run {
        vertices,
        result,
        verified,
        nanos: [enumerate, invariants, classify, verify],
    })
}

/// The number of readings that finished, stopped, or are not applicable.
fn reading_counts(result: &DerivedClassification) -> [usize; 3] {
    let mut counts = [0; 3];
    for record in result.invariants() {
        for kind in DerivedInvariantKind::ALL {
            counts[match record.reading(kind) {
                InvariantReading::Finished(_) => 0,
                InvariantReading::Stopped(_) => 1,
                InvariantReading::NotApplicable(_) => 2,
            }] += 1;
        }
    }
    counts
}

/// Walk totals: walks, vertices, blocked, examined, target cuts, unmatched,
/// and merges.
fn walk_totals(result: &DerivedClassification) -> [usize; 7] {
    let mut totals = [result.walks().len(), 0, 0, 0, 0, 0, 0];
    for walk in result.walks() {
        let values = [
            walk.vertices(),
            walk.blocked(),
            walk.examined(),
            walk.target_cuts(),
            walk.unmatched(),
            walk.merges(),
        ];
        for (total, value) in totals[1..].iter_mut().zip(values) {
            *total += value;
        }
    }
    totals
}

fn family_json(run: &Run) -> String {
    let result = &run.result;
    let merged = result.family().len() - result.classes().len();
    let duplicates = result
        .classes()
        .iter()
        .flat_map(|class| class.merges())
        .filter(|merge| merge.is_duplicate())
        .count();
    let [finished, stopped, not_applicable] = reading_counts(result);
    let [walks, vertices, blocked, examined, cuts, unmatched, merges] = walk_totals(result);
    let mut kinds = String::new();
    for kind in DerivedInvariantKind::ALL {
        let count = result
            .separations()
            .iter()
            .filter(|separation| separation.witness().kind() == kind)
            .count();
        let separator = if kinds.is_empty() { "" } else { "," };
        write!(kinds, "{separator}\"{kind:?}\":{count}").expect("writing to a String cannot fail");
    }
    let open: Vec<String> = result
        .unresolved()
        .iter()
        .map(|pair| {
            let (left, right) = pair.classes();
            let members = |class: usize| format!("{:?}", result.classes()[class].members());
            format!("[{},{}]", members(left), members(right))
        })
        .collect();
    let open = open.join(",").replace(' ', "");
    let [enumerate, invariants, classify, verify] = run.nanos;
    format!(
        "{{\"vertices\":{},\"members\":{},\"classes\":{},\"merged\":{merged},\
         \"duplicates\":{duplicates},\"separated\":{},\"unresolved\":{},\"open_pairs\":[{open}],\"status\":\"{}\",\
         \"verified\":{},\"stage1\":{{\"finished\":{finished},\"stopped\":{stopped},\
         \"not_applicable\":{not_applicable}}},\"stage2\":{{\"groups\":{},\"separations_by_kind\":{{{kinds}}}}},\
         \"stage3\":{{\"walks\":{walks},\"vertices\":{vertices},\"blocked\":{blocked},\
         \"examined\":{examined},\"target_cuts\":{cuts},\"unmatched\":{unmatched},\"merges\":{merges}}},\
         \"nanoseconds\":{{\"enumerate\":{enumerate},\"invariants\":{invariants},\
         \"classify\":{classify},\"verify\":{verify}}}}}",
        run.vertices,
        result.family().len(),
        result.classes().len(),
        result.separations().len(),
        result.unresolved().len(),
        result.status().as_str(),
        run.verified,
        result.groups().len(),
    )
}

fn record_json(options: &Options, limits: &ClassificationLimits, runs: &[Run]) -> String {
    let discovery = &limits.discovery;
    let families: Vec<String> = runs.iter().map(family_json).collect();
    format!(
        "{{\"schema\":\"derived-classification-study-v1\",\"field\":{},\"max_vertices\":{},\
         \"limits\":{{\"hochschild_degree\":{},\"walk_vertices\":{},\"walk_mutations\":{},\
         \"walk_terms\":{},\"walk_matrix_entries\":{},\
         \"through_silting\":{}}},\"families\":[{}]}}\n",
        options.field.modulus(),
        options.vertices,
        limits.invariants.hochschild_degree,
        discovery.max_vertices,
        discovery.max_directed_mutations,
        discovery.max_total_terms,
        discovery.max_matrix_entries,
        discovery.through_silting,
        families.join(",")
    )
}

fn print_table(runs: &[Run]) {
    println!(
        "n  members  classes  merged  separated  unresolved  walks  vertices  classify_s  verify_s"
    );
    for run in runs {
        let result = &run.result;
        let [walks, vertices, ..] = walk_totals(result);
        println!(
            "{:<2} {:>8} {:>8} {:>7} {:>10} {:>11} {:>6} {:>9} {:>11.3} {:>9.3}",
            run.vertices,
            result.family().len(),
            result.classes().len(),
            result.family().len() - result.classes().len(),
            result.separations().len(),
            result.unresolved().len(),
            walks,
            vertices,
            run.nanos[2] as f64 / 1e9,
            run.nanos[3] as f64 / 1e9,
        );
    }
}

/// Classifies every member with at most `options.vertices` vertices as one
/// family, verifies the atlas, and writes it to `path`.
fn write_atlas(
    path: &str,
    options: &Options,
    limits: &ClassificationLimits,
) -> Result<(), Failure> {
    let control = ComputationControl::new();
    let mut family = Vec::new();
    for vertices in 1..=options.vertices {
        family.extend(gentle(vertices, options.field)?);
    }
    let result = classify_derived(&family, limits, &control).map_err(Failure::failed)?;
    let text = result
        .to_artifact()
        .map_err(Failure::failed)?
        .to_canonical_json();
    let clock = Instant::now();
    crate::files::verified(&text)?;
    let seconds = clock.elapsed().as_secs_f64();
    write(path, &text)?;
    println!(
        "atlas: {path}, {} bytes, {} members, {} classes, {} unresolved, verified in {seconds:.3} s",
        text.len(),
        family.len(),
        result.classes().len(),
        result.unresolved().len(),
    );
    Ok(())
}

fn write(path: &str, text: &str) -> Result<(), Failure> {
    std::fs::write(path, text)
        .map_err(|error| Failure::Failed(format!("cannot write {path:?}: {error}")))
}

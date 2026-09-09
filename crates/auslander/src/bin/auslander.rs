//! Local inspection and verification for portable Auslander values.

use std::process::ExitCode;

use auslander::batch_stream::{
    HOMOLOGICAL_STREAM_ENGINE_ID, HOMOLOGICAL_STREAM_PORTABLE_KIND,
    HOMOLOGICAL_STREAM_PORTABLE_SCHEMA, HomologicalStreamParseLimits, HomologicalStreamPortable,
    HomologicalStreamPortableStatus, HomologicalStreamVerifyLimits,
};
use auslander::census::{
    CENSUS_PORTABLE_KIND, CENSUS_PORTABLE_SCHEMA, CensusParseLimits, CensusPortable,
    CensusPortableStatus, CensusVerifyLimits, VerifiedCensus,
};
use auslander::control::ComputationControl;
use auslander::derived_artifact::{
    ArtifactParseLimits, ArtifactVerificationOutcome, ArtifactVerifyLimits,
    DERIVED_ARTIFACT_SCHEMA, DerivedArtifact, VerifiedDerivedArtifact, verify_derived_artifact,
};

fn usage() {
    eprintln!("usage: auslander <inspect|verify|canonicalize|fingerprint> FILE");
}

fn read(path: &str) -> Result<String, String> {
    std::fs::read_to_string(path).map_err(|error| format!("cannot read {path:?}: {error}"))
}

enum PortableValue {
    Derived(Box<DerivedArtifact>),
    Census(Box<CensusPortable>),
    Homological(Box<HomologicalStreamPortable>),
}

impl PortableValue {
    fn parse(text: &str) -> Result<Self, String> {
        if text.starts_with("{\"schema\":\"auslander-derived-v1\"") {
            DerivedArtifact::from_json(text, ArtifactParseLimits::default())
                .map(Box::new)
                .map(Self::Derived)
                .map_err(|error| error.to_string())
        } else if text.starts_with(&format!(
            "{{\"schema\":\"{HOMOLOGICAL_STREAM_PORTABLE_SCHEMA}\",\"kind\":\"{HOMOLOGICAL_STREAM_PORTABLE_KIND}\""
        )) {
            HomologicalStreamPortable::from_json(text, HomologicalStreamParseLimits::default())
                .map(Box::new)
                .map(Self::Homological)
                .map_err(|error| error.to_string())
        } else if text.starts_with("{\"schema\":\"auslander-computation-v1\"") {
            CensusPortable::from_json(text, CensusParseLimits::default())
                .map(Box::new)
                .map(Self::Census)
                .map_err(|error| error.to_string())
        } else {
            Err("unsupported portable schema".to_string())
        }
    }

    fn inspect(&self) {
        match self {
            Self::Derived(artifact) => inspect_derived(artifact),
            Self::Census(census) => inspect_census(census),
            Self::Homological(stream) => inspect_homological(stream),
        }
    }

    fn verify(self) -> Result<VerifiedValue, String> {
        match self {
            Self::Derived(artifact) => verify_derived(*artifact),
            Self::Census(census) => census
                .verify(CensusVerifyLimits::default())
                .map(Box::new)
                .map(VerifiedValue::Census)
                .map_err(|error| error.to_string()),
            Self::Homological(stream) => stream
                .verify(HomologicalStreamVerifyLimits::default())
                .map(Box::new)
                .map(VerifiedValue::Homological)
                .map_err(|error| error.to_string()),
        }
    }
}

fn inspect_derived(artifact: &DerivedArtifact) {
    println!("schema {DERIVED_ARTIFACT_SCHEMA}");
    println!("source_field {}", artifact.source_certificate().field);
    println!("mutations {}", artifact.mutations().len());
    println!("target_field {}", artifact.target_certificate().field);
    println!("fingerprint {}", artifact.fingerprint());
}

fn inspect_census(census: &CensusPortable) {
    println!("schema {CENSUS_PORTABLE_SCHEMA}");
    println!("kind {CENSUS_PORTABLE_KIND}");
    println!("field {}", census.certificate().field);
    let dimensions = census
        .dimensions()
        .iter()
        .map(usize::to_string)
        .collect::<Vec<_>>()
        .join(",");
    println!("dimensions {dimensions}");
    println!("cursor {}", census.cursor());
    println!("raw_space_size {}", census.raw_space_size());
    println!("status {}", census_status(census.status()));
    println!("representatives {}", census.representatives().len());
    println!("assignments {}", census.assignments().len());
    println!("fingerprint {}", census.fingerprint());
}

fn inspect_homological(stream: &HomologicalStreamPortable) {
    println!("schema {HOMOLOGICAL_STREAM_PORTABLE_SCHEMA}");
    println!("kind {HOMOLOGICAL_STREAM_PORTABLE_KIND}");
    println!("engine {HOMOLOGICAL_STREAM_ENGINE_ID}");
    println!("census_fingerprint {}", stream.census_fingerprint());
    println!("max_degree {}", stream.max_degree());
    println!("next_source {}", stream.next_source());
    println!("rows {}", stream.rows().len());
    println!("status {}", homological_status(stream.status()));
    println!("fingerprint {}", stream.fingerprint());
}

fn homological_status(status: &HomologicalStreamPortableStatus) -> &'static str {
    match status {
        HomologicalStreamPortableStatus::Active => "active",
        HomologicalStreamPortableStatus::Complete => "complete",
        HomologicalStreamPortableStatus::Cut(_) => "cut",
    }
}

fn census_status(status: &CensusPortableStatus) -> &'static str {
    match status {
        CensusPortableStatus::Complete => "complete",
        CensusPortableStatus::Cut(_) => "cut",
    }
}

fn verify_derived(artifact: DerivedArtifact) -> Result<VerifiedValue, String> {
    let text = artifact.to_canonical_json();
    match verify_derived_artifact(
        &text,
        ArtifactVerifyLimits::default(),
        &ComputationControl::new(),
    )
    .map_err(|error| error.to_string())?
    {
        ArtifactVerificationOutcome::Verified(value) => Ok(VerifiedValue::Derived(value)),
        ArtifactVerificationOutcome::Cut(cut) => {
            Err(format!("artifact verification stopped: {cut:?}"))
        }
    }
}

enum VerifiedValue {
    Derived(Box<VerifiedDerivedArtifact>),
    Census(Box<VerifiedCensus>),
    Homological(Box<auslander::batch_stream::VerifiedHomologicalStream>),
}

impl VerifiedValue {
    fn fingerprint(&self) -> &str {
        match self {
            Self::Derived(value) => value.artifact().fingerprint(),
            Self::Census(value) => value.portable().fingerprint(),
            Self::Homological(value) => value.portable().fingerprint(),
        }
    }

    fn canonical_json(&self) -> String {
        match self {
            Self::Derived(value) => value.artifact().to_canonical_json(),
            Self::Census(value) => value.portable().to_canonical_json(),
            Self::Homological(value) => value.portable().to_canonical_json(),
        }
    }
}

enum Command {
    Inspect,
    Verify,
    Canonicalize,
    Fingerprint,
}

impl Command {
    fn parse(command: &str) -> Result<Command, String> {
        if command == "inspect" {
            Ok(Command::Inspect)
        } else if command == "verify" {
            Ok(Command::Verify)
        } else if command == "canonicalize" {
            Ok(Command::Canonicalize)
        } else if command == "fingerprint" {
            Ok(Command::Fingerprint)
        } else {
            usage();
            Err(format!("unknown command {command:?}"))
        }
    }

    fn run(self, text: &str) -> Result<(), String> {
        let value = PortableValue::parse(text)?;
        match self {
            Command::Inspect => {
                value.inspect();
                Ok(())
            }
            output => print_value(output, value),
        }
    }
}

fn print_value(command: Command, value: PortableValue) -> Result<(), String> {
    let verified = value.verify()?;
    match command {
        Command::Verify => println!("verified {}", verified.fingerprint()),
        Command::Canonicalize => println!("{}", verified.canonical_json()),
        Command::Fingerprint => println!("{}", verified.fingerprint()),
        Command::Inspect => unreachable!("inspect does not verify a value first"),
    }
    Ok(())
}

fn arguments() -> Result<(Command, String), String> {
    let mut arguments = std::env::args().skip(1);
    let Some(command) = arguments.next() else {
        usage();
        return Err("missing command".to_string());
    };
    let Some(path) = arguments.next() else {
        usage();
        return Err("missing artifact path".to_string());
    };
    if arguments.next().is_some() {
        usage();
        return Err("too many arguments".to_string());
    }
    Ok((Command::parse(&command)?, path))
}

fn run() -> Result<(), String> {
    let (command, path) = arguments()?;
    let text = read(&path)?;
    command.run(&text)
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("auslander: {error}");
            ExitCode::FAILURE
        }
    }
}

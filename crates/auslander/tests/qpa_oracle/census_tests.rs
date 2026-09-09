#[test]
fn census_qpa_oracle_matches_library() {
    let document = expected_document();
    let mismatches = compare_document(&document);
    assert!(
        mismatches.is_empty(),
        "census QPA mismatch:\n{}",
        mismatches.join("\n")
    );
}

#[test]
fn census_qpa_oracle_records_real_provenance() {
    let document = expected_document();
    assert!(document
        .provenance
        .iter()
        .all(|(_, value)| !value.is_empty()));
    assert!(document
        .provenance
        .iter()
        .any(|(key, value)| key == "qpa_version" && value == "1.36"));
}

#[test]
fn census_qpa_oracle_corruption_is_rejected_or_mismatches() {
    let text = expected_text();
    let wrong_schema = replace_once(&text, SCHEMA, "auslander-qpa-census-oracle-v0");
    assert!(parse_document(&wrong_schema).is_err());
    let wrong_counts = replace_once(&text, "\"accepted_modules\":10", "\"accepted_modules\":11");
    assert!(parse_document(&wrong_counts).is_err());

    let wrong_ext = replace_once(&text, "\"self_ext\":[5,0,1,0]", "\"self_ext\":[5,0,1,1]");
    let parsed = parse_document(&wrong_ext).expect("the changed Ext row remains well-formed");
    assert!(compare_document(&parsed)
        .iter()
        .any(|mismatch| mismatch == "d2112: self_ext"));
}

#[cfg(unix)]
#[test]
fn census_live_gap_run_agrees_with_qpa_oracle_and_library() {
    if env::var("QPA_ORACLE").as_deref() != Ok("1") {
        println!("live census QPA run skipped; set QPA_ORACLE=1 to invoke GAP+QPA");
        return;
    }
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("clock after the epoch")
        .as_nanos();
    let workdir = env::temp_dir().join(format!("qpa-census-oracle-{}-{nanos}", std::process::id()));
    fs::create_dir(&workdir).expect("can create a fresh census GAP working directory");
    let script = super::oracle_dir().join("generate_census_fixtures.g");
    let output = super::gap_command(&workdir)
        .arg(&script)
        .output()
        .unwrap_or_else(|error| panic!("cannot launch GAP (set GAP_BIN to the binary): {error}"));
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "census GAP process failed:\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_eq!(
        stdout.lines().last(),
        Some(SENTINEL),
        "census QPA generator did not finish:\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let generated = workdir.join(GENERATED_OUTPUT);
    let generated_text = fs::read_to_string(&generated)
        .unwrap_or_else(|error| panic!("cannot read {}: {error}", generated.display()));
    let fresh = parse_document(&generated_text).expect("fresh census QPA output parses");
    let committed = expected_document();
    assert_eq!(
        without_provenance(&fresh),
        without_provenance(&committed),
        "fresh census QPA values differ from committed truth"
    );
    let mismatches = compare_document(&fresh);
    assert!(
        mismatches.is_empty(),
        "fresh census QPA mismatch:\n{}",
        mismatches.join("\n")
    );
    fs::remove_dir_all(&workdir).expect("can remove the completed census GAP directory");
}

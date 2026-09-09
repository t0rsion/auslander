    fn corrupted(from: &str, to: &str) -> String {
        let text = committed_text();
        let replaced = text.replacen(from, to, 1);
        assert_ne!(text, replaced, "corruption target {from:?} not found");
        replaced
    }

    /// The corrupted document must fail the strict reader.
    fn read_error(from: &str, to: &str) -> String {
        parse_document(&corrupted(from, to), SCHEMA)
            .expect_err("the corrupted document must be rejected")
    }

    /// Two corruptions in one document, for a value the schema stores twice.
    fn corrupted_pair(first: (&str, &str), second: (&str, &str)) -> String {
        let text = corrupted(first.0, first.1);
        let replaced = text.replacen(second.0, second.1, 1);
        assert_ne!(text, replaced, "corruption target {:?} not found", second.0);
        replaced
    }

    /// The corrupted document still reads; the comparator must flag it.
    fn mismatches_of(text: String) -> Vec<String> {
        let doc = parse_document(&text, SCHEMA)
            .unwrap_or_else(|e| panic!("the corrupted document must still read: {e}"));
        compare(&doc)
    }

    fn corrupted_mismatches(from: &str, to: &str) -> Vec<String> {
        mismatches_of(corrupted(from, to))
    }

    /// The slot layer is not part of the shape comparison, so a corruption of
    /// an approximation is checked at that depth.
    fn corrupted_slot_mismatches(from: &str, to: &str) -> Vec<String> {
        let doc = parse_document(&corrupted(from, to), SCHEMA)
            .unwrap_or_else(|e| panic!("the corrupted document must still read: {e}"));
        compare_at(&doc, SttDepth::Slots)
    }

    #[test]
    fn parser_rejects_a_duplicated_key() {
        let text = corrupted("\"dim\": 3,", "\"dim\": 3,\n      \"dim\": 3,");
        let err = json::parse(&text).unwrap_err();
        assert!(err.contains("duplicate key \"dim\""), "{err}");
    }

    #[test]
    fn parser_rejects_a_trailing_comma() {
        let text = corrupted(
            "\"cartan\": [[1, 1], [0, 1]],",
            "\"cartan\": [[1, 1], [0, 1],],",
        );
        let err = json::parse(&text).unwrap_err();
        assert!(err.contains("unexpected"), "{err}");
    }

    /// The corrupted string is derived from the pinned SCHEMA constant, so
    /// this test tracks the real schema string instead of a stale copy.
    #[test]
    fn reader_rejects_the_previous_schema_version() {
        let from = format!("\"schema\": \"{SCHEMA}\"");
        let to = from.replace("-v9", "-v8");
        assert_ne!(from, to, "the pinned schema must carry the v9 marker");
        let err = read_error(&from, &to);
        assert!(err.contains("schema"), "{err}");
    }

    #[test]
    fn reader_rejects_an_unknown_classical_tilting_key() {
        let err = read_error(
            "\"bound\": 1, \"module_dimvec\"",
            "\"bound\": 1, \"surprise\": 0, \"module_dimvec\"",
        );
        assert!(err.contains("unknown key \"surprise\""), "{err}");
        assert!(err.contains("classical_tilting entry 0"), "{err}");
    }

    #[test]
    fn reader_rejects_an_unknown_target_key() {
        let err = read_error(
            "\"algebra\": \"endomorphism-opposite\", \"dimension\"",
            "\"algebra\": \"endomorphism-opposite\", \"surprise\": 0, \"dimension\"",
        );
        assert!(err.contains("unknown key \"surprise\""), "{err}");
        assert!(err.contains("target"), "{err}");
    }

    #[test]
    fn reader_rejects_an_unknown_target_skip_reason() {
        let computed = "{\"status\": \"computed\", \"algebra\": \"endomorphism-opposite\", \
            \"dimension\": 5, \"cartan\": [[1, 0, 0], [1, 1, 0], [0, 1, 1]], \
            \"radical_layers\": [3, 2], \"simple_ext1\": [[0, 0, 0], [1, 0, 0], [0, 1, 0]]}";
        let err = read_error(
            computed,
            "{\"status\": \"skipped\", \"reason\": \"unknown\"}",
        );
        assert!(err.contains("unknown skipped reason"), "{err}");
    }

    #[test]
    fn reader_accepts_a_typed_target_skip() {
        let computed = "{\"status\": \"computed\", \"algebra\": \"endomorphism-opposite\", \
            \"dimension\": 5, \"cartan\": [[1, 0, 0], [1, 1, 0], [0, 1, 1]], \
            \"radical_layers\": [3, 2], \"simple_ext1\": [[0, 0, 0], [1, 0, 0], [0, 1, 0]]}";
        let text = corrupted(
            computed,
            "{\"status\": \"skipped\", \"reason\": \"operation-unavailable\"}",
        );
        let document = parse_document(&text, SCHEMA).expect("the typed skip must parse");
        assert!(document.fixtures.iter().any(|fixture| {
            fixture.classical_tilting.iter().any(|record| {
                matches!(
                    &record.target,
                    Some(TargetOracle::Skipped {
                        reason: TargetSkipReason::OperationUnavailable
                    })
                )
            })
        }));
    }

    #[test]
    fn reader_rejects_target_layers_with_the_wrong_total() {
        let err = read_error(
            "\"radical_layers\": [3, 2], \"simple_ext1\"",
            "\"radical_layers\": [3, 1], \"simple_ext1\"",
        );
        assert!(err.contains("radical layers"), "{err}");
        assert!(err.contains("dimension 5"), "{err}");
    }

    #[test]
    fn reader_rejects_a_nonexact_qpa_tilting_coresolution() {
        let err = read_error(
            "\"coresolutions_exact\": [true, true, true]",
            "\"coresolutions_exact\": [true, false, true]",
        );
        assert!(
            err.contains("requires every coresolution to be exact"),
            "{err}"
        );
    }

    #[test]
    fn reader_rejects_qpa_tilting_without_coresolution_exactness() {
        let err = read_error(", \"coresolutions_exact\": [true, true, true]", "");
        assert!(err.contains("missing coresolutions_exact"), "{err}");
    }

    #[test]
    fn reader_rejects_a_qpa_false_record_with_positive_only_fields() {
        let err = read_error(
            "\"qpa_tilting\": true, \"projective_dimension\": 1",
            "\"qpa_tilting\": false, \"projective_dimension\": 1",
        );
        assert!(
            err.contains("unknown key \"projective_dimension\""),
            "{err}"
        );
    }

    #[test]
    fn reader_rejects_a_changed_classical_tilting_construction() {
        let err = read_error(
            "\"construction\": \"S0+P0+P2\"",
            "\"construction\": \"other\"",
        );
        assert!(err.contains("construction is \"other\""), "{err}");
    }

    #[test]
    fn reader_rejects_a_missing_root_field() {
        let err = read_error("  \"max_ext_degree\": 4,\n", "");
        assert!(err.contains("missing max_ext_degree"), "{err}");
    }

    #[test]
    fn reader_rejects_a_changed_max_ext_degree() {
        let err = read_error("\"max_ext_degree\": 4", "\"max_ext_degree\": 3");
        assert!(err.contains("max_ext_degree is 3"), "{err}");
    }

    #[test]
    fn reader_rejects_a_changed_projdim_bound() {
        let err = read_error("\"projdim_bound\": 6", "\"projdim_bound\": 5");
        assert!(err.contains("projdim_bound is 5"), "{err}");
    }

    #[test]
    fn reader_rejects_an_unknown_top_level_key() {
        let err = read_error(
            "\"max_ext_degree\": 4,",
            "\"max_ext_degree\": 4,\n  \"surprise\": 1,",
        );
        assert!(err.contains("unknown key \"surprise\""), "{err}");
    }

    #[test]
    fn reader_rejects_an_unknown_fixture_key() {
        let err = read_error("\"dim\": 3,", "\"dim\": 3,\n      \"surprise\": 1,");
        assert!(err.contains("unknown key \"surprise\""), "{err}");
        assert!(err.contains("linear-an-2/f5"), "{err}");
    }

    #[test]
    fn reader_rejects_a_missing_fixture_field() {
        let err = read_error("      \"dim\": 3,\n", "");
        assert!(err.contains("missing dim"), "{err}");
    }

    #[test]
    fn reader_rejects_an_unknown_convention() {
        let err = read_error("\"convention\": \"right\"", "\"convention\": \"sideways\"");
        assert!(err.contains("convention"), "{err}");
    }

    #[test]
    fn reader_rejects_a_wrong_order_id() {
        let err = read_error("\"order\": \"deglex-arrowid-v1\",", "\"order\": \"lex\",");
        assert!(err.contains("order"), "{err}");
    }

    #[test]
    fn reader_rejects_provenance_with_an_unknown_key() {
        let err = read_error(
            "    \"qpa_version\": \"1.36\",\n",
            "    \"qpa_version\": \"1.36\",\n    \"surprise\": \"x\",\n",
        );
        assert!(err.contains("provenance"), "{err}");
        assert!(err.contains("surprise"), "{err}");
    }

    #[test]
    fn reader_rejects_an_empty_provenance_value() {
        let err = read_error("\"qpa_version\": \"1.36\"", "\"qpa_version\": \"\"");
        assert!(err.contains("qpa_version is empty"), "{err}");
    }

    #[test]
    fn reader_rejects_a_non_prime_field() {
        let err = read_error("\"field\": 2,", "\"field\": 4,");
        assert!(err.contains("not prime"), "{err}");
    }

    #[test]
    fn reader_rejects_a_case_that_names_another_field() {
        let err = read_error("\"field\": 3,", "\"field\": 7,");
        assert!(err.contains("does not name field 7"), "{err}");
    }

    #[test]
    fn reader_rejects_wrong_num_vertices() {
        let err = read_error("\"num_vertices\": 2,", "\"num_vertices\": 99,");
        assert!(
            err.contains("designated_modules has 6 entries, expected 297"),
            "{err}"
        );
    }

    #[test]
    fn reader_rejects_an_arrow_endpoint_out_of_range() {
        let err = read_error(
            "{\"name\": \"a1\", \"source\": 0, \"target\": 1}",
            "{\"name\": \"a1\", \"source\": 0, \"target\": 9}",
        );
        assert!(err.contains("target 9 is not a vertex below 2"), "{err}");
    }

    #[test]
    fn reader_rejects_a_duplicate_arrow_name() {
        let err = read_error(
            "{\"name\": \"a2\", \"source\": 0, \"target\": 1}",
            "{\"name\": \"a1\", \"source\": 0, \"target\": 1}",
        );
        assert!(err.contains("duplicate arrow name \"a1\""), "{err}");
    }

    #[test]
    fn reader_rejects_a_relation_path_index_out_of_range() {
        let err = read_error(
            "{\"coeff\": 1, \"path\": [0, 0]}",
            "{\"coeff\": 1, \"path\": [0, 9]}",
        );
        assert!(err.contains("arrow index 9 is not below 1"), "{err}");
    }

    #[test]
    fn reader_rejects_a_relation_without_terms() {
        let err = read_error(
            "{\"terms\": [{\"coeff\": 1, \"path\": [0, 0]}]}",
            "{\"terms\": []}",
        );
        assert!(err.contains("terms is empty"), "{err}");
    }

    #[test]
    fn reader_rejects_a_truncated_tau_dimvec() {
        let err = read_error(
            "\"tau\": [{\"dimvec\": [0, 1]}",
            "\"tau\": [{\"dimvec\": [0]}",
        );
        assert!(
            err.contains("tau[0] dimvec has 1 entries, expected 2"),
            "{err}"
        );
    }

    #[test]
    fn reader_rejects_a_tau_entry_with_two_keys() {
        let err = read_error(
            "{\"projective\": true}",
            "{\"projective\": true, \"dimvec\": [0, 0]}",
        );
        assert!(err.contains("exactly one of projective or dimvec"), "{err}");
    }

    #[test]
    fn reader_rejects_projective_false() {
        let err = read_error("{\"projective\": true}", "{\"projective\": false}");
        assert!(err.contains("projective must be true"), "{err}");
    }

    #[test]
    fn reader_rejects_an_unknown_outcome_key() {
        let err = read_error("{\"finite\": 1}", "{\"bounded\": 1}");
        assert!(err.contains("unknown key \"bounded\""), "{err}");
    }

    #[test]
    fn reader_rejects_an_outcome_with_two_keys() {
        let err = read_error("{\"finite\": 1}", "{\"finite\": 1, \"at_least\": 7}");
        assert!(err.contains("exactly one of finite or at_least"), "{err}");
    }

    #[test]
    fn reader_rejects_at_least_off_the_bound() {
        let err = read_error("{\"at_least\": 7}", "{\"at_least\": 8}");
        assert!(err.contains("at_least is 8, expected 7"), "{err}");
    }

    #[test]
    fn reader_rejects_finite_beyond_the_bound() {
        let err = read_error("{\"finite\": 2}", "{\"finite\": 9}");
        assert!(err.contains("finite value 9 exceeds bound 6"), "{err}");
    }

    #[test]
    fn reader_rejects_a_wrong_decomposition_module() {
        let err = read_error(
            "\"module\": \"radicals-of-projectives\"",
            "\"module\": \"socles-of-projectives\"",
        );
        assert!(err.contains("module"), "{err}");
    }

    #[test]
    fn reader_rejects_unsorted_decomposition_summands() {
        let err = read_error(
            "\"summands\": [{\"dimvec\": [0, 0, 1], \"multiplicity\": 1}, {\"dimvec\": [0, 1, 0], \"multiplicity\": 1}]",
            "\"summands\": [{\"dimvec\": [0, 1, 0], \"multiplicity\": 1}, {\"dimvec\": [0, 0, 1], \"multiplicity\": 1}]",
        );
        assert!(err.contains("not sorted ascending"), "{err}");
    }

    #[test]
    fn reader_rejects_unmerged_decomposition_summands() {
        let err = read_error(
            "[{\"dimvec\": [0, 0, 0, 1], \"multiplicity\": 2}",
            "[{\"dimvec\": [0, 0, 0, 1], \"multiplicity\": 1}, {\"dimvec\": [0, 0, 0, 1], \"multiplicity\": 1}",
        );
        assert!(err.contains("repeat dimvec"), "{err}");
    }

    #[test]
    fn reader_rejects_a_zero_multiplicity() {
        let err = read_error("\"multiplicity\": 1}", "\"multiplicity\": 0}");
        assert!(err.contains("multiplicity is 0"), "{err}");
    }

    #[test]
    fn reader_rejects_an_unknown_summand_key() {
        let err = read_error(
            "{\"dimvec\": [0, 1], \"multiplicity\": 1}",
            "{\"dimvec\": [0, 1], \"multiplicity\": 1, \"surprise\": 1}",
        );
        assert!(err.contains("unknown key \"surprise\""), "{err}");
    }

    #[test]
    fn reader_rejects_a_truncated_ext_row() {
        let err = read_error("[[1, 0, 0, 0, 0], [0, 1, 0, 0, 0]],", "[[1, 0, 0, 0, 0]],");
        assert!(err.contains("ext row 0 has 1 entries, expected 2"), "{err}");
    }

    #[test]
    fn reader_rejects_a_truncated_ext_table() {
        let err = read_error("[0, 1, 0, 0, 0]]", "[0, 1, 0]]");
        assert!(err.contains("ext[0][1] has 3 entries, expected 5"), "{err}");
    }

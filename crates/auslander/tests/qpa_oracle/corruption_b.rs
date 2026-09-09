    #[test]
    fn reader_rejects_duplicate_fixtures() {
        let err = read_error(
            "\"family\": \"linear-an-3\",",
            "\"family\": \"linear-an-2\",",
        );
        assert!(err.contains("duplicate fixture linear-an-2/f5"), "{err}");
    }

    #[test]
    fn reader_rejects_a_presentation_id_conflict() {
        let err = read_error(
            "\"presentation_id\": \"a3-mod-ab\",",
            "\"presentation_id\": \"a3-mod-ab-x\",",
        );
        assert!(
            err.contains("identical presentations under different presentation_ids"),
            "{err}"
        );
    }

    #[test]
    fn compare_rejects_a_renamed_fixture() {
        let mismatches = corrupted_mismatches(
            "\"family\": \"gentle-tree\",",
            "\"family\": \"bogus-algebra\",",
        );
        assert!(
            mismatches
                .iter()
                .any(|m| m.contains("not in the fixture manifest")),
            "{mismatches:?}"
        );
        assert!(
            mismatches
                .iter()
                .any(|m| m.contains("gentle-tree/f5: missing from oracle file")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_dim() {
        let mismatches = corrupted_mismatches("\"dim\": 3,", "\"dim\": 4,");
        assert!(
            mismatches.iter().any(|m| m.contains("dim is 4, ours is 3")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_cartan_value() {
        // kronecker-2. No reader check pins a Cartan row, so the comparator
        // is what catches this.
        let mismatches = corrupted_mismatches(
            "\"cartan\": [[1, 2], [0, 1]],",
            "\"cartan\": [[1, 5], [0, 1]],",
        );
        assert!(
            mismatches.iter().any(|m| m.contains("cartan")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_injectives_value() {
        let mismatches = corrupted_mismatches(
            "\"injectives\": [[1, 0], [1, 1]],",
            "\"injectives\": [[1, 0], [7, 1]],",
        );
        assert!(
            mismatches.iter().any(|m| m.contains("injectives")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_projdim_value() {
        let mismatches = corrupted_mismatches(
            "\"projdim\": [{\"finite\": 1}, {\"finite\": 0}],",
            "\"projdim\": [{\"finite\": 3}, {\"finite\": 0}],",
        );
        assert!(
            mismatches.iter().any(|m| m.contains("projdim(S_0)")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_injdim_value() {
        let mismatches = corrupted_mismatches(
            "\"injdim\": [{\"finite\": 0}, {\"finite\": 1}],",
            "\"injdim\": [{\"at_least\": 7}, {\"finite\": 1}],",
        );
        assert!(
            mismatches.iter().any(|m| m.contains("injdim(S_0)")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_tau_value() {
        let mismatches = corrupted_mismatches(
            "\"tau\": [{\"dimvec\": [0, 1]}",
            "\"tau\": [{\"dimvec\": [0, 7]}",
        );
        assert!(
            mismatches.iter().any(|m| m.contains("tau(S_0)")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_tau_injectives_value() {
        let mismatches = corrupted_mismatches(
            "\"tau_injectives\": [{\"dimvec\": [0, 1]}",
            "\"tau_injectives\": [{\"dimvec\": [0, 7]}",
        );
        assert!(
            mismatches.iter().any(|m| m.contains("tau_injectives(I_0)")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_decomposition_multiplicity() {
        let mismatches = corrupted_mismatches(
            "{\"dimvec\": [0, 0, 0, 1], \"multiplicity\": 2}",
            "{\"dimvec\": [0, 0, 0, 1], \"multiplicity\": 3}",
        );
        assert!(
            mismatches.iter().any(|m| m.contains("decomposition")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_ext_value() {
        let mismatches = corrupted_mismatches(
            "[[1, 0, 0, 0, 0], [0, 1, 0, 0, 0]],",
            "[[1, 0, 0, 0, 0], [0, 7, 0, 0, 0]],",
        );
        assert!(
            mismatches.iter().any(|m| m.contains("Ext(S_")),
            "{mismatches:?}"
        );
    }

    /// The documented coefficient rule applies: a coefficient that reduces to
    /// zero drops its term. Here that empties the only relation of
    /// dual-numbers, and a loop with no relation is infinite dimensional.
    #[test]
    fn compare_rejects_a_relation_that_vanishes_mod_p() {
        let mismatches = corrupted_mismatches(
            "{\"coeff\": 1, \"path\": [0, 0]}",
            "{\"coeff\": 5, \"path\": [0, 0]}",
        );
        assert!(
            mismatches
                .iter()
                .any(|m| m.contains("infinite dimensional")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn reader_rejects_a_reordered_designated_list() {
        let err = read_error(
            "\"designated_modules\": [\n        {\"kind\": \"simple\", \"index\": 0},",
            "\"designated_modules\": [\n        {\"kind\": \"injective\", \"index\": 0},",
        );
        assert!(err.contains("designated_modules"), "{err}");
    }

    #[test]
    fn reader_rejects_an_ar_entry_naming_another_module() {
        let err = read_error(
            "{\"module\": {\"kind\": \"simple\", \"index\": 1}, \"projective\": true}",
            "{\"module\": {\"kind\": \"simple\", \"index\": 0}, \"projective\": true}",
        );
        assert!(
            err.contains("module does not match designated entry 1"),
            "{err}"
        );
    }

    #[test]
    fn reader_rejects_a_middle_count_that_disagrees_with_the_summands() {
        let err = read_error("\"num_middle_summands\": 1}", "\"num_middle_summands\": 2}");
        assert!(err.contains("multiplicities add to 1"), "{err}");
    }

    #[test]
    fn reader_rejects_a_middle_dimvec_the_summands_do_not_add_to() {
        let err = read_error("\"middle_dimvec\": [1, 1]", "\"middle_dimvec\": [1, 2]");
        assert!(err.contains("middle_dimvec"), "{err}");
    }

    #[test]
    fn reader_rejects_an_irreducible_total_off_the_valuations() {
        let err = read_error(
            "\"present\": true, \"total\": 1, \"sources\": [{\"dimvec\": [1, 1], \"valuation\": 1}]",
            "\"present\": true, \"total\": 2, \"sources\": [{\"dimvec\": [1, 1], \"valuation\": 1}]",
        );
        assert!(err.contains("valuations add to 1"), "{err}");
    }

    #[test]
    fn reader_rejects_present_with_no_irreducible_morphisms() {
        let err = read_error(
            "\"present\": false, \"total\": 0, \"sources\": []",
            "\"present\": true, \"total\": 0, \"sources\": []",
        );
        assert!(err.contains("present is true with total 0"), "{err}");
    }

    #[test]
    fn reader_rejects_a_wrong_ext_algebra_module() {
        let err = read_error(
            "\"module\": \"sum-of-simples\"",
            "\"module\": \"sum-of-radicals\"",
        );
        assert!(err.contains("sum-of-simples"), "{err}");
    }

    #[test]
    fn reader_rejects_a_changed_ext_algebra_max_degree() {
        let err = read_error("\"max_degree\": 4", "\"max_degree\": 3");
        assert!(err.contains("max_degree is 3"), "{err}");
    }

    #[test]
    fn reader_rejects_ext_algebra_degrees_that_do_not_add_up() {
        let err = read_error(
            "\"dims\": [2, 1, 0, 0, 0], \"min_generators\": [2, 1, 0, 0, 0]",
            "\"dims\": [2, 1, 0, 0, 0], \"min_generators\": [2, 0, 0, 0, 0]",
        );
        assert!(err.contains("do not add up"), "{err}");
    }

    #[test]
    fn reader_rejects_a_yoneda_rank_above_the_target_dimension() {
        let err = read_error(
            "\"dim_ext2_ik\": 0, \"yoneda_map_rank\": 0}",
            "\"dim_ext2_ik\": 0, \"yoneda_map_rank\": 1}",
        );
        assert!(
            err.contains("yoneda_map_rank 1 exceeds dim_ext2_ik 0"),
            "{err}"
        );
    }

    #[test]
    fn reader_rejects_tau_period_bounds_that_disagree() {
        let err = read_error(
            "{\"none_up_to\": 6}, {\"none_up_to\": 6}",
            "{\"none_up_to\": 6}, {\"none_up_to\": 5}",
        );
        assert!(err.contains("bounds 6 and 5 disagree"), "{err}");
    }

    #[test]
    fn reader_rejects_an_unknown_tau_period_key() {
        let err = read_error(
            "\"tau_period\": [{\"none_up_to\": 6}",
            "\"tau_period\": [{\"forever\": 6}",
        );
        assert!(err.contains("unknown key \"forever\""), "{err}");
    }

    #[test]
    fn compare_rejects_a_wrong_ar_translate() {
        let mismatches = corrupted_mismatches(
            "\"tau\": [0, 1], \"middle_dimvec\": [1, 1]",
            "\"tau\": [1, 1], \"middle_dimvec\": [1, 1]",
        );
        assert!(
            mismatches
                .iter()
                .any(|m| m.contains("almost-split sequence at S_0")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_irreducible_source() {
        let mismatches = corrupted_mismatches(
            "\"into\": {\"present\": true, \"total\": 1, \"sources\": [{\"dimvec\": [1, 1], \"valuation\": 1}]}",
            "\"into\": {\"present\": true, \"total\": 1, \"sources\": [{\"dimvec\": [1, 0], \"valuation\": 1}]}",
        );
        assert!(
            mismatches
                .iter()
                .any(|m| m.contains("irreducible morphisms into S_0")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_irreducible_target() {
        let mismatches = corrupted_mismatches(
            "\"out_of\": {\"present\": true, \"total\": 1, \"targets\": [{\"dimvec\": [1, 0], \"valuation\": 1}]}",
            "\"out_of\": {\"present\": true, \"total\": 1, \"targets\": [{\"dimvec\": [0, 1], \"valuation\": 1}]}",
        );
        assert!(
            mismatches
                .iter()
                .any(|m| m.contains("irreducible morphisms out of")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_ext_algebra_dimension() {
        let mismatches = corrupted_mismatches(
            "\"dims\": [2, 1, 0, 0, 0], \"min_generators\": [2, 1, 0, 0, 0]",
            "\"dims\": [2, 2, 0, 0, 0], \"min_generators\": [2, 2, 0, 0, 0]",
        );
        assert!(
            mismatches.iter().any(|m| m.contains("ext_algebra dims")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_yoneda_target_dimension() {
        let mismatches = corrupted_mismatches(
            "\"dim_ext2_ik\": 0, \"yoneda_map_rank\": 0}",
            "\"dim_ext2_ik\": 1, \"yoneda_map_rank\": 0}",
        );
        assert!(
            mismatches.iter().any(|m| m.contains("Yoneda product")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_stable_hom_dimension() {
        let mismatches = corrupted_mismatches(
            "\"stable_hom\": [[1, 0, 0, 0, 1, 0]",
            "\"stable_hom\": [[1, 0, 0, 0, 2, 0]",
        );
        assert!(
            mismatches.iter().any(|m| m.contains("stable Hom")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_tau_rigid_flag() {
        let mismatches = mismatches_of(corrupted_pair(
            (
                "\"tau_rigid\": [true, true, true, true, true, true]",
                "\"tau_rigid\": [false, true, true, true, true, true]",
            ),
            (
                "\"tau_rigid_designated\": [true, true, true, true, true, true]",
                "\"tau_rigid_designated\": [false, true, true, true, true, true]",
            ),
        ));
        assert!(
            mismatches.iter().any(|m| m.contains("is tau-rigid false")),
            "{mismatches:?}"
        );
    }

    /// The v8 block repeats the v6 tau-rigidity list, so the reader requires
    /// the two to agree and a document that changes one alone is rejected.
    #[test]
    fn reader_rejects_tau_rigid_lists_that_disagree() {
        let err = read_error(
            "\"tau_rigid\": [true, true, true, true, true, true]",
            "\"tau_rigid\": [false, true, true, true, true, true]",
        );
        assert!(err.contains("tau_rigid_designated disagrees"), "{err}");
    }

    #[test]
    fn compare_rejects_a_wrong_rigid_flag() {
        let mismatches = corrupted_mismatches(
            "\n      \"rigid\": [true, true, true, true, true, true]",
            "\n      \"rigid\": [false, true, true, true, true, true]",
        );
        assert!(
            mismatches.iter().any(|m| m.contains("is rigid false")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_tau_period() {
        let mismatches = corrupted_mismatches(
            "\"tau_period\": [{\"none_up_to\": 6}",
            "\"tau_period\": [{\"period\": 2}",
        );
        assert!(
            mismatches
                .iter()
                .any(|m| m.contains("the tau period of S_0")),
            "{mismatches:?}"
        );
    }

    /// The other side of the rule: coefficients congruent mod the field build
    /// the same ideal, so the comparison stays clean.
    #[test]
    fn congruent_coefficients_build_the_same_ideal() {
        let doc = parse_document(
            &corrupted(
                "{\"coeff\": 1, \"path\": [0, 0]}",
                "{\"coeff\": 6, \"path\": [0, 0]}",
            ),
            SCHEMA,
        )
        .expect("a congruent coefficient still reads");
        assert_eq!(compare(&doc), Vec::<String>::new());
    }

    /// Everything gated on the closure marker is absent when the walk did not
    /// close, so a total there is an unknown key.
    #[test]
    fn reader_rejects_a_total_on_a_walk_that_did_not_close() {
        let err = read_error(
            "\"not_computed\": {\"reason\": \"walk-not-closed\"}",
            "\"total\": 5, \"not_computed\": {\"reason\": \"walk-not-closed\"}",
        );
        assert!(err.contains("unknown key \"total\""), "{err}");
    }

    #[test]
    fn reader_rejects_a_histogram_that_misses_a_pair() {
        let err = read_error("\"histogram\": [1, 2, 2],", "\"histogram\": [1, 2, 1],");
        assert!(err.contains("histogram does not add to total"), "{err}");
    }

    /// `|M| + |P| = n` is what makes a pair basic, and the reader checks it
    /// on every entry that carries the labels.
    #[test]
    fn reader_rejects_a_pair_whose_labels_do_not_add_up() {
        let err = read_error(
            "{\"module_dimvecs\": [[0, 1]], \"projective_support\": [0]},",
            "{\"module_dimvecs\": [[0, 1]], \"projective_support\": []},",
        );
        assert!(err.contains("do not add to 2"), "{err}");
    }

    #[test]
    fn reader_rejects_unsorted_pair_dimvecs() {
        let err = read_error(
            "{\"module_dimvecs\": [[0, 1], [1, 1]], \"projective_support\": []},",
            "{\"module_dimvecs\": [[1, 1], [0, 1]], \"projective_support\": []},",
        );
        assert!(err.contains("not sorted ascending"), "{err}");
    }

    /// `cyclic-nakayama-3-3-3` is the witness that a repeated dimension vector
    /// is two non-isomorphic summands: its three projectives all have
    /// dimension vector `[1, 1, 1]`. Merging the repetition drops a summand,
    /// and the label count catches it.
    #[test]
    fn reader_rejects_a_merged_pair_repetition() {
        let err = read_error(
            "{\"module_dimvecs\": [[0, 0, 1], [1, 1, 1], [1, 1, 1]], \"projective_support\": []},",
            "{\"module_dimvecs\": [[0, 0, 1], [1, 1, 1]], \"projective_support\": []},",
        );
        assert!(err.contains("do not add to 3"), "{err}");
    }

    #[test]
    fn reader_rejects_an_approximation_whose_cokernel_does_not_add_up() {
        let err = read_error(
            "\"target_dimvec\": [1, 1], \"rank\": 1, \"kernel_dimvec\": [0, 0], \
             \"cokernel_dimvec\": [1, 0]",
            "\"target_dimvec\": [1, 1], \"rank\": 1, \"kernel_dimvec\": [0, 0], \
             \"cokernel_dimvec\": [0, 0]",
        );
        assert!(
            err.contains("image and cokernel do not add to the target"),
            "{err}"
        );
    }

    #[test]
    fn reader_rejects_an_edge_count_off_the_degree_histogram() {
        let err = read_error(
            "\"degree_histogram\": [0, 0, 5, 0], \"edges\": 5, \"connected\": true",
            "\"degree_histogram\": [0, 0, 5, 0], \"edges\": 6, \"connected\": true",
        );
        assert!(err.contains("edge ends against 6 edges"), "{err}");
    }

    /// A closed walk certifies the indecomposable list, so its count must be
    /// the size of the exhaustive catalog where one exists.
    #[test]
    fn compare_rejects_a_wrong_indecomposable_count() {
        let mismatches = corrupted_mismatches(
            "\"indecomposables\": {\"closed\": true, \"count\": 3},",
            "\"indecomposables\": {\"closed\": true, \"count\": 4},",
        );
        assert!(
            mismatches.iter().any(|m| m.contains("our catalog has 3")),
            "{mismatches:?}"
        );
    }

    /// The same witness at the comparator: replacing one of the two repeated
    /// `[1, 1, 1]` entries changes which modules the pair holds, and the pair
    /// lists then differ.
    #[test]
    fn compare_rejects_a_changed_pair_repetition() {
        let mismatches = corrupted_mismatches(
            "{\"module_dimvecs\": [[0, 0, 1], [1, 1, 1], [1, 1, 1]], \"projective_support\": []},",
            "{\"module_dimvecs\": [[0, 0, 1], [1, 1, 0], [1, 1, 1]], \"projective_support\": []},",
        );
        assert!(
            mismatches
                .iter()
                .any(|m| m.contains("the pair lists first differ")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_approximation_target() {
        let mismatches = corrupted_slot_mismatches(
            "\"target_dimvec\": [1, 1], \"rank\": 1, \"kernel_dimvec\": [0, 0], \
             \"cokernel_dimvec\": [1, 0]",
            "\"target_dimvec\": [1, 2], \"rank\": 1, \"kernel_dimvec\": [0, 0], \
             \"cokernel_dimvec\": [1, 1]",
        );
        assert!(
            mismatches
                .iter()
                .any(|m| m.contains("the approximation at")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_classical_tilting_dimension() {
        let mismatches = corrupted_mismatches(
            "\"module_dimvec\": [2, 1, 2]",
            "\"module_dimvec\": [3, 1, 2]",
        );
        assert!(
            mismatches
                .iter()
                .any(|m| m.contains("linear-a3-pd1") && m.contains("dimension")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_wrong_classical_tilting_coresolution_terms() {
        let mismatches = corrupted_mismatches(
            "\"coresolutions\": [[[1, 1, 1], [1, 1, 1]]",
            "\"coresolutions\": [[[2, 1, 1], [1, 1, 1]]",
        );
        assert!(
            mismatches
                .iter()
                .any(|m| m.contains("linear-a3-pd1") && m.contains("summed QPA coresolution")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_a_wrong_target_ext_matrix() {
        let mismatches = corrupted_mismatches(
            "\"simple_ext1\": [[0, 0, 0], [1, 0, 0], [0, 1, 0]]",
            "\"simple_ext1\": [[0, 0, 0], [1, 0, 0], [1, 0, 0]]",
        );
        assert!(
            mismatches
                .iter()
                .any(|m| m.contains("linear-a3-pd1") && m.contains("vertex permutation")),
            "{mismatches:?}"
        );
    }

    #[test]
    fn compare_rejects_wrong_target_radical_layers() {
        let mismatches = corrupted_mismatches(
            "\"radical_layers\": [3, 2], \"simple_ext1\"",
            "\"radical_layers\": [2, 3], \"simple_ext1\"",
        );
        assert!(
            mismatches
                .iter()
                .any(|m| m.contains("linear-a3-pd1") && m.contains("radical layers")),
            "{mismatches:?}"
        );
    }

    /// The exchange graph shape is a self-consistency check on the library's
    /// enumerated set, and a corrupted shape that still passes the reader's
    /// internal arithmetic must still fail the comparison.
    #[test]
    fn compare_rejects_a_wrong_exchange_graph_shape() {
        let mismatches = corrupted_mismatches(
            "\"degree_histogram\": [0, 0, 5, 0], \"edges\": 5, \"connected\": true",
            "\"degree_histogram\": [0, 1, 3, 1], \"edges\": 5, \"connected\": true",
        );
        assert!(
            mismatches
                .iter()
                .any(|m| m.contains("exchange graph self-consistency")),
            "{mismatches:?}"
        );
    }

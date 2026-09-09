#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::algebra::{dual_numbers, linear_an};
    use crate::field::PrimeField;

    fn f5() -> PrimeField {
        PrimeField::new(5).unwrap()
    }

    #[test]
    fn coordinate_order_and_cardinality_are_checked() {
        let algebra = linear_an(3, f5());
        let census = Census::new(&algebra, vec![1, 1, 1]).unwrap();
        assert_eq!(census.domain().coordinate_count(), 2);
        assert_eq!(
            census
                .domain()
                .coordinates()
                .iter()
                .map(|coordinate| (
                    coordinate.arrow().index(),
                    coordinate.row(),
                    coordinate.column()
                ))
                .collect::<Vec<_>>(),
            vec![(0, 0, 0), (1, 0, 0)]
        );
        assert_eq!(census.domain().raw_space_size(), 25);
    }

    #[test]
    fn relation_filtering_counts_invalid_dual_number_matrices() {
        let algebra = dual_numbers(f5());
        let census = Census::new(&algebra, vec![1]).unwrap();
        let CensusOutcome::Complete(result) = census.run_with(
            CensusLimits {
                retention: CensusRetention::AllAssignments,
                max_candidates: 32,
                max_representatives: 32,
                max_assignments: 32,
                max_isomorphism_checks: 32,
                max_work_units: 128,
            },
            None,
        ) else {
            panic!("the five-entry domain should finish")
        };
        assert_eq!(result.cursor(), 5);
        assert_eq!(result.candidates(), 5);
        assert_eq!(result.accepted_modules(), 1);
        assert_eq!(result.rejected_candidates(), 4);
        assert!(result.verify());
    }

    #[test]
    fn nonzero_linear_a2_scalars_are_deduplicated_with_witnesses() {
        let algebra = linear_an(2, f5());
        let census = Census::new(&algebra, vec![1, 1]).unwrap();
        let CensusOutcome::Complete(result) = census.run_with(
            CensusLimits {
                retention: CensusRetention::AllAssignments,
                max_candidates: 32,
                max_representatives: 32,
                max_assignments: 32,
                max_isomorphism_checks: 32,
                max_work_units: 128,
            },
            None,
        ) else {
            panic!("the 25-entry domain should finish")
        };
        assert_eq!(result.cursor(), 5);
        assert_eq!(result.representatives().len(), 2);
        assert_eq!(result.assignments().len(), 3);
        assert!(result
            .assignments()
            .iter()
            .all(|assignment| assignment.witness().is_isomorphism()));
        assert!(result.verify());
    }

    #[test]
    fn limits_return_a_replayable_exact_cut() {
        let algebra = linear_an(2, f5());
        let census = Census::new(&algebra, vec![1, 1]).unwrap();
        let outcome = census.run_with(
            CensusLimits {
                retention: CensusRetention::AllAssignments,
                max_candidates: 2,
                max_representatives: 32,
                max_assignments: 32,
                max_isomorphism_checks: 32,
                max_work_units: 128,
            },
            None,
        );
        let CensusOutcome::Cut(cut) = outcome else {
            panic!("candidate limit should cut the domain")
        };
        assert_eq!(cut.cursor(), 2);
        assert_eq!(cut.reason(), &CensusCutReason::CandidateLimit { limit: 2 });
        assert!(cut.verify());

        let resumed = census
            .resume(
                &cut,
                CensusLimits {
                    retention: CensusRetention::AllAssignments,
                    max_candidates: 32,
                    max_representatives: 32,
                    max_assignments: 32,
                    max_isomorphism_checks: 32,
                    max_work_units: 128,
                },
                None,
            )
            .unwrap();
        assert!(matches!(resumed, CensusOutcome::Complete(_)));
        assert!(resumed.verify());
    }

    #[test]
    fn assignment_retention_has_its_own_hard_limit() {
        let algebra = linear_an(2, f5());
        let census = Census::new(&algebra, vec![1, 1]).unwrap();
        let outcome = census.run_with(
            CensusLimits {
                retention: CensusRetention::AllAssignments,
                max_candidates: 32,
                max_representatives: 32,
                max_assignments: 0,
                max_isomorphism_checks: 32,
                max_work_units: 128,
            },
            None,
        );
        let CensusOutcome::Cut(cut) = outcome else {
            panic!("zero assignment budget should cut at the first duplicate")
        };
        assert_eq!(cut.cursor(), 2);
        assert_eq!(cut.reason(), &CensusCutReason::AssignmentLimit { limit: 0 });
        assert!(cut.verify());
    }

    #[test]
    fn work_and_isomorphism_limits_are_typed_cuts() {
        let algebra = linear_an(2, f5());
        let census = Census::new(&algebra, vec![1, 1]).unwrap();
        let work = census.run_with(
            CensusLimits {
                retention: CensusRetention::AllAssignments,
                max_candidates: 32,
                max_representatives: 32,
                max_assignments: 32,
                max_isomorphism_checks: 32,
                max_work_units: 0,
            },
            None,
        );
        let CensusOutcome::Cut(work_cut) = work else {
            panic!("zero work budget should cut")
        };
        assert_eq!(
            work_cut.reason(),
            &CensusCutReason::WorkLimit {
                stage: CensusWorkStage::Candidate,
                limit: 0,
            }
        );
        assert!(work_cut.verify());

        let isomorphism = census.run_with(
            CensusLimits {
                retention: CensusRetention::AllAssignments,
                max_candidates: 32,
                max_representatives: 32,
                max_assignments: 32,
                max_isomorphism_checks: 0,
                max_work_units: 32,
            },
            None,
        );
        let CensusOutcome::Cut(iso_cut) = isomorphism else {
            panic!("zero isomorphism budget should cut")
        };
        assert_eq!(iso_cut.cursor(), 1);
        assert_eq!(
            iso_cut.reason(),
            &CensusCutReason::IsomorphismLimit { limit: 0 }
        );
        assert!(iso_cut.verify());
    }

    #[test]
    fn representative_limit_stops_before_unclassified_candidate() {
        let algebra = linear_an(2, f5());
        let census = Census::new(&algebra, vec![1, 1]).unwrap();
        let outcome = census.run_with(
            CensusLimits {
                retention: CensusRetention::AllAssignments,
                max_candidates: 32,
                max_representatives: 1,
                max_assignments: 32,
                max_isomorphism_checks: 32,
                max_work_units: 128,
            },
            None,
        );
        let CensusOutcome::Cut(cut) = outcome else {
            panic!("representative limit should cut")
        };
        assert_eq!(cut.cursor(), 1);
        assert_eq!(cut.representatives().len(), 1);
        assert_eq!(
            cut.reason(),
            &CensusCutReason::RepresentativeLimit { limit: 1 }
        );
        assert!(cut.verify());
    }

    #[test]
    fn cancellation_preserves_the_unvisited_cursor_and_progress() {
        let algebra = linear_an(2, f5());
        let census = Census::new(&algebra, vec![1, 1]).unwrap();
        let control = ComputationControl::new();
        control.cancel();
        let outcome = census.run_with(CensusLimits::default(), Some(&control));
        let CensusOutcome::Cut(cut) = outcome else {
            panic!("cancelled census should cut")
        };
        assert_eq!(cut.cursor(), 0);
        assert_eq!(cut.reason(), &CensusCutReason::Cancelled);
        assert_eq!(control.progress().completed_work(), 0);
        assert!(cut.verify());
    }

    #[test]
    fn search_space_overflow_is_typed() {
        let algebra = dual_numbers(f5());
        assert_eq!(
            checked_search_space_size(&algebra, &[12]).unwrap_err(),
            CensusError::SearchSpaceOverflow {
                coordinates: 144,
                modulus: 5,
            }
        );
    }

    fn census_limits() -> CensusLimits {
        CensusLimits {
            retention: CensusRetention::AllAssignments,
            max_candidates: 32,
            max_representatives: 32,
            max_assignments: 32,
            max_isomorphism_checks: 32,
            max_work_units: 128,
        }
    }

    #[test]
    fn portable_cut_round_trips_and_resumes_on_a_fresh_algebra() {
        let original_algebra = linear_an(2, f5());
        let census = Census::new(&original_algebra, vec![1, 1]).unwrap();
        let cut_limits = CensusLimits {
            max_candidates: 2,
            ..census_limits()
        };
        let CensusOutcome::Cut(cut) = census.run_with(cut_limits, None) else {
            panic!("the candidate limit should produce a cut")
        };
        let portable = CensusPortable::from_cut(&cut);
        let text = portable.to_canonical_json();
        let parsed = CensusPortable::from_json(&text, CensusParseLimits::default()).unwrap();
        assert_eq!(parsed.to_canonical_json(), text);

        let verified = verify_census_portable(&text, CensusVerifyLimits::default()).unwrap();
        assert!(!Arc::ptr_eq(
            verified.census().domain().algebra(),
            census.domain().algebra()
        ));
        let resumed = verified.resume(census_limits(), None).unwrap();
        let CensusOutcome::Complete(result) = resumed else {
            panic!("the resumed census should complete")
        };
        let expected_outcome = census.run_with(census_limits(), None);
        let CensusOutcome::Complete(expected_result) = expected_outcome else {
            panic!("the full census should complete")
        };
        let expected = CensusPortable::from_result(&expected_result);
        assert_eq!(CensusPortable::from_result(&result), expected);
    }

    #[test]
    fn portable_complete_value_replays_with_exact_witnesses() {
        let algebra = linear_an(2, f5());
        let census = Census::new(&algebra, vec![1, 1]).unwrap();
        let CensusOutcome::Complete(result) = census.run_with(census_limits(), None) else {
            panic!("the five-entry domain should complete")
        };
        let portable = CensusPortable::from_result(&result);
        let text = portable.to_canonical_json();
        assert!(text.contains("\"certificate\":\"{\\\"schema\\\""));
        assert!(text.contains("\"raw_space_size\":\"5\""));
        assert!(text.contains("\"cursor\":\"5\""));
        assert!(text.contains("\"limits\":{\"max_candidates\":32"));
        assert!(text.contains("\"counts\":{\"candidates\":5"));
        let verified = verify_census_portable(&text, CensusVerifyLimits::default()).unwrap();
        assert!(matches!(verified.outcome(), CensusOutcome::Complete(_)));
        assert_eq!(verified.portable(), &portable);
    }

    #[test]
    fn portable_parser_rejects_limits_schema_and_fingerprint_mutations() {
        let algebra = linear_an(2, f5());
        let census = Census::new(&algebra, vec![1, 1]).unwrap();
        let outcome = census.run_with(
            CensusLimits {
                retention: CensusRetention::AllAssignments,
                max_candidates: 2,
                ..census_limits()
            },
            None,
        );
        let portable = CensusPortable::from_outcome(&outcome).unwrap();
        let text = portable.to_canonical_json();
        let strict = CensusParseLimits {
            max_input_bytes: text.len() - 1,
            ..CensusParseLimits::default()
        };
        assert!(matches!(
            CensusPortable::from_json(&text, strict),
            Err(CensusPortableError::ParseLimit { .. })
        ));
        let array_limited = CensusParseLimits {
            max_array_elements: 1,
            ..CensusParseLimits::default()
        };
        assert!(matches!(
            CensusPortable::from_json(&text, array_limited),
            Err(CensusPortableError::ParseLimit { .. })
        ));

        let wrong_schema = text.replacen(CENSUS_PORTABLE_SCHEMA, "other-schema", 1);
        assert!(matches!(
            CensusPortable::from_json(&wrong_schema, CensusParseLimits::default()),
            Err(CensusPortableError::Schema { .. })
        ));

        let mut wrong_fingerprint = portable;
        let replacement = if wrong_fingerprint.fingerprint.starts_with('0') {
            "1"
        } else {
            "0"
        };
        wrong_fingerprint
            .fingerprint
            .replace_range(0..1, replacement);
        assert!(matches!(
            CensusPortable::from_json(
                &wrong_fingerprint.to_canonical_json(),
                CensusParseLimits::default()
            ),
            Err(CensusPortableError::FingerprintMismatch)
        ));
    }

    #[test]
    fn portable_verifier_rejects_resigned_domain_count_and_witness_mutations() {
        let algebra = linear_an(2, f5());
        let census = Census::new(&algebra, vec![1, 1]).unwrap();
        let CensusOutcome::Complete(result) = census.run_with(census_limits(), None) else {
            panic!("the five-entry domain should complete")
        };
        let original = CensusPortable::from_result(&result);

        let mut domain = original.clone();
        domain.raw_space_size += 1;
        domain.fingerprint = fingerprint(&domain.canonical_without_fingerprint());
        assert!(matches!(
            verify_census_portable(&domain.to_canonical_json(), CensusVerifyLimits::default()),
            Err(CensusPortableError::DomainMismatch { .. })
        ));

        let mut oversized_cursor = original.clone();
        oversized_cursor.cursor = u128::MAX;
        oversized_cursor.fingerprint =
            fingerprint(&oversized_cursor.canonical_without_fingerprint());
        assert!(matches!(
            verify_census_portable(
                &oversized_cursor.to_canonical_json(),
                CensusVerifyLimits::default()
            ),
            Err(CensusPortableError::CounterOverflow { field: "cursor" })
        ));

        let mut counts = original.clone();
        counts.candidates += 1;
        counts.fingerprint = fingerprint(&counts.canonical_without_fingerprint());
        assert!(matches!(
            verify_census_portable(&counts.to_canonical_json(), CensusVerifyLimits::default()),
            Err(CensusPortableError::CountMismatch { .. })
        ));

        let mut witness = original;
        witness.assignments[0].coordinates[0] = (witness.assignments[0].coordinates[0] + 1) % 5;
        witness.fingerprint = fingerprint(&witness.canonical_without_fingerprint());
        assert!(matches!(
            verify_census_portable(&witness.to_canonical_json(), CensusVerifyLimits::default()),
            Err(CensusPortableError::Witness(_)) | Err(CensusPortableError::ReplayMismatch { .. })
        ));
    }

    #[test]
    fn representatives_only_matches_all_assignments_on_small_field() {
        let algebra = linear_an(3, PrimeField::new(2).unwrap());
        let census = Census::new(&algebra, vec![1, 1, 1]).unwrap();
        let all_limits = CensusLimits {
            retention: CensusRetention::AllAssignments,
            ..census_limits()
        };
        let compact_limits = CensusLimits {
            retention: CensusRetention::RepresentativesOnly,
            max_assignments: 0,
            ..census_limits()
        };
        let CensusOutcome::Complete(all) = census.run_with(all_limits, None) else {
            panic!("the all-assignment census should complete")
        };
        let CensusOutcome::Complete(compact) = census.run_with(compact_limits, None) else {
            panic!("the representatives-only census should complete")
        };
        assert_eq!(compact.cursor(), all.cursor());
        assert_eq!(compact.candidates(), all.candidates());
        assert_eq!(compact.accepted_modules(), all.accepted_modules());
        assert_eq!(compact.rejected_candidates(), all.rejected_candidates());
        assert_eq!(compact.isomorphism_checks(), all.isomorphism_checks());
        assert_eq!(compact.work_units(), all.work_units());
        assert_eq!(compact.representatives().len(), all.representatives().len());
        assert!(compact.assignments().is_empty());
        assert!(compact
            .representatives()
            .iter()
            .zip(all.representatives())
            .all(|(left, right)| left.cursor() == right.cursor()
                && left.coordinates() == right.coordinates()));
        assert!(all.verify());
        assert!(compact.verify());
    }

    #[test]
    fn representatives_only_resume_preserves_retention_and_ignores_assignment_limit() {
        let algebra = linear_an(2, f5());
        let census = Census::new(&algebra, vec![1, 1]).unwrap();
        let cut_limits = CensusLimits {
            retention: CensusRetention::RepresentativesOnly,
            max_candidates: 2,
            max_assignments: 0,
            ..census_limits()
        };
        let CensusOutcome::Cut(cut) = census.run_with(cut_limits, None) else {
            panic!("the compact candidate limit should produce a cut")
        };
        let resumed_limits = CensusLimits {
            retention: CensusRetention::RepresentativesOnly,
            max_assignments: 0,
            ..census_limits()
        };
        let resumed = census.resume(&cut, resumed_limits, None).unwrap();
        let CensusOutcome::Complete(result) = resumed else {
            panic!("the compact census should resume to completion")
        };
        assert!(result.assignments().is_empty());
        assert!(result.verify());
        let wrong_retention = CensusLimits {
            retention: CensusRetention::AllAssignments,
            ..resumed_limits
        };
        assert!(matches!(
            census.resume(&cut, wrong_retention, None),
            Err(CensusResumeError::RetentionMismatch {
                checkpoint: CensusRetention::RepresentativesOnly,
                requested: CensusRetention::AllAssignments,
            })
        ));
    }

    #[test]
    fn compact_portable_checkpoint_replays_counts_without_assignments() {
        let algebra = linear_an(2, f5());
        let census = Census::new(&algebra, vec![1, 1]).unwrap();
        let limits = CensusLimits {
            retention: CensusRetention::RepresentativesOnly,
            max_assignments: 0,
            ..census_limits()
        };
        let outcome = census.run_with(limits, None);
        let CensusOutcome::Complete(result) = &outcome else {
            panic!("the compact census should complete")
        };
        let portable = CensusPortable::from_result(result);
        assert!(portable.assignments().is_empty());
        let text = portable.to_canonical_json();
        assert!(text.contains("\"retention\":\"representatives_only\""));
        let parsed = CensusPortable::from_json(&text, CensusParseLimits::default()).unwrap();
        let verified = verify_census_portable(&text, CensusVerifyLimits::default()).unwrap();
        assert_eq!(parsed, portable);
        assert_eq!(verified.portable(), &portable);
        let CensusOutcome::Complete(replayed) = verified.outcome() else {
            panic!("the compact portable value should verify as complete")
        };
        assert_eq!(replayed.accepted_modules(), result.accepted_modules());
        assert_eq!(replayed.rejected_candidates(), result.rejected_candidates());
        assert!(replayed.assignments().is_empty());
    }

    #[test]
    fn compact_portable_cut_round_trips_and_resumes() {
        let algebra = linear_an(2, f5());
        let census = Census::new(&algebra, vec![1, 1]).unwrap();
        let cut_limits = CensusLimits {
            retention: CensusRetention::RepresentativesOnly,
            max_candidates: 2,
            max_assignments: 0,
            ..census_limits()
        };
        let CensusOutcome::Cut(cut) = census.run_with(cut_limits, None) else {
            panic!("the compact candidate limit should produce a cut")
        };
        let portable = CensusPortable::from_cut(&cut);
        assert!(portable.assignments().is_empty());
        let text = portable.to_canonical_json();
        let verified = verify_census_portable(&text, CensusVerifyLimits::default()).unwrap();
        assert!(verified.portable().assignments().is_empty());
        let limits = CensusLimits {
            retention: CensusRetention::RepresentativesOnly,
            max_assignments: 0,
            ..census_limits()
        };
        let CensusOutcome::Complete(result) = verified.resume(limits, None).unwrap() else {
            panic!("the compact portable cut should resume to completion")
        };
        assert!(result.assignments().is_empty());
        assert!(result.verify());
    }

    #[test]
    fn compact_portable_parser_rejects_assignments_and_unknown_retention() {
        let algebra = linear_an(2, f5());
        let census = Census::new(&algebra, vec![1, 1]).unwrap();
        let limits = CensusLimits {
            retention: CensusRetention::RepresentativesOnly,
            max_assignments: 0,
            ..census_limits()
        };
        let CensusOutcome::Complete(result) = census.run_with(limits, None) else {
            panic!("the compact census should complete")
        };
        let compact = CensusPortable::from_result(&result);
        let all_limits = CensusLimits {
            retention: CensusRetention::AllAssignments,
            max_assignments: 32,
            ..census_limits()
        };
        let CensusOutcome::Complete(all_result) = census.run_with(all_limits, None) else {
            panic!("the all-assignment census should complete")
        };
        let mut forged = compact.clone();
        forged.assignments = CensusPortable::from_result(&all_result).assignments;
        forged.fingerprint = fingerprint(&forged.canonical_without_fingerprint());
        assert!(matches!(
            CensusPortable::from_json(&forged.to_canonical_json(), CensusParseLimits::default()),
            Err(CensusPortableError::CountMismatch { .. })
        ));

        let unknown = compact
            .to_canonical_json()
            .replace("representatives_only", "compact");
        assert!(matches!(
            CensusPortable::from_json(&unknown, CensusParseLimits::default()),
            Err(CensusPortableError::Retention { .. })
        ));
    }
}

fn validate_dimensions(algebra: &Algebra, dimensions: &[usize]) -> Result<(), CensusError> {
    let expected = algebra.quiver().num_vertices() as usize;
    (dimensions.len() == expected)
        .then_some(())
        .ok_or(CensusError::DimensionVectorLength {
            expected,
            got: dimensions.len(),
        })
}

fn coordinate_layout(
    algebra: &Algebra,
    dimensions: &[usize],
) -> Result<Vec<CensusCoordinate>, CensusError> {
    let mut entry_counts = Vec::with_capacity(algebra.quiver().num_arrows());
    let mut total = 0usize;
    for index in 0..algebra.quiver().num_arrows() {
        let arrow = ArrowId(index as u32);
        let rows = dimensions[algebra.quiver().source(arrow) as usize];
        let columns = dimensions[algebra.quiver().target(arrow) as usize];
        let entries = rows
            .checked_mul(columns)
            .ok_or(CensusError::MatrixEntryOverflow {
                arrow,
                rows,
                columns,
            })?;
        total = total
            .checked_add(entries)
            .ok_or(CensusError::CoordinateCountOverflow)?;
        entry_counts.push((arrow, rows, columns));
    }
    let mut coordinates = Vec::new();
    coordinates
        .try_reserve(total)
        .map_err(|_| CensusError::CoordinateAllocationFailed { coordinates: total })?;
    for (arrow, rows, columns) in entry_counts {
        append_coordinates(&mut coordinates, arrow, rows, columns);
    }
    Ok(coordinates)
}

fn append_coordinates(
    coordinates: &mut Vec<CensusCoordinate>,
    arrow: ArrowId,
    rows: usize,
    columns: usize,
) {
    for row in 0..rows {
        for column in 0..columns {
            coordinates.push(CensusCoordinate { arrow, row, column });
        }
    }
}

fn checked_power(modulus: u64, exponent: usize) -> Result<u128, CensusError> {
    let mut value = 1u128;
    for _ in 0..exponent {
        value = value
            .checked_mul(u128::from(modulus))
            .ok_or(CensusError::SearchSpaceOverflow {
                coordinates: exponent,
                modulus,
            })?;
    }
    Ok(value)
}

fn enumerate_state(mut state: CensusState, control: Option<&ComputationControl>) -> CensusOutcome {
    update_progress(control, &state, false);
    while !state.complete() {
        if is_cancelled(control) {
            return CensusOutcome::Cut(CensusCut {
                state,
                reason: CensusCutReason::Cancelled,
            });
        }
        let work_before = state.work_units;
        let checks_before = state.isomorphism_checks;
        match process_candidate(&mut state) {
            Ok(Some(reason)) => {
                update_progress(control, &state, false);
                return CensusOutcome::Cut(CensusCut { state, reason });
            }
            Ok(None) => update_progress(control, &state, false),
            Err(error) => {
                state.work_units = work_before;
                state.isomorphism_checks = checks_before;
                update_progress(control, &state, false);
                return CensusOutcome::Failed(CensusFailed { state, error });
            }
        }
    }
    update_progress(control, &state, true);
    CensusOutcome::Complete(CensusResult { state })
}

fn process_candidate(state: &mut CensusState) -> Result<Option<CensusCutReason>, CensusFailure> {
    if state.candidates >= state.limits.max_candidates {
        return Ok(Some(CensusCutReason::CandidateLimit {
            limit: state.limits.max_candidates,
        }));
    }
    if !reserve_work(state)? {
        return Ok(Some(CensusCutReason::WorkLimit {
            stage: CensusWorkStage::Candidate,
            limit: state.limits.max_work_units,
        }));
    }
    let coordinates = coordinates_at(&state.domain, state.cursor);
    let module = match build_module(&state.domain, &coordinates) {
        Ok(module) => module,
        Err(ModuleError::RelationActsNonzero { .. }) => {
            commit_rejected(state)?;
            return Ok(None);
        }
        Err(error) => {
            return Err(CensusFailure::CandidateConstruction {
                candidate_cursor: state.cursor,
                error,
            });
        }
    };
    classify_candidate(state, module, coordinate_values(&coordinates))
}

fn reserve_work(state: &mut CensusState) -> Result<bool, CensusFailure> {
    if state.work_units >= state.limits.max_work_units {
        return Ok(false);
    }
    state.work_units = state
        .work_units
        .checked_add(1)
        .ok_or(CensusFailure::WorkOverflow {
            candidate_cursor: state.cursor,
        })?;
    Ok(true)
}

fn commit_rejected(state: &mut CensusState) -> Result<(), CensusFailure> {
    state.candidates = state
        .candidates
        .checked_add(1)
        .ok_or(CensusFailure::WorkOverflow {
            candidate_cursor: state.cursor,
        })?;
    state.rejected_candidates =
        state
            .rejected_candidates
            .checked_add(1)
            .ok_or(CensusFailure::WorkOverflow {
                candidate_cursor: state.cursor,
            })?;
    state.cursor = state
        .cursor
        .checked_add(1)
        .ok_or(CensusFailure::WorkOverflow {
            candidate_cursor: state.cursor,
        })?;
    Ok(())
}

fn classify_candidate(
    state: &mut CensusState,
    module: Module,
    coordinates: Vec<u64>,
) -> Result<Option<CensusCutReason>, CensusFailure> {
    let mut coordinates = Some(coordinates);
    for representative in 0..state.representatives.len() {
        match compare_representative(state, &module, &mut coordinates, representative)? {
            CandidateComparison::Continue => {}
            CandidateComparison::Classified => return Ok(None),
            CandidateComparison::Cut(reason) => return Ok(Some(reason)),
        }
    }
    if state.representatives.len() >= state.limits.max_representatives {
        return Ok(Some(CensusCutReason::RepresentativeLimit {
            limit: state.limits.max_representatives,
        }));
    }
    commit_representative(
        state,
        module,
        coordinates.expect("no comparison classified this candidate"),
    )?;
    Ok(None)
}

enum CandidateComparison {
    Continue,
    Classified,
    Cut(CensusCutReason),
}

fn compare_representative(
    state: &mut CensusState,
    module: &Module,
    coordinates: &mut Option<Vec<u64>>,
    representative: usize,
) -> Result<CandidateComparison, CensusFailure> {
    if state.isomorphism_checks >= state.limits.max_isomorphism_checks {
        return Ok(CandidateComparison::Cut(
            CensusCutReason::IsomorphismLimit {
                limit: state.limits.max_isomorphism_checks,
            },
        ));
    }
    if !reserve_work(state)? {
        return Ok(CandidateComparison::Cut(CensusCutReason::WorkLimit {
            stage: CensusWorkStage::Isomorphism,
            limit: state.limits.max_work_units,
        }));
    }
    let target = state.representatives[representative].module.clone();
    let outcome = is_isomorphic(module, &target).map_err(|error| CensusFailure::Isomorphism {
        candidate_cursor: state.cursor,
        representative,
        error,
    })?;
    increment_isomorphism_checks(state)?;
    match outcome {
        IsoOutcome::Isomorphic(witness) => {
            commit_duplicate(state, coordinates, representative, witness)
        }
        IsoOutcome::NotIsomorphic(_) => Ok(CandidateComparison::Continue),
        IsoOutcome::Unknown { reason } => Ok(CandidateComparison::Cut(
            CensusCutReason::UnknownIsomorphism {
                representative,
                reason,
            },
        )),
    }
}

fn increment_isomorphism_checks(state: &mut CensusState) -> Result<(), CensusFailure> {
    state.isomorphism_checks =
        state
            .isomorphism_checks
            .checked_add(1)
            .ok_or(CensusFailure::WorkOverflow {
                candidate_cursor: state.cursor,
            })?;
    Ok(())
}

fn commit_duplicate(
    state: &mut CensusState,
    coordinates: &mut Option<Vec<u64>>,
    representative: usize,
    witness: Morphism,
) -> Result<CandidateComparison, CensusFailure> {
    if state.limits.retention == CensusRetention::RepresentativesOnly {
        coordinates.take();
        drop(witness);
        commit_accepted(state)?;
        advance_cursor(state)?;
        return Ok(CandidateComparison::Classified);
    }
    if state.assignments.len() >= state.limits.max_assignments {
        return Ok(CandidateComparison::Cut(CensusCutReason::AssignmentLimit {
            limit: state.limits.max_assignments,
        }));
    }
    commit_assignment(
        state,
        coordinates
            .take()
            .expect("one candidate can be classified only once"),
        representative,
        witness,
    )?;
    Ok(CandidateComparison::Classified)
}

fn commit_assignment(
    state: &mut CensusState,
    coordinates: Vec<u64>,
    representative: usize,
    witness: Morphism,
) -> Result<(), CensusFailure> {
    let cursor = state.cursor;
    commit_accepted(state)?;
    state.assignments.push(CensusAssignment {
        cursor,
        coordinates,
        representative,
        witness,
    });
    advance_cursor(state)
}

fn commit_accepted(state: &mut CensusState) -> Result<(), CensusFailure> {
    state.candidates = state
        .candidates
        .checked_add(1)
        .ok_or(CensusFailure::WorkOverflow {
            candidate_cursor: state.cursor,
        })?;
    state.accepted_modules =
        state
            .accepted_modules
            .checked_add(1)
            .ok_or(CensusFailure::WorkOverflow {
                candidate_cursor: state.cursor,
            })?;
    Ok(())
}

fn commit_representative(
    state: &mut CensusState,
    module: Module,
    coordinates: Vec<u64>,
) -> Result<(), CensusFailure> {
    let cursor = state.cursor;
    commit_accepted(state)?;
    state.representatives.push(CensusRepresentative {
        cursor,
        coordinates,
        module,
    });
    advance_cursor(state)
}

fn advance_cursor(state: &mut CensusState) -> Result<(), CensusFailure> {
    state.cursor = state
        .cursor
        .checked_add(1)
        .ok_or(CensusFailure::WorkOverflow {
            candidate_cursor: state.cursor,
        })?;
    Ok(())
}

fn is_cancelled(control: Option<&ComputationControl>) -> bool {
    control.is_some_and(ComputationControl::is_cancelled)
}

fn update_progress(control: Option<&ComputationControl>, state: &CensusState, complete: bool) {
    let Some(control) = control else {
        return;
    };
    let stage = if complete {
        ProgressStage::Complete
    } else {
        ProgressStage::Census
    };
    control.update(stage, state.work_units, state.limits.max_work_units);
}

fn coordinates_at(domain: &CensusDomain, cursor: u128) -> Vec<Fp> {
    let field = domain.algebra.field();
    let modulus = u128::from(field.modulus());
    let mut value = cursor;
    let mut coordinates = vec![field.zero(); domain.coordinate_count()];
    for coordinate in coordinates.iter_mut().rev() {
        *coordinate = field.elem((value % modulus) as i64);
        value /= modulus;
    }
    coordinates
}

fn coordinate_values(coordinates: &[Fp]) -> Vec<u64> {
    coordinates.iter().map(|value| value.raw()).collect()
}

fn build_module(domain: &CensusDomain, coordinates: &[Fp]) -> Result<Module, ModuleError> {
    let mut maps = Vec::with_capacity(domain.algebra.quiver().num_arrows());
    let mut offset = 0usize;
    for index in 0..domain.algebra.quiver().num_arrows() {
        let arrow = ArrowId(index as u32);
        let rows = domain.dimensions[domain.algebra.quiver().source(arrow) as usize];
        let columns = domain.dimensions[domain.algebra.quiver().target(arrow) as usize];
        let entries = rows * columns;
        maps.push(DenseMat::from_flat(
            rows,
            columns,
            &coordinates[offset..offset + entries],
        ));
        offset += entries;
    }
    Module::new(domain.algebra.clone(), domain.dimensions.clone(), maps)
}

fn build_module_from_values(domain: &CensusDomain, values: &[u64]) -> Result<Module, ModuleError> {
    let field = domain.algebra.field();
    if values.len() != domain.coordinate_count() {
        return Err(ModuleError::MapCountMismatch {
            expected: domain.coordinate_count(),
            got: values.len(),
        });
    }
    if let Some((index, _)) = values
        .iter()
        .enumerate()
        .find(|(_, value)| **value >= field.modulus())
    {
        let coordinate = domain.coordinates[index];
        return Err(ModuleError::NonCanonicalEntry {
            arrow: coordinate.arrow,
            row: coordinate.row,
            col: coordinate.column,
        });
    }
    let coordinates: Vec<Fp> = values
        .iter()
        .map(|value| field.elem(*value as i64))
        .collect();
    build_module(domain, &coordinates)
}

fn verify_state_data(state: &CensusState) -> bool {
    let Ok(cursor) = usize::try_from(state.cursor) else {
        return false;
    };
    state.cursor <= state.domain.raw_space_size()
        && state.candidates == cursor
        && accepted_count_is_consistent(state)
        && candidate_count_is_consistent(state)
        && verify_representatives(state)
        && verify_assignments(state)
}

fn accepted_count_is_consistent(state: &CensusState) -> bool {
    match state.limits.retention {
        CensusRetention::AllAssignments => state
            .representatives
            .len()
            .checked_add(state.assignments.len())
            .is_some_and(|count| state.accepted_modules == count),
        CensusRetention::RepresentativesOnly => {
            state.assignments.is_empty() && state.accepted_modules >= state.representatives.len()
        }
    }
}

fn candidate_count_is_consistent(state: &CensusState) -> bool {
    state
        .accepted_modules
        .checked_add(state.rejected_candidates)
        .is_some_and(|count| state.candidates == count)
}

fn verify_representatives(state: &CensusState) -> bool {
    state.representatives.iter().all(|rep| {
        rep.cursor < state.cursor
            && rep.coordinates.len() == state.domain.coordinate_count()
            && Arc::ptr_eq(rep.module.algebra(), &state.domain.algebra)
            && build_module_from_values(&state.domain, &rep.coordinates)
                .is_ok_and(|module| same_representation(&module, &rep.module))
    })
}

fn verify_assignments(state: &CensusState) -> bool {
    state.assignments.iter().all(|assignment| {
        assignment.cursor < state.cursor
            && assignment.representative < state.representatives.len()
            && assignment.coordinates.len() == state.domain.coordinate_count()
            && assignment.witness.is_isomorphism()
            && build_module_from_values(&state.domain, &assignment.coordinates)
                .is_ok_and(|module| same_representation(&module, assignment.witness.source()))
            && same_representation(
                assignment.witness.target(),
                &state.representatives[assignment.representative].module,
            )
    })
}

fn replay_complete(state: &CensusState) -> bool {
    let census = Census {
        domain: state.domain.clone(),
    };
    match census.run_with(state.limits, None) {
        CensusOutcome::Complete(result) => same_replay_data(state, &result.state),
        CensusOutcome::Cut(_) | CensusOutcome::Failed(_) => false,
    }
}

fn replay_prefix(state: &CensusState) -> bool {
    let mut limits = state.limits;
    let Ok(cursor) = usize::try_from(state.cursor) else {
        return false;
    };
    limits.max_candidates = cursor;
    let census = Census {
        domain: state.domain.clone(),
    };
    let outcome = census.run_with(limits, None);
    let replay = match outcome {
        CensusOutcome::Complete(result) => result.state,
        CensusOutcome::Cut(cut) => cut.state,
        CensusOutcome::Failed(_) => return false,
    };
    same_replay_data(state, &replay)
}

fn replay_cut(state: &CensusState, reason: &CensusCutReason) -> bool {
    let census = Census {
        domain: state.domain.clone(),
    };
    let CensusOutcome::Cut(cut) = census.run_with(state.limits, None) else {
        return false;
    };
    same_replay_data(state, &cut.state) && reason == &cut.reason
}

fn same_replay_data(left: &CensusState, right: &CensusState) -> bool {
    same_prefix_data(left, right)
        && left.isomorphism_checks == right.isomorphism_checks
        && left.work_units == right.work_units
}

fn same_prefix_data(left: &CensusState, right: &CensusState) -> bool {
    left.domain == right.domain
        && left.cursor == right.cursor
        && left.candidates == right.candidates
        && left.accepted_modules == right.accepted_modules
        && left.rejected_candidates == right.rejected_candidates
        && representative_data_equal(&left.representatives, &right.representatives)
        && assignment_data_equal(&left.assignments, &right.assignments)
}

fn representative_data_equal(
    left: &[CensusRepresentative],
    right: &[CensusRepresentative],
) -> bool {
    left.len() == right.len()
        && left.iter().zip(right).all(|(a, b)| {
            a.cursor == b.cursor
                && a.coordinates == b.coordinates
                && same_representation(&a.module, &b.module)
        })
}

fn assignment_data_equal(left: &[CensusAssignment], right: &[CensusAssignment]) -> bool {
    left.len() == right.len()
        && left.iter().zip(right).all(|(a, b)| {
            a.cursor == b.cursor
                && a.coordinates == b.coordinates
                && a.representative == b.representative
                && same_representation(a.witness.source(), b.witness.source())
                && same_representation(a.witness.target(), b.witness.target())
                && (0..a.witness.source().algebra().quiver().num_vertices())
                    .all(|vertex| a.witness.map_at(vertex) == b.witness.map_at(vertex))
        })
}

pub(crate) fn tilting_candidate(algebra: &Arc<Algebra>, id: &str) -> Result<Module, String> {
    let parts = match id {
        "linear-a3-pd1" => vec![
            Module::simple(algebra, 0),
            Module::projective(algebra, 0),
            Module::projective(algebra, 2),
        ],
        "a3-mod-ab-da-pd2" => (0..3)
            .map(|vertex| Module::injective(algebra, vertex))
            .collect(),
        _ => return Err(format!("unknown classical-tilting candidate {id:?}")),
    };
    Ok(direct_sum(&parts.iter().collect::<Vec<_>>()).0)
}

pub(crate) fn summed_coresolution_dims(
    coresolutions: &[Vec<Vec<usize>>],
    n: usize,
) -> Result<Vec<Vec<usize>>, String> {
    let len = coresolutions.iter().map(Vec::len).max().unwrap_or(0);
    // QPA's lower-to-upper complex order ends at the projective. Reverse each
    // list before adding the per-projective coresolutions term by term.
    (0..len)
        .map(|degree| {
            let mut sum = vec![0usize; n];
            for term in coresolutions
                .iter()
                .filter_map(|complex| complex.len().checked_sub(degree + 1).map(|i| &complex[i]))
            {
                for (entry, value) in sum.iter_mut().zip(term) {
                    *entry = entry.checked_add(*value).ok_or_else(|| {
                        "summed QPA coresolution dimension overflows usize".to_string()
                    })?;
                }
            }
            Ok(sum)
        })
        .collect()
}

pub(crate) fn target_invariants(target: &Arc<Algebra>) -> Result<TargetInvariants, String> {
    let n = target.quiver().num_vertices() as usize;
    let radical_dimensions: Vec<usize> = (0..=target.nilpotency_degree())
        .map(|power| {
            (0..n)
                .flat_map(|source| {
                    (0..n).map(move |sink| {
                        target
                            .radical_power_matrix(source as u32, sink as u32, power)
                            .rows()
                    })
                })
                .sum()
        })
        .collect();
    let radical_layers = radical_dimensions
        .windows(2)
        .map(|pair| pair[0] - pair[1])
        .collect();
    let simples: Vec<Module> = (0..n as u32)
        .map(|vertex| Module::simple(target, vertex))
        .collect();
    let simple_ext1 = simples
        .iter()
        .map(|source| {
            simples
                .iter()
                .map(|sink| {
                    ext_dim(source, sink, 1)
                        .map_err(|error| format!("target Ext^1 failed: {error}"))
                })
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(TargetInvariants {
        dimension: target.dim(),
        cartan: target.cartan_matrix(),
        radical_layers,
        simple_ext1,
    })
}

pub(crate) fn matrices_match_under_permutation(
    expected: &TargetInvariants,
    ours: &TargetInvariants,
) -> bool {
    fn search(
        expected: &TargetInvariants,
        ours: &TargetInvariants,
        permutation: &mut Vec<usize>,
        unused: &mut Vec<usize>,
    ) -> bool {
        if unused.is_empty() {
            let n = permutation.len();
            return (0..n).all(|i| {
                (0..n).all(|j| {
                    expected.cartan[permutation[i]][permutation[j]] == ours.cartan[i][j]
                        && expected.simple_ext1[permutation[i]][permutation[j]]
                            == ours.simple_ext1[i][j]
                })
            });
        }
        for at in 0..unused.len() {
            let vertex = unused.remove(at);
            permutation.push(vertex);
            if search(expected, ours, permutation, unused) {
                return true;
            }
            permutation.pop();
            unused.insert(at, vertex);
        }
        false
    }

    let n = expected.cartan.len();
    n == ours.cartan.len()
        && search(
            expected,
            ours,
            &mut Vec::with_capacity(n),
            &mut (0..n).collect(),
        )
}

pub(crate) fn compare_target(
    mismatches: &mut Vec<String>,
    ctx: &str,
    id: &str,
    tilting: &ClassicalTiltingModule,
    expected: &TargetOracle,
) {
    let TargetOracle::Computed(expected) = expected else {
        return;
    };
    let outcome = match present_target(tilting, &TargetLimits::default()) {
        Ok(outcome) => outcome,
        Err(error) => {
            mismatches.push(format!("{ctx}: {id}: target recovery failed: {error}"));
            return;
        }
    };
    let TargetPresentationOutcome::Presented(presented) = outcome else {
        mismatches.push(format!(
            "{ctx}: {id}: QPA computed the split target, ours returned {outcome:?}"
        ));
        return;
    };
    let ours = match target_invariants(presented.target()) {
        Ok(invariants) => invariants,
        Err(error) => {
            mismatches.push(format!("{ctx}: {id}: {error}"));
            return;
        }
    };
    if expected.dimension != ours.dimension {
        mismatches.push(format!(
            "{ctx}: {id}: target dimension is {}, ours is {}",
            expected.dimension, ours.dimension
        ));
    }
    if expected.radical_layers != ours.radical_layers {
        mismatches.push(format!(
            "{ctx}: {id}: target radical layers are {:?}, ours are {:?}",
            expected.radical_layers, ours.radical_layers
        ));
    }
    if !matrices_match_under_permutation(expected, &ours) {
        mismatches.push(format!(
            "{ctx}: {id}: no vertex permutation matches target Cartan {:?} and simple Ext^1 {:?} to ours {:?} and {:?}",
            expected.cartan, expected.simple_ext1, ours.cartan, ours.simple_ext1
        ));
    }
}

pub(crate) fn compare_tilting_success(
    mismatches: &mut Vec<String>,
    ctx: &str,
    algebra: &Arc<Algebra>,
    expected: &ClassicalTiltingRecord,
    ours: &ClassicalTiltingModule,
) {
    if Some(ours.projective_dimension()) != expected.projective_dimension {
        mismatches.push(format!(
            "{ctx}: {} has projective dimension {:?}, ours is {}",
            expected.id,
            expected.projective_dimension,
            ours.projective_dimension()
        ));
    }
    let qpa_dims = match summed_coresolution_dims(
        &expected.coresolutions,
        algebra.quiver().num_vertices() as usize,
    ) {
        Ok(dims) => dims,
        Err(error) => {
            mismatches.push(format!("{ctx}: {}: {error}", expected.id));
            return;
        }
    };
    let our_dims: Vec<Vec<usize>> = ours
        .generation_complex()
        .complex()
        .terms()
        .iter()
        .map(|term| term.dim_vector().to_vec())
        .collect();
    if qpa_dims != our_dims {
        mismatches.push(format!(
            "{ctx}: {} has summed QPA coresolution {qpa_dims:?}, ours is {our_dims:?}",
            expected.id
        ));
    }
    compare_target(
        mismatches,
        ctx,
        &expected.id,
        ours,
        expected
            .target
            .as_ref()
            .expect("QPA-positive records carry a target outcome"),
    );
}

pub(crate) fn compare_classical_candidate(
    mismatches: &mut Vec<String>,
    ctx: &str,
    algebra: &Arc<Algebra>,
    expected: &ClassicalTiltingRecord,
) {
    let candidate = match tilting_candidate(algebra, &expected.id) {
        Ok(candidate) => candidate,
        Err(error) => {
            mismatches.push(format!("{ctx}: {error}"));
            return;
        }
    };
    if candidate.dim_vector() != expected.module_dimvec {
        mismatches.push(format!(
            "{ctx}: {} ({}) has dimension {:?}, ours is {:?}",
            expected.id,
            expected.construction,
            expected.module_dimvec,
            candidate.dim_vector()
        ));
        return;
    }
    let limits = TiltingLimits {
        max_projective_dimension: expected.bound,
        max_generation_steps: expected.bound.saturating_add(1),
    };
    match ClassicalTiltingModule::classify(&candidate, limits) {
        Ok(ClassicalTiltingResult::Tilting(ours)) if expected.qpa_tilting => {
            compare_tilting_success(mismatches, ctx, algebra, expected, &ours)
        }
        Ok(other) => mismatches.push(format!(
            "{ctx}: {} is tilting {} in QPA, ours returned {other:?}",
            expected.id, expected.qpa_tilting
        )),
        Err(error) => mismatches.push(format!("{ctx}: {}: {error}", expected.id)),
    }
}

pub(crate) fn compare_classical_tilting(mismatches: &mut Vec<String>, ctx: &str, fx: &Fixture) {
    if fx.classical_tilting.is_empty() {
        return;
    }
    let algebra = match build_algebra(fx) {
        Ok(algebra) => algebra,
        Err(error) => {
            mismatches.push(format!("{ctx}: classical tilting: {error}"));
            return;
        }
    };
    for expected in &fx.classical_tilting {
        compare_classical_candidate(mismatches, ctx, &algebra, expected);
    }
}

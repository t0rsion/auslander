/// The schema v8 support tau-tilting layer.
///
/// Everything gated on the closure marker is compared only where the marker
/// admits it, and against a route that certifies completeness: the catalog
/// enumeration where an exhaustive catalog exists, otherwise a closed mutation
/// graph. Where the oracle carries a pair list and neither route reaches one,
/// the route is named in a mismatch, never passed silently. Where the oracle
/// carries none, there is nothing to compare and nothing is claimed.
pub(crate) fn compare_stt(
    mismatches: &mut Vec<String>,
    ctx: &str,
    fx: &Fixture,
    ours: &OurSupportTauTilting,
    depth: SttDepth,
) {
    let Some(theirs) = &fx.stt else {
        return;
    };
    let n = fx.quiver.num_vertices as usize;
    for (t, (theirs, our)) in theirs
        .tau_rigid_designated
        .iter()
        .zip(&ours.tau_rigid_designated)
        .enumerate()
    {
        if theirs != our {
            mismatches.push(format!(
                "{ctx}: {} is tau-rigid {theirs}, ours is {our}",
                fx.designated[t].label()
            ));
        }
    }
    match (theirs.indecomposables, &ours.enumeration) {
        (Closure::Closed { count }, OurStt::Catalog { catalog_len, .. })
            if count != *catalog_len =>
        {
            mismatches.push(format!(
                "{ctx}: the closed walk found {count} indecomposables, our catalog has {catalog_len}"
            ));
        }
        (Closure::NotClosed { cap }, OurStt::Catalog { catalog_len, .. }) => {
            mismatches.push(format!(
                "{ctx}: the walk did not close inside {cap}, yet our catalog lists {catalog_len} indecomposables"
            ));
        }
        _ => {}
    }
    match &theirs.body {
        // GAP enumerated no pairs, so the oracle holds no total, no histogram
        // and no pair list, and nothing gated on completeness is compared.
        // The closure marker itself is compared above, and the truncation
        // cross-check on `kronecker-2` is
        // `kronecker_2_truncates_on_both_sides`.
        SttBody::NotComputed { .. } => {}
        SttBody::Enumerated(values) => {
            let Some(pairs) = ours.enumeration.pairs() else {
                mismatches.push(format!(
                    "{ctx}: GAP enumerated {} pairs, ours came from {}",
                    values.total,
                    ours.enumeration.route()
                ));
                return;
            };
            compare_stt_values(mismatches, ctx, values, ours, pairs, n, depth);
        }
    }
}

pub(crate) fn compare_stt_values(
    mismatches: &mut Vec<String>,
    ctx: &str,
    theirs: &SttValues,
    ours: &OurSupportTauTilting,
    pairs: &[OurPair],
    n: usize,
    depth: SttDepth,
) {
    if theirs.total != pairs.len() {
        mismatches.push(format!(
            "{ctx}: {} support tau-tilting pairs, ours has {} from {}",
            theirs.total,
            pairs.len(),
            ours.enumeration.route()
        ));
    }
    let mut histogram = vec![0usize; n + 1];
    for pair in pairs {
        if let Some(slot) = histogram.get_mut(pair.record.summand_count()) {
            *slot += 1;
        }
    }
    if theirs.histogram != histogram {
        mismatches.push(format!(
            "{ctx}: the pair histogram is {:?}, ours is {histogram:?}",
            theirs.histogram
        ));
    }
    let mut our_records: Vec<PairRecord> = pairs.iter().map(|p| p.record.clone()).collect();
    our_records.sort();
    let mut their_records = theirs.pairs.clone();
    their_records.sort();
    if let Some(i) = first_difference(&their_records, &our_records) {
        mismatches.push(format!(
            "{ctx}: the pair lists first differ at entry {i}: {:?} against ours {:?}",
            their_records.get(i),
            our_records.get(i)
        ));
    }
    let slots: usize = pairs.iter().map(|p| p.record.summand_count()).sum();
    if theirs.approximation_slots != slots {
        mismatches.push(format!(
            "{ctx}: {} approximation slots, ours has {slots}",
            theirs.approximation_slots
        ));
    }
    let exchange = our_exchange_shape(pairs, n);
    if theirs.exchange != exchange {
        mismatches.push(format!(
            "{ctx}: the exchange graph self-consistency shape is {:?}, ours is {exchange:?}",
            theirs.exchange
        ));
    }
    if depth == SttDepth::Shape {
        return;
    }
    compare_stt_slots(mismatches, ctx, theirs, pairs);
}

/// The per-slot layer: the sampled approximations.
///
/// A pair record is a weak identity, so a recorded slot is matched against
/// every slot of ours that carries the same record and summand dimension
/// vector, and the recorded invariants must occur among theirs. On
/// `cyclic-nakayama-3-3-3` that set has more than one element by construction.
pub(crate) fn compare_stt_slots(
    mismatches: &mut Vec<String>,
    ctx: &str,
    theirs: &SttValues,
    pairs: &[OurPair],
) {
    for entry in &theirs.approximations {
        let mut candidates = Vec::new();
        for pair in pairs.iter().filter(|p| p.record == entry.pair) {
            for (i, x) in pair.summands.iter().enumerate() {
                if x.dim_vector() != entry.summand_dimvec {
                    continue;
                }
                let rest: Vec<Module> = pair
                    .summands
                    .iter()
                    .enumerate()
                    .filter(|(j, _)| *j != i)
                    .map(|(_, m)| m.clone())
                    .collect();
                match approximation_invariants(x, &rest) {
                    Ok(invariants) => candidates.push(invariants),
                    Err(e) => mismatches.push(format!("{ctx}: {e}")),
                }
            }
        }
        if candidates.is_empty() {
            mismatches.push(format!(
                "{ctx}: no slot of ours carries the pair {:?} with summand {:?}",
                entry.pair, entry.summand_dimvec
            ));
        } else if !candidates.contains(&entry.invariants) {
            mismatches.push(format!(
                "{ctx}: the approximation at {:?} summand {:?} is {:?}, ours are {candidates:?}",
                entry.pair, entry.summand_dimvec, entry.invariants
            ));
        }
    }
}

pub(crate) fn compare_fixture_scalars(
    mismatches: &mut Vec<String>,
    ctx: &str,
    fx: &Fixture,
    ours: &Computed,
) {
    if fx.dim != ours.dim {
        mismatches.push(format!("{ctx}: dim is {}, ours is {}", fx.dim, ours.dim));
    }
    if fx.cartan != ours.cartan {
        mismatches.push(format!(
            "{ctx}: cartan is {:?}, ours is {:?}",
            fx.cartan, ours.cartan
        ));
    }
    if fx.injectives != ours.injectives {
        mismatches.push(format!(
            "{ctx}: injectives is {:?}, ours is {:?}",
            fx.injectives, ours.injectives
        ));
    }
}

pub(crate) fn compare_fixture_indexed<T: PartialEq + std::fmt::Debug>(
    mismatches: &mut Vec<String>,
    ctx: &str,
    label: &str,
    module: &str,
    theirs: &[T],
    ours: &[T],
) {
    for (index, (their, our)) in theirs.iter().zip(ours).enumerate() {
        if their != our {
            mismatches.push(format!(
                "{ctx}: {label}({module}_{index}) is {their:?}, ours is {our:?}"
            ));
        }
    }
}

pub(crate) fn compare_fixture_decomposition_and_ext(
    mismatches: &mut Vec<String>,
    ctx: &str,
    fx: &Fixture,
    ours: &Computed,
) {
    if fx.decomposition != ours.decomposition {
        mismatches.push(format!(
            "{ctx}: decomposition summands are {:?}, ours are {:?}",
            fx.decomposition, ours.decomposition
        ));
    }
    for (i, (their_row, our_row)) in fx.ext.iter().zip(&ours.ext).enumerate() {
        for (j, (theirs, our)) in their_row.iter().zip(our_row).enumerate() {
            if theirs != our {
                mismatches.push(format!(
                    "{ctx}: Ext(S_{i}, S_{j}) is {theirs:?}, ours is {our:?}"
                ));
            }
        }
    }
}

pub(crate) fn compare_fixture(
    mismatches: &mut Vec<String>,
    ctx: &str,
    fx: &Fixture,
    ours: &Computed,
) {
    compare_fixture_scalars(mismatches, ctx, fx, ours);
    compare_fixture_indexed(mismatches, ctx, "projdim", "S", &fx.projdim, &ours.projdim);
    compare_fixture_indexed(mismatches, ctx, "injdim", "S", &fx.injdim, &ours.injdim);
    compare_fixture_indexed(mismatches, ctx, "tau", "S", &fx.tau, &ours.tau);
    compare_fixture_indexed(
        mismatches,
        ctx,
        "tau_injectives",
        "I",
        &fx.tau_injectives,
        &ours.tau_injectives,
    );
    compare_fixture_decomposition_and_ext(mismatches, ctx, fx, ours);
    compare_ar_layer(mismatches, ctx, fx, ours);
}

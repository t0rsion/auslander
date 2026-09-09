pub(crate) fn read_ext(
    value: &json::Value,
    n: usize,
    ctx: &str,
) -> Result<Vec<Vec<Vec<usize>>>, String> {
    let items = as_array(value, &format!("{ctx}: ext"))?;
    if items.len() != n {
        return Err(format!("{ctx}: ext has {} rows, expected {n}", items.len()));
    }
    let mut ext = Vec::with_capacity(n);
    for (i, row) in items.iter().enumerate() {
        let cells = as_array(row, &format!("{ctx}: ext row {i}"))?;
        if cells.len() != n {
            return Err(format!(
                "{ctx}: ext row {i} has {} entries, expected {n}",
                cells.len()
            ));
        }
        let mut out_row = Vec::with_capacity(n);
        for (j, cell) in cells.iter().enumerate() {
            out_row.push(usize_row(
                cell,
                MAX_EXT_DEGREE + 1,
                &format!("{ctx}: ext[{i}][{j}]"),
            )?);
        }
        ext.push(out_row);
    }
    Ok(ext)
}

pub(crate) fn read_bool(
    pairs: &[(String, json::Value)],
    key: &str,
    ctx: &str,
) -> Result<bool, String> {
    match get(pairs, key, ctx)? {
        json::Value::Bool(b) => Ok(*b),
        other => Err(format!("{ctx}: {key} is {other:?}, expected a boolean")),
    }
}

/// Dimension vectors sorted ascending, repetitions preserved. Merging them
/// would erase the `cyclic-nakayama-3-3-3` witness, where two entries
/// `[1, 1, 1]` are two non-isomorphic projectives.
pub(crate) fn read_dimvec_list(
    value: &json::Value,
    n: usize,
    ctx: &str,
) -> Result<Vec<Vec<usize>>, String> {
    let items = as_array(value, ctx)?;
    let mut out: Vec<Vec<usize>> = Vec::with_capacity(items.len());
    for (i, item) in items.iter().enumerate() {
        let dimvec = usize_row(item, n, &format!("{ctx} entry {i}"))?;
        if dimvec.iter().all(|&d| d == 0) {
            return Err(format!("{ctx}: entry {i} is the zero dimension vector"));
        }
        if out.last().is_some_and(|prev| *prev > dimvec) {
            return Err(format!("{ctx}: entries are not sorted ascending at {i}"));
        }
        out.push(dimvec);
    }
    Ok(out)
}

/// A 0-based vertex subset, strictly ascending and inside the quiver.
pub(crate) fn read_vertex_subset(
    value: &json::Value,
    n: usize,
    ctx: &str,
) -> Result<Vec<u32>, String> {
    let items = as_array(value, ctx)?;
    let mut out: Vec<u32> = Vec::with_capacity(items.len());
    for (i, item) in items.iter().enumerate() {
        let v = usize_value(item, ctx)?;
        if v >= n {
            return Err(format!("{ctx}: vertex {v} is not below {n}"));
        }
        if out.last().is_some_and(|&prev| prev as usize >= v) {
            return Err(format!("{ctx}: vertices are not strictly ascending at {i}"));
        }
        out.push(v as u32);
    }
    Ok(out)
}

/// The pair labels of an entry that carries them, checked against `|M| + |P| =
/// n`, the defining count of a basic support tau-tilting pair.
pub(crate) fn read_pair_record(
    pairs: &[(String, json::Value)],
    n: usize,
    ctx: &str,
) -> Result<PairRecord, String> {
    let module_dimvecs = read_dimvec_list(
        get(pairs, "module_dimvecs", ctx)?,
        n,
        &format!("{ctx}: module_dimvecs"),
    )?;
    let projective_support = read_vertex_subset(
        get(pairs, "projective_support", ctx)?,
        n,
        &format!("{ctx}: projective_support"),
    )?;
    if module_dimvecs.len() + projective_support.len() != n {
        return Err(format!(
            "{ctx}: {} module summands and {} projective vertices do not add to {n}",
            module_dimvecs.len(),
            projective_support.len()
        ));
    }
    Ok(PairRecord {
        module_dimvecs,
        projective_support,
    })
}

pub(crate) fn read_closure(value: &json::Value, ctx: &str) -> Result<Closure, String> {
    let pairs = as_object(value, ctx)?;
    if read_bool(pairs, "closed", ctx)? {
        check_keys(pairs, &["closed", "count"], ctx)?;
        let count = read_usize(pairs, "count", ctx)?;
        if count == 0 {
            return Err(format!("{ctx}: a closed walk found no indecomposables"));
        }
        Ok(Closure::Closed { count })
    } else {
        check_keys(pairs, &["closed", "cap"], ctx)?;
        Ok(Closure::NotClosed {
            cap: read_usize(pairs, "cap", ctx)?,
        })
    }
}

pub(crate) fn read_brute_agreement(
    value: &json::Value,
    ctx: &str,
) -> Result<BruteAgreement, String> {
    let pairs = as_object(value, ctx)?;
    if read_bool(pairs, "available", ctx)? {
        check_keys(pairs, &["available", "max_length", "agrees"], ctx)?;
        Ok(BruteAgreement::Available {
            max_length: read_usize(pairs, "max_length", ctx)?,
            agrees: read_bool(pairs, "agrees", ctx)?,
        })
    } else {
        check_keys(pairs, &["available", "reason"], ctx)?;
        Ok(BruteAgreement::Unavailable {
            reason: read_str(pairs, "reason", ctx)?,
        })
    }
}

pub(crate) fn read_approx_row(
    pairs: &[(String, json::Value)],
    key: &str,
    n: usize,
    actx: &str,
) -> Result<Vec<usize>, String> {
    usize_row(get(pairs, key, actx)?, n, &format!("{actx}: {key}"))
}

pub(crate) fn read_approx_invariants(
    pairs: &[(String, json::Value)],
    n: usize,
    actx: &str,
) -> Result<ApproxInvariants, String> {
    Ok(ApproxInvariants {
        source_dimvec: read_approx_row(pairs, "source_dimvec", n, actx)?,
        target_dimvec: read_approx_row(pairs, "target_dimvec", n, actx)?,
        rank: read_usize(pairs, "rank", actx)?,
        kernel_dimvec: read_approx_row(pairs, "kernel_dimvec", n, actx)?,
        cokernel_dimvec: read_approx_row(pairs, "cokernel_dimvec", n, actx)?,
    })
}

pub(crate) fn validate_approximation(
    pair: &PairRecord,
    summand_dimvec: &[usize],
    invariants: &ApproxInvariants,
    n: usize,
    actx: &str,
) -> Result<(), String> {
    if !pair
        .module_dimvecs
        .iter()
        .any(|candidate| candidate.as_slice() == summand_dimvec)
    {
        return Err(format!(
            "{actx}: summand_dimvec {summand_dimvec:?} is not one of the pair's summands"
        ));
    }
    if invariants.source_dimvec != summand_dimvec {
        return Err(format!(
            "{actx}: source_dimvec {:?} is not the summand {summand_dimvec:?}",
            invariants.source_dimvec
        ));
    }
    if invariants.rank + invariants.kernel_dimvec.iter().sum::<usize>()
        != invariants.source_dimvec.iter().sum::<usize>()
    {
        return Err(format!("{actx}: rank and kernel do not add to the source"));
    }
    for vertex in 0..n {
        let image = invariants.source_dimvec[vertex] - invariants.kernel_dimvec[vertex];
        if invariants.kernel_dimvec[vertex] > invariants.source_dimvec[vertex]
            || image + invariants.cokernel_dimvec[vertex] != invariants.target_dimvec[vertex]
        {
            return Err(format!(
                "{actx}: image and cokernel do not add to the target at vertex {vertex}"
            ));
        }
    }
    Ok(())
}

pub(crate) fn read_approximation(
    value: &json::Value,
    n: usize,
    ctx: &str,
    index: usize,
) -> Result<ApproxRecord, String> {
    let actx = format!("{ctx} entry {index}");
    let pairs = as_object(value, &actx)?;
    check_keys(
        pairs,
        &[
            "module_dimvecs",
            "projective_support",
            "summand_dimvec",
            "source_dimvec",
            "target_dimvec",
            "rank",
            "kernel_dimvec",
            "cokernel_dimvec",
        ],
        &actx,
    )?;
    let pair = read_pair_record(pairs, n, &actx)?;
    let summand_dimvec = read_approx_row(pairs, "summand_dimvec", n, &actx)?;
    let invariants = read_approx_invariants(pairs, n, &actx)?;
    validate_approximation(&pair, &summand_dimvec, &invariants, n, &actx)?;
    Ok(ApproxRecord {
        pair,
        summand_dimvec,
        invariants,
    })
}

/// One approximation slot. The invariants are cross-checked against each
/// other before they are compared: `Source(f)` is the summand, the rank is
/// `dim Source - dim Kernel`, and the image is `Source - Kernel` componentwise
/// so the cokernel is `Target - Source + Kernel`.
pub(crate) fn read_approximations(
    value: &json::Value,
    n: usize,
    ctx: &str,
) -> Result<Vec<ApproxRecord>, String> {
    let items = as_array(value, ctx)?;
    items
        .iter()
        .enumerate()
        .map(|(i, item)| read_approximation(item, n, ctx, i))
        .collect()
}

pub(crate) fn read_exchange(
    value: &json::Value,
    n: usize,
    total: usize,
    ctx: &str,
) -> Result<ExchangeShape, String> {
    let pairs = as_object(value, ctx)?;
    check_keys(pairs, &["degree_histogram", "edges", "connected"], ctx)?;
    let degree_histogram = usize_row(
        get(pairs, "degree_histogram", ctx)?,
        n + 2,
        &format!("{ctx}: degree_histogram"),
    )?;
    let edges = read_usize(pairs, "edges", ctx)?;
    if degree_histogram.iter().sum::<usize>() != total {
        return Err(format!(
            "{ctx}: degree_histogram does not cover {total} pairs"
        ));
    }
    let ends: usize = degree_histogram
        .iter()
        .enumerate()
        .map(|(d, count)| d * count)
        .sum();
    if ends != 2 * edges {
        return Err(format!("{ctx}: {ends} edge ends against {edges} edges"));
    }
    Ok(ExchangeShape {
        degree_histogram,
        edges,
        connected: read_bool(pairs, "connected", ctx)?,
    })
}

pub(crate) fn read_stt_pair_records(
    pairs: &[(String, json::Value)],
    n: usize,
    total: usize,
    sctx: &str,
) -> Result<Vec<PairRecord>, String> {
    let pctx = format!("{sctx}: pairs");
    let items = as_array(get(pairs, "pairs", sctx)?, &pctx)?;
    if items.len() != total {
        return Err(format!(
            "{pctx} has {} entries, expected total {total}",
            items.len()
        ));
    }
    items
        .iter()
        .enumerate()
        .map(|(index, item)| {
            let ictx = format!("{pctx} entry {index}");
            let pairs = as_object(item, &ictx)?;
            check_keys(pairs, &["module_dimvecs", "projective_support"], &ictx)?;
            read_pair_record(pairs, n, &ictx)
        })
        .collect()
}

pub(crate) fn validate_stt_histogram(
    histogram: &[usize],
    pair_records: &[PairRecord],
    sctx: &str,
) -> Result<(), String> {
    for (summand_count, count) in histogram.iter().enumerate() {
        let seen = pair_records
            .iter()
            .filter(|pair| pair.summand_count() == summand_count)
            .count();
        if seen != *count {
            return Err(format!(
                "{sctx}: histogram claims {count} pairs with {summand_count} summands, the list has {seen}"
            ));
        }
    }
    Ok(())
}

pub(crate) fn validate_stt_slots(
    approximation_slots: usize,
    pair_records: &[PairRecord],
    sctx: &str,
) -> Result<(), String> {
    let slots: usize = pair_records.iter().map(PairRecord::summand_count).sum();
    if approximation_slots != slots {
        return Err(format!(
            "{sctx}: approximation_slots is {approximation_slots}, the pair list has {slots}"
        ));
    }
    Ok(())
}

pub(crate) fn read_stt_tail(
    pairs: &[(String, json::Value)],
    n: usize,
    total: usize,
    approximation_slots: usize,
    sctx: &str,
) -> Result<(Vec<ApproxRecord>, ExchangeShape), String> {
    let approximations = read_approximations(
        get(pairs, "approximations", sctx)?,
        n,
        &format!("{sctx}: approximations"),
    )?;
    if approximations.len() != approximation_slots.min(APPROX_SAMPLE) {
        return Err(format!(
            "{sctx}: {} approximation entries, expected {}",
            approximations.len(),
            approximation_slots.min(APPROX_SAMPLE)
        ));
    }
    let exchange = read_exchange(
        get(pairs, "exchange_graph_self_consistency", sctx)?,
        n,
        total,
        &format!("{sctx}: exchange_graph_self_consistency"),
    )?;
    Ok((approximations, exchange))
}

pub(crate) fn validate_tau_rigid_copy(
    designated: &[bool],
    expected: &[bool],
    sctx: &str,
) -> Result<(), String> {
    if designated != expected {
        return Err(format!(
            "{sctx}: tau_rigid_designated disagrees with the v6 tau_rigid list"
        ));
    }
    Ok(())
}

pub(crate) fn read_stt_tau_rigid(
    pairs: &[(String, json::Value)],
    expected: &[bool],
    sctx: &str,
) -> Result<Vec<bool>, String> {
    let designated = read_bool_list(
        get(pairs, "tau_rigid_designated", sctx)?,
        expected.len(),
        "tau_rigid_designated",
        sctx,
    )?;
    validate_tau_rigid_copy(&designated, expected, sctx)?;
    Ok(designated)
}

pub(crate) fn read_stt_values(
    pairs: &[(String, json::Value)],
    n: usize,
    sctx: &str,
) -> Result<SttValues, String> {
    let total = read_usize(pairs, "total", sctx)?;
    let histogram = usize_row(
        get(pairs, "histogram", sctx)?,
        n + 1,
        &format!("{sctx}: histogram"),
    )?;
    if histogram.iter().sum::<usize>() != total {
        return Err(format!("{sctx}: histogram does not add to total {total}"));
    }
    let pair_records = read_stt_pair_records(pairs, n, total, sctx)?;
    validate_stt_histogram(&histogram, &pair_records, sctx)?;
    let approximation_slots = read_usize(pairs, "approximation_slots", sctx)?;
    validate_stt_slots(approximation_slots, &pair_records, sctx)?;
    let (approximations, exchange) = read_stt_tail(pairs, n, total, approximation_slots, sctx)?;
    Ok(SttValues {
        total,
        histogram,
        pairs: pair_records,
        approximation_slots,
        approximations,
        exchange,
    })
}

pub(crate) fn read_stt_header<'a>(
    value: &'a json::Value,
    tau_rigid: &[bool],
    sctx: &str,
) -> Result<SttHeader<'a>, String> {
    let pairs = as_object(value, sctx)?;
    let indecomposables = read_closure(get(pairs, "indecomposables", sctx)?, sctx)?;
    let closed = matches!(indecomposables, Closure::Closed { .. });
    check_keys(
        pairs,
        if closed {
            &STT_KEYS_CLOSED[..]
        } else {
            &STT_KEYS_OPEN[..]
        },
        sctx,
    )?;
    let brute = read_brute_agreement(get(pairs, "brute_agreement", sctx)?, sctx)?;
    let tau_rigid_designated = read_stt_tau_rigid(pairs, tau_rigid, sctx)?;
    Ok((pairs, indecomposables, brute, tau_rigid_designated))
}

pub(crate) fn read_stt_not_computed(
    pairs: &[(String, json::Value)],
    indecomposables: Closure,
    brute: BruteAgreement,
    tau_rigid_designated: Vec<bool>,
    sctx: &str,
) -> Result<SupportTauTilting, String> {
    let nctx = format!("{sctx}: not_computed");
    let pairs = as_object(get(pairs, "not_computed", sctx)?, &nctx)?;
    check_keys(pairs, &["reason"], &nctx)?;
    Ok(SupportTauTilting {
        indecomposables,
        brute,
        tau_rigid_designated,
        body: SttBody::NotComputed {
            reason: read_str(pairs, "reason", &nctx)?,
        },
    })
}

/// The v8 `support_tau_tilting` block.
///
/// Everything gated on the closure marker is present exactly when the marker
/// says the walk closed. The totals, the histogram, the pair list, the slot
/// count and the graph shape are cross-checked against each other before any
/// of them is compared.
pub(crate) fn read_support_tau_tilting(
    value: &json::Value,
    n: usize,
    tau_rigid: &[bool],
    ctx: &str,
) -> Result<SupportTauTilting, String> {
    let sctx = format!("{ctx}: support_tau_tilting");
    let (pairs, indecomposables, brute, tau_rigid_designated) =
        read_stt_header(value, tau_rigid, &sctx)?;
    if !matches!(indecomposables, Closure::Closed { .. }) {
        return read_stt_not_computed(pairs, indecomposables, brute, tau_rigid_designated, &sctx);
    }
    let values = read_stt_values(pairs, n, &sctx)?;
    Ok(SupportTauTilting {
        indecomposables,
        brute,
        tau_rigid_designated,
        body: SttBody::Enumerated(Box::new(values)),
    })
}

pub(crate) fn read_target_skip(
    pairs: &[(String, json::Value)],
    ctx: &str,
) -> Result<TargetOracle, String> {
    check_keys(pairs, &["status", "reason"], ctx)?;
    let reason = match read_str(pairs, "reason", ctx)?.as_str() {
        "operation-unavailable" => TargetSkipReason::OperationUnavailable,
        "endomorphism-presentation-failed" => TargetSkipReason::EndomorphismPresentationFailed,
        "opposite-algebra-failed" => TargetSkipReason::OppositeAlgebraFailed,
        "invariant-computation-failed" => TargetSkipReason::InvariantComputationFailed,
        other => return Err(format!("{ctx}: unknown skipped reason {other:?}")),
    };
    Ok(TargetOracle::Skipped { reason })
}

pub(crate) fn read_target_cartan(
    pairs: &[(String, json::Value)],
    expected_vertices: usize,
    ctx: &str,
) -> Result<(usize, Vec<Vec<usize>>), String> {
    let cartan_value = get(pairs, "cartan", ctx)?;
    let n = as_array(cartan_value, &format!("{ctx}: cartan"))?.len();
    if n != expected_vertices {
        return Err(format!(
            "{ctx}: cartan has {n} rows, expected {expected_vertices}"
        ));
    }
    Ok((n, read_matrix(cartan_value, n, n, "cartan", ctx)?))
}

pub(crate) fn read_target_radical_layers(
    pairs: &[(String, json::Value)],
    dimension: usize,
    ctx: &str,
) -> Result<Vec<usize>, String> {
    let radical_layers = as_array(get(pairs, "radical_layers", ctx)?, ctx)?
        .iter()
        .enumerate()
        .map(|(i, value)| usize_value(value, &format!("{ctx}: radical_layers entry {i}")))
        .collect::<Result<Vec<_>, _>>()?;
    if radical_layers.is_empty() || radical_layers.iter().sum::<usize>() != dimension {
        return Err(format!(
            "{ctx}: radical layers must be nonempty and sum to dimension {dimension}"
        ));
    }
    if radical_layers.last() == Some(&0) {
        return Err(format!("{ctx}: radical layers end in zero"));
    }
    Ok(radical_layers)
}

pub(crate) fn read_target_computed(
    pairs: &[(String, json::Value)],
    expected_vertices: usize,
    ctx: &str,
) -> Result<TargetOracle, String> {
    check_keys(
        pairs,
        &[
            "status",
            "algebra",
            "dimension",
            "cartan",
            "radical_layers",
            "simple_ext1",
        ],
        ctx,
    )?;
    let algebra = read_str(pairs, "algebra", ctx)?;
    if algebra != "endomorphism-opposite" {
        return Err(format!(
            "{ctx}: algebra is {algebra:?}, expected \"endomorphism-opposite\""
        ));
    }
    let (n, cartan) = read_target_cartan(pairs, expected_vertices, ctx)?;
    let dimension = read_usize(pairs, "dimension", ctx)?;
    let cartan_dimension = cartan.iter().flatten().copied().sum::<usize>();
    if cartan_dimension != dimension {
        return Err(format!(
            "{ctx}: cartan entries sum to {cartan_dimension}, expected dimension {dimension}"
        ));
    }
    let radical_layers = read_target_radical_layers(pairs, dimension, ctx)?;
    let simple_ext1 = read_matrix(get(pairs, "simple_ext1", ctx)?, n, n, "simple_ext1", ctx)?;
    Ok(TargetOracle::Computed(TargetInvariants {
        dimension,
        cartan,
        radical_layers,
        simple_ext1,
    }))
}

pub(crate) fn read_target_oracle(
    value: &json::Value,
    expected_vertices: usize,
    ctx: &str,
) -> Result<TargetOracle, String> {
    let pairs = as_object(value, ctx)?;
    let status = read_str(pairs, "status", ctx)?;
    if status == "skipped" {
        return read_target_skip(pairs, ctx);
    }
    if status != "computed" {
        return Err(format!(
            "{ctx}: status is {status:?}, expected \"computed\" or \"skipped\""
        ));
    }
    read_target_computed(pairs, expected_vertices, ctx)
}

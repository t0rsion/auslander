pub(crate) fn read_decomposition(
    value: &json::Value,
    n: usize,
    ctx: &str,
) -> Result<Vec<(Vec<usize>, usize)>, String> {
    let dctx = format!("{ctx}: decomposition");
    let pairs = as_object(value, &dctx)?;
    check_keys(pairs, &["module", "summands"], &dctx)?;
    let module = read_str(pairs, "module", &dctx)?;
    if module != DECOMPOSITION_MODULE {
        return Err(format!(
            "{dctx}: module is {module:?}, expected {DECOMPOSITION_MODULE:?}"
        ));
    }
    read_weighted_dimvecs(
        get(pairs, "summands", &dctx)?,
        n,
        "multiplicity",
        &format!("{dctx} summands"),
    )
}

pub(crate) fn read_module_ref(
    value: &json::Value,
    n: usize,
    ctx: &str,
) -> Result<ModuleRef, String> {
    let pairs = as_object(value, ctx)?;
    check_keys(pairs, &["kind", "index"], ctx)?;
    let kind = match read_str(pairs, "kind", ctx)?.as_str() {
        "simple" => ModuleKind::Simple,
        "projective" => ModuleKind::Projective,
        "injective" => ModuleKind::Injective,
        other => return Err(format!("{ctx}: unknown kind {other:?}")),
    };
    let index = read_usize(pairs, "index", ctx)?;
    if index >= n {
        return Err(format!("{ctx}: index {index} is not a vertex below {n}"));
    }
    Ok(ModuleRef { kind, index })
}

/// The designated list is fixed by construction: every simple, then every
/// indecomposable projective, then every indecomposable injective, in vertex
/// order. The reader pins that shape, so the comparator never has to guess
/// which module an entry names.
pub(crate) fn read_designated(
    value: &json::Value,
    n: usize,
    ctx: &str,
) -> Result<Vec<ModuleRef>, String> {
    let dctx = format!("{ctx}: designated_modules");
    let items = as_array(value, &dctx)?;
    let expected = designated_refs(n);
    if items.len() != expected.len() {
        return Err(format!(
            "{dctx} has {} entries, expected {}",
            items.len(),
            expected.len()
        ));
    }
    let refs = items
        .iter()
        .enumerate()
        .map(|(i, item)| read_module_ref(item, n, &format!("{dctx}[{i}]")))
        .collect::<Result<Vec<_>, String>>()?;
    if refs != expected {
        return Err(format!(
            "{dctx} is not the simples, then the projectives, then the injectives, in vertex order"
        ));
    }
    Ok(refs)
}

pub(crate) fn read_ar_middle(
    pairs: &[(String, json::Value)],
    n: usize,
    ictx: &str,
) -> Result<ArSequence, String> {
    let tau = usize_row(get(pairs, "tau", ictx)?, n, &format!("{ictx} tau"))?;
    let middle_dimvec = usize_row(
        get(pairs, "middle_dimvec", ictx)?,
        n,
        &format!("{ictx} middle_dimvec"),
    )?;
    let middle = read_weighted_dimvecs(
        get(pairs, "middle", ictx)?,
        n,
        "multiplicity",
        &format!("{ictx} middle"),
    )?;
    let num_middle_summands = read_usize(pairs, "num_middle_summands", ictx)?;
    let counted: usize = middle.iter().map(|(_, multiplicity)| multiplicity).sum();
    if counted != num_middle_summands {
        return Err(format!(
            "{ictx}: num_middle_summands is {num_middle_summands}, \
             but the summand multiplicities add to {counted}"
        ));
    }
    let totals = middle_totals(&middle, n);
    if totals != middle_dimvec {
        return Err(format!(
            "{ictx}: the summand dimension vectors add to {totals:?}, \
             not to middle_dimvec {middle_dimvec:?}"
        ));
    }
    Ok(ArSequence::Sequence {
        tau,
        middle_dimvec,
        middle,
        num_middle_summands,
    })
}

pub(crate) fn middle_totals(middle: &[(Vec<usize>, usize)], n: usize) -> Vec<usize> {
    let mut totals = vec![0usize; n];
    for (dimvec, multiplicity) in middle {
        for (slot, dimension) in totals.iter_mut().zip(dimvec) {
            *slot += dimension * multiplicity;
        }
    }
    totals
}

pub(crate) fn read_ar_entry_sequence(
    pairs: &[(String, json::Value)],
    n: usize,
    ictx: &str,
) -> Result<ArSequence, String> {
    let projective = match get(pairs, "projective", ictx)? {
        json::Value::Bool(value) => *value,
        other => return Err(format!("{ictx}: projective is {other:?}, expected a bool")),
    };
    if projective {
        check_keys(pairs, &["module", "projective"], ictx)?;
        Ok(ArSequence::Projective)
    } else {
        check_keys(
            pairs,
            &[
                "module",
                "projective",
                "tau",
                "middle_dimvec",
                "middle",
                "num_middle_summands",
            ],
            ictx,
        )?;
        read_ar_middle(pairs, n, ictx)
    }
}

pub(crate) fn read_ar_entry(
    value: &json::Value,
    n: usize,
    designated: &[ModuleRef],
    sequence_index: usize,
    actx: &str,
) -> Result<ArEntry, String> {
    let ictx = format!("{actx}[{sequence_index}]");
    let pairs = as_object(value, &ictx)?;
    let module = read_module_ref(get(pairs, "module", &ictx)?, n, &format!("{ictx} module"))?;
    if module != designated[sequence_index] {
        return Err(format!(
            "{ictx}: module does not match designated entry {sequence_index}"
        ));
    }
    let sequence = read_ar_entry_sequence(pairs, n, &ictx)?;
    Ok(ArEntry { module, sequence })
}

pub(crate) fn read_ar_sequences(
    value: &json::Value,
    n: usize,
    designated: &[ModuleRef],
    ctx: &str,
) -> Result<Vec<ArEntry>, String> {
    let actx = format!("{ctx}: ar_sequences");
    let items = as_array(value, &actx)?;
    if items.len() != designated.len() {
        return Err(format!(
            "{actx} has {} entries, expected {}",
            items.len(),
            designated.len()
        ));
    }
    items
        .iter()
        .enumerate()
        .map(|(t, item)| read_ar_entry(item, n, designated, t, &actx))
        .collect()
}

pub(crate) fn validate_irr_side(
    present: bool,
    total: usize,
    endpoints: &[(Vec<usize>, usize)],
    ctx: &str,
) -> Result<(), String> {
    let counted: usize = endpoints.iter().map(|(_, value)| value).sum();
    if counted != total {
        return Err(format!(
            "{ctx}: total is {total}, but the valuations add to {counted}"
        ));
    }
    if present != (total > 0) {
        return Err(format!("{ctx}: present is {present} with total {total}"));
    }
    Ok(())
}

pub(crate) fn read_irr_side(
    value: &json::Value,
    n: usize,
    endpoint_key: &str,
    ctx: &str,
) -> Result<IrrSide, String> {
    let pairs = as_object(value, ctx)?;
    check_keys(pairs, &["present", "total", endpoint_key], ctx)?;
    let present = match get(pairs, "present", ctx)? {
        json::Value::Bool(b) => *b,
        other => return Err(format!("{ctx}: present is {other:?}, expected a bool")),
    };
    let total = read_usize(pairs, "total", ctx)?;
    let endpoints = read_weighted_dimvecs(
        get(pairs, endpoint_key, ctx)?,
        n,
        "valuation",
        &format!("{ctx} {endpoint_key}"),
    )?;
    validate_irr_side(present, total, &endpoints, ctx)?;
    Ok(IrrSide {
        present,
        total,
        endpoints,
    })
}

pub(crate) fn read_irr_entry(
    value: &json::Value,
    n: usize,
    designated: &[ModuleRef],
    index: usize,
    ictx: &str,
) -> Result<IrrEntry, String> {
    let ectx = format!("{ictx}[{index}]");
    let pairs = as_object(value, &ectx)?;
    check_keys(pairs, &["module", "into", "out_of"], &ectx)?;
    let module = read_module_ref(get(pairs, "module", &ectx)?, n, &format!("{ectx} module"))?;
    if module != designated[index] {
        return Err(format!(
            "{ectx}: module does not match designated entry {index}"
        ));
    }
    let into = read_irr_side(
        get(pairs, "into", &ectx)?,
        n,
        "sources",
        &format!("{ectx} into"),
    )?;
    let out_of = read_irr_side(
        get(pairs, "out_of", &ectx)?,
        n,
        "targets",
        &format!("{ectx} out_of"),
    )?;
    Ok(IrrEntry {
        module,
        into,
        out_of,
    })
}

pub(crate) fn read_irreducible_maps(
    value: &json::Value,
    n: usize,
    designated: &[ModuleRef],
    ctx: &str,
) -> Result<Vec<IrrEntry>, String> {
    let ictx = format!("{ctx}: irreducible_maps");
    let items = as_array(value, &ictx)?;
    if items.len() != designated.len() {
        return Err(format!(
            "{ictx} has {} entries, expected {}",
            items.len(),
            designated.len()
        ));
    }
    items
        .iter()
        .enumerate()
        .map(|(t, item)| read_irr_entry(item, n, designated, t, &ictx))
        .collect()
}

pub(crate) fn read_ext_algebra(value: &json::Value, ctx: &str) -> Result<ExtAlgebra, String> {
    let ectx = format!("{ctx}: ext_algebra");
    let pairs = as_object(value, &ectx)?;
    check_keys(
        pairs,
        &[
            "module",
            "max_degree",
            "dims",
            "min_generators",
            "product_rank",
        ],
        &ectx,
    )?;
    let module = read_str(pairs, "module", &ectx)?;
    if module != EXT_ALGEBRA_MODULE {
        return Err(format!(
            "{ectx}: module is {module:?}, expected {EXT_ALGEBRA_MODULE:?}"
        ));
    }
    let max_degree = read_usize(pairs, "max_degree", &ectx)?;
    if max_degree != MAX_EXT_DEGREE {
        return Err(format!(
            "{ectx}: max_degree is {max_degree}, expected {MAX_EXT_DEGREE}"
        ));
    }
    let (dims, min_generators, product_rank) = read_ext_algebra_rows(pairs, &ectx)?;
    validate_ext_algebra_rows(&dims, &min_generators, &product_rank, &ectx)?;
    Ok(ExtAlgebra {
        dims,
        min_generators,
        product_rank,
    })
}

pub(crate) fn read_ext_algebra_rows(
    pairs: &[(String, json::Value)],
    ectx: &str,
) -> Result<ExtAlgebraRows, String> {
    let width = MAX_EXT_DEGREE + 1;
    let dims = usize_row(get(pairs, "dims", ectx)?, width, &format!("{ectx} dims"))?;
    let min_generators = usize_row(
        get(pairs, "min_generators", ectx)?,
        width,
        &format!("{ectx} min_generators"),
    )?;
    let product_rank = usize_row(
        get(pairs, "product_rank", ectx)?,
        width,
        &format!("{ectx} product_rank"),
    )?;
    Ok((dims, min_generators, product_rank))
}

pub(crate) fn validate_ext_algebra_rows(
    dims: &[usize],
    min_generators: &[usize],
    product_rank: &[usize],
    ectx: &str,
) -> Result<(), String> {
    for k in 0..dims.len() {
        if min_generators[k] + product_rank[k] != dims[k] {
            return Err(format!(
                "{ectx}: degree {k} has dims {}, min_generators {} and product_rank {}, \
                 which do not add up",
                dims[k], min_generators[k], product_rank[k]
            ));
        }
    }
    Ok(())
}

pub(crate) fn read_vertex_index(
    pairs: &[(String, json::Value)],
    key: &str,
    n: usize,
    ctx: &str,
) -> Result<usize, String> {
    let value = read_usize(pairs, key, ctx)?;
    if value >= n {
        return Err(format!("{ctx}: {key} is {value}, not a vertex below {n}"));
    }
    Ok(value)
}

pub(crate) fn read_yoneda_dimensions(
    pairs: &[(String, json::Value)],
    ctx: &str,
) -> Result<(usize, usize, usize, usize), String> {
    Ok((
        read_usize(pairs, "dim_ext1_ij", ctx)?,
        read_usize(pairs, "dim_ext1_jk", ctx)?,
        read_usize(pairs, "dim_ext2_ik", ctx)?,
        read_usize(pairs, "yoneda_map_rank", ctx)?,
    ))
}

pub(crate) fn read_yoneda_product(
    value: &json::Value,
    n: usize,
    yctx: &str,
    index: usize,
) -> Result<YonedaProduct, String> {
    let ectx = format!("{yctx}[{index}]");
    let pairs = as_object(value, &ectx)?;
    check_keys(
        pairs,
        &[
            "i",
            "j",
            "k",
            "dim_ext1_ij",
            "dim_ext1_jk",
            "dim_ext2_ik",
            "yoneda_map_rank",
        ],
        &ectx,
    )?;
    let i = read_vertex_index(pairs, "i", n, &ectx)?;
    let j = read_vertex_index(pairs, "j", n, &ectx)?;
    let k = read_vertex_index(pairs, "k", n, &ectx)?;
    let (dim_ext1_ij, dim_ext1_jk, dim_ext2_ik, yoneda_map_rank) =
        read_yoneda_dimensions(pairs, &ectx)?;
    if dim_ext1_ij == 0 || dim_ext1_jk == 0 {
        return Err(format!("{ectx}: a factor of the product is zero"));
    }
    if yoneda_map_rank > dim_ext2_ik {
        return Err(format!(
            "{ectx}: yoneda_map_rank {yoneda_map_rank} exceeds dim_ext2_ik {dim_ext2_ik}"
        ));
    }
    Ok(YonedaProduct {
        i,
        j,
        k,
        dim_ext1_ij,
        dim_ext1_jk,
        dim_ext2_ik,
        yoneda_map_rank,
    })
}

pub(crate) fn read_yoneda_products(
    value: &json::Value,
    n: usize,
    ctx: &str,
) -> Result<Vec<YonedaProduct>, String> {
    let yctx = format!("{ctx}: yoneda_products");
    let items = as_array(value, &yctx)?;
    let mut out: Vec<YonedaProduct> = Vec::with_capacity(items.len());
    for (t, item) in items.iter().enumerate() {
        let entry = read_yoneda_product(item, n, &yctx, t)?;
        if let Some(prev) = out.last()
            && (prev.i, prev.j, prev.k) >= (entry.i, entry.j, entry.k)
        {
            return Err(format!("{yctx}: triples are not strictly ascending at {t}"));
        }
        out.push(entry);
    }
    Ok(out)
}

pub(crate) fn read_bool_list(
    value: &json::Value,
    len: usize,
    label: &str,
    ctx: &str,
) -> Result<Vec<bool>, String> {
    let bctx = format!("{ctx}: {label}");
    let items = as_array(value, &bctx)?;
    if items.len() != len {
        return Err(format!(
            "{bctx} has {} entries, expected {len}",
            items.len()
        ));
    }
    items
        .iter()
        .map(|item| match item {
            json::Value::Bool(b) => Ok(*b),
            other => Err(format!("{bctx}: {other:?} is not a bool")),
        })
        .collect()
}

pub(crate) fn read_tau_period_entry(
    value: &json::Value,
    tctx: &str,
    index: usize,
    bound: &mut Option<usize>,
) -> Result<TauPeriod, String> {
    let ectx = format!("{tctx}[{index}]");
    let pairs = as_object(value, &ectx)?;
    if pairs.len() != 1 {
        return Err(format!(
            "{ectx}: expected exactly one of period or none_up_to"
        ));
    }
    let (key, inner) = &pairs[0];
    let degree = usize_value(inner, &ectx)?;
    match key.as_str() {
        "period" => {
            if degree == 0 {
                return Err(format!("{ectx}: period is 0"));
            }
            Ok(TauPeriod::Period(degree))
        }
        "none_up_to" => {
            if let Some(previous) = *bound
                && previous != degree
            {
                return Err(format!("{tctx}: bounds {previous} and {degree} disagree"));
            }
            *bound = Some(degree);
            Ok(TauPeriod::NoneUpTo(degree))
        }
        other => Err(format!("{ectx}: unknown key {other:?}")),
    }
}

pub(crate) fn validate_tau_periods(
    out: &[TauPeriod],
    bound: usize,
    tctx: &str,
) -> Result<(), String> {
    for (index, entry) in out.iter().enumerate() {
        if let TauPeriod::Period(period) = entry
            && *period > bound
        {
            return Err(format!(
                "{tctx}[{index}]: period {period} exceeds the bound {bound}"
            ));
        }
    }
    Ok(())
}

/// Reads the `tau_period` list and the bound it was computed with. Every
/// `none_up_to` entry must name the same bound, and no period may exceed it.
/// At least one entry must be `none_up_to`: the designated list always holds
/// the indecomposable projectives, whose translate is zero, so no projective
/// is ever periodic.
pub(crate) fn read_tau_period(
    value: &json::Value,
    len: usize,
    ctx: &str,
) -> Result<(Vec<TauPeriod>, usize), String> {
    let tctx = format!("{ctx}: tau_period");
    let items = as_array(value, &tctx)?;
    if items.len() != len {
        return Err(format!(
            "{tctx} has {} entries, expected {len}",
            items.len()
        ));
    }
    let mut out = Vec::with_capacity(items.len());
    let mut bound: Option<usize> = None;
    for (t, item) in items.iter().enumerate() {
        out.push(read_tau_period_entry(item, &tctx, t, &mut bound)?);
    }
    let Some(bound) = bound else {
        return Err(format!(
            "{tctx}: no none_up_to entry names the search bound"
        ));
    };
    validate_tau_periods(&out, bound, &tctx)?;
    Ok((out, bound))
}

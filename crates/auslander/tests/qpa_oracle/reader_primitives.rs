pub(crate) fn as_object<'a>(
    value: &'a json::Value,
    ctx: &str,
) -> Result<&'a [(String, json::Value)], String> {
    match value {
        json::Value::Obj(pairs) => Ok(pairs),
        other => Err(format!("{ctx}: {other:?} is not an object")),
    }
}

pub(crate) fn as_array<'a>(value: &'a json::Value, ctx: &str) -> Result<&'a [json::Value], String> {
    value
        .as_arr()
        .ok_or_else(|| format!("{ctx}: expected an array"))
}

pub(crate) fn check_keys(
    pairs: &[(String, json::Value)],
    allowed: &[&str],
    ctx: &str,
) -> Result<(), String> {
    for (key, _) in pairs {
        if !allowed.contains(&key.as_str()) {
            return Err(format!("{ctx}: unknown key {key:?}"));
        }
    }
    Ok(())
}

pub(crate) fn get<'a>(
    pairs: &'a [(String, json::Value)],
    key: &str,
    ctx: &str,
) -> Result<&'a json::Value, String> {
    pairs
        .iter()
        .find(|(k, _)| k == key)
        .map(|(_, v)| v)
        .ok_or_else(|| format!("{ctx}: missing {key}"))
}

pub(crate) fn read_str(
    pairs: &[(String, json::Value)],
    key: &str,
    ctx: &str,
) -> Result<String, String> {
    match get(pairs, key, ctx)? {
        json::Value::Str(s) if !s.is_empty() => Ok(s.clone()),
        json::Value::Str(_) => Err(format!("{ctx}: {key} is empty")),
        other => Err(format!("{ctx}: {key} is {other:?}, expected a string")),
    }
}

pub(crate) fn usize_value(value: &json::Value, ctx: &str) -> Result<usize, String> {
    value
        .as_usize()
        .ok_or_else(|| format!("{ctx}: {value:?} is not a non-negative integer"))
}

pub(crate) fn read_usize(
    pairs: &[(String, json::Value)],
    key: &str,
    ctx: &str,
) -> Result<usize, String> {
    usize_value(get(pairs, key, ctx)?, &format!("{ctx}: {key}"))
}

pub(crate) fn usize_row(
    value: &json::Value,
    expected_len: usize,
    ctx: &str,
) -> Result<Vec<usize>, String> {
    let items = as_array(value, ctx)?;
    if items.len() != expected_len {
        return Err(format!(
            "{ctx} has {} entries, expected {expected_len}",
            items.len()
        ));
    }
    items.iter().map(|item| usize_value(item, ctx)).collect()
}

pub(crate) fn read_matrix(
    value: &json::Value,
    rows: usize,
    cols: usize,
    label: &str,
    ctx: &str,
) -> Result<Vec<Vec<usize>>, String> {
    let items = as_array(value, &format!("{ctx}: {label}"))?;
    if items.len() != rows {
        return Err(format!(
            "{ctx}: {label} has {} rows, expected {rows}",
            items.len()
        ));
    }
    items
        .iter()
        .enumerate()
        .map(|(i, row)| usize_row(row, cols, &format!("{ctx}: {label} row {i}")))
        .collect()
}

pub(crate) fn read_outcome(
    value: &json::Value,
    bound: usize,
    ctx: &str,
) -> Result<DimOutcome, String> {
    let pairs = as_object(value, ctx)?;
    if pairs.len() != 1 {
        return Err(format!("{ctx}: expected exactly one of finite or at_least"));
    }
    let (key, inner) = &pairs[0];
    let d = usize_value(inner, ctx)?;
    match key.as_str() {
        "finite" => {
            if d > bound {
                Err(format!("{ctx}: finite value {d} exceeds bound {bound}"))
            } else {
                Ok(DimOutcome::Finite(d))
            }
        }
        "at_least" => {
            if d != bound + 1 {
                Err(format!("{ctx}: at_least is {d}, expected {}", bound + 1))
            } else {
                Ok(DimOutcome::AtLeast(d))
            }
        }
        other => Err(format!("{ctx}: unknown key {other:?}")),
    }
}

pub(crate) fn read_outcomes(
    value: &json::Value,
    n: usize,
    bound: usize,
    label: &str,
    ctx: &str,
) -> Result<Vec<DimOutcome>, String> {
    let items = as_array(value, &format!("{ctx}: {label}"))?;
    if items.len() != n {
        return Err(format!(
            "{ctx}: {label} has {} entries, expected {n}",
            items.len()
        ));
    }
    items
        .iter()
        .enumerate()
        .map(|(i, item)| read_outcome(item, bound, &format!("{ctx}: {label}[{i}]")))
        .collect()
}

pub(crate) fn read_tau_outcome(
    value: &json::Value,
    n: usize,
    ctx: &str,
) -> Result<TauOutcome, String> {
    let pairs = as_object(value, ctx)?;
    if pairs.len() != 1 {
        return Err(format!(
            "{ctx}: expected exactly one of projective or dimvec"
        ));
    }
    let (key, inner) = &pairs[0];
    match key.as_str() {
        "projective" => match inner {
            json::Value::Bool(true) => Ok(TauOutcome::Projective),
            _ => Err(format!("{ctx}: projective must be true")),
        },
        "dimvec" => Ok(TauOutcome::Dimvec(usize_row(
            inner,
            n,
            &format!("{ctx} dimvec"),
        )?)),
        other => Err(format!("{ctx}: unknown key {other:?}")),
    }
}

pub(crate) fn read_tau_list(
    value: &json::Value,
    n: usize,
    label: &str,
    ctx: &str,
) -> Result<Vec<TauOutcome>, String> {
    let items = as_array(value, &format!("{ctx}: {label}"))?;
    if items.len() != n {
        return Err(format!(
            "{ctx}: {label} has {} entries, expected {n}",
            items.len()
        ));
    }
    items
        .iter()
        .enumerate()
        .map(|(i, item)| read_tau_outcome(item, n, &format!("{ctx}: {label}[{i}]")))
        .collect()
}

pub(crate) fn read_arrow(
    value: &json::Value,
    num_vertices: u32,
    arrows: &[ArrowSpec],
    qctx: &str,
    index: usize,
) -> Result<ArrowSpec, String> {
    let actx = format!("{qctx}: arrow {index}");
    let pairs = as_object(value, &actx)?;
    check_keys(pairs, &["name", "source", "target"], &actx)?;
    let name = read_str(pairs, "name", &actx)?;
    let source = read_usize(pairs, "source", &actx)?;
    let target = read_usize(pairs, "target", &actx)?;
    for (endpoint, vertex) in [("source", source), ("target", target)] {
        if vertex >= num_vertices as usize {
            return Err(format!(
                "{actx}: {endpoint} {vertex} is not a vertex below {num_vertices}"
            ));
        }
    }
    if arrows.iter().any(|arrow| arrow.name == name) {
        return Err(format!("{actx}: duplicate arrow name {name:?}"));
    }
    Ok(ArrowSpec {
        name,
        source: source as u32,
        target: target as u32,
    })
}

pub(crate) fn read_quiver(value: &json::Value, ctx: &str) -> Result<QuiverSpec, String> {
    let qctx = format!("{ctx}: quiver");
    let pairs = as_object(value, &qctx)?;
    check_keys(pairs, &["num_vertices", "arrows"], &qctx)?;
    let num_vertices = read_usize(pairs, "num_vertices", &qctx)?;
    if num_vertices == 0 {
        return Err(format!("{qctx}: num_vertices is 0"));
    }
    let num_vertices = u32::try_from(num_vertices)
        .map_err(|_| format!("{qctx}: num_vertices does not fit u32"))?;
    let items = as_array(get(pairs, "arrows", &qctx)?, &qctx)?;
    let mut arrows: Vec<ArrowSpec> = Vec::with_capacity(items.len());
    for (i, item) in items.iter().enumerate() {
        arrows.push(read_arrow(item, num_vertices, &arrows, &qctx, i)?);
    }
    Ok(QuiverSpec {
        num_vertices,
        arrows,
    })
}

pub(crate) fn read_relation_term(
    value: &json::Value,
    num_arrows: usize,
    ictx: &str,
    index: usize,
) -> Result<TermSpec, String> {
    let tctx = format!("{ictx} term {index}");
    let pairs = as_object(value, &tctx)?;
    check_keys(pairs, &["coeff", "path"], &tctx)?;
    let coeff = match get(pairs, "coeff", &tctx)? {
        json::Value::Num(n) => *n,
        other => return Err(format!("{tctx}: coeff is {other:?}, expected an integer")),
    };
    let path_items = as_array(get(pairs, "path", &tctx)?, &tctx)?;
    if path_items.is_empty() {
        return Err(format!("{tctx}: path is empty"));
    }
    let path = path_items
        .iter()
        .map(|item| {
            let arrow = usize_value(item, &tctx)?;
            if arrow >= num_arrows {
                return Err(format!(
                    "{tctx}: arrow index {arrow} is not below {num_arrows}"
                ));
            }
            Ok(arrow as u32)
        })
        .collect::<Result<Vec<_>, String>>()?;
    Ok(TermSpec { coeff, path })
}

pub(crate) fn read_relation(
    value: &json::Value,
    num_arrows: usize,
    rctx: &str,
    index: usize,
) -> Result<Vec<TermSpec>, String> {
    let ictx = format!("{rctx} entry {index}");
    let pairs = as_object(value, &ictx)?;
    check_keys(pairs, &["terms"], &ictx)?;
    let term_items = as_array(get(pairs, "terms", &ictx)?, &ictx)?;
    if term_items.is_empty() {
        return Err(format!("{ictx}: terms is empty"));
    }
    term_items
        .iter()
        .enumerate()
        .map(|(j, item)| read_relation_term(item, num_arrows, &ictx, j))
        .collect()
}

pub(crate) fn read_relations(
    value: &json::Value,
    num_arrows: usize,
    ctx: &str,
) -> Result<Vec<Vec<TermSpec>>, String> {
    let rctx = format!("{ctx}: relations");
    let items = as_array(value, &rctx)?;
    items
        .iter()
        .enumerate()
        .map(|(i, item)| read_relation(item, num_arrows, &rctx, i))
        .collect()
}

/// A list of dimension vectors with a positive weight each, sorted
/// lexicographically ascending with equal dimension vectors merged. The
/// weight key is `multiplicity` for Krull-Schmidt summands and `valuation`
/// for irreducible morphisms.
pub(crate) fn read_weighted_dimvecs(
    value: &json::Value,
    n: usize,
    weight_key: &str,
    ctx: &str,
) -> Result<Vec<(Vec<usize>, usize)>, String> {
    let items = as_array(value, ctx)?;
    let mut entries: Vec<(Vec<usize>, usize)> = Vec::with_capacity(items.len());
    for (i, item) in items.iter().enumerate() {
        let (dimvec, weight) = read_weighted_entry(item, n, weight_key, ctx, i)?;
        check_weighted_order(entries.last(), &dimvec, ctx, i)?;
        entries.push((dimvec, weight));
    }
    Ok(entries)
}

pub(crate) fn read_weighted_entry(
    value: &json::Value,
    n: usize,
    weight_key: &str,
    ctx: &str,
    index: usize,
) -> Result<(Vec<usize>, usize), String> {
    let sctx = format!("{ctx} entry {index}");
    let pairs = as_object(value, &sctx)?;
    check_keys(pairs, &["dimvec", weight_key], &sctx)?;
    let dimvec = usize_row(get(pairs, "dimvec", &sctx)?, n, &format!("{sctx} dimvec"))?;
    let weight = read_usize(pairs, weight_key, &sctx)?;
    if weight == 0 {
        return Err(format!("{sctx}: {weight_key} is 0"));
    }
    Ok((dimvec, weight))
}

pub(crate) fn check_weighted_order(
    previous: Option<&(Vec<usize>, usize)>,
    dimvec: &[usize],
    ctx: &str,
    index: usize,
) -> Result<(), String> {
    let Some((previous, _)) = previous else {
        return Ok(());
    };
    match previous.as_slice().cmp(dimvec) {
        std::cmp::Ordering::Less => Ok(()),
        std::cmp::Ordering::Equal => Err(format!("{ctx}: entries repeat dimvec at entry {index}")),
        std::cmp::Ordering::Greater => Err(format!(
            "{ctx}: entries are not sorted ascending at entry {index}"
        )),
    }
}

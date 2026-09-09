pub(crate) fn read_tilting_header(
    pairs: &[(String, json::Value)],
    ictx: &str,
) -> Result<(bool, usize, Option<usize>), String> {
    let qpa_tilting = read_bool(pairs, "qpa_tilting", ictx)?;
    let short = [
        "id",
        "construction",
        "bound",
        "module_dimvec",
        "qpa_tilting",
    ];
    let full = [
        "id",
        "construction",
        "bound",
        "module_dimvec",
        "qpa_tilting",
        "projective_dimension",
        "coresolutions",
        "coresolutions_exact",
        "target",
    ];
    check_keys(pairs, if qpa_tilting { &full } else { &short }, ictx)?;
    let projective_dimension = qpa_tilting
        .then(|| read_usize(pairs, "projective_dimension", ictx))
        .transpose()?;
    let bound = read_usize(pairs, "bound", ictx)?;
    if projective_dimension.is_some_and(|pd| pd > bound) {
        return Err(format!(
            "{ictx}: projective dimension exceeds the recorded bound {bound}"
        ));
    }
    Ok((qpa_tilting, bound, projective_dimension))
}

pub(crate) fn read_coresolution_row(
    value: &json::Value,
    n: usize,
    max_terms: usize,
    cctx: &str,
    index: usize,
) -> Result<Vec<Vec<usize>>, String> {
    let jctx = format!("{cctx} entry {index}");
    let terms = as_array(value, &jctx)?;
    if terms.is_empty() || terms.len() > max_terms {
        return Err(format!(
            "{jctx} has {} terms, expected between 1 and {}",
            terms.len(),
            max_terms
        ));
    }
    terms
        .iter()
        .enumerate()
        .map(|(term_index, term)| usize_row(term, n, &format!("{jctx} term {term_index}")))
        .collect()
}

pub(crate) fn read_coresolutions(
    pairs: &[(String, json::Value)],
    n: usize,
    ictx: &str,
    projective_dimension: usize,
) -> Result<CoresolutionValues, String> {
    let max_terms = projective_dimension
        .checked_add(2)
        .ok_or_else(|| format!("{ictx}: coresolution length overflows usize"))?;
    let cctx = format!("{ictx}: coresolutions");
    let rows = as_array(get(pairs, "coresolutions", ictx)?, &cctx)?;
    if rows.len() != n {
        return Err(format!("{cctx} has {} entries, expected {n}", rows.len()));
    }
    let complexes = rows
        .iter()
        .enumerate()
        .map(|(index, row)| read_coresolution_row(row, n, max_terms, &cctx, index))
        .collect::<Result<Vec<_>, _>>()?;
    let exact = read_bool_list(
        get(pairs, "coresolutions_exact", ictx)?,
        n,
        "coresolutions_exact",
        ictx,
    )?;
    if exact.iter().any(|&value| !value) {
        return Err(format!(
            "{ictx}: qpa_tilting requires every coresolution to be exact"
        ));
    }
    Ok((complexes, exact))
}

pub(crate) fn read_tilting_identity(
    pairs: &[(String, json::Value)],
    n: usize,
    ictx: &str,
) -> Result<(String, String, Vec<usize>), String> {
    let id = read_str(pairs, "id", ictx)?;
    let construction = read_str(pairs, "construction", ictx)?;
    let module_dimvec = usize_row(
        get(pairs, "module_dimvec", ictx)?,
        n,
        &format!("{ictx}: module_dimvec"),
    )?;
    Ok((id, construction, module_dimvec))
}

pub(crate) fn read_classical_tilting_entry(
    value: &json::Value,
    n: usize,
    ctx: &str,
    index: usize,
) -> Result<ClassicalTiltingRecord, String> {
    let ictx = format!("{ctx} entry {index}");
    let pairs = as_object(value, &ictx)?;
    let (qpa_tilting, bound, projective_dimension) = read_tilting_header(pairs, &ictx)?;
    let (coresolutions, coresolutions_exact) = match projective_dimension {
        Some(pd) => read_coresolutions(pairs, n, &ictx, pd)?,
        None => (Vec::new(), Vec::new()),
    };
    let (id, construction, module_dimvec) = read_tilting_identity(pairs, n, &ictx)?;
    let target = projective_dimension
        .is_some()
        .then(|| read_target_oracle(get(pairs, "target", &ictx)?, n, &format!("{ictx}: target")))
        .transpose()?;
    Ok(ClassicalTiltingRecord {
        id,
        construction,
        bound,
        module_dimvec,
        qpa_tilting,
        projective_dimension,
        coresolutions,
        coresolutions_exact,
        target,
    })
}

pub(crate) fn read_classical_tilting(
    value: &json::Value,
    n: usize,
    ctx: &str,
) -> Result<Vec<ClassicalTiltingRecord>, String> {
    let items = as_array(value, ctx)?;
    let mut out = items
        .iter()
        .enumerate()
        .map(|(index, item)| read_classical_tilting_entry(item, n, ctx, index))
        .collect::<Result<Vec<_>, _>>()?;
    out.sort_by(|a, b| a.id.cmp(&b.id));
    if out.windows(2).any(|w| w[0].id == w[1].id) {
        return Err(format!("{ctx} has a duplicate candidate id"));
    }
    Ok(out)
}

pub(crate) fn read_fixture_identity(
    pairs: &[(String, json::Value)],
    case: &str,
    ctx: &str,
) -> Result<(u64, String, String), String> {
    let field = read_usize(pairs, "field", ctx)? as u64;
    PrimeField::new(field).map_err(|e| format!("{ctx}: field {field} rejected: {e}"))?;
    if case != format!("f{field}") {
        return Err(format!("{ctx}: case {case:?} does not name field {field}"));
    }
    let presentation_id = read_str(pairs, "presentation_id", ctx)?;
    let ideal_id = read_str(pairs, "ideal_id", ctx)?;
    let order = read_str(pairs, "order", ctx)?;
    if order != ORDER_ID {
        return Err(format!("{ctx}: order is {order:?}, expected {ORDER_ID:?}"));
    }
    Ok((field, presentation_id, ideal_id))
}

pub(crate) fn check_fixture_keys(
    pairs: &[(String, json::Value)],
    v8: bool,
    ctx: &str,
) -> Result<(), String> {
    let keys = if v8 {
        &FIXTURE_KEYS[..]
    } else {
        &FIXTURE_KEYS[..FIXTURE_KEYS.len() - 2]
    };
    check_keys(pairs, keys, ctx)
}

pub(crate) fn read_fixture_header<'a>(
    value: &'a json::Value,
    index: usize,
    v8: bool,
) -> Result<FixtureHeader<'a>, String> {
    let fallback = format!("fixture {index}");
    let pairs = as_object(value, &fallback)?;
    let family = read_str(pairs, "family", &fallback)?;
    let case = read_str(pairs, "case", &fallback)?;
    let ctx = format!("{family}/{case}");
    check_fixture_keys(pairs, v8, &ctx)?;
    let (field, presentation_id, ideal_id) = read_fixture_identity(pairs, &case, &ctx)?;
    let quiver = read_quiver(get(pairs, "quiver", &ctx)?, &ctx)?;
    let relations = read_relations(get(pairs, "relations", &ctx)?, quiver.arrows.len(), &ctx)?;
    Ok(FixtureHeader {
        pairs,
        family,
        case,
        field,
        presentation_id,
        ideal_id,
        quiver,
        relations,
    })
}

pub(crate) fn read_fixture_v8_details(
    pairs: &[(String, json::Value)],
    n: usize,
    ctx: &str,
    v8: bool,
    tau_rigid: &[bool],
) -> Result<(Option<SupportTauTilting>, Vec<ClassicalTiltingRecord>), String> {
    let stt = v8
        .then(|| {
            read_support_tau_tilting(get(pairs, "support_tau_tilting", ctx)?, n, tau_rigid, ctx)
        })
        .transpose()?;
    let classical_tilting = if v8 {
        read_classical_tilting(
            get(pairs, "classical_tilting", ctx)?,
            n,
            &format!("{ctx}: classical_tilting"),
        )?
    } else {
        Vec::new()
    };
    Ok((stt, classical_tilting))
}

pub(crate) fn read_fixture_details(
    pairs: &[(String, json::Value)],
    n: usize,
    ctx: &str,
    v8: bool,
) -> Result<FixtureDetails, String> {
    let designated = read_designated(get(pairs, "designated_modules", ctx)?, n, ctx)?;
    let width = designated.len();
    let (tau_period, tau_period_bound) =
        read_tau_period(get(pairs, "tau_period", ctx)?, width, ctx)?;
    let cartan = read_matrix(get(pairs, "cartan", ctx)?, n, n, "cartan", ctx)?;
    let tau_rigid = read_bool_list(get(pairs, "tau_rigid", ctx)?, width, "tau_rigid", ctx)?;
    let (stt, classical_tilting) = read_fixture_v8_details(pairs, n, ctx, v8, &tau_rigid)?;
    Ok(FixtureDetails {
        cartan,
        designated,
        tau_period,
        tau_period_bound,
        tau_rigid,
        stt,
        classical_tilting,
    })
}

pub(crate) fn read_fixture_dimension_values(
    pairs: &[(String, json::Value)],
    n: usize,
    ctx: &str,
) -> Result<FixtureDimensionValues, String> {
    Ok((
        read_usize(pairs, "dim", ctx)?,
        read_matrix(get(pairs, "injectives", ctx)?, n, n, "injectives", ctx)?,
        read_outcomes(
            get(pairs, "projdim", ctx)?,
            n,
            PROJDIM_BOUND,
            "projdim",
            ctx,
        )?,
        read_outcomes(get(pairs, "injdim", ctx)?, n, INJDIM_BOUND, "injdim", ctx)?,
    ))
}

pub(crate) fn read_fixture_translate_values(
    pairs: &[(String, json::Value)],
    n: usize,
    ctx: &str,
) -> Result<FixtureTranslateValues, String> {
    Ok((
        read_tau_list(get(pairs, "tau", ctx)?, n, "tau", ctx)?,
        read_tau_list(get(pairs, "tau_injectives", ctx)?, n, "tau_injectives", ctx)?,
        read_decomposition(get(pairs, "decomposition", ctx)?, n, ctx)?,
        read_ext(get(pairs, "ext", ctx)?, n, ctx)?,
    ))
}

pub(crate) fn read_fixture_core_values(
    pairs: &[(String, json::Value)],
    n: usize,
    ctx: &str,
) -> Result<FixtureCoreValues, String> {
    let (dim, injectives, projdim, injdim) = read_fixture_dimension_values(pairs, n, ctx)?;
    let (tau, tau_injectives, decomposition, ext) = read_fixture_translate_values(pairs, n, ctx)?;
    Ok(FixtureCoreValues {
        dim,
        injectives,
        projdim,
        injdim,
        tau,
        tau_injectives,
        decomposition,
        ext,
    })
}

pub(crate) fn read_fixture_ar_structures(
    pairs: &[(String, json::Value)],
    n: usize,
    designated: &[ModuleRef],
    ctx: &str,
) -> Result<FixtureArStructures, String> {
    Ok((
        read_ar_sequences(get(pairs, "ar_sequences", ctx)?, n, designated, ctx)?,
        read_irreducible_maps(get(pairs, "irreducible_maps", ctx)?, n, designated, ctx)?,
        read_ext_algebra(get(pairs, "ext_algebra", ctx)?, ctx)?,
        read_yoneda_products(get(pairs, "yoneda_products", ctx)?, n, ctx)?,
    ))
}

pub(crate) fn read_fixture_hom_values(
    pairs: &[(String, json::Value)],
    width: usize,
    ctx: &str,
) -> Result<(Vec<Vec<usize>>, Vec<bool>), String> {
    Ok((
        read_matrix(
            get(pairs, "stable_hom", ctx)?,
            width,
            width,
            "stable_hom",
            ctx,
        )?,
        read_bool_list(get(pairs, "rigid", ctx)?, width, "rigid", ctx)?,
    ))
}

pub(crate) fn read_fixture_ar_values(
    pairs: &[(String, json::Value)],
    n: usize,
    width: usize,
    designated: &[ModuleRef],
    ctx: &str,
) -> Result<FixtureArValues, String> {
    let (ar_sequences, irreducible_maps, ext_algebra, yoneda_products) =
        read_fixture_ar_structures(pairs, n, designated, ctx)?;
    let (stable_hom, rigid) = read_fixture_hom_values(pairs, width, ctx)?;
    Ok(FixtureArValues {
        ar_sequences,
        irreducible_maps,
        ext_algebra,
        yoneda_products,
        stable_hom,
        rigid,
    })
}

pub(crate) fn read_fixture(value: &json::Value, index: usize, v8: bool) -> Result<Fixture, String> {
    let header = read_fixture_header(value, index, v8)?;
    let ctx = format!("{}/{}", header.family, header.case);
    let n = header.quiver.num_vertices as usize;
    let details = read_fixture_details(header.pairs, n, &ctx, v8)?;
    let width = details.designated.len();
    let core = read_fixture_core_values(header.pairs, n, &ctx)?;
    let ar = read_fixture_ar_values(header.pairs, n, width, &details.designated, &ctx)?;
    Ok(Fixture {
        dim: core.dim,
        cartan: details.cartan,
        injectives: core.injectives,
        projdim: core.projdim,
        injdim: core.injdim,
        tau: core.tau,
        tau_injectives: core.tau_injectives,
        decomposition: core.decomposition,
        ext: core.ext,
        designated: details.designated,
        ar_sequences: ar.ar_sequences,
        irreducible_maps: ar.irreducible_maps,
        ext_algebra: ar.ext_algebra,
        yoneda_products: ar.yoneda_products,
        stable_hom: ar.stable_hom,
        tau_rigid: details.tau_rigid,
        rigid: ar.rigid,
        tau_period: details.tau_period,
        stt: details.stt,
        classical_tilting: details.classical_tilting,
        tau_period_bound: details.tau_period_bound,
        family: header.family,
        case: header.case,
        field: header.field,
        presentation_id: header.presentation_id,
        ideal_id: header.ideal_id,
        quiver: header.quiver,
        relations: header.relations,
    })
}

/// Two fixtures share a presentation_id if and only if their quiver and
/// relations are byte-identical (README, "Identity fields").
pub(crate) fn check_presentation_ids(fixtures: &[Fixture]) -> Result<(), String> {
    for (i, a) in fixtures.iter().enumerate() {
        for b in &fixtures[i + 1..] {
            let same_presentation = a.quiver == b.quiver && a.relations == b.relations;
            let same_id = a.presentation_id == b.presentation_id;
            if same_id && !same_presentation {
                return Err(format!(
                    "fixtures {}/{} and {}/{} share presentation_id {:?} but their presentations differ",
                    a.family, a.case, b.family, b.case, a.presentation_id
                ));
            }
            if !same_id && same_presentation {
                return Err(format!(
                    "fixtures {}/{} and {}/{} have identical presentations under different presentation_ids",
                    a.family, a.case, b.family, b.case
                ));
            }
        }
    }
    Ok(())
}

/// Requires every designated candidate once, on its construction fixture.
pub(crate) fn check_classical_tilting_manifest(fixtures: &[Fixture]) -> Result<(), String> {
    for &(family, case, id, construction, bound) in &CLASSICAL_TILTING_MANIFEST {
        let Some(fixture) = fixtures
            .iter()
            .find(|fixture| fixture.family == family && fixture.case == case)
        else {
            return Err(format!(
                "classical tilting candidate {id:?} requires fixture {family}/{case}"
            ));
        };
        let Some(record) = fixture
            .classical_tilting
            .iter()
            .find(|record| record.id == id)
        else {
            return Err(format!(
                "{family}/{case}: missing classical tilting candidate {id:?}"
            ));
        };
        if record.construction != construction {
            return Err(format!(
                "{family}/{case}: candidate {id:?} construction is {:?}, expected {construction:?}",
                record.construction
            ));
        }
        if record.bound != bound {
            return Err(format!(
                "{family}/{case}: candidate {id:?} bound is {}, expected {bound}",
                record.bound
            ));
        }
        if !record.qpa_tilting {
            return Err(format!(
                "{family}/{case}: designated candidate {id:?} is not QPA tilting"
            ));
        }
    }
    for fixture in fixtures {
        for record in &fixture.classical_tilting {
            if !CLASSICAL_TILTING_MANIFEST
                .iter()
                .any(|&(family, case, id, _, _)| {
                    fixture.family == family && fixture.case == case && record.id == id
                })
            {
                return Err(format!(
                    "{}/{}: classical tilting candidate {:?} is not in the oracle manifest",
                    fixture.family, fixture.case, record.id
                ));
            }
        }
    }
    Ok(())
}

pub(crate) fn read_document_bounds(
    pairs: &[(String, json::Value)],
    ctx: &str,
) -> Result<(), String> {
    for (key, expected) in [
        ("max_ext_degree", MAX_EXT_DEGREE),
        ("projdim_bound", PROJDIM_BOUND),
        ("injdim_bound", INJDIM_BOUND),
    ] {
        let value = read_usize(pairs, key, ctx)?;
        if value != expected {
            return Err(format!("{ctx}: {key} is {value}, expected {expected}"));
        }
    }
    Ok(())
}

pub(crate) fn read_document_provenance(
    pairs: &[(String, json::Value)],
    ctx: &str,
) -> Result<Vec<(String, String)>, String> {
    let pctx = "provenance";
    let ppairs = as_object(get(pairs, "provenance", ctx)?, pctx)?;
    check_keys(ppairs, &PROVENANCE_KEYS, pctx)?;
    PROVENANCE_KEYS
        .iter()
        .map(|key| Ok((key.to_string(), read_str(ppairs, key, pctx)?)))
        .collect()
}

pub(crate) fn read_document_metadata(
    pairs: &[(String, json::Value)],
    expected: &str,
    ctx: &str,
) -> Result<DocumentMetadata, String> {
    check_keys(pairs, &ROOT_KEYS, ctx)?;
    let schema = read_str(pairs, "schema", ctx)?;
    if schema != expected {
        return Err(format!(
            "{ctx}: schema is {schema:?}, expected {expected:?}"
        ));
    }
    let v8 = expected == SCHEMA;
    let left_convention = match read_str(pairs, "convention", ctx)?.as_str() {
        "right" => false,
        "left" => true,
        other => {
            return Err(format!(
                "{ctx}: convention is {other:?}, expected \"left\" or \"right\""
            ));
        }
    };
    read_document_bounds(pairs, ctx)?;
    let provenance = read_document_provenance(pairs, ctx)?;
    Ok((v8, left_convention, provenance))
}

pub(crate) fn read_document_fixtures(
    pairs: &[(String, json::Value)],
    v8: bool,
    ctx: &str,
) -> Result<Vec<Fixture>, String> {
    let items = as_array(get(pairs, "fixtures", ctx)?, ctx)?;
    let fixtures = items
        .iter()
        .enumerate()
        .map(|(i, item)| read_fixture(item, i, v8))
        .collect::<Result<Vec<_>, String>>()?;
    for (i, fx) in fixtures.iter().enumerate() {
        if fixtures[..i]
            .iter()
            .any(|other| other.family == fx.family && other.case == fx.case)
        {
            return Err(format!("duplicate fixture {}/{}", fx.family, fx.case));
        }
    }
    Ok(fixtures)
}

/// Parses and validates a document against exactly one schema string, `SCHEMA`
/// for the oracle and `SNAPSHOT_SCHEMA` for the native snapshot. Every
/// structural defect is an error: wrong schema string, unknown or missing
/// keys, wrong pinned bounds, malformed presentations, malformed typed
/// outcomes, unsorted or unmerged decomposition summands, duplicate fixtures,
/// inconsistent presentation ids, and every cross-check inside the oracle block.
/// A stale document fails loudly instead of silently skipping checks.
pub(crate) fn parse_document(text: &str, expected: &str) -> Result<Document, String> {
    let root = json::parse(text)?;
    let ctx = "document";
    let pairs = as_object(&root, ctx)?;
    let (v8, left_convention, provenance) = read_document_metadata(pairs, expected, ctx)?;
    let fixtures = read_document_fixtures(pairs, v8, ctx)?;
    check_presentation_ids(&fixtures)?;
    if v8 {
        check_classical_tilting_manifest(&fixtures)?;
    }
    Ok(Document {
        left_convention,
        provenance,
        fixtures,
    })
}

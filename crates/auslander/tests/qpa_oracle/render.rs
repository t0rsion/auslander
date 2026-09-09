pub(crate) fn oracle_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/qpa-oracle")
}

pub(crate) fn committed_text() -> String {
    let path = oracle_dir().join("qpa_expected.json");
    fs::read_to_string(&path).unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()))
}

pub(crate) fn committed_doc() -> Document {
    parse_document(&committed_text(), SCHEMA)
        .unwrap_or_else(|e| panic!("qpa_expected.json rejected: {e}"))
}

pub(crate) fn int_row(row: &[usize]) -> String {
    let items: Vec<String> = row.iter().map(usize::to_string).collect();
    format!("[{}]", items.join(", "))
}

pub(crate) fn int_matrix(mat: &[Vec<usize>]) -> String {
    let rows: Vec<String> = mat.iter().map(|r| int_row(r)).collect();
    format!("[{}]", rows.join(", "))
}

pub(crate) fn outcome_json(outcome: &DimOutcome) -> String {
    match outcome {
        DimOutcome::Finite(d) => format!("{{\"finite\": {d}}}"),
        DimOutcome::AtLeast(d) => format!("{{\"at_least\": {d}}}"),
    }
}

pub(crate) fn outcome_row(outcomes: &[DimOutcome]) -> String {
    let items: Vec<String> = outcomes.iter().map(outcome_json).collect();
    format!("[{}]", items.join(", "))
}

pub(crate) fn tau_json(outcome: &TauOutcome) -> String {
    match outcome {
        TauOutcome::Projective => "{\"projective\": true}".to_string(),
        TauOutcome::Dimvec(v) => format!("{{\"dimvec\": {}}}", int_row(v)),
    }
}

pub(crate) fn tau_row(outcomes: &[TauOutcome]) -> String {
    let items: Vec<String> = outcomes.iter().map(tau_json).collect();
    format!("[{}]", items.join(", "))
}

pub(crate) fn weighted_dimvecs_json(entries: &[(Vec<usize>, usize)], weight_key: &str) -> String {
    let items: Vec<String> = entries
        .iter()
        .map(|(dimvec, weight)| {
            format!(
                "{{\"dimvec\": {}, \"{weight_key}\": {weight}}}",
                int_row(dimvec)
            )
        })
        .collect();
    format!("[{}]", items.join(", "))
}

pub(crate) fn module_ref_json(r: &ModuleRef) -> String {
    format!(
        "{{\"kind\": \"{}\", \"index\": {}}}",
        r.kind.name(),
        r.index
    )
}

pub(crate) fn ar_entry_json(entry: &ArEntry) -> String {
    let head = module_ref_json(&entry.module);
    match &entry.sequence {
        ArSequence::Projective => {
            format!("{{\"module\": {head}, \"projective\": true}}")
        }
        ArSequence::Sequence {
            tau,
            middle_dimvec,
            middle,
            num_middle_summands,
        } => format!(
            "{{\"module\": {head}, \"projective\": false, \"tau\": {}, \
             \"middle_dimvec\": {}, \"middle\": {}, \"num_middle_summands\": {num_middle_summands}}}",
            int_row(tau),
            int_row(middle_dimvec),
            weighted_dimvecs_json(middle, "multiplicity")
        ),
    }
}

pub(crate) fn irr_side_json(side: &IrrSide, endpoint_key: &str) -> String {
    format!(
        "{{\"present\": {}, \"total\": {}, \"{endpoint_key}\": {}}}",
        side.present,
        side.total,
        weighted_dimvecs_json(&side.endpoints, "valuation")
    )
}

pub(crate) fn irr_entry_json(entry: &IrrEntry) -> String {
    format!(
        "{{\"module\": {}, \"into\": {}, \"out_of\": {}}}",
        module_ref_json(&entry.module),
        irr_side_json(&entry.into, "sources"),
        irr_side_json(&entry.out_of, "targets")
    )
}

pub(crate) fn yoneda_json(y: &YonedaProduct) -> String {
    format!(
        "{{\"i\": {}, \"j\": {}, \"k\": {}, \"dim_ext1_ij\": {}, \"dim_ext1_jk\": {}, \
         \"dim_ext2_ik\": {}, \"yoneda_map_rank\": {}}}",
        y.i, y.j, y.k, y.dim_ext1_ij, y.dim_ext1_jk, y.dim_ext2_ik, y.yoneda_map_rank
    )
}

pub(crate) fn bool_row(values: &[bool]) -> String {
    let items: Vec<String> = values.iter().map(bool::to_string).collect();
    format!("[{}]", items.join(", "))
}

pub(crate) fn tau_period_row(values: &[TauPeriod]) -> String {
    let items: Vec<String> = values
        .iter()
        .map(|value| match value {
            TauPeriod::Period(p) => format!("{{\"period\": {p}}}"),
            TauPeriod::NoneUpTo(b) => format!("{{\"none_up_to\": {b}}}"),
        })
        .collect();
    format!("[{}]", items.join(", "))
}

/// One JSON fragment per line, matching the generator's layout, so a diff of
/// two documents points at the entry that changed.
pub(crate) fn push_fragment_lines(out: &mut String, name: &str, items: &[String]) {
    if items.is_empty() {
        out.push_str(&format!("      \"{name}\": [],\n"));
        return;
    }
    out.push_str(&format!("      \"{name}\": [\n"));
    for (i, item) in items.iter().enumerate() {
        let comma = if i + 1 < items.len() { "," } else { "" };
        out.push_str(&format!("        {item}{comma}\n"));
    }
    out.push_str("      ],\n");
}

pub(crate) fn arrow_json(arrow: &ArrowSpec) -> String {
    format!(
        "{{\"name\": \"{}\", \"source\": {}, \"target\": {}}}",
        arrow.name, arrow.source, arrow.target
    )
}

pub(crate) fn relation_json(terms: &[TermSpec]) -> String {
    let items: Vec<String> = terms
        .iter()
        .map(|term| {
            let path: Vec<String> = term.path.iter().map(u32::to_string).collect();
            format!(
                "{{\"coeff\": {}, \"path\": [{}]}}",
                term.coeff,
                path.join(", ")
            )
        })
        .collect();
    format!("{{\"terms\": [{}]}}", items.join(", "))
}

/// Renders a v6 document from fixture presentations plus library-computed
/// values, in the layout `generate_fixtures.g` writes. The provenance block
/// names this library, never GAP.
pub(crate) fn render_document(fixtures: &[(&Fixture, &Computed)], convention: &str) -> String {
    let fixtures: Vec<_> = fixtures
        .iter()
        .copied()
        .filter(|(fx, _)| {
            FIXTURE_MANIFEST
                .iter()
                .any(|&(family, case)| fx.family == family && fx.case == case)
        })
        .collect();
    let mut out = String::new();
    out.push_str("{\n");
    out.push_str(&format!("  \"schema\": \"{SNAPSHOT_SCHEMA}\",\n"));
    out.push_str(&format!("  \"convention\": \"{convention}\",\n"));
    out.push_str(&format!("  \"max_ext_degree\": {MAX_EXT_DEGREE},\n"));
    out.push_str(&format!("  \"projdim_bound\": {PROJDIM_BOUND},\n"));
    out.push_str(&format!("  \"injdim_bound\": {INJDIM_BOUND},\n"));
    out.push_str("  \"provenance\": {\n");
    out.push_str("    \"gap_version\": \"none\",\n");
    out.push_str("    \"qpa_version\": \"none\",\n");
    out.push_str(
        "    \"command\": \"QPA_ORACLE_WRITE=1 cargo test -p auslander --test qpa_oracle\"\n",
    );
    out.push_str("  },\n");
    out.push_str("  \"fixtures\": [\n");
    for (idx, (fx, ours)) in fixtures.iter().enumerate() {
        out.push_str("    {\n");
        out.push_str(&format!("      \"family\": \"{}\",\n", fx.family));
        out.push_str(&format!("      \"case\": \"{}\",\n", fx.case));
        out.push_str(&format!("      \"field\": {},\n", fx.field));
        out.push_str(&format!(
            "      \"presentation_id\": \"{}\",\n",
            fx.presentation_id
        ));
        out.push_str(&format!("      \"ideal_id\": \"{}\",\n", fx.ideal_id));
        out.push_str(&format!("      \"order\": \"{ORDER_ID}\",\n"));
        out.push_str("      \"quiver\": {\n");
        out.push_str(&format!(
            "        \"num_vertices\": {},\n",
            fx.quiver.num_vertices
        ));
        out.push_str("        \"arrows\": [\n");
        for (i, arrow) in fx.quiver.arrows.iter().enumerate() {
            let comma = if i + 1 < fx.quiver.arrows.len() {
                ","
            } else {
                ""
            };
            out.push_str(&format!("          {}{comma}\n", arrow_json(arrow)));
        }
        out.push_str("        ]\n");
        out.push_str("      },\n");
        if fx.relations.is_empty() {
            out.push_str("      \"relations\": [],\n");
        } else {
            out.push_str("      \"relations\": [\n");
            for (i, relation) in fx.relations.iter().enumerate() {
                let comma = if i + 1 < fx.relations.len() { "," } else { "" };
                out.push_str(&format!("        {}{comma}\n", relation_json(relation)));
            }
            out.push_str("      ],\n");
        }
        out.push_str(&format!("      \"dim\": {},\n", ours.dim));
        out.push_str(&format!(
            "      \"cartan\": {},\n",
            int_matrix(&ours.cartan)
        ));
        out.push_str(&format!(
            "      \"injectives\": {},\n",
            int_matrix(&ours.injectives)
        ));
        out.push_str(&format!(
            "      \"projdim\": {},\n",
            outcome_row(&ours.projdim)
        ));
        out.push_str(&format!(
            "      \"injdim\": {},\n",
            outcome_row(&ours.injdim)
        ));
        out.push_str(&format!("      \"tau\": {},\n", tau_row(&ours.tau)));
        out.push_str(&format!(
            "      \"tau_injectives\": {},\n",
            tau_row(&ours.tau_injectives)
        ));
        out.push_str(&format!(
            "      \"decomposition\": {{\"module\": \"{DECOMPOSITION_MODULE}\", \"summands\": {}}},\n",
            weighted_dimvecs_json(&ours.decomposition, "multiplicity")
        ));
        out.push_str("      \"ext\": [\n");
        for (i, row) in ours.ext.iter().enumerate() {
            let comma = if i + 1 < ours.ext.len() { "," } else { "" };
            out.push_str(&format!("        {}{comma}\n", int_matrix(row)));
        }
        out.push_str("      ],\n");
        let designated: Vec<String> = ours.designated.iter().map(module_ref_json).collect();
        push_fragment_lines(&mut out, "designated_modules", &designated);
        let ar: Vec<String> = ours.ar_sequences.iter().map(ar_entry_json).collect();
        push_fragment_lines(&mut out, "ar_sequences", &ar);
        let irr: Vec<String> = ours.irreducible_maps.iter().map(irr_entry_json).collect();
        push_fragment_lines(&mut out, "irreducible_maps", &irr);
        out.push_str(&format!(
            "      \"ext_algebra\": {{\"module\": \"{EXT_ALGEBRA_MODULE}\", \
             \"max_degree\": {MAX_EXT_DEGREE}, \"dims\": {}, \"min_generators\": {}, \
             \"product_rank\": {}}},\n",
            int_row(&ours.ext_algebra.dims),
            int_row(&ours.ext_algebra.min_generators),
            int_row(&ours.ext_algebra.product_rank)
        ));
        let yoneda: Vec<String> = ours.yoneda_products.iter().map(yoneda_json).collect();
        push_fragment_lines(&mut out, "yoneda_products", &yoneda);
        out.push_str(&format!(
            "      \"stable_hom\": {},\n",
            int_matrix(&ours.stable_hom)
        ));
        out.push_str(&format!(
            "      \"tau_rigid\": {},\n",
            bool_row(&ours.tau_rigid)
        ));
        out.push_str(&format!("      \"rigid\": {},\n", bool_row(&ours.rigid)));
        out.push_str(&format!(
            "      \"tau_period\": {}\n",
            tau_period_row(&ours.tau_period)
        ));
        let comma = if idx + 1 < fixtures.len() { "," } else { "" };
        out.push_str(&format!("    }}{comma}\n"));
    }
    out.push_str("  ]\n");
    out.push_str("}\n");
    out
}

/// Renders the document with this library's right-module values for every
/// fixture of `doc`.
pub(crate) fn rendered_from_computed(doc: &Document) -> String {
    let computed: Vec<(&Fixture, Arc<Computed>)> = doc
        .fixtures
        .iter()
        .map(|fx| {
            let value = computed_for(fx, false)
                .unwrap_or_else(|e| panic!("{}/{}: {e}", fx.family, fx.case));
            (fx, value)
        })
        .collect();
    let refs: Vec<(&Fixture, &Computed)> = computed
        .iter()
        .map(|(fx, value)| (*fx, value.as_ref()))
        .collect();
    render_document(&refs, "right")
}

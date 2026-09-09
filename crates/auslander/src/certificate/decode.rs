use super::parser::{
    Value, as_string, as_u32, as_u64, as_usize, decode_list, decode_relation, decode_relations,
    decode_word, decode_words, obj_fields, shape, tuple,
};
use super::{
    AmbiguityEntry, AmbiguityKind, AutomatonData, CertParseError, Certificate, FinitenessData,
    OriginTerm, QuiverData, Trace, TraceStep,
};

fn decode_quiver(value: &Value) -> Result<QuiverData, CertParseError> {
    let mut values = obj_fields(value, "quiver", &["vertices", "arrows"])?.into_iter();
    Ok(QuiverData {
        vertices: as_u32(
            values.next().expect("one value per object key"),
            "quiver.vertices",
        )?,
        arrows: decode_list(
            values.next().expect("one value per object key"),
            "quiver.arrows",
            |pair| {
                let [source, target] =
                    tuple(pair, "quiver.arrows", "expected a [source, target] pair")?;
                Ok((
                    as_u32(source, "quiver.arrows")?,
                    as_u32(target, "quiver.arrows")?,
                ))
            },
        )?,
    })
}

fn decode_origin_term(value: &Value) -> Result<OriginTerm, CertParseError> {
    let mut values = obj_fields(
        value,
        "origin term",
        &["coeff", "left", "input_index", "right"],
    )?
    .into_iter();
    Ok(OriginTerm {
        coeff: as_u64(
            values.next().expect("one value per object key"),
            "origin term coeff",
        )?,
        left: decode_word(
            values.next().expect("one value per object key"),
            "origin term left",
        )?,
        input_index: as_usize(
            values.next().expect("one value per object key"),
            "origin term input_index",
        )?,
        right: decode_word(
            values.next().expect("one value per object key"),
            "origin term right",
        )?,
    })
}

fn decode_step(value: &Value) -> Result<TraceStep, CertParseError> {
    let mut values = obj_fields(
        value,
        "trace step",
        &["word", "basis_index", "left", "right", "coeff"],
    )?
    .into_iter();
    Ok(TraceStep {
        word: decode_word(
            values.next().expect("one value per object key"),
            "trace step word",
        )?,
        basis_index: as_usize(
            values.next().expect("one value per object key"),
            "trace step basis_index",
        )?,
        left: decode_word(
            values.next().expect("one value per object key"),
            "trace step left",
        )?,
        right: decode_word(
            values.next().expect("one value per object key"),
            "trace step right",
        )?,
        coeff: as_u64(
            values.next().expect("one value per object key"),
            "trace step coeff",
        )?,
    })
}

fn decode_trace(value: &Value) -> Result<Trace, CertParseError> {
    let mut values = obj_fields(value, "trace", &["start", "steps"])?.into_iter();
    Ok(Trace {
        start: decode_relation(
            values.next().expect("one value per object key"),
            "trace start",
        )?,
        steps: decode_list(
            values.next().expect("one value per object key"),
            "trace steps",
            decode_step,
        )?,
    })
}

fn decode_kind(value: &Value) -> Result<AmbiguityKind, CertParseError> {
    match as_string(value, "ambiguity kind")?.as_str() {
        "overlap" => Ok(AmbiguityKind::Overlap),
        "inclusion" => Ok(AmbiguityKind::Inclusion),
        other => Err(shape(
            "ambiguity kind",
            format!("expected \"overlap\" or \"inclusion\", got {other:?}"),
        )),
    }
}

fn decode_ambiguity(value: &Value) -> Result<AmbiguityEntry, CertParseError> {
    let mut values =
        obj_fields(value, "ambiguity", &["i", "j", "kind", "offset", "trace"])?.into_iter();
    Ok(AmbiguityEntry {
        i: as_usize(
            values.next().expect("one value per object key"),
            "ambiguity i",
        )?,
        j: as_usize(
            values.next().expect("one value per object key"),
            "ambiguity j",
        )?,
        kind: decode_kind(values.next().expect("one value per object key"))?,
        offset: as_usize(
            values.next().expect("one value per object key"),
            "ambiguity offset",
        )?,
        trace: decode_trace(values.next().expect("one value per object key"))?,
    })
}

fn decode_automaton(value: &Value) -> Result<AutomatonData, CertParseError> {
    let mut values = obj_fields(value, "automaton", &["states", "transitions"])?.into_iter();
    Ok(AutomatonData {
        states: decode_words(
            values.next().expect("one value per object key"),
            "automaton.states",
        )?,
        transitions: decode_list(
            values.next().expect("one value per object key"),
            "automaton.transitions",
            |triple| {
                let [state, arrow, next] = tuple(
                    triple,
                    "automaton.transitions",
                    "expected a [state, arrow, next state] triple",
                )?;
                Ok((
                    as_usize(state, "automaton.transitions")?,
                    as_u32(arrow, "automaton.transitions")?,
                    as_usize(next, "automaton.transitions")?,
                ))
            },
        )?,
    })
}

struct BasicFields {
    schema: String,
    field: u64,
    quiver: QuiverData,
    order: String,
}

struct CollectionFields {
    input_relations: Vec<super::RelationData>,
    basis: Vec<super::RelationData>,
    origin: Vec<Vec<OriginTerm>>,
    membership: Vec<Trace>,
    ambiguities: Vec<AmbiguityEntry>,
    normal_words: Vec<Vec<u32>>,
    automaton: AutomatonData,
    finiteness: FinitenessData,
}

fn certificate_fields(value: &Value) -> Result<Vec<&Value>, CertParseError> {
    obj_fields(
        value,
        "certificate",
        &[
            "schema",
            "field",
            "quiver",
            "order",
            "input_relations",
            "basis",
            "origin",
            "membership",
            "ambiguities",
            "normal_words",
            "automaton",
            "finiteness",
        ],
    )
}

fn decode_basic_fields(values: &[&Value]) -> Result<BasicFields, CertParseError> {
    Ok(BasicFields {
        schema: as_string(values[0], "schema")?,
        field: as_u64(values[1], "field")?,
        quiver: decode_quiver(values[2])?,
        order: as_string(values[3], "order")?,
    })
}

fn decode_collection_fields(values: &[&Value]) -> Result<CollectionFields, CertParseError> {
    Ok(CollectionFields {
        input_relations: decode_relations(values[4], "input_relations")?,
        basis: decode_relations(values[5], "basis")?,
        origin: decode_list(values[6], "origin", |terms| {
            decode_list(terms, "origin", decode_origin_term)
        })?,
        membership: decode_list(values[7], "membership", decode_trace)?,
        ambiguities: decode_list(values[8], "ambiguities", decode_ambiguity)?,
        normal_words: decode_words(values[9], "normal_words")?,
        automaton: decode_automaton(values[10])?,
        finiteness: decode_finiteness(values[11])?,
    })
}

pub(super) fn certificate(value: &Value) -> Result<Certificate, CertParseError> {
    let values = certificate_fields(value)?;
    let basic = decode_basic_fields(&values)?;
    let collections = decode_collection_fields(&values)?;
    Ok(Certificate {
        schema: basic.schema,
        field: basic.field,
        quiver: basic.quiver,
        order: basic.order,
        input_relations: collections.input_relations,
        basis: collections.basis,
        origin: collections.origin,
        membership: collections.membership,
        ambiguities: collections.ambiguities,
        normal_words: collections.normal_words,
        automaton: collections.automaton,
        finiteness: collections.finiteness,
    })
}

fn decode_finiteness(value: &Value) -> Result<FinitenessData, CertParseError> {
    let (key, payload) = finiteness_pair(value)?;
    match key {
        "finite" => decode_finite_flag(payload),
        "infinite" => decode_infinite_witness(payload),
        _ => Err(shape(
            "finiteness",
            "expected exactly one key, \"finite\" or \"infinite\"".to_string(),
        )),
    }
}

fn finiteness_pair(value: &Value) -> Result<(&str, &Value), CertParseError> {
    let Value::Obj(pairs) = value else {
        return Err(shape("finiteness", "expected an object".to_string()));
    };
    match pairs.as_slice() {
        [(key, payload)] => Ok((key, payload)),
        _ => Err(shape(
            "finiteness",
            "expected exactly one key, \"finite\" or \"infinite\"".to_string(),
        )),
    }
}

fn decode_finite_flag(value: &Value) -> Result<FinitenessData, CertParseError> {
    match value {
        Value::Bool(true) => Ok(FinitenessData::Finite),
        _ => Err(shape(
            "finiteness",
            "the value of \"finite\" must be the literal true".to_string(),
        )),
    }
}

fn decode_infinite_witness(value: &Value) -> Result<FinitenessData, CertParseError> {
    let fields = obj_fields(value, "finiteness.infinite", &["prefix", "cycle"])?;
    Ok(FinitenessData::Infinite {
        prefix: decode_word(fields[0], "finiteness.infinite.prefix")?,
        cycle: decode_word(fields[1], "finiteness.infinite.cycle")?,
    })
}

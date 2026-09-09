use std::fmt;

use super::{
    AmbiguityEntry, Certificate, FinitenessData, OriginTerm, RelationData, Trace, TraceStep,
};

macro_rules! json_object {
    ($out:expr; $($key:literal => $write:expr),+ $(,)?) => {{
        let out = $out;
        out.push('{');
        let mut needs_separator = false;
        $(
            if std::mem::replace(&mut needs_separator, true) { out.push(','); }
            out.push_str(concat!("\"", $key, "\":"));
            ($write)(out);
        )+
        out.push('}');
    }};
}

pub(super) fn certificate(certificate: &Certificate) -> String {
    let mut out = String::new();
    json_object!(&mut out;
        "schema" => |out: &mut String| push_string(out, &certificate.schema),
        "field" => |out: &mut String| push_number(out, certificate.field),
        "quiver" => |out: &mut String| json_object!(out;
            "vertices" => |out: &mut String| push_number(out, certificate.quiver.vertices),
            "arrows" => |out: &mut String| push_list(out, &certificate.quiver.arrows, |out, &(s, t)| {
                out.push('['); push_number(out, s); out.push(','); push_number(out, t); out.push(']');
            }),
        ),
        "order" => |out: &mut String| push_string(out, &certificate.order),
        "input_relations" => |out: &mut String| push_list(out, &certificate.input_relations, push_relation),
        "basis" => |out: &mut String| push_list(out, &certificate.basis, push_relation),
        "origin" => |out: &mut String| push_list(out, &certificate.origin, |out, terms| push_list(out, terms, push_origin_term)),
        "membership" => |out: &mut String| push_list(out, &certificate.membership, push_trace),
        "ambiguities" => |out: &mut String| push_list(out, &certificate.ambiguities, push_ambiguity),
        "normal_words" => |out: &mut String| push_list(out, &certificate.normal_words, |out, word| push_word(out, word)),
        "automaton" => |out: &mut String| json_object!(out;
            "states" => |out: &mut String| push_list(out, &certificate.automaton.states, |out, word| push_word(out, word)),
            "transitions" => |out: &mut String| push_list(out, &certificate.automaton.transitions, |out, &(state, arrow, next)| {
                out.push('['); push_number(out, state); out.push(','); push_number(out, arrow); out.push(','); push_number(out, next); out.push(']');
            }),
        ),
        "finiteness" => |out: &mut String| match &certificate.finiteness {
            FinitenessData::Finite => json_object!(out; "finite" => |out: &mut String| out.push_str("true")),
            FinitenessData::Infinite { prefix, cycle } => json_object!(out;
                "infinite" => |out: &mut String| json_object!(out;
                    "prefix" => |out: &mut String| push_word(out, prefix),
                    "cycle" => |out: &mut String| push_word(out, cycle),
                ),
            ),
        },
    );
    out
}

fn push_string(out: &mut String, s: &str) {
    assert!(
        s.chars()
            .all(|c| c.is_ascii() && !c.is_ascii_control() && c != '"' && c != '\\'),
        "certificate strings must be printable ASCII without quotes or backslashes"
    );
    out.push('"');
    out.push_str(s);
    out.push('"');
}

fn push_number(out: &mut String, number: impl fmt::Display) {
    out.push_str(&number.to_string());
}

fn push_list<T>(out: &mut String, items: &[T], mut push_item: impl FnMut(&mut String, &T)) {
    out.push('[');
    for (i, item) in items.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        push_item(out, item);
    }
    out.push(']');
}

fn push_word(out: &mut String, word: &[u32]) {
    push_list(out, word, |out, a| out.push_str(&a.to_string()));
}

fn push_relation(out: &mut String, relation: &RelationData) {
    push_list(out, relation, |out, (coeff, word)| {
        out.push('[');
        out.push_str(&coeff.to_string());
        out.push(',');
        push_word(out, word);
        out.push(']');
    });
}

fn push_origin_term(out: &mut String, term: &OriginTerm) {
    json_object!(out;
        "coeff" => |out: &mut String| push_number(out, term.coeff),
        "left" => |out: &mut String| push_word(out, &term.left),
        "input_index" => |out: &mut String| push_number(out, term.input_index),
        "right" => |out: &mut String| push_word(out, &term.right),
    );
}

fn push_trace(out: &mut String, trace: &Trace) {
    json_object!(out;
        "start" => |out: &mut String| push_relation(out, &trace.start),
        "steps" => |out: &mut String| push_list(out, &trace.steps, push_step),
    );
}

fn push_step(out: &mut String, step: &TraceStep) {
    json_object!(out;
        "word" => |out: &mut String| push_word(out, &step.word),
        "basis_index" => |out: &mut String| push_number(out, step.basis_index),
        "left" => |out: &mut String| push_word(out, &step.left),
        "right" => |out: &mut String| push_word(out, &step.right),
        "coeff" => |out: &mut String| push_number(out, step.coeff),
    );
}

fn push_ambiguity(out: &mut String, entry: &AmbiguityEntry) {
    json_object!(out;
        "i" => |out: &mut String| push_number(out, entry.i),
        "j" => |out: &mut String| push_number(out, entry.j),
        "kind" => |out: &mut String| push_string(out, entry.kind.as_str()),
        "offset" => |out: &mut String| push_number(out, entry.offset),
        "trace" => |out: &mut String| push_trace(out, &entry.trace),
    );
}

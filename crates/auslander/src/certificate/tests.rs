use super::*;
use crate::order::ORDER_ID;

fn sample() -> Certificate {
    Certificate {
        schema: CERT_SCHEMA.to_string(),
        field: 2,
        quiver: QuiverData {
            vertices: 1,
            arrows: vec![(0, 0)],
        },
        order: ORDER_ID.to_string(),
        input_relations: vec![vec![(1, vec![0, 0])]],
        basis: vec![vec![(1, vec![0, 0])]],
        origin: vec![vec![OriginTerm {
            coeff: 1,
            left: vec![],
            input_index: 0,
            right: vec![],
        }]],
        membership: vec![Trace {
            start: vec![(1, vec![0, 0])],
            steps: vec![TraceStep {
                word: vec![0, 0],
                basis_index: 0,
                left: vec![],
                right: vec![],
                coeff: 1,
            }],
        }],
        ambiguities: vec![AmbiguityEntry {
            i: 0,
            j: 0,
            kind: AmbiguityKind::Overlap,
            offset: 1,
            trace: Trace {
                start: vec![],
                steps: vec![],
            },
        }],
        normal_words: vec![vec![], vec![0]],
        automaton: AutomatonData {
            states: vec![vec![], vec![0]],
            transitions: vec![(0, 0, 1)],
        },
        finiteness: FinitenessData::Finite,
    }
}

const SAMPLE_JSON: &str = concat!(
    "{\"schema\":\"auslander-completion-certificate-v1\",\"field\":2,",
    "\"quiver\":{\"vertices\":1,\"arrows\":[[0,0]]},",
    "\"order\":\"deglex-arrowid-v1\",",
    "\"input_relations\":[[[1,[0,0]]]],",
    "\"basis\":[[[1,[0,0]]]],",
    "\"origin\":[[{\"coeff\":1,\"left\":[],\"input_index\":0,\"right\":[]}]],",
    "\"membership\":[{\"start\":[[1,[0,0]]],\"steps\":",
    "[{\"word\":[0,0],\"basis_index\":0,\"left\":[],\"right\":[],\"coeff\":1}]}],",
    "\"ambiguities\":[{\"i\":0,\"j\":0,\"kind\":\"overlap\",\"offset\":1,",
    "\"trace\":{\"start\":[],\"steps\":[]}}],",
    "\"normal_words\":[[],[0]],",
    "\"automaton\":{\"states\":[[],[0]],\"transitions\":[[0,0,1]]},",
    "\"finiteness\":{\"finite\":true}}"
);

#[test]
fn canonical_json_is_byte_exact() {
    assert_eq!(sample().to_canonical_json(), SAMPLE_JSON);
}

#[test]
fn json_round_trip_reproduces_the_certificate() {
    let c = sample();
    assert_eq!(Certificate::from_json(&c.to_canonical_json()), Ok(c));
}

#[test]
fn canonical_text_round_trips_byte_exact() {
    let parsed = Certificate::from_json(SAMPLE_JSON).unwrap();
    assert_eq!(parsed.to_canonical_json(), SAMPLE_JSON);
}

#[test]
fn whitespace_between_tokens_is_accepted() {
    let spaced = SAMPLE_JSON
        .replace("\"field\":2,", "\"field\" : 2 ,\n")
        .replace("\"normal_words\":", " \"normal_words\"\t: ");
    assert_eq!(Certificate::from_json(&spaced), Ok(sample()));
}

#[test]
fn duplicate_key_rejected() {
    let text = SAMPLE_JSON.replacen("\"field\":2,", "\"field\":2,\"field\":2,", 1);
    assert!(matches!(
        Certificate::from_json(&text),
        Err(CertParseError::Syntax { .. })
    ));
}

#[test]
fn unknown_key_rejected() {
    let text = SAMPLE_JSON.replacen("\"field\":2,", "\"field\":2,\"extra\":3,", 1);
    assert!(matches!(
        Certificate::from_json(&text),
        Err(CertParseError::Shape { .. })
    ));
    let nested = SAMPLE_JSON.replacen("{\"vertices\":1,", "{\"vertices\":1,\"loops\":0,", 1);
    assert!(matches!(
        Certificate::from_json(&nested),
        Err(CertParseError::Shape { .. })
    ));
}

#[test]
fn missing_key_rejected() {
    let text = SAMPLE_JSON.replacen("\"order\":\"deglex-arrowid-v1\",", "", 1);
    assert!(matches!(
        Certificate::from_json(&text),
        Err(CertParseError::Shape { .. })
    ));
}

#[test]
fn trailing_comma_rejected() {
    let text = SAMPLE_JSON.replacen(
        "\"normal_words\":[[],[0]],",
        "\"normal_words\":[[],[0],],",
        1,
    );
    assert!(matches!(
        Certificate::from_json(&text),
        Err(CertParseError::Syntax { .. })
    ));
}

#[test]
fn wrong_type_rejected() {
    let text = SAMPLE_JSON.replacen("\"field\":2,", "\"field\":\"2\",", 1);
    assert!(matches!(
        Certificate::from_json(&text),
        Err(CertParseError::Shape { .. })
    ));
}

#[test]
fn truncated_input_rejected() {
    for len in [0, 1, SAMPLE_JSON.len() / 2, SAMPLE_JSON.len() - 1] {
        assert!(
            matches!(
                Certificate::from_json(&SAMPLE_JSON[..len]),
                Err(CertParseError::Syntax { .. })
            ),
            "prefix of length {len}"
        );
    }
}

#[test]
fn leading_zero_number_rejected() {
    let text = SAMPLE_JSON.replacen("\"field\":2,", "\"field\":02,", 1);
    assert!(matches!(
        Certificate::from_json(&text),
        Err(CertParseError::Syntax { .. })
    ));
}

#[test]
fn float_and_escape_rejected() {
    let float = SAMPLE_JSON.replacen("\"field\":2,", "\"field\":2.0,", 1);
    assert!(matches!(
        Certificate::from_json(&float),
        Err(CertParseError::Syntax { .. })
    ));
    let escape = SAMPLE_JSON.replacen("\"kind\":\"overlap\"", "\"kind\":\"over\\lap\"", 1);
    assert!(matches!(
        Certificate::from_json(&escape),
        Err(CertParseError::Syntax { .. })
    ));
}

#[test]
fn trailing_content_rejected() {
    let text = format!("{SAMPLE_JSON} ");
    assert_eq!(Certificate::from_json(&text), Ok(sample()));
    let text = format!("{SAMPLE_JSON}0");
    assert!(matches!(
        Certificate::from_json(&text),
        Err(CertParseError::Syntax { .. })
    ));
}

#[test]
fn bad_kind_rejected() {
    let text = SAMPLE_JSON.replacen("\"kind\":\"overlap\"", "\"kind\":\"overlaps\"", 1);
    assert!(matches!(
        Certificate::from_json(&text),
        Err(CertParseError::Shape { .. })
    ));
}

#[test]
fn arrow_index_above_u32_rejected() {
    let text = SAMPLE_JSON.replacen(
        "\"normal_words\":[[],[0]]",
        "\"normal_words\":[[],[4294967296]]",
        1,
    );
    assert!(matches!(
        Certificate::from_json(&text),
        Err(CertParseError::Shape { .. })
    ));
}

#[test]
fn inclusion_kind_round_trips() {
    let mut c = sample();
    c.ambiguities[0].kind = AmbiguityKind::Inclusion;
    assert_eq!(Certificate::from_json(&c.to_canonical_json()), Ok(c));
}

#[test]
fn infinite_finiteness_round_trips() {
    let mut c = sample();
    c.finiteness = FinitenessData::Infinite {
        prefix: vec![0],
        cycle: vec![0, 0],
    };
    let json = c.to_canonical_json();
    assert!(json.contains("\"finiteness\":{\"infinite\":{\"prefix\":[0],\"cycle\":[0,0]}}"));
    assert_eq!(Certificate::from_json(&json), Ok(c));
}

#[test]
fn finiteness_with_false_rejected() {
    let text = SAMPLE_JSON.replacen("{\"finite\":true}", "{\"finite\":false}", 1);
    assert!(matches!(
        Certificate::from_json(&text),
        Err(CertParseError::Shape { .. })
    ));
}

#[test]
fn false_outside_finiteness_rejected() {
    let text = SAMPLE_JSON.replacen("\"field\":2,", "\"field\":false,", 1);
    assert!(matches!(
        Certificate::from_json(&text),
        Err(CertParseError::Shape { .. })
    ));
}

#[test]
fn finiteness_with_both_keys_rejected() {
    let text = SAMPLE_JSON.replacen(
        "{\"finite\":true}",
        "{\"finite\":true,\"infinite\":{\"prefix\":[],\"cycle\":[0]}}",
        1,
    );
    assert!(matches!(
        Certificate::from_json(&text),
        Err(CertParseError::Shape { .. })
    ));
}

#[test]
fn malformed_transition_triple_rejected() {
    let text = SAMPLE_JSON.replacen("\"transitions\":[[0,0,1]]", "\"transitions\":[[0,0]]", 1);
    assert!(matches!(
        Certificate::from_json(&text),
        Err(CertParseError::Shape { .. })
    ));
}

fn nested_arrays(depth: usize) -> String {
    let mut text = String::new();
    for _ in 0..depth {
        text.push('[');
    }
    for _ in 0..depth {
        text.push(']');
    }
    text
}

#[test]
fn container_depth_at_the_limit_parses() {
    // Structurally fine at depth 64. The value is no certificate, so the
    // rejection is a shape error, not a syntax error.
    assert!(matches!(
        Certificate::from_json(&nested_arrays(MAX_JSON_DEPTH)),
        Err(CertParseError::Shape { .. })
    ));
}

#[test]
fn container_depth_above_the_limit_rejected() {
    assert!(matches!(
        Certificate::from_json(&nested_arrays(MAX_JSON_DEPTH + 1)),
        Err(CertParseError::Syntax { .. })
    ));
}

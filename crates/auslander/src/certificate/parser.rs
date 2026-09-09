use super::{CertParseError, MAX_JSON_DEPTH};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Value {
    Num(u64),
    Str(String),
    Bool(bool),
    Arr(Vec<Value>),
    Obj(Vec<(String, Value)>),
}

fn syntax(byte: usize, message: &str) -> CertParseError {
    CertParseError::Syntax {
        byte,
        message: message.to_string(),
    }
}

pub(super) fn shape(context: &str, message: String) -> CertParseError {
    CertParseError::Shape {
        context: context.to_string(),
        message,
    }
}

pub(super) fn parse(text: &str) -> Result<Value, CertParseError> {
    let bytes = text.as_bytes();
    let mut pos = 0;
    let value = parse_value(bytes, &mut pos, 0)?;
    skip_ws(bytes, &mut pos);
    if pos != bytes.len() {
        return Err(syntax(pos, "trailing content"));
    }
    Ok(value)
}

fn skip_ws(bytes: &[u8], pos: &mut usize) {
    while matches!(bytes.get(*pos), Some(b' ' | b'\t' | b'\n' | b'\r')) {
        *pos += 1;
    }
}

fn expect(bytes: &[u8], pos: &mut usize, ch: u8) -> Result<(), CertParseError> {
    skip_ws(bytes, pos);
    if bytes.get(*pos) == Some(&ch) {
        *pos += 1;
        Ok(())
    } else {
        Err(syntax(*pos, &format!("expected '{}'", ch as char)))
    }
}

/// `depth` counts the containers enclosing this value. A container that
/// would sit deeper than [`MAX_JSON_DEPTH`] levels is rejected before the
/// parser recurses into it.
fn parse_value(bytes: &[u8], pos: &mut usize, depth: usize) -> Result<Value, CertParseError> {
    skip_ws(bytes, pos);
    match bytes.get(*pos) {
        Some(b'{') => {
            check_depth(pos, depth)?;
            parse_obj(bytes, pos, depth + 1)
        }
        Some(b'[') => {
            check_depth(pos, depth)?;
            parse_arr(bytes, pos, depth + 1)
        }
        Some(b'"') => Ok(Value::Str(parse_string(bytes, pos)?)),
        Some(b'0'..=b'9') => parse_num(bytes, pos),
        Some(b't' | b'f') => parse_bool(bytes, pos),
        _ => Err(syntax(
            *pos,
            "expected an object, array, string, boolean, or unsigned integer",
        )),
    }
}

fn check_depth(pos: &mut usize, depth: usize) -> Result<(), CertParseError> {
    (depth < MAX_JSON_DEPTH).then_some(()).ok_or_else(|| {
        syntax(
            *pos,
            &format!("containers nest deeper than {MAX_JSON_DEPTH} levels"),
        )
    })
}

fn parse_bool(bytes: &[u8], pos: &mut usize) -> Result<Value, CertParseError> {
    for (literal, value) in [(&b"true"[..], true), (&b"false"[..], false)] {
        if bytes[*pos..].starts_with(literal) {
            *pos += literal.len();
            return Ok(Value::Bool(value));
        }
    }
    Err(syntax(*pos, "expected 'true' or 'false'"))
}

fn parse_num(bytes: &[u8], pos: &mut usize) -> Result<Value, CertParseError> {
    let start = *pos;
    while matches!(bytes.get(*pos), Some(b'0'..=b'9')) {
        *pos += 1;
    }
    let digits = &bytes[start..*pos];
    if digits.len() > 1 && digits[0] == b'0' {
        return Err(syntax(start, "number has a leading zero"));
    }
    if matches!(bytes.get(*pos), Some(b'.' | b'e' | b'E')) {
        return Err(syntax(*pos, "number must be an unsigned integer"));
    }
    std::str::from_utf8(digits)
        .expect("digits are ASCII")
        .parse()
        .map(Value::Num)
        .map_err(|_| syntax(start, "number does not fit in u64"))
}

fn parse_string(bytes: &[u8], pos: &mut usize) -> Result<String, CertParseError> {
    expect(bytes, pos, b'"')?;
    let start = *pos;
    loop {
        if bytes.get(*pos) == Some(&b'"') {
            let text = std::str::from_utf8(&bytes[start..*pos]).expect("checked ASCII");
            *pos += 1;
            return Ok(text.to_string());
        }
        if let Some(message) = string_byte_error(bytes.get(*pos)) {
            return Err(syntax(*pos, message));
        }
        *pos += 1;
    }
}

fn string_byte_error(byte: Option<&u8>) -> Option<&'static str> {
    match byte {
        Some(b'\\') => Some("escape sequences are not canonical"),
        Some(&value) => string_ascii_error(value),
        None => Some("unterminated string"),
    }
}

fn string_ascii_error(byte: u8) -> Option<&'static str> {
    if byte < 0x20 {
        Some("control character in string")
    } else if byte >= 0x80 {
        Some("non-ASCII character in string")
    } else {
        None
    }
}

fn collection_separator(
    bytes: &[u8],
    pos: &mut usize,
    close: u8,
    expected: &str,
) -> Result<bool, CertParseError> {
    skip_ws(bytes, pos);
    match bytes.get(*pos) {
        Some(b',') => {
            *pos += 1;
            Ok(false)
        }
        Some(&value) if value == close => {
            *pos += 1;
            Ok(true)
        }
        _ => Err(syntax(*pos, expected)),
    }
}

fn parse_nonempty_array(
    bytes: &[u8],
    pos: &mut usize,
    depth: usize,
) -> Result<Vec<Value>, CertParseError> {
    let mut items = Vec::new();
    loop {
        items.push(parse_value(bytes, pos, depth)?);
        if collection_separator(bytes, pos, b']', "expected ',' or ']'")? {
            return Ok(items);
        }
    }
}

fn parse_arr(bytes: &[u8], pos: &mut usize, depth: usize) -> Result<Value, CertParseError> {
    expect(bytes, pos, b'[')?;
    skip_ws(bytes, pos);
    if bytes.get(*pos) == Some(&b']') {
        *pos += 1;
        return Ok(Value::Arr(Vec::new()));
    }
    parse_nonempty_array(bytes, pos, depth).map(Value::Arr)
}

fn parse_object_pair(
    bytes: &[u8],
    pos: &mut usize,
    depth: usize,
    keys: &mut std::collections::BTreeSet<String>,
) -> Result<(String, Value), CertParseError> {
    skip_ws(bytes, pos);
    let key = parse_string(bytes, pos)?;
    if !keys.insert(key.clone()) {
        return Err(syntax(*pos, &format!("duplicate key {key:?}")));
    }
    expect(bytes, pos, b':')?;
    let value = parse_value(bytes, pos, depth)?;
    Ok((key, value))
}

fn parse_nonempty_object(
    bytes: &[u8],
    pos: &mut usize,
    depth: usize,
) -> Result<Vec<(String, Value)>, CertParseError> {
    let mut pairs = Vec::new();
    let mut keys = std::collections::BTreeSet::new();
    loop {
        pairs.push(parse_object_pair(bytes, pos, depth, &mut keys)?);
        if collection_separator(bytes, pos, b'}', "expected ',' or '}'")? {
            return Ok(pairs);
        }
    }
}

fn parse_obj(bytes: &[u8], pos: &mut usize, depth: usize) -> Result<Value, CertParseError> {
    expect(bytes, pos, b'{')?;
    skip_ws(bytes, pos);
    if bytes.get(*pos) == Some(&b'}') {
        *pos += 1;
        return Ok(Value::Obj(Vec::new()));
    }
    parse_nonempty_object(bytes, pos, depth).map(Value::Obj)
}

/// The object's values in the order of `keys`. Rejects unknown keys and
/// missing keys; the parser already rejects duplicates.
pub(super) fn obj_fields<'a>(
    value: &'a Value,
    context: &str,
    keys: &[&str],
) -> Result<Vec<&'a Value>, CertParseError> {
    let Value::Obj(pairs) = value else {
        return Err(shape(context, "expected an object".to_string()));
    };
    for (k, _) in pairs {
        if !keys.contains(&k.as_str()) {
            return Err(shape(context, format!("unknown key {k:?}")));
        }
    }
    keys.iter()
        .map(|key| {
            pairs
                .iter()
                .find(|(k, _)| k == key)
                .map(|(_, v)| v)
                .ok_or_else(|| shape(context, format!("missing key {key:?}")))
        })
        .collect()
}

pub(super) fn as_u64(value: &Value, context: &str) -> Result<u64, CertParseError> {
    match value {
        Value::Num(n) => Ok(*n),
        _ => Err(shape(context, "expected an unsigned integer".to_string())),
    }
}

pub(super) fn as_u32(value: &Value, context: &str) -> Result<u32, CertParseError> {
    u32::try_from(as_u64(value, context)?)
        .map_err(|_| shape(context, "number does not fit in u32".to_string()))
}

pub(super) fn as_usize(value: &Value, context: &str) -> Result<usize, CertParseError> {
    usize::try_from(as_u64(value, context)?)
        .map_err(|_| shape(context, "number does not fit in usize".to_string()))
}

pub(super) fn as_string(value: &Value, context: &str) -> Result<String, CertParseError> {
    match value {
        Value::Str(s) => Ok(s.clone()),
        _ => Err(shape(context, "expected a string".to_string())),
    }
}

pub(super) fn as_arr<'a>(value: &'a Value, context: &str) -> Result<&'a [Value], CertParseError> {
    match value {
        Value::Arr(items) => Ok(items),
        _ => Err(shape(context, "expected an array".to_string())),
    }
}

pub(super) fn decode_list<T>(
    value: &Value,
    context: &str,
    mut decode: impl FnMut(&Value) -> Result<T, CertParseError>,
) -> Result<Vec<T>, CertParseError> {
    as_arr(value, context)?.iter().map(&mut decode).collect()
}

pub(super) fn tuple<'a, const N: usize>(
    value: &'a Value,
    context: &str,
    message: &str,
) -> Result<[&'a Value; N], CertParseError> {
    let parts = as_arr(value, context)?;
    if parts.len() != N {
        return Err(shape(context, message.to_string()));
    }
    Ok(std::array::from_fn(|index| &parts[index]))
}

pub(super) fn decode_word(value: &Value, context: &str) -> Result<Vec<u32>, CertParseError> {
    decode_list(value, context, |item| as_u32(item, context))
}

pub(super) fn decode_words(value: &Value, context: &str) -> Result<Vec<Vec<u32>>, CertParseError> {
    decode_list(value, context, |item| decode_word(item, context))
}

pub(super) fn decode_relation(
    value: &Value,
    context: &str,
) -> Result<super::RelationData, CertParseError> {
    decode_list(value, context, |term| {
        let [coeff, word] = tuple(term, context, "expected a [coefficient, word] pair")?;
        Ok((as_u64(coeff, context)?, decode_word(word, context)?))
    })
}

pub(super) fn decode_relations(
    value: &Value,
    context: &str,
) -> Result<Vec<super::RelationData>, CertParseError> {
    decode_list(value, context, |item| decode_relation(item, context))
}

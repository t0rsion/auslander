use std::collections::BTreeSet;

use super::{CertParseError, MAX_JSON_DEPTH};
use crate::portable::{Cursor, CursorLimits, PortableError};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Value {
    Num(u64),
    Str(String),
    Bool(bool),
    Arr(Vec<Value>),
    Obj(Vec<(String, Value)>),
}

impl From<PortableError> for CertParseError {
    fn from(error: PortableError) -> Self {
        match error {
            PortableError::Syntax { byte, message } => CertParseError::Syntax { byte, message },
            PortableError::ParseLimit { path, used, limit } => {
                shape(&path, format!("needs {used} units, limit {limit}"))
            }
        }
    }
}

pub(super) fn shape(context: &str, message: String) -> CertParseError {
    CertParseError::Shape {
        context: context.to_string(),
        message,
    }
}

pub(super) fn parse(text: &str) -> Result<Value, CertParseError> {
    let mut c = Cursor::new(text, CursorLimits::NONE)?;
    let value = parse_value(&mut c, 0)?;
    c.end()?;
    Ok(value)
}

/// `depth` counts the containers enclosing this value. A container that
/// would sit deeper than [`MAX_JSON_DEPTH`] levels is rejected before the
/// parser recurses into it.
fn parse_value(c: &mut Cursor, depth: usize) -> Result<Value, CertParseError> {
    match c.peek() {
        Some(open @ (b'{' | b'[')) => parse_container(c, open, depth),
        Some(b'"') => Ok(Value::Str(c.string("string")?)),
        Some(b'0'..=b'9') => Ok(Value::Num(c.u64("number")?)),
        Some(b't' | b'f') => Ok(Value::Bool(c.bool()?)),
        _ => Err(c
            .syntax("expected an object, array, string, boolean, or unsigned integer")
            .into()),
    }
}

fn parse_container(c: &mut Cursor, open: u8, depth: usize) -> Result<Value, CertParseError> {
    if depth >= MAX_JSON_DEPTH {
        let message = format!("containers nest deeper than {MAX_JSON_DEPTH} levels");
        return Err(c.syntax(message).into());
    }
    if open == b'{' {
        return parse_obj(c, depth + 1);
    }
    let items = c.array("array", usize::MAX, |c, _| parse_value(c, depth + 1))?;
    Ok(Value::Arr(items))
}

fn parse_obj(c: &mut Cursor, depth: usize) -> Result<Value, CertParseError> {
    c.token(b'{')?;
    let mut pairs = Vec::new();
    let mut keys = BTreeSet::new();
    if c.eat(b'}') {
        return Ok(Value::Obj(pairs));
    }
    loop {
        let key = c.string("object key")?;
        if !keys.insert(key.clone()) {
            return Err(c.syntax(format!("duplicate key {key:?}")).into());
        }
        c.token(b':')?;
        pairs.push((key, parse_value(c, depth)?));
        if !c.more(b'}')? {
            return Ok(Value::Obj(pairs));
        }
    }
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

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Num(i64),
    Bool(bool),
    Str(String),
    Arr(Vec<Value>),
    Obj(Vec<(String, Value)>),
}

impl Value {
    pub fn as_usize(&self) -> Option<usize> {
        match self {
            Value::Num(n) => usize::try_from(*n).ok(),
            _ => None,
        }
    }

    pub fn as_arr(&self) -> Option<&[Value]> {
        match self {
            Value::Arr(items) => Some(items),
            _ => None,
        }
    }
}

pub fn parse(text: &str) -> Result<Value, String> {
    let bytes = text.as_bytes();
    let mut pos = 0;
    let value = parse_value(bytes, &mut pos)?;
    skip_ws(bytes, &mut pos);
    if pos != bytes.len() {
        return Err(format!("trailing content at byte {pos}"));
    }
    Ok(value)
}

fn skip_ws(bytes: &[u8], pos: &mut usize) {
    while *pos < bytes.len() && bytes[*pos].is_ascii_whitespace() {
        *pos += 1;
    }
}

fn expect(bytes: &[u8], pos: &mut usize, ch: u8) -> Result<(), String> {
    skip_ws(bytes, pos);
    if bytes.get(*pos) == Some(&ch) {
        *pos += 1;
        Ok(())
    } else {
        Err(format!(
            "expected '{}' at byte {}, found {:?}",
            ch as char,
            pos,
            bytes.get(*pos).map(|&b| b as char)
        ))
    }
}

fn parse_value(bytes: &[u8], pos: &mut usize) -> Result<Value, String> {
    skip_ws(bytes, pos);
    match bytes.get(*pos) {
        Some(b'{') => parse_obj(bytes, pos),
        Some(b'[') => parse_arr(bytes, pos),
        Some(b'"') => Ok(Value::Str(parse_str(bytes, pos)?)),
        Some(b'-' | b'0'..=b'9') => parse_num(bytes, pos),
        Some(b't' | b'f') => parse_bool(bytes, pos),
        other => Err(format!(
            "unexpected {:?} at byte {}",
            other.map(|&b| b as char),
            pos
        )),
    }
}

fn parse_bool(bytes: &[u8], pos: &mut usize) -> Result<Value, String> {
    for (word, value) in [("true", true), ("false", false)] {
        if bytes[*pos..].starts_with(word.as_bytes()) {
            *pos += word.len();
            return Ok(Value::Bool(value));
        }
    }
    Err(format!("bad keyword at byte {pos}"))
}

fn parse_num(bytes: &[u8], pos: &mut usize) -> Result<Value, String> {
    let start = *pos;
    if bytes.get(*pos) == Some(&b'-') {
        *pos += 1;
    }
    while matches!(bytes.get(*pos), Some(b'0'..=b'9')) {
        *pos += 1;
    }
    std::str::from_utf8(&bytes[start..*pos])
        .ok()
        .and_then(|s| s.parse().ok())
        .map(Value::Num)
        .ok_or_else(|| format!("bad number at byte {start}"))
}

fn parse_escape(bytes: &[u8], pos: &mut usize, out: &mut String) -> Result<(), String> {
    *pos += 1;
    match bytes.get(*pos) {
        Some(b'n') => out.push('\n'),
        Some(b't') => out.push('\t'),
        Some(&c) => out.push(c as char),
        None => return Err("unterminated escape".to_string()),
    }
    *pos += 1;
    Ok(())
}

fn parse_str(bytes: &[u8], pos: &mut usize) -> Result<String, String> {
    expect(bytes, pos, b'"')?;
    let mut out = String::new();
    loop {
        match bytes.get(*pos) {
            Some(b'"') => {
                *pos += 1;
                return Ok(out);
            }
            Some(b'\\') => parse_escape(bytes, pos, &mut out)?,
            Some(&c) => {
                out.push(c as char);
                *pos += 1;
            }
            None => return Err("unterminated string".to_string()),
        }
    }
}

fn parse_obj_pair(
    bytes: &[u8],
    pos: &mut usize,
    pairs: &mut Vec<(String, Value)>,
) -> Result<(), String> {
    skip_ws(bytes, pos);
    let key = parse_str(bytes, pos)?;
    if pairs.iter().any(|(k, _)| *k == key) {
        return Err(format!("duplicate key {key:?} at byte {pos}"));
    }
    expect(bytes, pos, b':')?;
    let value = parse_value(bytes, pos)?;
    pairs.push((key, value));
    Ok(())
}

fn parse_arr(bytes: &[u8], pos: &mut usize) -> Result<Value, String> {
    expect(bytes, pos, b'[')?;
    let mut items = Vec::new();
    skip_ws(bytes, pos);
    if bytes.get(*pos) == Some(&b']') {
        *pos += 1;
        return Ok(Value::Arr(items));
    }
    loop {
        items.push(parse_value(bytes, pos)?);
        skip_ws(bytes, pos);
        match bytes.get(*pos) {
            Some(b',') => *pos += 1,
            Some(b']') => {
                *pos += 1;
                return Ok(Value::Arr(items));
            }
            other => {
                return Err(format!(
                    "expected ',' or ']' at byte {}, found {:?}",
                    pos,
                    other.map(|&b| b as char)
                ));
            }
        }
    }
}

fn parse_obj(bytes: &[u8], pos: &mut usize) -> Result<Value, String> {
    expect(bytes, pos, b'{')?;
    let mut pairs: Vec<(String, Value)> = Vec::new();
    skip_ws(bytes, pos);
    if bytes.get(*pos) == Some(&b'}') {
        *pos += 1;
        return Ok(Value::Obj(pairs));
    }
    loop {
        parse_obj_pair(bytes, pos, &mut pairs)?;
        skip_ws(bytes, pos);
        match bytes.get(*pos) {
            Some(b',') => *pos += 1,
            Some(b'}') => {
                *pos += 1;
                return Ok(Value::Obj(pairs));
            }
            other => {
                return Err(format!(
                    "expected ',' or '}}' at byte {}, found {:?}",
                    pos,
                    other.map(|&b| b as char)
                ));
            }
        }
    }
}

use std::fmt::Display;

/// The FNV-1a hash of `text` as 16 lowercase hexadecimal digits.
///
/// It detects accidental corruption. Anyone can recompute it, so it does
/// not authenticate.
pub(crate) fn fingerprint(text: &str) -> String {
    let mut value = 0xcbf29ce484222325u64;
    for byte in text.bytes() {
        value ^= u64::from(byte);
        value = value.wrapping_mul(0x100000001b3);
    }
    format!("{value:016x}")
}

/// Whether `value` has the shape of a [`fingerprint`].
pub(crate) fn is_fingerprint(value: &str) -> bool {
    value.len() == 16
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

/// Opens a canonical object with the members `schema`, `kind`, and
/// `engine`, as [`super::Cursor::header`] reads them.
pub(crate) fn open_header([schema, kind, engine]: [&str; 3]) -> String {
    let mut output = String::from("{\"schema\":");
    push_ascii(&mut output, schema);
    output.push_str(",\"kind\":");
    push_ascii(&mut output, kind);
    output.push_str(",\"engine\":");
    push_ascii(&mut output, engine);
    output
}

/// Closes an open canonical object with its final `fingerprint` field.
pub(crate) fn seal(mut body: String, fingerprint: &str) -> String {
    body.push_str(",\"fingerprint\":\"");
    body.push_str(fingerprint);
    body.push_str("\"}");
    body
}

/// Writes `items` as a JSON array, one `push_item` call per element.
pub(crate) fn push_list<T>(
    output: &mut String,
    items: &[T],
    mut push_item: impl FnMut(&mut String, &T),
) {
    output.push('[');
    for (index, item) in items.iter().enumerate() {
        if index != 0 {
            output.push(',');
        }
        push_item(output, item);
    }
    output.push(']');
}

/// Writes `values` as a JSON array of decimal numbers.
pub(crate) fn push_numbers<T: Display>(output: &mut String, values: &[T]) {
    push_list(output, values, |output, value| {
        output.push_str(&value.to_string());
    });
}

/// Writes an object whose values are decimal numbers, in the given order.
pub(crate) fn push_number_object<T: Display>(output: &mut String, fields: &[(&str, T)]) {
    output.push('{');
    for (index, (key, value)) in fields.iter().enumerate() {
        if index != 0 {
            output.push(',');
        }
        output.push('"');
        output.push_str(key);
        output.push_str("\":");
        output.push_str(&value.to_string());
    }
    output.push('}');
}

/// Writes `,"key":value` for each of `fields`, continuing an open object.
pub(crate) fn push_number_fields<T: Display>(output: &mut String, fields: &[(&str, T)]) {
    for (key, value) in fields {
        output.push_str(",\"");
        output.push_str(key);
        output.push_str("\":");
        output.push_str(&value.to_string());
    }
}

/// Writes the object `{"kind":"<kind>"}` extended by the decimal `fields`.
///
/// `kind` must satisfy [`push_ascii`].
pub(crate) fn push_tagged_numbers<T: Display>(
    output: &mut String,
    kind: &str,
    fields: &[(&str, T)],
) {
    output.push_str("{\"kind\":");
    push_ascii(output, kind);
    push_number_fields(output, fields);
    output.push('}');
}

/// Writes `bytes` as a quoted string, escaping only `"` and `\`.
///
/// The bytes must be printable ASCII for [`super::Cursor::escaped_string`]
/// to read them back.
pub(crate) fn push_escaped(output: &mut String, bytes: &[u8]) {
    output.push('"');
    for &byte in bytes {
        if matches!(byte, b'"' | b'\\') {
            output.push('\\');
        }
        output.push(byte as char);
    }
    output.push('"');
}

/// Writes `value` as a quoted string without escapes.
///
/// # Panics
/// Panics when `value` contains a quote, a backslash, or a byte outside
/// printable ASCII. Portable values built by this crate store only fixed
/// ASCII identifiers.
pub(crate) fn push_ascii(output: &mut String, value: &str) {
    assert!(
        value
            .bytes()
            .all(|byte| (0x20..=0x7e).contains(&byte) && byte != b'"' && byte != b'\\'),
        "portable strings must be printable ASCII without quotes or backslashes"
    );
    output.push('"');
    output.push_str(value);
    output.push('"');
}

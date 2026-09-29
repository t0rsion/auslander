//! WebAssembly exports of the portable artifact verifier.
//!
//! The module exports three functions with the C ABI:
//!
//! - `alloc(len)` returns a zeroed buffer of `len` bytes.
//! - `verify(ptr, len)` reads `len` bytes at `ptr` as one portable value and
//!   returns a pointer to a result buffer. The buffer holds a 4-byte
//!   little-endian length `n`, then `n` bytes of UTF-8 JSON from
//!   [`verify_json`].
//! - `dealloc(ptr, len)` frees a buffer from `alloc` (with its `len`) or a
//!   result buffer (with `len = 4 + n`).
//!
//! `verify` runs [`auslander::artifact::verify_artifact`] with default limits
//! on the calling thread. The verifier code and limits are the native ones.

use auslander::artifact::{ArtifactLimits, ArtifactVerification, verify_artifact};
use auslander::control::ComputationControl;

/// Returns a zeroed buffer of `len` bytes for the caller to fill.
///
/// The pointer is non-null even for `len = 0`. Free it with [`dealloc`].
#[unsafe(no_mangle)]
pub extern "C" fn alloc(len: usize) -> *mut u8 {
    Box::into_raw(vec![0u8; len].into_boxed_slice()).cast()
}

/// Frees a buffer from [`alloc`] or [`verify`].
///
/// # Safety
/// `ptr` and `len` must describe one buffer from [`alloc`], or one result
/// from [`verify`] with `len` equal to 4 plus its stored length. The buffer
/// is not used afterwards.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn dealloc(ptr: *mut u8, len: usize) {
    // SAFETY: the caller passes a boxed slice of exactly `len` bytes.
    drop(unsafe { Box::from_raw(std::ptr::slice_from_raw_parts_mut(ptr, len)) });
}

/// Verifies `len` bytes at `ptr` and returns a length-prefixed JSON result.
///
/// # Safety
/// `ptr` must be non-null and valid for reads of `len` bytes. The caller
/// frees the result with [`dealloc`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verify(ptr: *const u8, len: usize) -> *mut u8 {
    // SAFETY: the caller guarantees `len` readable bytes at `ptr`.
    let input = unsafe { std::slice::from_raw_parts(ptr, len) };
    let json = verify_json(input);
    let length = u32::try_from(json.len()).expect("a result is shorter than 4 GiB");
    let mut output = Vec::with_capacity(4 + json.len());
    output.extend_from_slice(&length.to_le_bytes());
    output.extend_from_slice(json.as_bytes());
    Box::into_raw(output.into_boxed_slice()).cast()
}

/// Verifies one portable value and describes the outcome as JSON.
///
/// The object has the members `status`, `kind`, `fingerprint`, `summary`,
/// and `error`, in that order. `status` is `verified`, `verified-cut`,
/// `stopped`, or `rejected`. `kind` is the kind name, or `null` when the
/// header named no registered kind. `fingerprint` and the `summary` pairs
/// are present only for an accepted value. `error` is the verifier message
/// for a stopped or rejected value, and `null` otherwise.
pub fn verify_json(input: &[u8]) -> String {
    let text = match std::str::from_utf8(input) {
        Ok(text) => text,
        Err(error) => {
            let message = format!("input is not UTF-8 at byte {}", error.valid_up_to());
            return result("rejected", None, None, &[], Some(&message));
        }
    };
    let limits = ArtifactLimits::default();
    match verify_artifact(text, &limits, &ComputationControl::new()) {
        Ok(ArtifactVerification::Verified(value)) => {
            let report = value.report();
            let status = value.status().as_str();
            let kind = Some(report.kind().name());
            result(
                status,
                kind,
                Some(report.fingerprint()),
                report.summary(),
                None,
            )
        }
        Ok(ArtifactVerification::Stopped { kind, cut }) => {
            let message = format!("artifact verification stopped: {cut:?}");
            result("stopped", Some(kind.name()), None, &[], Some(&message))
        }
        Err(error) => {
            let kind = error.kind().map(|kind| kind.name());
            result("rejected", kind, None, &[], Some(&error.to_string()))
        }
    }
}

fn result(
    status: &str,
    kind: Option<&str>,
    fingerprint: Option<&str>,
    summary: &[(&str, String)],
    error: Option<&str>,
) -> String {
    let mut output = String::from("{\"status\":");
    push_string(&mut output, status);
    output.push_str(",\"kind\":");
    push_optional(&mut output, kind);
    output.push_str(",\"fingerprint\":");
    push_optional(&mut output, fingerprint);
    output.push_str(",\"summary\":[");
    for (index, (label, value)) in summary.iter().enumerate() {
        if index != 0 {
            output.push(',');
        }
        output.push('[');
        push_string(&mut output, label);
        output.push(',');
        push_string(&mut output, value);
        output.push(']');
    }
    output.push_str("],\"error\":");
    push_optional(&mut output, error);
    output.push('}');
    output
}

fn push_optional(output: &mut String, value: Option<&str>) {
    match value {
        Some(value) => push_string(output, value),
        None => output.push_str("null"),
    }
}

/// Writes `value` as a JSON string. Control characters use `\u` escapes.
fn push_string(output: &mut String, value: &str) {
    output.push('"');
    for character in value.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            control if u32::from(control) < 0x20 => {
                output.push_str(&format!("\\u{:04x}", u32::from(control)));
            }
            other => output.push(other),
        }
    }
    output.push('"');
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strings_escape_quotes_backslashes_and_control_characters() {
        let mut output = String::new();
        push_string(&mut output, "a\"b\\c\nd\u{1}é");
        assert_eq!(output, "\"a\\\"b\\\\c\\u000ad\\u0001é\"");
    }

    #[test]
    fn invalid_utf8_is_rejected_with_its_offset() {
        assert_eq!(
            verify_json(b"{\xff"),
            "{\"status\":\"rejected\",\"kind\":null,\"fingerprint\":null,\"summary\":[],\
             \"error\":\"input is not UTF-8 at byte 1\"}"
        );
    }
}

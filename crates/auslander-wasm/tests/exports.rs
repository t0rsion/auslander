//! Native tests of the exported C ABI and its JSON result.

mod fixtures;

use auslander::artifact::{ArtifactLimits, ArtifactVerification, verify_artifact};
use auslander::control::ComputationControl;
use auslander_wasm::{alloc, dealloc, verify, verify_json};

/// Calls the exports the way `web/worker.js` does.
fn call_exports(input: &[u8]) -> String {
    let pointer = alloc(input.len());
    // SAFETY: `alloc` returned `input.len()` writable bytes.
    unsafe { std::ptr::copy_nonoverlapping(input.as_ptr(), pointer, input.len()) };
    // SAFETY: the buffer holds `input.len()` initialized bytes.
    let result = unsafe { verify(pointer, input.len()) };
    // SAFETY: the buffer came from `alloc` with this length.
    unsafe { dealloc(pointer, input.len()) };
    // SAFETY: a result starts with its 4-byte little-endian length.
    let length = u32::from_le_bytes(unsafe { *result.cast::<[u8; 4]>() }) as usize;
    // SAFETY: the result holds `length` bytes after the prefix.
    let bytes = unsafe { std::slice::from_raw_parts(result.add(4), length) }.to_vec();
    // SAFETY: the result buffer holds 4 plus `length` bytes.
    unsafe { dealloc(result, 4 + length) };
    String::from_utf8(bytes).unwrap()
}

fn native(text: &str) -> (String, String, String) {
    let limits = ArtifactLimits::default();
    match verify_artifact(text, &limits, &ComputationControl::new()) {
        Ok(ArtifactVerification::Verified(value)) => (
            value.status().as_str().to_string(),
            value.report().kind().name().to_string(),
            value.report().fingerprint().to_string(),
        ),
        Ok(ArtifactVerification::Stopped { kind, .. }) => {
            ("stopped".into(), kind.name().into(), String::new())
        }
        Err(error) => ("rejected".into(), String::new(), error.to_string()),
    }
}

#[test]
fn every_fixture_matches_the_native_dispatch() {
    let mut statuses = Vec::new();
    for (name, text) in fixtures::corpus() {
        let json = call_exports(text.as_bytes());
        assert_eq!(json, verify_json(text.as_bytes()), "{name}");
        let (status, kind, fingerprint) = native(&text);
        let expected = format!("{{\"status\":\"{status}\",\"kind\":\"{kind}\",");
        assert!(json.starts_with(&expected), "{name}: {json}");
        if status.starts_with("verified") {
            assert!(json.contains(&format!("\"fingerprint\":\"{fingerprint}\"")));
        }
        statuses.push(status);
    }
    for status in ["verified", "verified-cut", "stopped"] {
        assert!(statuses.iter().any(|found| found == status), "no {status}");
    }
}

#[test]
fn a_flipped_digit_is_rejected_with_the_native_message() {
    for (name, text) in fixtures::corpus() {
        let position = text.rfind(|c: char| c.is_ascii_digit()).unwrap();
        let mut bytes = text.into_bytes();
        bytes[position] = if bytes[position] == b'0' { b'1' } else { b'0' };
        let tampered = String::from_utf8(bytes).unwrap();
        let (status, _, message) = native(&tampered);
        assert_eq!(status, "rejected", "{name}");
        let json = call_exports(tampered.as_bytes());
        assert!(
            json.starts_with("{\"status\":\"rejected\""),
            "{name}: {json}"
        );
        assert!(
            json.contains(&message.replace('"', "\\\"")),
            "{name}: {json}"
        );
    }
}

#[test]
fn an_empty_input_is_rejected_without_a_kind() {
    let json = call_exports(b"");
    assert!(json.starts_with("{\"status\":\"rejected\",\"kind\":null"));
}

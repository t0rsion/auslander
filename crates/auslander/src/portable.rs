//! Strict canonical JSON shared by every portable artifact.
//!
//! [`Cursor`] reads one document with keys in a fixed order. It checks
//! caller limits before it allocates: string lengths, integer digits,
//! numeric values, and array elements. The writer functions produce the
//! canonical bytes the cursor reads back. [`fingerprint`] is the FNV-1a
//! corruption check over those bytes. It does not authenticate.
//!
//! Every format reads a ceiling or a work counter as `u64`, so a value has
//! one meaning on every host. Indices, dimensions, degrees, and lengths of
//! stored data are `usize`. A 32-bit host rejects such a value above
//! 4294967295 with `integer exceeds usize`, because it cannot hold that
//! much data.
//!
//! Strings hold printable ASCII (`0x20..=0x7e`). Whitespace between tokens
//! is space, tab, line feed, or carriage return. Each artifact maps
//! [`PortableError`] into its own error type, so public `Display` text
//! stays with the artifact.

mod cursor;
mod write;

pub(crate) use cursor::{Cursor, CursorLimits};
pub(crate) use write::{
    fingerprint, is_fingerprint, open_header, push_ascii, push_escaped, push_list,
    push_number_fields, push_number_object, push_numbers, push_tagged_numbers, seal,
};

/// A syntax or limit rejection from [`Cursor`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum PortableError {
    /// The byte at offset `byte` breaks the strict grammar.
    Syntax { byte: usize, message: String },
    /// The field at `path` needs `used` units against a caller `limit`.
    ParseLimit {
        path: String,
        used: usize,
        limit: usize,
    },
}

/// The first header identifier that differs from its expected value, as
/// [`Cursor::header`] reports it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum HeaderMismatch {
    Schema { found: String },
    Kind { found: String },
    Engine { found: String },
}

impl PortableError {
    fn limit(path: &str, used: usize, limit: usize) -> Self {
        Self::ParseLimit {
            path: path.to_string(),
            used,
            limit,
        }
    }
}

#[cfg(test)]
mod tests;

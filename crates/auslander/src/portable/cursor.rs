use super::write::is_fingerprint;
use super::{HeaderMismatch, PortableError};

/// Caller limits that [`Cursor`] checks before it allocates.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CursorLimits {
    /// The greatest byte count of the whole input.
    pub(crate) input_bytes: usize,
    /// The greatest digit count of one unsigned integer.
    pub(crate) integer_digits: usize,
    /// The greatest byte count of one unescaped string.
    pub(crate) string_bytes: usize,
    /// The maximum number of integers in the document.
    pub(crate) numeric_values: usize,
    /// The maximum number of array elements in the document.
    pub(crate) array_elements: usize,
}

impl CursorLimits {
    /// No limit on any counter.
    pub(crate) const NONE: Self = Self {
        input_bytes: usize::MAX,
        integer_digits: usize::MAX,
        string_bytes: usize::MAX,
        numeric_values: usize::MAX,
        array_elements: usize::MAX,
    };
}

/// A position in one strict JSON document with running limit counters.
///
/// Every reader skips leading whitespace. Objects are read key by key in
/// the order the caller names, so an unknown, missing, or reordered key is
/// a syntax error.
pub(crate) struct Cursor<'a> {
    bytes: &'a [u8],
    position: usize,
    limits: CursorLimits,
    numeric_values: usize,
    array_elements: usize,
}

/// An unsigned integer type that [`Cursor::uint`] reads.
pub(crate) trait Unsigned: Copy + Default + TryFrom<u128> {
    /// The type name in the overflow message.
    const NAME: &'static str;
}

impl Unsigned for u64 {
    const NAME: &'static str = "u64";
}

impl Unsigned for usize {
    const NAME: &'static str = "usize";
}

fn printable(byte: u8) -> bool {
    (0x20..=0x7e).contains(&byte)
}

impl<'a> Cursor<'a> {
    /// Starts at byte 0 of `text`. Rejects text longer than
    /// `limits.input_bytes` with path `$`.
    pub(crate) fn new(text: &'a str, limits: CursorLimits) -> Result<Self, PortableError> {
        if text.len() > limits.input_bytes {
            return Err(PortableError::limit("$", text.len(), limits.input_bytes));
        }
        Ok(Self {
            bytes: text.as_bytes(),
            position: 0,
            limits,
            numeric_values: 0,
            array_elements: 0,
        })
    }

    /// A syntax error at the current byte.
    pub(crate) fn syntax(&self, message: impl Into<String>) -> PortableError {
        PortableError::Syntax {
            byte: self.position,
            message: message.into(),
        }
    }

    fn whitespace(&mut self) {
        while matches!(
            self.bytes.get(self.position),
            Some(b' ' | b'\t' | b'\n' | b'\r')
        ) {
            self.position += 1;
        }
    }

    /// The next byte after whitespace, left unconsumed.
    pub(crate) fn peek(&mut self) -> Option<u8> {
        self.whitespace();
        self.bytes.get(self.position).copied()
    }

    /// Consumes `byte` when it is the next byte after whitespace.
    pub(crate) fn eat(&mut self, byte: u8) -> bool {
        let found = self.peek() == Some(byte);
        self.position += usize::from(found);
        found
    }

    /// Consumes `byte` or rejects.
    pub(crate) fn token(&mut self, byte: u8) -> Result<(), PortableError> {
        if self.eat(byte) {
            Ok(())
        } else {
            Err(self.syntax(format!("expected byte {}", byte as char)))
        }
    }

    /// Consumes the object key `key` and its colon.
    pub(crate) fn key(&mut self, key: &str) -> Result<(), PortableError> {
        if self.string("object key")? != key {
            return Err(self.syntax(format!("expected key {key:?}")));
        }
        self.token(b':')
    }

    /// Consumes a comma, then the object key `key` and its colon.
    pub(crate) fn next_key(&mut self, key: &str) -> Result<(), PortableError> {
        self.token(b',')?;
        self.key(key)
    }

    /// Consumes a comma and the object key `key`, then reads its value.
    pub(crate) fn next<T, E: From<PortableError>>(
        &mut self,
        key: &str,
        read: impl FnOnce(&mut Self) -> Result<T, E>,
    ) -> Result<T, E> {
        self.next_key(key)?;
        read(self)
    }

    /// Consumes a comma and returns true, or consumes `close` and returns
    /// false.
    pub(crate) fn more(&mut self, close: u8) -> Result<bool, PortableError> {
        if self.eat(b',') {
            return Ok(true);
        }
        if self.eat(close) {
            return Ok(false);
        }
        Err(self.syntax(if close == b']' {
            "expected comma or array end"
        } else {
            "expected comma or object end"
        }))
    }

    /// Reads the leading members `schema`, `kind`, and `engine` of an open
    /// object and compares them with `expected`, in that order.
    ///
    /// A limit error names each member `{prefix}{key}`.
    pub(crate) fn header<E>(&mut self, prefix: &str, expected: [&str; 3]) -> Result<(), E>
    where
        E: From<PortableError> + From<HeaderMismatch>,
    {
        for (index, key) in ["schema", "kind", "engine"].into_iter().enumerate() {
            if index != 0 {
                self.token(b',')?;
            }
            self.key(key)?;
            let found = self.string(&format!("{prefix}{key}"))?;
            if found != expected[index] {
                return Err(E::from(match index {
                    0 => HeaderMismatch::Schema { found },
                    1 => HeaderMismatch::Kind { found },
                    _ => HeaderMismatch::Engine { found },
                }));
            }
        }
        Ok(())
    }

    /// Rejects `value` at the current byte unless it has the shape of a
    /// [`super::fingerprint`].
    pub(crate) fn fingerprint_shape(&self, value: &str) -> Result<(), PortableError> {
        if !is_fingerprint(value) {
            return Err(self.syntax("fingerprint must contain 16 lowercase hexadecimal digits"));
        }
        Ok(())
    }

    /// Rejects anything but whitespace after the document.
    pub(crate) fn end(&mut self) -> Result<(), PortableError> {
        if self.peek().is_some() {
            return Err(self.syntax("trailing content"));
        }
        Ok(())
    }

    /// Reads a string without escapes. A string longer than
    /// `string_bytes` is rejected with `path`.
    pub(crate) fn string(&mut self, path: &str) -> Result<String, PortableError> {
        self.token(b'"')?;
        let start = self.position;
        loop {
            match self.bytes.get(self.position) {
                Some(b'"') => break,
                Some(&byte) if printable(byte) && byte != b'\\' => self.position += 1,
                Some(_) => return Err(self.syntax("string contains a forbidden byte")),
                None => return Err(self.syntax("unterminated string")),
            }
        }
        let length = self.position - start;
        if length > self.limits.string_bytes {
            return Err(PortableError::limit(path, length, self.limits.string_bytes));
        }
        self.position += 1;
        let text = &self.bytes[start..start + length];
        Ok(std::str::from_utf8(text)
            .expect("printable ASCII")
            .to_string())
    }

    /// Reads a string whose only escapes are `\"` and `\\`.
    /// The decoded length is checked against `limit` before each byte is
    /// stored.
    pub(crate) fn escaped_string(
        &mut self,
        path: &str,
        limit: usize,
    ) -> Result<String, PortableError> {
        self.token(b'"')?;
        let mut output = String::new();
        while let Some(byte) = self.escaped_byte()? {
            if output.len() == limit {
                return Err(PortableError::limit(path, limit + 1, limit));
            }
            output.push(char::from(byte));
        }
        Ok(output)
    }

    fn escaped_byte(&mut self) -> Result<Option<u8>, PortableError> {
        match self.raw_byte()? {
            b'"' => Ok(None),
            b'\\' if matches!(self.bytes.get(self.position), Some(b'"' | b'\\')) => {
                self.raw_byte().map(Some)
            }
            b'\\' => Err(self.syntax("escape must be quote or backslash")),
            byte => Ok(Some(byte)),
        }
    }

    fn raw_byte(&mut self) -> Result<u8, PortableError> {
        match self.bytes.get(self.position) {
            Some(&byte) if printable(byte) => {
                self.position += 1;
                Ok(byte)
            }
            Some(_) => Err(self.syntax("string contains a forbidden byte")),
            None => Err(self.syntax("unterminated string")),
        }
    }

    /// Reads an unsigned decimal integer. `path` names it when it has more
    /// than `integer_digits` digits.
    pub(crate) fn u128(&mut self, path: &str) -> Result<u128, PortableError> {
        self.whitespace();
        let start = self.position;
        while self
            .bytes
            .get(self.position)
            .is_some_and(u8::is_ascii_digit)
        {
            self.position += 1;
        }
        let digits = &self.bytes[start..self.position];
        self.check_integer(path, digits)?;
        let value = std::str::from_utf8(digits)
            .expect("ASCII digits")
            .parse()
            .map_err(|_| self.syntax("integer exceeds u128"))?;
        self.numeric_values += 1;
        Ok(value)
    }

    fn check_integer(&self, path: &str, digits: &[u8]) -> Result<(), PortableError> {
        if digits.is_empty() {
            return Err(self.syntax("expected unsigned integer"));
        }
        if digits.len() > self.limits.integer_digits {
            let limit = self.limits.integer_digits;
            return Err(PortableError::limit(path, digits.len(), limit));
        }
        if digits.len() > 1 && digits[0] == b'0' {
            return Err(self.syntax("integer has a leading zero"));
        }
        if matches!(self.bytes.get(self.position), Some(b'.' | b'e' | b'E')) {
            return Err(self.syntax("number must be an unsigned integer"));
        }
        if self.numeric_values == self.limits.numeric_values {
            let limit = self.limits.numeric_values;
            return Err(PortableError::limit("numeric values", limit + 1, limit));
        }
        Ok(())
    }

    /// Reads an unsigned integer that fits in `T`.
    ///
    /// A larger value is a syntax error that names `T`. A 32-bit host
    /// rejects a `usize` value above 4294967295 that a 64-bit host accepts,
    /// so formats read ceilings and work counters as `u64`.
    pub(crate) fn uint<T: Unsigned>(&mut self, path: &str) -> Result<T, PortableError> {
        T::try_from(self.u128(path)?)
            .map_err(|_| self.syntax(format!("integer exceeds {}", T::NAME)))
    }

    /// Reads an unsigned integer that fits in `u64`.
    pub(crate) fn u64(&mut self, path: &str) -> Result<u64, PortableError> {
        self.uint(path)
    }

    /// Reads an unsigned integer that fits in `usize`.
    pub(crate) fn usize(&mut self, path: &str) -> Result<usize, PortableError> {
        self.uint(path)
    }

    /// Reads a decimal integer with an optional leading `-` that fits in
    /// `i128`. The minus sign must touch the first digit, and `-0` is
    /// rejected, so each value has one spelling.
    pub(crate) fn i128(&mut self, path: &str) -> Result<i128, PortableError> {
        let negative = self.eat(b'-');
        if negative
            && !self
                .bytes
                .get(self.position)
                .is_some_and(u8::is_ascii_digit)
        {
            return Err(self.syntax("expected a digit after the minus sign"));
        }
        let magnitude = self.u128(path)?;
        let value = if negative {
            0i128.checked_sub_unsigned(magnitude)
        } else {
            i128::try_from(magnitude).ok()
        };
        match value {
            Some(0) if negative => Err(self.syntax("integer is negative zero")),
            Some(value) => Ok(value),
            None => Err(self.syntax("integer exceeds i128")),
        }
    }

    /// Reads the literal `true` or `false`.
    pub(crate) fn bool(&mut self) -> Result<bool, PortableError> {
        self.whitespace();
        for (literal, value) in [(&b"true"[..], true), (&b"false"[..], false)] {
            if self.bytes[self.position..].starts_with(literal) {
                self.position += literal.len();
                return Ok(value);
            }
        }
        Err(self.syntax("expected true or false"))
    }

    /// Reads an array, calling `next` with each element index.
    ///
    /// Before `next` runs, the element counts against `limit` (reported
    /// with `path`) and against the document-wide `array_elements`.
    pub(crate) fn array<T, E: From<PortableError>>(
        &mut self,
        path: &str,
        limit: usize,
        mut next: impl FnMut(&mut Self, usize) -> Result<T, E>,
    ) -> Result<Vec<T>, E> {
        self.token(b'[')?;
        let mut output = Vec::new();
        if self.eat(b']') {
            return Ok(output);
        }
        loop {
            self.count_element(path, output.len(), limit)?;
            output.push(next(self, output.len())?);
            if !self.more(b']')? {
                return Ok(output);
            }
        }
    }

    fn count_element(
        &mut self,
        path: &str,
        index: usize,
        limit: usize,
    ) -> Result<(), PortableError> {
        if index == limit {
            return Err(PortableError::limit(path, limit + 1, limit));
        }
        if self.array_elements == self.limits.array_elements {
            let limit = self.limits.array_elements;
            return Err(PortableError::limit("array elements", limit + 1, limit));
        }
        self.array_elements += 1;
        Ok(())
    }

    /// Reads an array of at most `limit` unsigned integers.
    pub(crate) fn numbers(
        &mut self,
        path: &str,
        limit: usize,
    ) -> Result<Vec<usize>, PortableError> {
        self.array(path, limit, |cursor, _| cursor.usize(path))
    }

    /// Reads an object of unsigned integers under `keys`, in that order.
    /// The digit limit names each value `path.key`.
    pub(crate) fn uint_object<T: Unsigned, const N: usize>(
        &mut self,
        path: &str,
        keys: [&str; N],
    ) -> Result<[T; N], PortableError> {
        self.token(b'{')?;
        let values = self.uint_fields(path, keys)?;
        self.token(b'}')?;
        Ok(values)
    }

    /// Reads the leading unsigned-integer members of an open object, as
    /// [`Cursor::uint_object`] does, and leaves the object open.
    pub(crate) fn uint_fields<T: Unsigned, const N: usize>(
        &mut self,
        path: &str,
        keys: [&str; N],
    ) -> Result<[T; N], PortableError> {
        let mut values = [T::default(); N];
        for (index, key) in keys.into_iter().enumerate() {
            if index != 0 {
                self.token(b',')?;
            }
            self.key(key)?;
            values[index] = self.uint(&format!("{path}.{key}"))?;
        }
        Ok(values)
    }

    /// Returns one object verbatim, without checking its members.
    ///
    /// The scan tracks braces outside strings and skips escaped bytes. The
    /// caller parses the returned text with the embedded format's own
    /// strict parser. An object longer than `limit` bytes is rejected with
    /// `path`.
    pub(crate) fn raw_object(
        &mut self,
        path: &str,
        limit: usize,
    ) -> Result<&'a str, PortableError> {
        if self.peek() != Some(b'{') {
            return Err(self.syntax("expected an object"));
        }
        let start = self.position;
        let mut scan = ObjectScan::default();
        while let Some(&byte) = self.bytes.get(self.position) {
            self.position += 1;
            if self.position - start > limit {
                return Err(PortableError::limit(path, self.position - start, limit));
            }
            if scan.closes(byte) {
                let text = &self.bytes[start..self.position];
                return Ok(std::str::from_utf8(text).expect("the input is UTF-8"));
            }
        }
        Err(self.syntax("unterminated object"))
    }
}

#[derive(Default)]
struct ObjectScan {
    depth: usize,
    in_string: bool,
    escaped: bool,
}

impl ObjectScan {
    /// Consumes one byte and reports whether it closes the outer object.
    fn closes(&mut self, byte: u8) -> bool {
        if self.in_string {
            self.string_byte(byte);
            return false;
        }
        match byte {
            b'"' => self.in_string = true,
            b'{' => self.depth += 1,
            b'}' if self.depth == 1 => return true,
            b'}' if self.depth > 1 => self.depth -= 1,
            _ => {}
        }
        false
    }

    fn string_byte(&mut self, byte: u8) {
        if self.escaped {
            self.escaped = false;
        } else if byte == b'\\' {
            self.escaped = true;
        } else if byte == b'"' {
            self.in_string = false;
        }
    }
}

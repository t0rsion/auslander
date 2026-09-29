use super::*;

fn limits(edit: impl FnOnce(&mut CursorLimits)) -> CursorLimits {
    let mut limits = CursorLimits::NONE;
    edit(&mut limits);
    limits
}

fn read<T>(
    text: &str,
    limits: CursorLimits,
    value: impl FnOnce(&mut Cursor) -> Result<T, PortableError>,
) -> Result<T, PortableError> {
    let mut cursor = Cursor::new(text, limits)?;
    let read = value(&mut cursor)?;
    cursor.end()?;
    Ok(read)
}

fn i128_of(text: &str) -> Result<i128, PortableError> {
    read(text, CursorLimits::NONE, |c| c.i128("n"))
}

fn is_limit(result: Result<impl std::fmt::Debug, PortableError>, path: &str, used: usize) -> bool {
    matches!(result, Err(PortableError::ParseLimit { path: p, used: u, .. }) if p == path && u == used)
}

/// The FNV-1a offset basis is the fingerprint of the empty text, and the
/// published test vector for `a` is `af63dc4c8601ec8c`.
#[test]
fn fingerprints_match_the_fnv_1a_vectors() {
    assert_eq!(fingerprint(""), "cbf29ce484222325");
    assert_eq!(fingerprint("a"), "af63dc4c8601ec8c");
    assert!(is_fingerprint(&fingerprint("anything")));
    assert!(!is_fingerprint("CBF29CE484222325"));
    assert!(!is_fingerprint("cbf29ce48422232"));
}

/// `i128` accepts both ends of its range and rejects one past each end,
/// `-0`, a detached sign, and a leading zero.
#[test]
fn signed_integers_have_exact_bounds_and_one_spelling() {
    assert_eq!(i128_of(&i128::MAX.to_string()).unwrap(), i128::MAX);
    assert_eq!(i128_of(&i128::MIN.to_string()).unwrap(), i128::MIN);
    assert_eq!(i128_of(" -7").unwrap(), -7);
    for text in [
        "170141183460469231731687303715884105728",
        "-170141183460469231731687303715884105729",
        "-0",
        "- 1",
        "-",
        "01",
        "1.0",
        "1e3",
    ] {
        assert!(
            matches!(i128_of(text), Err(PortableError::Syntax { .. })),
            "{text}"
        );
    }
}

/// `u64` reads `u64::MAX` and rejects the next value by name.
#[test]
fn unsigned_integers_name_the_type_they_exceed() {
    let max = u64::MAX.to_string();
    assert_eq!(read(&max, CursorLimits::NONE, |c| c.u64("n")), Ok(u64::MAX));
    let over = (u128::from(u64::MAX) + 1).to_string();
    let error = read(&over, CursorLimits::NONE, |c| c.u64("n")).unwrap_err();
    assert!(
        matches!(error, PortableError::Syntax { message, .. } if message == "integer exceeds u64")
    );
}

/// Every counter accepts exactly its limit and rejects one more.
#[test]
fn every_counter_accepts_its_limit_and_rejects_one_more() {
    let digits = limits(|l| l.integer_digits = 3);
    assert_eq!(read("999", digits, |c| c.u64("n")), Ok(999));
    assert!(is_limit(read("1000", digits, |c| c.u64("n")), "n", 4));

    let input = limits(|l| l.input_bytes = 3);
    assert!(Cursor::new("123", input).is_ok());
    assert!(is_limit(Cursor::new("1234", input).map(|_| ()), "$", 4));

    let string = limits(|l| l.string_bytes = 2);
    assert_eq!(read("\"ab\"", string, |c| c.string("s")).unwrap(), "ab");
    assert!(is_limit(read("\"abc\"", string, |c| c.string("s")), "s", 3));

    let numbers = limits(|l| l.numeric_values = 2);
    assert_eq!(
        read("[1,2]", numbers, |c| c.numbers("a", 9)).unwrap(),
        [1, 2]
    );
    let over = read("[1,2,3]", numbers, |c| c.numbers("a", 9));
    assert!(is_limit(over, "numeric values", 3));

    let elements = limits(|l| l.array_elements = 2);
    assert_eq!(
        read("[1,2]", elements, |c| c.numbers("a", 9)).unwrap(),
        [1, 2]
    );
    let over = read("[1,2,3]", elements, |c| c.numbers("a", 9));
    assert!(is_limit(over, "array elements", 3));

    let none = CursorLimits::NONE;
    assert_eq!(read("[]", none, |c| c.numbers("a", 0)).unwrap(), [0; 0]);
    assert_eq!(read("[5]", none, |c| c.numbers("a", 1)).unwrap(), [5]);
    assert!(is_limit(read("[5,6]", none, |c| c.numbers("a", 1)), "a", 2));
}

/// An escaped string holds exactly `limit` decoded bytes, and only `\"`
/// and `\\` escape.
#[test]
fn escaped_strings_decode_two_escapes_up_to_their_limit() {
    let none = CursorLimits::NONE;
    let decoded = read(r#""a\"\\""#, none, |c| c.escaped_string("s", 3));
    assert_eq!(decoded.unwrap(), "a\"\\");
    assert!(is_limit(
        read(r#""abcd""#, none, |c| c.escaped_string("s", 3)),
        "s",
        4
    ));
    let bad = read(r#""\n""#, none, |c| c.escaped_string("s", 9));
    assert!(matches!(bad, Err(PortableError::Syntax { .. })));
    let control = read("\"a\tb\"", none, |c| c.escaped_string("s", 9));
    assert!(matches!(control, Err(PortableError::Syntax { .. })));
}

/// A raw object ends at its matching brace, skips braces inside strings,
/// and holds at most `limit` bytes.
#[test]
fn raw_objects_scan_nested_braces_up_to_their_limit() {
    let text = r#"{"a":{"b":"}\"{"}}"#;
    let whole = text.len();
    let scan = |limit| {
        read(text, CursorLimits::NONE, |c| {
            c.raw_object("o", limit).map(str::len)
        })
    };
    assert_eq!(scan(whole), Ok(whole));
    assert!(is_limit(scan(whole - 1), "o", whole));
    let open = read("{\"a\":{}", CursorLimits::NONE, |c| {
        c.raw_object("o", 99).map(str::len)
    });
    assert!(matches!(open, Err(PortableError::Syntax { .. })));
}

/// Keys are read in the named order, and a boolean is one of two literals.
#[test]
fn keys_and_literals_are_strict() {
    let none = CursorLimits::NONE;
    let object = |text| {
        read(text, none, |c| {
            c.token(b'{')?;
            let values = c.uint_fields::<u64, 2>("o", ["x", "y"])?;
            c.next_key("flag")?;
            let flag = c.bool()?;
            c.token(b'}')?;
            Ok((values, flag))
        })
    };
    assert_eq!(object(r#"{"x":1,"y":2,"flag":true}"#), Ok(([1, 2], true)));
    for text in [
        r#"{"y":2,"x":1,"flag":true}"#,
        r#"{"x":1,"y":2,"flag":True}"#,
        r#"{"x":1,"y":2,"flag":false,"z":0}"#,
        r#"{"x":1,"y":2,"flag":false} x"#,
    ] {
        assert!(
            matches!(object(text), Err(PortableError::Syntax { .. })),
            "{text}"
        );
    }
}

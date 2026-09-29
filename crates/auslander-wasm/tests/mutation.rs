//! Seeded mutation tests of every artifact verifier through the dispatch.
//!
//! Each committed artifact and each parity fixture is mutated by byte flips,
//! key deletions, number perturbations, and array reorders. When a document
//! ends with an FNV-1a fingerprint of its preceding bytes, most mutants are
//! resealed so the edit reaches the semantic checks. The verifier must never
//! panic. It may accept a mutant only when the edit lies in a field whose
//! edited value the replay itself checks, or in a walk record, which the
//! atlas verifier documents as unchecked. See `benign`.

mod fixtures;

use std::panic::{AssertUnwindSafe, catch_unwind};

use auslander_wasm::verify_json;

const RESEARCH: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../auslander/artifacts/research/"
);

/// Every committed artifact that a verifier replays.
fn committed() -> Vec<(&'static str, String)> {
    let names = [
        "derived-atlas-f2-n3.json",
        "commutative-square-f2-d1111-self-ext-1-3.json",
        "commutative-square-f2-d2112-self-ext-1-3.json",
    ];
    let read = |name| std::fs::read_to_string(format!("{RESEARCH}{name}")).unwrap();
    names.into_iter().map(|name| (name, read(name))).collect()
}

/// A xorshift64* generator, so every run sees the same mutants.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn below(&mut self, bound: usize) -> usize {
        (self.next() % bound as u64) as usize
    }

    fn pick<T: Copy>(&mut self, items: &[T]) -> Option<T> {
        (!items.is_empty()).then(|| items[self.below(items.len())])
    }
}

/// The strict JSON structure of one canonical document: for each byte,
/// whether it lies inside a string, quotes included.
struct Layout<'a> {
    bytes: &'a [u8],
    in_string: Vec<bool>,
}

impl<'a> Layout<'a> {
    fn new(text: &'a str) -> Layout<'a> {
        let bytes = text.as_bytes();
        let (mut inside, mut escaped) = (false, false);
        let in_string = bytes
            .iter()
            .map(|&byte| {
                let opens = !inside && byte == b'"';
                let closes = inside && !escaped && byte == b'"';
                let mark = inside || opens;
                escaped = inside && !escaped && byte == b'\\';
                inside = (inside || opens) && !closes;
                mark
            })
            .collect();
        Layout { bytes, in_string }
    }

    fn structural(&self, at: usize) -> bool {
        !self.in_string[at]
    }

    /// Whether `at` is the opening quote of a string.
    fn opens_string(&self, at: usize) -> bool {
        self.in_string[at] && (at == 0 || !self.in_string[at - 1])
    }

    /// The end, exclusive, of the value that starts at `start`.
    fn value_end(&self, start: usize) -> usize {
        match self.bytes[start] {
            b'"' => (start + 1..self.bytes.len())
                .find(|&at| at + 1 == self.bytes.len() || !self.in_string[at + 1])
                .map_or(self.bytes.len(), |at| at + 1),
            b'{' | b'[' => self.container_end(start),
            _ => (start..self.bytes.len())
                .find(|&at| !matches!(self.bytes[at], b'0'..=b'9' | b'a'..=b'z' | b'-'))
                .unwrap_or(self.bytes.len()),
        }
    }

    fn container_end(&self, start: usize) -> usize {
        let mut depth = 0usize;
        for at in start..self.bytes.len() {
            if self.structural(at) {
                match self.bytes[at] {
                    b'{' | b'[' => depth += 1,
                    b'}' | b']' => depth -= 1,
                    _ => {}
                }
                if depth == 0 {
                    return at + 1;
                }
            }
        }
        self.bytes.len()
    }

    /// The opening quotes of every object key.
    fn keys(&self) -> Vec<usize> {
        let opens_key = |at: usize| {
            self.bytes[at] == b'"'
                && at > 0
                && matches!(self.bytes[at - 1], b'{' | b',')
                && self.structural(at - 1)
                && self.bytes.get(self.value_end(at)) == Some(&b':')
        };
        (0..self.bytes.len()).filter(|&at| opens_key(at)).collect()
    }

    /// The element spans of the array that opens at `start`.
    fn elements(&self, start: usize) -> Vec<(usize, usize)> {
        let mut spans = Vec::new();
        let mut at = start + 1;
        while self.bytes.get(at).is_some_and(|&byte| byte != b']') {
            let end = self.value_end(at);
            spans.push((at, end));
            at = end + usize::from(self.bytes.get(end) == Some(&b','));
        }
        spans
    }

    /// The object keys and array levels that enclose byte `site`.
    fn path(&self, site: usize) -> Vec<String> {
        let mut stack: Vec<String> = Vec::new();
        for at in 0..site.min(self.bytes.len()) {
            self.step_path(at, &mut stack);
        }
        stack
    }

    fn step_path(&self, at: usize, stack: &mut Vec<String>) {
        let byte = self.bytes[at];
        if !self.structural(at) {
            if self.opens_string(at) && self.bytes.get(self.value_end(at)) == Some(&b':') {
                let key = &self.bytes[at + 1..self.value_end(at) - 1];
                *stack.last_mut().unwrap() = String::from_utf8_lossy(key).into_owned();
            }
            return;
        }
        match byte {
            b'{' => stack.push(String::new()),
            b'[' => stack.push("[]".into()),
            b'}' | b']' => drop(stack.pop()),
            _ => {}
        }
    }
}

/// One mutation: the edited bytes and the byte offset of the edit.
struct Mutant {
    operator: &'static str,
    bytes: Vec<u8>,
    site: usize,
}

fn splice(text: &str, (start, end): (usize, usize), with: &[u8]) -> Vec<u8> {
    let mut bytes = text.as_bytes()[..start].to_vec();
    bytes.extend_from_slice(with);
    bytes.extend_from_slice(&text.as_bytes()[end..]);
    bytes
}

fn flip(text: &str, rng: &mut Rng) -> Option<Mutant> {
    let site = rng.below(text.len());
    let old = text.as_bytes()[site];
    let new = match rng.below(3) {
        0 => old ^ (1 << rng.below(8)),
        1 => b" \"\\,:[]{}0-9a"[rng.below(13)],
        _ => 0x20 + rng.below(95) as u8,
    };
    let bytes = splice(text, (site, site + 1), &[new]);
    Some(Mutant {
        operator: "flip",
        bytes,
        site,
    })
}

fn delete_key(text: &str, rng: &mut Rng) -> Option<Mutant> {
    let layout = Layout::new(text);
    let key = rng.pick(&layout.keys())?;
    let value = layout.value_end(key) + 1;
    let end = layout.value_end(value);
    let span = match layout.bytes[key - 1] {
        b',' => (key - 1, end),
        _ => (key, end + usize::from(layout.bytes.get(end) == Some(&b','))),
    };
    Some(Mutant {
        operator: "delete-key",
        bytes: splice(text, span, b""),
        site: key + 1,
    })
}

fn perturb_number(text: &str, rng: &mut Rng) -> Option<Mutant> {
    let bytes = text.as_bytes();
    let starts: Vec<usize> = (0..bytes.len())
        .filter(|&at| bytes[at].is_ascii_digit() && (at == 0 || !bytes[at - 1].is_ascii_digit()))
        .collect();
    let start = rng.pick(&starts)?;
    let end = (start..bytes.len())
        .find(|&at| !bytes[at].is_ascii_digit())
        .unwrap_or(bytes.len());
    let value: u128 = text[start..end].parse().unwrap_or(0);
    let replacement = match rng.below(6) {
        0 => value.saturating_add(1),
        1 => value.saturating_sub(1),
        2 => 0,
        3 => value.saturating_mul(2).saturating_add(1),
        4 => u128::from(u32::MAX) + 1,
        _ => u128::from(u64::MAX),
    };
    Some(Mutant {
        operator: "number",
        bytes: splice(text, (start, end), replacement.to_string().as_bytes()),
        site: start,
    })
}

fn reorder(text: &str, rng: &mut Rng) -> Option<Mutant> {
    let layout = Layout::new(text);
    let arrays: Vec<usize> = (0..text.len())
        .filter(|&at| layout.structural(at) && layout.bytes[at] == b'[')
        .filter(|&at| layout.bytes.get(at + 1) != Some(&b']'))
        .collect();
    let start = rng.pick(&arrays)?;
    let spans = layout.elements(start);
    let (left, right) = (rng.below(spans.len()), rng.below(spans.len()));
    if left == right {
        return None;
    }
    let (left, right) = (spans[left.min(right)], spans[left.max(right)]);
    let mut bytes = text.as_bytes()[..left.0].to_vec();
    bytes.extend_from_slice(&text.as_bytes()[right.0..right.1]);
    bytes.extend_from_slice(&text.as_bytes()[left.1..right.0]);
    bytes.extend_from_slice(&text.as_bytes()[left.0..left.1]);
    bytes.extend_from_slice(&text.as_bytes()[right.1..]);
    Some(Mutant {
        operator: "reorder",
        bytes,
        site: start + 1,
    })
}

const OPERATORS: [fn(&str, &mut Rng) -> Option<Mutant>; 4] =
    [flip, delete_key, perturb_number, reorder];

/// The FNV-1a fingerprint that every portable format uses.
fn fingerprint(text: &[u8]) -> String {
    let hash = text.iter().fold(0xcbf2_9ce4_8422_2325u64, |value, &byte| {
        (value ^ u64::from(byte)).wrapping_mul(0x0100_0000_01b3)
    });
    format!("{hash:016x}")
}

const SEAL: &[u8] = b",\"fingerprint\":\"";

/// `bytes` with its trailing fingerprint recomputed, when it has one.
fn reseal(bytes: &[u8]) -> Option<Vec<u8>> {
    let at = bytes
        .windows(SEAL.len())
        .rposition(|window| window == SEAL)?;
    let tail = &bytes[at + SEAL.len()..];
    if tail.len() != 18 || !tail.ends_with(b"\"}") {
        return None;
    }
    let mut sealed = bytes[..at + SEAL.len()].to_vec();
    sealed.extend_from_slice(fingerprint(&bytes[..at]).as_bytes());
    sealed.extend_from_slice(b"\"}");
    Some(sealed)
}

/// Whether an accepted edit at `path` can still state a true claim.
///
/// A declared limit or stream configuration only bounds the replay, which
/// ran under the edited value. The self-Ext locus is recomputed over the
/// stored degree range. A recipe step is replayed to the stored target, and
/// an isomorphism coordinate is verified, so an accepted edit there is a
/// checked merge. The merges of a class form a set, so their order carries
/// no claim. A separation is rebuilt from the recomputed readings of its
/// members, so accepted members are a checked witness. The atlas verifier
/// documents its walk records as unchecked, except the member and the merge
/// count.
fn benign(path: &[String]) -> bool {
    let joined = path.join("/");
    let checked_walk_field = ["walks/[]/member", "walks/[]/merges"].contains(&joined.as_str());
    path.first().is_some_and(|key| key.ends_with("limits"))
        || joined == "classes/[]/merges/[]"
        || CHECKED.iter().any(|prefix| joined.starts_with(prefix))
        || (joined.starts_with("walks/[]/") && !checked_walk_field)
}

/// Path prefixes where an accepted edit still states a true claim. See
/// `benign`.
const CHECKED: [&str; 8] = [
    "config",
    "mutations",
    "first_degree",
    "last_degree",
    "classes/[]/merges/[]/recipe",
    "classes/[]/merges/[]/vertex_map",
    "classes/[]/merges/[]/arrow_images",
    "separations/[]/members",
];

/// The verifier outcome as `verify_json` reports it, or the panic message.
fn outcome(bytes: &[u8]) -> Result<String, String> {
    catch_unwind(AssertUnwindSafe(|| verify_json(bytes))).map_err(|panic| {
        let text = panic.downcast_ref::<String>().cloned();
        let text = text.or_else(|| panic.downcast_ref::<&str>().map(|s| s.to_string()));
        text.unwrap_or_default()
    })
}

#[derive(Default)]
struct Tally {
    cases: usize,
    accepted: usize,
    failures: Vec<String>,
}

impl Tally {
    fn run(&mut self, name: &str, original: &str, mutant: Mutant, sealed: bool) {
        let bytes = match sealed {
            true => reseal(&mutant.bytes).unwrap_or(mutant.bytes),
            false => mutant.bytes,
        };
        if bytes == original.as_bytes() {
            return;
        }
        self.cases += 1;
        let path = Layout::new(original).path(mutant.site);
        let describe = |what: &str| format!("{name} {} at {:?}: {what}", mutant.operator, path);
        match outcome(&bytes) {
            Err(panic) => self.failures.push(describe(&format!("panic {panic}"))),
            Ok(json) if json.starts_with("{\"status\":\"verified") => {
                self.accepted += 1;
                if !benign(&path) {
                    self.failures.push(describe("accepted"));
                }
            }
            Ok(_) => {}
        }
    }
}

/// Runs `cases` mutants of each document and returns the tally.
fn mutate(documents: &[(&str, String)], cases: usize, seed: u64) -> Tally {
    let mut rng = Rng(seed);
    let mut tally = Tally::default();
    for (name, text) in documents {
        let sealable = reseal(text.as_bytes()).as_deref() == Some(text.as_bytes());
        for _ in 0..cases {
            let operator = OPERATORS[rng.below(OPERATORS.len())];
            let Some(mutant) = operator(text, &mut rng) else {
                continue;
            };
            let sealed = sealable && rng.below(8) != 0;
            tally.run(name, text, mutant, sealed);
        }
    }
    tally
}

fn assert_clean(tally: &Tally) {
    eprintln!(
        "{} mutants, {} accepted, {} failures",
        tally.cases,
        tally.accepted,
        tally.failures.len()
    );
    let shown: Vec<_> = tally.failures.iter().take(20).collect();
    assert!(tally.failures.is_empty(), "{shown:#?}");
}

/// Every document that the fast run mutates: the parity corpus without its
/// largest atlas, whose full replay is slow in the dev profile.
fn fast_documents() -> Vec<(&'static str, String)> {
    let corpus = fixtures::corpus().into_iter();
    corpus
        .filter(|(name, _)| *name != "derived-atlas-n3.json")
        .collect()
}

#[test]
fn mutants_never_panic_and_never_verify_a_changed_claim() {
    assert_clean(&mutate(&fast_documents(), 150, 0x5eed_0001));
}

/// `MUTATION_SEED` and `MUTATION_CASES` override the seed and the cases per
/// document, for longer exploration runs.
#[test]
#[ignore = "heavy: every committed artifact and the whole corpus, about a minute"]
fn many_mutants_of_every_artifact() {
    let mut documents = fixtures::corpus();
    documents.extend(committed());
    let setting = |name, default| {
        let value = std::env::var(name).ok();
        value.map_or(default, |value| value.parse().unwrap())
    };
    let cases = setting("MUTATION_CASES", 400) as usize;
    assert_clean(&mutate(
        &documents,
        cases,
        setting("MUTATION_SEED", 0x5eed_0002),
    ));
}

#[test]
fn the_layout_reads_keys_elements_and_paths() {
    let text = r#"{"a":[1,{"b":"x\"y"}],"c":{"d":[]},"fingerprint":"0000000000000000"}"#;
    let layout = Layout::new(text);
    let keys: Vec<&str> = layout
        .keys()
        .into_iter()
        .map(|at| &text[at + 1..layout.value_end(at) - 1])
        .collect();
    assert_eq!(keys, ["a", "b", "c", "d", "fingerprint"]);
    assert_eq!(layout.elements(5), [(6, 7), (8, 20)]);
    assert_eq!(layout.path(text.find("x").unwrap()), ["a", "[]", "b"]);
    let sealed = reseal(text.as_bytes()).unwrap();
    assert_eq!(reseal(&sealed).unwrap(), sealed);
}

//! Helpers shared by more than one integration test binary.
//!
//! Every binary that declares `mod common;` compiles the whole file, so items
//! it does not call would warn.
#![allow(dead_code)]

use std::env;
use std::fs;
use std::io::Read;
use std::path::Path;
use std::process::{Command, Stdio};
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

use auslander::algebra::Algebra;
use auslander::almost_split::{
    AlmostSplitOutcome, AlmostSplitSequence, AlmostSplitWitness, ArDualityWitness, CatalogWitness,
    almost_split, almost_split_via_catalog,
};
use auslander::arquiver::IndecomposableCatalog;
use auslander::completion::CompletionLimits;
use auslander::ext::{ExtClass, ExtSpace};
use auslander::field::{Fp, PrimeField};
use auslander::indec::IndecomposableModule;
use auslander::linalg::DenseMat;
use auslander::module::{Module, direct_sum};
use auslander::quiver::{ArrowId, Quiver};
use auslander::relation::{Presentation, Relation};

pub fn f2() -> PrimeField {
    PrimeField::new(2).unwrap()
}

pub fn f5() -> PrimeField {
    PrimeField::new(5).unwrap()
}

pub fn ids(raw: &[u32]) -> Vec<ArrowId> {
    raw.iter().copied().map(ArrowId).collect()
}

/// The presentation of the preprojective algebra of A_3 over F_2: the double
/// quiver `a: 0 -> 1` (id 0), `b: 1 -> 2` (1), `abar: 1 -> 0` (2),
/// `bbar: 2 -> 1` (3) with relations `a·abar`, `abar·a - b·bbar`, `bbar·b`.
/// Separate from [`preprojective_a3`] because one test completes it under
/// tight [`CompletionLimits`].
pub fn preprojective_a3_presentation() -> Presentation {
    let field = f2();
    let quiver = Quiver::new(3, &[(0, 1), (1, 2), (1, 0), (2, 1)]).unwrap();
    let relations = vec![
        Relation::new(&quiver, field, vec![(field.one(), ids(&[0, 2]))]).unwrap(),
        Relation::new(
            &quiver,
            field,
            vec![(field.one(), ids(&[2, 0])), (field.elem(-1), ids(&[1, 3]))],
        )
        .unwrap(),
        Relation::new(&quiver, field, vec![(field.one(), ids(&[3, 1]))]).unwrap(),
    ];
    Presentation::new(quiver, field, relations).unwrap()
}

/// The preprojective algebra of A_3 over F_2: dimension 10, self-injective.
/// The `preprojective-a3` `f2` fixture of the QPA oracle.
pub fn preprojective_a3() -> Arc<Algebra> {
    Algebra::new(
        preprojective_a3_presentation(),
        &CompletionLimits::default(),
    )
    .unwrap()
}

/// The quiver of [`inhomogeneous`]: arrows `a: 0 -> 1` (id 0), `b: 1 -> 4` (1),
/// `c: 0 -> 2` (2), `d: 2 -> 3` (3), `e: 3 -> 4` (4).
pub fn inhomogeneous_quiver() -> Quiver {
    Quiver::new(5, &[(0, 1), (1, 4), (0, 2), (2, 3), (3, 4)]).unwrap()
}

/// The inhomogeneous algebra `kQ/(ab - cde)` over F_5: dimension 13. The
/// relation mixes path lengths, so a short normal word sits inside a deep
/// radical power.
pub fn inhomogeneous() -> Arc<Algebra> {
    let field = f5();
    let quiver = inhomogeneous_quiver();
    let relation = Relation::new(
        &quiver,
        field,
        vec![
            (field.one(), ids(&[0, 1])),
            (field.elem(-1), ids(&[2, 3, 4])),
        ],
    )
    .unwrap();
    let presentation = Presentation::new(quiver, field, vec![relation]).unwrap();
    Algebra::new(presentation, &CompletionLimits::default()).unwrap()
}

/// The `k`-th standard basis class of `space`.
pub fn basis_class(space: &ExtSpace, k: usize) -> ExtClass {
    let field = space.source().field();
    let mut coords = vec![field.zero(); space.dim()];
    coords[k] = field.one();
    space.class_from_coordinates(&coords).unwrap()
}

pub fn duality_sequence(m: &IndecomposableModule) -> AlmostSplitSequence {
    match almost_split(m).unwrap() {
        AlmostSplitOutcome::Sequence(sequence) => sequence,
        AlmostSplitOutcome::Projective => panic!("expected a sequence, got Projective"),
    }
}

pub fn catalog_sequence(
    m: &IndecomposableModule,
    catalog: &IndecomposableCatalog,
) -> AlmostSplitSequence {
    match almost_split_via_catalog(m, catalog).unwrap() {
        AlmostSplitOutcome::Sequence(sequence) => sequence,
        AlmostSplitOutcome::Projective => panic!("expected a sequence, got Projective"),
    }
}

pub fn duality_witness(sequence: &AlmostSplitSequence) -> &ArDualityWitness {
    match sequence.witness() {
        AlmostSplitWitness::ArDuality(witness) => witness,
        AlmostSplitWitness::ExhaustiveCatalog(_) => panic!("expected the AR duality witness"),
    }
}

pub fn catalog_witness(sequence: &AlmostSplitSequence) -> &CatalogWitness {
    match sequence.witness() {
        AlmostSplitWitness::ExhaustiveCatalog(witness) => witness,
        AlmostSplitWitness::ArDuality(_) => panic!("expected the catalog witness"),
    }
}

/// Rewrites `path` with `bytes` when `var` holds exactly `"1"`, and reports
/// whether it did. Any other value, `"0"` included, leaves the caller's
/// byte-for-byte comparison armed.
///
/// Setting `var` under CI is a hard error. GitHub Actions always sets `CI`, so
/// a rewrite there would overwrite the committed goldens instead of comparing
/// against them, and every golden gate would pass by construction.
///
/// After the write the file is read back and checked against `bytes`, so the
/// write path cannot leave a golden the next run trusts.
pub fn rewrite_golden(var: &str, path: &Path, bytes: &[u8]) -> bool {
    let requested = env::var(var).as_deref() == Ok("1");
    assert!(
        !(requested && env::var("CI").is_ok()),
        "{var} is set under CI: the goldens would be rewritten, not compared"
    );
    if !requested {
        return false;
    }
    fs::write(path, bytes).unwrap_or_else(|e| panic!("cannot write {}: {e}", path.display()));
    let back =
        fs::read(path).unwrap_or_else(|e| panic!("cannot read back {}: {e}", path.display()));
    assert_eq!(
        back,
        bytes,
        "{} does not hold the bytes just written",
        path.display()
    );
    true
}

/// FNV-1a, 64 bit. Written out here so a fingerprint does not depend on any
/// hasher with unspecified cross-process behavior.
pub fn fnv1a(bytes: &[u8]) -> u64 {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for &byte in bytes {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    hash
}

/// The one line a child test prints: `marker`, the FNV-1a hash of `payload`,
/// and its byte length.
pub fn fingerprint(marker: &str, payload: &str) -> String {
    format!(
        "{marker}{:016x}:len:{}",
        fnv1a(payload.as_bytes()),
        payload.len()
    )
}

/// Runs the current test binary on `test_name` alone with `child_env` set to
/// `"1"`, and returns its stdout.
///
/// The child is polled and killed after `timeout`, so a hang fails one test
/// instead of stalling the run. The child must report `1 passed`, which catches
/// a renamed test that would otherwise pass vacuously.
pub fn child_test_stdout(test_name: &str, child_env: &str, timeout: Duration) -> String {
    let exe = env::current_exe().expect("path of the running test binary");
    let mut child = Command::new(exe)
        .args(["--exact", test_name, "--nocapture"])
        .env(child_env, "1")
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("spawn the child test process");
    let deadline = Instant::now() + timeout;
    let status = loop {
        match child.try_wait().expect("poll the child test process") {
            Some(status) => break status,
            None if Instant::now() >= deadline => {
                child.kill().ok();
                child.wait().ok();
                panic!("{test_name} ran past {timeout:?}");
            }
            None => thread::sleep(Duration::from_millis(50)),
        }
    };
    let mut stdout = String::new();
    child
        .stdout
        .take()
        .expect("stdout was piped")
        .read_to_string(&mut stdout)
        .expect("read child output");
    assert!(status.success(), "child test failed:\n{stdout}");
    assert!(
        stdout.contains("1 passed"),
        "child ran zero tests; was {test_name} renamed?\n{stdout}"
    );
    stdout
}

/// The `marker` and everything after it, from the one line of `stdout` that
/// carries it.
///
/// The marker is found ANYWHERE in the line, not only at its start. When
/// `available_parallelism()` is 1, libtest prints the test name before running
/// the test, so the child's own `println!` continues that line instead of
/// starting one, and a start-anchored search finds nothing. That happens on a
/// single-core machine and under `taskset -c 1`, and it made every
/// fresh-process gate fail for a reason unrelated to determinism.
///
/// Searching the whole line cannot turn a failure into a false pass: the
/// marker must still appear, and the caller still compares the payload after
/// it.
pub fn marked_line(stdout: &str, marker: &str) -> String {
    stdout
        .lines()
        .find_map(|line| line.find(marker).map(|at| line[at..].to_string()))
        .unwrap_or_else(|| panic!("child printed no {marker} line:\n{stdout}"))
}

/// xorshift64, the seeded stream behind the randomized suites. A seed of zero
/// is a fixed point, so callers must pass a nonzero one.
pub struct XorShift64(pub u64);

impl XorShift64 {
    pub fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    pub fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
}

/// Distinct nonzero seed per (test, field, algebra, case), splittable from the
/// printed value alone. `base` separates one suite's stream from another's.
pub fn case_seed(base: u64, test: u64, p: u64, algebra_idx: usize, case: usize) -> u64 {
    let raw = base
        ^ test.wrapping_mul(0x9e37_79b9_7f4a_7c15)
        ^ p.wrapping_mul(0xd1b5_4a32_d192_ed03)
        ^ (algebra_idx as u64).wrapping_mul(0x94d0_49bb_1331_11eb)
        ^ (case as u64).wrapping_mul(0x2545_f491_4f6c_dd1d);
    if raw == 0 { base } else { raw }
}

pub fn rand_elem(rng: &mut XorShift64, field: &PrimeField) -> Fp {
    field.elem(rng.below(field.modulus()) as i64)
}

/// A random direct sum of projectives, simples, and injectives with total
/// dimension at most `budget`.
pub fn random_sum_module(rng: &mut XorShift64, algebra: &Arc<Algebra>, budget: usize) -> Module {
    let n = algebra.quiver().num_vertices();
    let mut parts: Vec<Module> = Vec::new();
    let mut total = 0usize;
    for _ in 0..1 + rng.below(3) {
        let v = rng.below(u64::from(n)) as u32;
        let part = match rng.below(3) {
            0 => Module::simple(algebra, v),
            1 => Module::projective(algebra, v),
            _ => Module::injective(algebra, v),
        };
        if total + part.total_dim() > budget {
            break;
        }
        total += part.total_dim();
        parts.push(part);
    }
    if parts.is_empty() {
        parts.push(Module::simple(algebra, 0));
    }
    let refs: Vec<&Module> = parts.iter().collect();
    direct_sum(&refs).0
}

/// An invertible `d × d` matrix built from random elementary row operations on
/// the identity.
pub fn random_invertible(rng: &mut XorShift64, field: &PrimeField, d: usize) -> DenseMat {
    let mut g = DenseMat::identity(d);
    if d == 0 {
        return g;
    }
    for _ in 0..2 * d + 2 {
        let i = rng.below(d as u64) as usize;
        match rng.below(3) {
            0 if d >= 2 => {
                let j = (i + 1 + rng.below(d as u64 - 1) as usize) % d;
                for c in 0..d {
                    let (a, b) = (g.get(i, c), g.get(j, c));
                    g.set(i, c, b);
                    g.set(j, c, a);
                }
            }
            1 => {
                let c = field.elem(1 + rng.below(field.modulus() - 1) as i64);
                for k in 0..d {
                    g.set(i, k, field.mul(g.get(i, k), c));
                }
            }
            _ if d >= 2 => {
                let j = (i + 1 + rng.below(d as u64 - 1) as usize) % d;
                let c = rand_elem(rng, field);
                for k in 0..d {
                    g.set(i, k, field.add(g.get(i, k), field.mul(c, g.get(j, k))));
                }
            }
            _ => {}
        }
    }
    g
}

/// `G⁻¹`, column by column from `G x = e_j`.
pub fn inverse(g: &DenseMat, field: &PrimeField) -> DenseMat {
    let d = g.rows();
    let mut inv = DenseMat::zero(d, d);
    for j in 0..d {
        let mut unit = vec![field.zero(); d];
        unit[j] = field.one();
        let col = g
            .solve(&unit, field)
            .expect("G is a product of elementary matrices");
        for (i, &v) in col.iter().enumerate() {
            inv.set(i, j, v);
        }
    }
    inv
}

/// `M'(a) = G_{s(a)} · M(a) · G_{t(a)}⁻¹` for random invertible `G_v`, together
/// with the matrices `G_v`, which form the isomorphism `M' → M`. The result is
/// isomorphic to `m` but not in the standard summand basis.
pub fn random_basis_change(rng: &mut XorShift64, m: &Module) -> (Module, Vec<DenseMat>) {
    let field = m.field();
    let quiver = m.algebra().quiver();
    let g: Vec<DenseMat> = m
        .dim_vector()
        .iter()
        .map(|&d| random_invertible(rng, &field, d))
        .collect();
    let g_inv: Vec<DenseMat> = g.iter().map(|x| inverse(x, &field)).collect();
    let maps: Vec<DenseMat> = (0..quiver.num_arrows())
        .map(|i| {
            let a = ArrowId(i as u32);
            let (s, t) = (quiver.source(a) as usize, quiver.target(a) as usize);
            g[s].mul(m.map(a), &field).mul(&g_inv[t], &field)
        })
        .collect();
    let transformed = Module::new(m.algebra().clone(), m.dim_vector().to_vec(), maps)
        .expect("a vertexwise basis change preserves the relations");
    (transformed, g)
}

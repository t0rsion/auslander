use std::env;
use std::sync::Arc;
use std::time::{Duration, Instant};

use auslander::algebra::{
    Algebra, commutative_square, cyclic_nakayama, kronecker, linear_an, path_algebra as kq,
    radical_square_zero_cycle, truncated_poly,
};
use auslander::completion::CompletionLimits;
use auslander::dynkin::{DynkinType, dynkin_quiver};
use auslander::field::{Fp, PrimeField};
use auslander::linalg::{DenseMat, SparseMat, SparseRow};
use auslander::module::{Module, direct_sum};
use auslander::quiver::{ArrowId, Quiver};
use auslander::relation::{Presentation, Relation};

/// Work per case before the timer is read, so a fast case is not measured
/// against clock resolution.
pub(crate) const TARGET: Duration = Duration::from_millis(20);

/// Reruns per case. The report is the best of these.
pub(crate) const TRIALS: usize = 5;

/// A xorshift64 stream, so every matrix in a run is the same on every run.
pub(crate) struct Rng(pub(crate) u64);

impl Rng {
    pub(crate) fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    pub(crate) fn elem(&mut self, f: PrimeField) -> Fp {
        f.elem((self.next() % f.modulus()) as i64)
    }

    /// A nonzero element, for the inverse benchmark and sparse entries.
    pub(crate) fn unit(&mut self, f: PrimeField) -> Fp {
        f.elem(1 + (self.next() % (f.modulus() - 1)) as i64)
    }
}

pub(crate) struct Runner {
    trials: usize,
    group_filter: Option<String>,
    case_filter: Option<String>,
    counts: bool,
    ran: usize,
}

impl Runner {
    pub(crate) fn from_args() -> Runner {
        let args: Vec<String> = env::args().skip(1).collect();
        let value = |flag: &str| {
            args.iter()
                .position(|a| a == flag)
                .and_then(|i| args.get(i + 1))
                .cloned()
        };
        Runner {
            trials: value("--trials")
                .and_then(|v| v.parse().ok())
                .unwrap_or(TRIALS),
            group_filter: value("--group"),
            case_filter: value("--case"),
            counts: args.iter().any(|a| a == "--counts"),
            ran: 0,
        }
    }

    pub(crate) fn header(&self) {
        println!("# auslander perf harness");
        println!("# profiling feature\t{}", auslander::profile::ENABLED);
        println!("# trials\t{}", self.trials);
        println!("# mode\t{}", if self.counts { "counts" } else { "time" });
        if self.counts {
            println!("group\tcase\tsite\tcalls\tdistinct");
        } else {
            println!("group\tcase\tns_per_op\treps\ttrials");
        }
    }

    pub(crate) fn footer(&self) {
        println!("# cases\t{}", self.ran);
    }

    fn wanted(&self, group: &str, name: &str) -> bool {
        self.group_filter.as_ref().is_none_or(|g| g == group)
            && self.case_filter.as_ref().is_none_or(|c| name.contains(c))
    }

    /// Measures one case. `weight` is the number of operations one call of `f`
    /// performs, so the report is per operation and not per call.
    pub(crate) fn case(&mut self, group: &str, name: &str, weight: u64, mut f: impl FnMut()) {
        if !self.wanted(group, name) {
            return;
        }
        self.ran += 1;
        if self.counts {
            auslander::profile::reset();
            f();
            let counts = auslander::profile::snapshot();
            let distinct = auslander::profile::distinct_snapshot();
            let mut ranked: Vec<(&str, u64, usize)> = auslander::profile::NAMES
                .iter()
                .copied()
                .zip(counts)
                .zip(distinct)
                .map(|((site, calls), distinct)| (site, calls, distinct))
                .filter(|&(_, n, _)| n > 0)
                .collect();
            ranked.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
            for (site, calls, distinct) in ranked {
                println!("{group}\t{name}\t{site}\t{calls}\t{distinct}");
            }
            return;
        }
        let start = Instant::now();
        f();
        let once = start.elapsed().as_secs_f64();
        let reps = if once <= 0.0 {
            1_000
        } else {
            (TARGET.as_secs_f64() / once).ceil() as usize
        }
        .clamp(1, 10_000_000);
        let mut best = f64::INFINITY;
        for _ in 0..self.trials {
            let start = Instant::now();
            for _ in 0..reps {
                f();
            }
            let per = start.elapsed().as_secs_f64() / (reps as u64 * weight) as f64;
            best = best.min(per);
        }
        println!(
            "{group}\t{name}\t{:.1}\t{reps}\t{}",
            best * 1e9,
            self.trials
        );
    }
}

pub(crate) fn f2() -> PrimeField {
    PrimeField::new(2).expect("2 is prime")
}

pub(crate) fn f5() -> PrimeField {
    PrimeField::new(5).expect("5 is prime")
}

pub(crate) fn f_mersenne() -> PrimeField {
    PrimeField::new((1 << 31) - 1).expect("2^31 - 1 is prime")
}

pub(crate) fn dense(rows: usize, cols: usize, f: PrimeField, rng: &mut Rng) -> DenseMat {
    let data: Vec<Vec<Fp>> = (0..rows)
        .map(|_| (0..cols).map(|_| rng.elem(f)).collect())
        .collect();
    DenseMat::from_rows(&data)
}

/// A square matrix of rank about `n / 2`, so `rref` finds pivots and
/// `kernel_basis` returns a basis of about half the width.
pub(crate) fn half_rank(n: usize, f: PrimeField, rng: &mut Rng) -> DenseMat {
    dense(n, n / 2, f, rng).mul(&dense(n / 2, n, f, rng), &f)
}

/// A product of a unit lower and a unit upper triangular matrix: invertible in
/// every characteristic, and dense enough that elimination does real work.
pub(crate) fn invertible(n: usize, f: PrimeField, rng: &mut Rng) -> DenseMat {
    let mut lower = DenseMat::identity(n);
    let mut upper = DenseMat::identity(n);
    for r in 0..n {
        for c in 0..n {
            if c < r {
                lower.set(r, c, rng.elem(f));
            } else if c > r {
                upper.set(r, c, rng.elem(f));
            }
        }
    }
    lower.mul(&upper, &f)
}

/// A square sparse matrix with `nnz` nonzero entries per row.
pub(crate) fn sparse(n: usize, nnz: usize, f: PrimeField, rng: &mut Rng) -> SparseMat {
    let rows: Vec<SparseRow> = (0..n)
        .map(|_| {
            let entries = (0..nnz)
                .map(|_| ((rng.next() as usize) % n, rng.unit(f)))
                .collect();
            SparseRow::from_entries(entries, &f)
        })
        .collect();
    SparseMat::from_rows(rows, n)
}

pub(crate) fn path_algebra(quiver: Quiver, field: PrimeField) -> Arc<Algebra> {
    kq(quiver, field).expect("the zero ideal over an acyclic quiver completes")
}

pub(crate) fn d4(field: PrimeField) -> Arc<Algebra> {
    path_algebra(
        dynkin_quiver(DynkinType::D(4)).expect("D_4 has a quiver"),
        field,
    )
}

fn ids(raw: &[u32]) -> Vec<ArrowId> {
    raw.iter().copied().map(ArrowId).collect()
}

/// The preprojective algebra of A_3 over F_2, as `tests/common/mod.rs` builds
/// it: the double quiver with relations `a·abar`, `abar·a - b·bbar`, `bbar·b`.
pub(crate) fn preprojective_a3_presentation() -> Presentation {
    let field = f2();
    let quiver = Quiver::new(3, &[(0, 1), (1, 2), (1, 0), (2, 1)]).expect("endpoints in range");
    let relations = vec![
        Relation::new(&quiver, field, vec![(field.one(), ids(&[0, 2]))]).expect("a·abar is a path"),
        Relation::new(
            &quiver,
            field,
            vec![(field.one(), ids(&[2, 0])), (field.elem(-1), ids(&[1, 3]))],
        )
        .expect("the two paths are parallel"),
        Relation::new(&quiver, field, vec![(field.one(), ids(&[3, 1]))]).expect("bbar·b is a path"),
    ];
    Presentation::new(quiver, field, relations).expect("the relations are uniform")
}

/// The inhomogeneous algebra `kQ/(ab - cde)` over F_5, as
/// `tests/common/mod.rs` builds it.
pub(crate) fn inhomogeneous_presentation() -> Presentation {
    let field = f5();
    let quiver =
        Quiver::new(5, &[(0, 1), (1, 4), (0, 2), (2, 3), (3, 4)]).expect("endpoints in range");
    let relation = Relation::new(
        &quiver,
        field,
        vec![
            (field.one(), ids(&[0, 1])),
            (field.elem(-1), ids(&[2, 3, 4])),
        ],
    )
    .expect("the two paths are parallel");
    Presentation::new(quiver, field, vec![relation]).expect("the relation is uniform")
}

pub(crate) fn build(presentation: Presentation) -> Arc<Algebra> {
    Algebra::new(presentation, &CompletionLimits::default()).expect("the fixture completes")
}

/// The regular module `A = P_0 + ... + P_{n-1}`.
pub(crate) fn regular(algebra: &Arc<Algebra>) -> Module {
    let parts: Vec<Module> = (0..algebra.quiver().num_vertices())
        .map(|v| Module::projective(algebra, v))
        .collect();
    let refs: Vec<&Module> = parts.iter().collect();
    direct_sum(&refs).0
}

/// The named fixture algebras, in the order the report lists them.
pub(crate) fn fixtures() -> Vec<(&'static str, Arc<Algebra>)> {
    vec![
        ("linear_an-5-f5", linear_an(5, f5())),
        ("linear_an-12-f5", linear_an(12, f5())),
        ("d4-f5", d4(f5())),
        ("commutative_square-f5", commutative_square(f5())),
        ("kronecker-2-f5", kronecker(2, f5())),
        (
            "cyclic_nakayama-333-f5",
            cyclic_nakayama(&[3, 3, 3], f5()).expect("the fixture is admissible"),
        ),
        (
            "truncated_poly-4-f5",
            truncated_poly(4, f5()).expect("the fixture is admissible"),
        ),
        (
            "radical_square_zero_cycle-4-f5",
            radical_square_zero_cycle(4, f5()),
        ),
        (
            "preprojective-a3-f2",
            build(preprojective_a3_presentation()),
        ),
        ("inhomogeneous-f5", build(inhomogeneous_presentation())),
    ]
}

/// The fixtures the module and machinery groups run on. The rest are covered
/// by the completion group, where their cost lives.
pub(crate) const CORE: &[&str] = &[
    "linear_an-5-f5",
    "linear_an-12-f5",
    "d4-f5",
    "preprojective-a3-f2",
    "inhomogeneous-f5",
];

pub(crate) fn core_fixtures() -> Vec<(&'static str, Arc<Algebra>)> {
    fixtures()
        .into_iter()
        .filter(|(name, _)| CORE.contains(name))
        .collect()
}

//! Wall clock and exact call counts for the workloads the crate is built on.
//!
//! The harness is hand written on [`std::time::Instant`]. The crate has one
//! dependency and no dev-dependency, and a bench framework would be the
//! largest thing in the tree.
//!
//! Each case is calibrated to about 20 ms of work, then run `trials` times.
//! The reported figure is the best trial, not the mean: on this box the CPU
//! throws intermittent machine-check errors, and a slow trial says more about
//! the machine than about the code.
//!
//! Usage:
//!
//! ```text
//! cargo bench -p auslander --bench perf --profile dev
//! cargo bench -p auslander --bench perf --profile release
//! cargo bench -p auslander --bench perf --features profiling -- --counts
//! cargo bench -p auslander --bench perf -- --group tautilting
//! ```
//!
//! Flags: `--counts` prints call counts instead of times (needs the
//! `profiling` feature), `--group <name>` and `--case <substring>` filter,
//! `--trials <n>` sets the trial count.
//!
//! Output is tab separated so a run can be pasted into a table without
//! retyping a number.

use std::env;
use std::hint::black_box;
use std::sync::Arc;
use std::time::{Duration, Instant};

use auslander::algebra::{
    Algebra, commutative_square, cyclic_nakayama, kronecker, linear_an, monomial_presentation,
    path_algebra as kq, radical_square_zero_cycle, truncated_poly,
};
use auslander::almost_split::almost_split;
use auslander::approx::left_approximation;
use auslander::ar::{tau, tau_via_nakayama_kernel, tau_via_transpose_dual};
use auslander::arquiver::{IndecomposableCatalog, ar_quiver};
use auslander::completion::CompletionLimits;
use auslander::decompose::{decompose, krull_schmidt};
use auslander::dynkin::{DynkinType, dynkin_quiver};
use auslander::endo::EndoAlgebra;
use auslander::ext::ExtSpace;
use auslander::field::{Fp, PrimeField};
use auslander::hom::{hom, hom_dim};
use auslander::indec::IndecomposableModule;
use auslander::iso::is_isomorphic;
use auslander::linalg::{DenseMat, SparseMat, SparseRow};
use auslander::module::{Module, direct_sum};
use auslander::monomial::linear_an_ideal;
use auslander::mutation::mutate_at;
use auslander::opposite::opposite;
use auslander::profile;
use auslander::quiver::{ArrowId, Quiver};
use auslander::radical::{radical, radical_series, socle, socle_series, top};
use auslander::relation::{Presentation, Relation};
use auslander::resolution::resolve;
use auslander::supporttau::enumerate_over_catalog;
use auslander::taugraph::{MutationGraphLimits, support_tau_tilting_graph};
use auslander::taurigid::{TauCache, is_tau_rigid_summandwise};
use auslander::verify::verify;

/// Work per case before the timer is read, so a fast case is not measured
/// against clock resolution.
const TARGET: Duration = Duration::from_millis(20);

/// Reruns per case. The report is the best of these.
const TRIALS: usize = 5;

fn main() {
    let mut runner = Runner::from_args();
    runner.header();
    primitives(&mut runner);
    module_layer(&mut runner);
    machinery(&mut runner);
    homological(&mut runner);
    tau_tilting(&mut runner);
    completion(&mut runner);
    leads(&mut runner);
    runner.footer();
}

/// A xorshift64 stream, so every matrix in a run is the same on every run.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn elem(&mut self, f: PrimeField) -> Fp {
        f.elem((self.next() % f.modulus()) as i64)
    }

    /// A nonzero element, for the inverse benchmark and sparse entries.
    fn unit(&mut self, f: PrimeField) -> Fp {
        f.elem(1 + (self.next() % (f.modulus() - 1)) as i64)
    }
}

struct Runner {
    trials: usize,
    group_filter: Option<String>,
    case_filter: Option<String>,
    counts: bool,
    ran: usize,
}

impl Runner {
    fn from_args() -> Runner {
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

    fn header(&self) {
        println!("# auslander perf harness");
        println!("# profiling feature\t{}", profile::ENABLED);
        println!("# trials\t{}", self.trials);
        println!("# mode\t{}", if self.counts { "counts" } else { "time" });
        if self.counts {
            println!("group\tcase\tsite\tcalls");
        } else {
            println!("group\tcase\tns_per_op\treps\ttrials");
        }
    }

    fn footer(&self) {
        println!("# cases\t{}", self.ran);
    }

    fn wanted(&self, group: &str, name: &str) -> bool {
        self.group_filter.as_ref().is_none_or(|g| g == group)
            && self.case_filter.as_ref().is_none_or(|c| name.contains(c))
    }

    /// Measures one case. `weight` is the number of operations one call of `f`
    /// performs, so the report is per operation and not per call.
    fn case(&mut self, group: &str, name: &str, weight: u64, mut f: impl FnMut()) {
        if !self.wanted(group, name) {
            return;
        }
        self.ran += 1;
        if self.counts {
            profile::reset();
            f();
            let counts = profile::snapshot();
            let mut ranked: Vec<(&str, u64)> = profile::NAMES
                .iter()
                .copied()
                .zip(counts)
                .filter(|&(_, n)| n > 0)
                .collect();
            ranked.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
            for (site, calls) in ranked {
                println!("{group}\t{name}\t{site}\t{calls}");
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

fn f2() -> PrimeField {
    PrimeField::new(2).expect("2 is prime")
}

fn f5() -> PrimeField {
    PrimeField::new(5).expect("5 is prime")
}

fn f_mersenne() -> PrimeField {
    PrimeField::new((1 << 31) - 1).expect("2^31 - 1 is prime")
}

fn dense(rows: usize, cols: usize, f: PrimeField, rng: &mut Rng) -> DenseMat {
    let data: Vec<Vec<Fp>> = (0..rows)
        .map(|_| (0..cols).map(|_| rng.elem(f)).collect())
        .collect();
    DenseMat::from_rows(&data)
}

/// A square matrix of rank about `n / 2`, so `rref` finds pivots and
/// `kernel_basis` returns a basis of about half the width.
fn half_rank(n: usize, f: PrimeField, rng: &mut Rng) -> DenseMat {
    dense(n, n / 2, f, rng).mul(&dense(n / 2, n, f, rng), &f)
}

/// A product of a unit lower and a unit upper triangular matrix: invertible in
/// every characteristic, and dense enough that elimination does real work.
fn invertible(n: usize, f: PrimeField, rng: &mut Rng) -> DenseMat {
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
fn sparse(n: usize, nnz: usize, f: PrimeField, rng: &mut Rng) -> SparseMat {
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

fn primitives(r: &mut Runner) {
    let fields = [("f2", f2()), ("f5", f5()), ("fp31", f_mersenne())];
    for (tag, f) in fields {
        let mut rng = Rng(0x243f_6a88_85a3_08d3);
        let xs: Vec<Fp> = (0..1024).map(|_| rng.elem(f)).collect();
        let ys: Vec<Fp> = (0..1024).map(|_| rng.unit(f)).collect();
        r.case("prim", &format!("PrimeField::mul {tag}"), 1024, || {
            let mut acc = f.zero();
            for (&a, &b) in xs.iter().zip(&ys) {
                acc = f.add(acc, f.mul(a, b));
            }
            black_box(acc);
        });
        r.case("prim", &format!("PrimeField::inv {tag}"), 1024, || {
            let mut acc = f.zero();
            for &a in &ys {
                acc = f.add(acc, f.inv(a));
            }
            black_box(acc);
        });

        for n in [10usize, 50, 200, 500] {
            let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
            let a = dense(n, n, f, &mut rng);
            let b = dense(n, n, f, &mut rng);
            let low = half_rank(n, f, &mut rng);
            let inv = invertible(n, f, &mut rng);
            let rhs = dense(n, n, f, &mut rng);
            let vec_rhs: Vec<Fp> = (0..n).map(|_| rng.elem(f)).collect();
            let sp = sparse(n, 4, f, &mut rng);
            let sq = sparse(n, 4, f, &mut rng);

            r.case("prim", &format!("DenseMat::mul {tag} n={n}"), 1, || {
                black_box(a.mul(&b, &f));
            });
            r.case("prim", &format!("DenseMat::rref {tag} n={n}"), 1, || {
                black_box(low.rref(&f));
            });
            r.case("prim", &format!("DenseMat::rank {tag} n={n}"), 1, || {
                black_box(low.rank(&f));
            });
            r.case(
                "prim",
                &format!("DenseMat::kernel_basis {tag} n={n}"),
                1,
                || {
                    black_box(low.kernel_basis(&f));
                },
            );
            r.case("prim", &format!("DenseMat::solve {tag} n={n}"), 1, || {
                black_box(inv.solve(&vec_rhs, &f));
            });
            r.case(
                "prim",
                &format!("DenseMat::solve_many {tag} n={n}"),
                1,
                || {
                    black_box(inv.solve_many(&rhs, &f));
                },
            );
            r.case("prim", &format!("DenseMat::inverse {tag} n={n}"), 1, || {
                black_box(inv.inverse(&f));
            });
            r.case("prim", &format!("SparseMat::mul {tag} n={n}"), 1, || {
                black_box(sp.mul(&sq, &f));
            });
            r.case("prim", &format!("SparseMat::rref {tag} n={n}"), 1, || {
                black_box(sp.rref(&f));
            });
            r.case(
                "prim",
                &format!("SparseMat::kernel_basis {tag} n={n}"),
                1,
                || {
                    black_box(sp.kernel_basis(&f));
                },
            );
        }
    }
}

fn path_algebra(quiver: Quiver, field: PrimeField) -> Arc<Algebra> {
    kq(quiver, field).expect("the zero ideal over an acyclic quiver completes")
}

fn d4(field: PrimeField) -> Arc<Algebra> {
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
fn preprojective_a3_presentation() -> Presentation {
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
fn inhomogeneous_presentation() -> Presentation {
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

fn build(presentation: Presentation) -> Arc<Algebra> {
    Algebra::new(presentation, &CompletionLimits::default()).expect("the fixture completes")
}

/// The regular module `A = P_0 + ... + P_{n-1}`.
fn regular(algebra: &Arc<Algebra>) -> Module {
    let parts: Vec<Module> = (0..algebra.quiver().num_vertices())
        .map(|v| Module::projective(algebra, v))
        .collect();
    let refs: Vec<&Module> = parts.iter().collect();
    direct_sum(&refs).0
}

/// The named fixture algebras, in the order the report lists them.
fn fixtures() -> Vec<(&'static str, Arc<Algebra>)> {
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
const CORE: &[&str] = &[
    "linear_an-5-f5",
    "linear_an-12-f5",
    "d4-f5",
    "preprojective-a3-f2",
    "inhomogeneous-f5",
];

fn core_fixtures() -> Vec<(&'static str, Arc<Algebra>)> {
    fixtures()
        .into_iter()
        .filter(|(name, _)| CORE.contains(name))
        .collect()
}

fn module_layer(r: &mut Runner) {
    for (name, algebra) in core_fixtures() {
        let a = regular(&algebra);
        let dims = a.dim_vector().to_vec();
        let maps: Vec<DenseMat> = (0..algebra.quiver().num_arrows())
            .map(|i| a.map(ArrowId(i as u32)).clone())
            .collect();
        r.case("module", &format!("Module::new A {name}"), 1, || {
            black_box(
                Module::new(algebra.clone(), dims.clone(), maps.clone()).expect("A is a module"),
            );
        });
        r.case("module", &format!("hom(A, A) {name}"), 1, || {
            black_box(hom(&a, &a).expect("one algebra"));
        });
        r.case("module", &format!("hom_dim(A, A) {name}"), 1, || {
            black_box(hom_dim(&a, &a).expect("one algebra"));
        });
        r.case("module", &format!("radical(A) {name}"), 1, || {
            black_box(radical(&a));
        });
        r.case("module", &format!("socle(A) {name}"), 1, || {
            black_box(socle(&a));
        });
        r.case("module", &format!("top(A) {name}"), 1, || {
            black_box(top(&a));
        });

        let longest = algebra
            .basis()
            .iter()
            .max_by_key(|w| w.len())
            .expect("a basis is nonempty")
            .clone();
        r.case(
            "module",
            &format!("word_action len={} {name}", longest.len()),
            1,
            || {
                black_box(a.word_action(&longest).expect("a basis word is a path"));
            },
        );

        let p0 = Module::projective(&algebra, 0);
        for k in [2usize, 4, 8, 16] {
            let parts: Vec<&Module> = (0..k).map(|_| &p0).collect();
            r.case("module", &format!("direct_sum k={k} {name}"), 1, || {
                black_box(direct_sum(&parts));
            });
        }
    }
}

fn machinery(r: &mut Runner) {
    for (name, algebra) in core_fixtures() {
        let a = regular(&algebra);
        r.case(
            "machinery",
            &format!("EndoAlgebra::new(A) {name}"),
            1,
            || {
                black_box(EndoAlgebra::new(&a));
            },
        );
        r.case("machinery", &format!("decompose(A) {name}"), 1, || {
            black_box(decompose(&a));
        });
        r.case("machinery", &format!("krull_schmidt(A) {name}"), 1, || {
            black_box(krull_schmidt(&a));
        });

        let summands = decompose(&a).summands().to_vec();
        let shuffled: Vec<&Module> = summands.iter().rev().collect();
        let b = direct_sum(&shuffled).0;
        r.case(
            "machinery",
            &format!("is_isomorphic(A, A') {name}"),
            1,
            || {
                black_box(is_isomorphic(&a, &b).expect("one algebra"));
            },
        );

        let simple = Module::simple(&algebra, 0);
        r.case("machinery", &format!("tau(S_0) indec {name}"), 1, || {
            black_box(tau(&simple).expect("the routes agree"));
        });

        // The gap between these two cases is the measured design rule that put
        // `is_tau_rigid_summandwise` in front of `is_tau_rigid`.
        let simples: Vec<Module> = (0..algebra.quiver().num_vertices())
            .map(|v| Module::simple(&algebra, v))
            .collect();
        let refs: Vec<&Module> = simples.iter().collect();
        let assembled = direct_sum(&refs).0;
        if tau(&assembled).is_ok() {
            r.case(
                "machinery",
                &format!("tau(S_0+..+S_n) assembled {name}"),
                1,
                || {
                    black_box(tau(&assembled).expect("the routes agree"));
                },
            );
        }

        r.case("machinery", &format!("opposite {name}"), 1, || {
            black_box(opposite(&algebra).expect("the opposite completes"));
        });
    }
}

fn homological(r: &mut Runner) {
    let algebras: Vec<(&'static str, Arc<Algebra>)> = vec![
        ("linear_an-5-f5", linear_an(5, f5())),
        ("d4-f5", d4(f5())),
        (
            "cyclic_nakayama-333-f5",
            cyclic_nakayama(&[3, 3, 3], f5()).expect("the fixture is admissible"),
        ),
        (
            "truncated_poly-4-f5",
            truncated_poly(4, f5()).expect("the fixture is admissible"),
        ),
        (
            "preprojective-a3-f2",
            build(preprojective_a3_presentation()),
        ),
    ];
    for (name, algebra) in algebras {
        let s0 = Module::simple(&algebra, 0);
        let s1 = Module::simple(&algebra, 1.min(algebra.quiver().num_vertices() - 1));
        r.case("homological", &format!("resolve(S_0, 5) {name}"), 1, || {
            black_box(resolve(&s0, 5));
        });
        for k in [1usize, 2] {
            r.case(
                "homological",
                &format!("ExtSpace::new(S_0, S_1, {k}) {name}"),
                1,
                || {
                    black_box(ExtSpace::new(&s0, &s1, k).expect("one algebra"));
                },
            );
        }

        // A Yoneda square needs a nonzero degree-1 class with matching ends.
        if let Ok(space) = ExtSpace::new(&s0, &s0, 1)
            && space.dim() > 0
        {
            let mut coords = vec![algebra.field().zero(); space.dim()];
            coords[0] = algebra.field().one();
            let class = space
                .class_from_coordinates(&coords)
                .expect("the coordinates fit the space");
            r.case("homological", &format!("ExtClass::then {name}"), 1, || {
                black_box(class.then(&class).expect("the middles agree"));
            });
        }

        if let Ok(indec) = IndecomposableModule::new(&s0) {
            r.case(
                "homological",
                &format!("almost_split(S_0) {name}"),
                1,
                || {
                    black_box(almost_split(&indec).expect("the translate is indecomposable"));
                },
            );
        }

        if ar_quiver(&algebra).is_ok() {
            r.case("homological", &format!("ar_quiver {name}"), 1, || {
                black_box(ar_quiver(&algebra).expect("the catalog is known"));
            });
        }
    }
}

fn tau_tilting(r: &mut Runner) {
    let algebras: Vec<(&'static str, Arc<Algebra>)> = vec![
        (
            "a2-f5",
            path_algebra(dynkin_quiver(DynkinType::A(2)).unwrap(), f5()),
        ),
        (
            "a3-f5",
            path_algebra(dynkin_quiver(DynkinType::A(3)).unwrap(), f5()),
        ),
        (
            "a4-f5",
            path_algebra(dynkin_quiver(DynkinType::A(4)).unwrap(), f5()),
        ),
        ("d4-f5", d4(f5())),
    ];
    for (name, algebra) in algebras {
        let catalog = IndecomposableCatalog::dynkin(&algebra).expect("the quiver is Dynkin");

        r.case(
            "tautilting",
            &format!("enumerate_over_catalog {name}"),
            1,
            || {
                black_box(enumerate_over_catalog(&catalog).expect("the catalog is complete"));
            },
        );

        let summands: Vec<(usize, Module)> = catalog
            .entries()
            .iter()
            .take(4)
            .enumerate()
            .map(|(i, e)| (i, e.module().clone()))
            .collect();
        r.case(
            "tautilting",
            &format!("is_tau_rigid_summandwise n={} {name}", summands.len()),
            1,
            || {
                let mut cache = TauCache::new();
                black_box(
                    is_tau_rigid_summandwise(&summands, &mut cache).expect("the translates exist"),
                );
            },
        );

        let targets: Vec<Module> = catalog
            .entries()
            .iter()
            .take(2)
            .map(|e| e.module().clone())
            .collect();
        let x = Module::simple(&algebra, 0);
        if left_approximation(&x, &targets).is_ok() {
            r.case(
                "tautilting",
                &format!("left_approximation {name}"),
                1,
                || {
                    black_box(left_approximation(&x, &targets).expect("the summands certify"));
                },
            );
        }

        let enumeration = enumerate_over_catalog(&catalog).expect("the catalog is complete");
        if let Some(pair) = enumeration
            .pairs()
            .iter()
            .find(|p| p.summand_count() > 0 && mutate_at(p, 0).is_ok())
        {
            r.case("tautilting", &format!("mutate_at slot=0 {name}"), 1, || {
                black_box(mutate_at(pair, 0).expect("the slot is a module summand"));
            });
        }

        let limits = MutationGraphLimits::default();
        r.case(
            "tautilting",
            &format!("support_tau_tilting_graph {name}"),
            1,
            || {
                black_box(
                    support_tau_tilting_graph(&algebra, &limits).expect("the walk stays in budget"),
                );
            },
        );

        // The graph is built outside the closure, so this case times the
        // closure recheck alone. The walk above already ran it once, and
        // ClosureWitness::verify is the slower half of a closing walk on D_4.
        let closed = support_tau_tilting_graph(&algebra, &limits)
            .expect("the walk stays in budget")
            .into_closed()
            .expect("the walk closes on a representation-finite fixture");
        r.case(
            "tautilting",
            &format!("ClosedSupportTauTiltingGraph::verify {name}"),
            1,
            || {
                assert!(black_box(closed.verify()), "the closure recheck failed");
            },
        );
    }
}

/// A named fixture together with the thunk that builds it from its
/// presentation, so the completion group times the build and not a clone.
type CompletionCase = (&'static str, Box<dyn Fn() -> Arc<Algebra>>);

fn completion(r: &mut Runner) {
    let cases: Vec<CompletionCase> = vec![
        (
            "linear_an-5-f5",
            Box::new(|| build(monomial_presentation(&linear_an_ideal(5), f5()))),
        ),
        (
            "linear_an-12-f5",
            Box::new(|| build(monomial_presentation(&linear_an_ideal(12), f5()))),
        ),
        (
            "commutative_square-f5",
            Box::new(|| commutative_square(f5())),
        ),
        ("kronecker-2-f5", Box::new(|| kronecker(2, f5()))),
        (
            "cyclic_nakayama-333-f5",
            Box::new(|| cyclic_nakayama(&[3, 3, 3], f5()).expect("admissible")),
        ),
        (
            "truncated_poly-4-f5",
            Box::new(|| truncated_poly(4, f5()).expect("admissible")),
        ),
        (
            "radical_square_zero_cycle-4-f5",
            Box::new(|| radical_square_zero_cycle(4, f5())),
        ),
        (
            "preprojective-a3-f2",
            Box::new(|| build(preprojective_a3_presentation())),
        ),
        (
            "inhomogeneous-f5",
            Box::new(|| build(inhomogeneous_presentation())),
        ),
    ];
    for (name, make) in cases {
        r.case("completion", &format!("Algebra::new {name}"), 1, || {
            black_box(make());
        });
        let json = make().certificate().to_canonical_json();
        r.case("completion", &format!("verify {name}"), 1, || {
            black_box(verify(&json).expect("the certificate verifies"));
        });
    }
}

/// Cases that isolate one suspected hot spot each, so a claim about it rests
/// on a measurement of it alone rather than on a share of a larger workload.
fn leads(r: &mut Runner) {
    for (name, algebra) in [
        ("linear_an-12-f5", linear_an(12, f5())),
        ("d4-f5", d4(f5())),
        (
            "preprojective-a3-f2",
            build(preprojective_a3_presentation()),
        ),
    ] {
        let a = regular(&algebra);
        let s0 = Module::simple(&algebra, 0);

        // The two tau routes apart, so the cross-check is the remainder.
        r.case("leads", &format!("tau route nakayama {name}"), 1, || {
            black_box(tau_via_nakayama_kernel(&s0));
        });
        r.case(
            "leads",
            &format!("tau route transpose_dual {name}"),
            1,
            || {
                black_box(tau_via_transpose_dual(&s0).expect("the opposite completes"));
            },
        );
        r.case(
            "leads",
            &format!("tau both routes checked {name}"),
            1,
            || {
                black_box(tau(&s0).expect("the routes agree"));
            },
        );

        // Loewy series, where `socle_series` recomputes the algebra's radical
        // powers once per vertex pair per degree.
        r.case("leads", &format!("radical_series(A) {name}"), 1, || {
            black_box(radical_series(&a));
        });
        r.case("leads", &format!("socle_series(A) {name}"), 1, || {
            black_box(socle_series(&a));
        });
        r.case(
            "leads",
            &format!("radical_power_matrix(0,0,1) {name}"),
            1,
            || {
                black_box(algebra.radical_power_matrix(0, 0, 1));
            },
        );
        let degree = algebra.nilpotency_degree();
        r.case(
            "leads",
            &format!("radical_power_matrix(0,0,{degree}) {name}"),
            1,
            || {
                black_box(algebra.radical_power_matrix(0, 0, degree));
            },
        );

        // Every basis word once, against the number of matrix products a
        // prefix table would need (one per word, not one per arrow).
        let words = algebra.basis().to_vec();
        let arrows: usize = words.iter().map(|w| w.len()).sum();
        r.case(
            "leads",
            &format!(
                "word_action over {} words, {arrows} arrows {name}",
                words.len()
            ),
            1,
            || {
                for w in &words {
                    black_box(a.word_action(w).expect("a basis word is a path"));
                }
            },
        );
    }
}

//! Wall clock and exact call counts for the workloads the crate is built on.
//!
//! The harness is hand written on [`std::time::Instant`]. The crate has one
//! dependency and no dev-dependency; a bench framework would be the largest
//! thing in the tree.
//!
//! Each case is calibrated to about 20 ms of work, then run `trials` times.
//! The reported figure is the best trial, not the mean: a slow trial on this
//! box is usually a machine-check error, not the code.
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
//! The `distinct` column of a `--counts` run is the number of different
//! modules the site ran on, by nominal identity. It is recorded at the four
//! sites that take a module and pay far more than a lock, and is zero
//! everywhere else, which means no record rather than a measured zero.
//!
//! Output is tab separated so a run can be pasted into a table without
//! retyping a number.

#[path = "perf/completion.rs"]
mod perf_completion;
#[path = "perf/derived.rs"]
mod perf_derived;
#[path = "perf/machinery.rs"]
mod perf_machinery;
#[path = "perf/modules.rs"]
mod perf_modules;
#[path = "perf/primitives.rs"]
mod perf_primitives;
#[path = "perf/support.rs"]
mod perf_support;
#[path = "perf/target.rs"]
mod perf_target;
#[path = "perf/tau.rs"]
mod perf_tau;

use perf_support::Runner;

fn main() {
    let mut runner = Runner::from_args();
    runner.header();
    perf_primitives::run(&mut runner);
    perf_modules::module_layer(&mut runner);
    perf_modules::compiled_families(&mut runner);
    perf_machinery::machinery(&mut runner);
    perf_machinery::homological(&mut runner);
    perf_target::target_layer(&mut runner);
    perf_derived::derived_layer(&mut runner);
    perf_derived::derived_workbench(&mut runner);
    perf_tau::run(&mut runner);
    perf_completion::run(&mut runner);
    runner.footer();
}

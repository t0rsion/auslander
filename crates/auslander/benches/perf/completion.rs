use std::hint::black_box;
use std::sync::Arc;

use auslander::algebra::{
    Algebra, commutative_square, cyclic_nakayama, kronecker, linear_an, monomial_presentation,
    radical_square_zero_cycle, truncated_poly,
};
use auslander::ar::{tau, tau_via_nakayama_kernel, tau_via_transpose_dual};
use auslander::module::Module;
use auslander::monomial::linear_an_ideal;
use auslander::radical::{radical_series, socle_series};
use auslander::verify::verify;

use super::perf_support::{
    Runner, build, d4, f5, inhomogeneous_presentation, preprojective_a3_presentation, regular,
};

/// A named fixture together with the thunk that builds it from its
/// presentation, so the completion group times the build and not a clone.
type CompletionCase = (&'static str, Box<dyn Fn() -> Arc<Algebra>>);

pub(crate) fn run(r: &mut Runner) {
    completion(r);
    leads(r);
}

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

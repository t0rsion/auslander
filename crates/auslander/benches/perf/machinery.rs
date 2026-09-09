use std::hint::black_box;
use std::sync::Arc;

use auslander::algebra::{Algebra, cyclic_nakayama, linear_an, truncated_poly};
use auslander::almost_split::almost_split;
use auslander::ar::tau;
use auslander::arquiver::ar_quiver;
use auslander::decompose::{decompose, krull_schmidt};
use auslander::endo::EndoAlgebra;
use auslander::ext::ExtSpace;
use auslander::indec::IndecomposableModule;
use auslander::iso::is_isomorphic;
use auslander::module::{Module, direct_sum};
use auslander::opposite::opposite;
use auslander::resolution::resolve;

use super::perf_support::{
    Runner, build, core_fixtures, d4, f5, preprojective_a3_presentation, regular,
};

pub(crate) fn machinery(r: &mut Runner) {
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

pub(crate) fn homological(r: &mut Runner) {
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

use std::hint::black_box;
use std::sync::Arc;

use auslander::algebra::Algebra;
use auslander::approx::left_approximation;
use auslander::arquiver::IndecomposableCatalog;
use auslander::dynkin::{DynkinType, dynkin_quiver};
use auslander::module::Module;
use auslander::mutation::mutate_at;
use auslander::supporttau::enumerate_over_catalog;
use auslander::taugraph::{MutationGraphLimits, support_tau_tilting_graph};
use auslander::taurigid::{TauCache, is_tau_rigid_summandwise};

use super::perf_support::{Runner, d4, f5, path_algebra};

pub(crate) fn run(r: &mut Runner) {
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

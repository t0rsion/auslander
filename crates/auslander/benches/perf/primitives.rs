use std::hint::black_box;

use auslander::field::Fp;

use super::perf_support::{Rng, Runner, dense, f_mersenne, f2, f5, half_rank, invertible, sparse};

pub(crate) fn run(r: &mut Runner) {
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

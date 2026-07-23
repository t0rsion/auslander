//! Textbook fixtures with hand-derived expected values.
//!
//! Every fact checked here is characteristic-free (path counts and ranks of integer
//! matrices reduced mod p never collide for these fixtures), so each fixture runs over
//! F_2 and F_5 and any disagreement between the two runs is a bug.
//!
//! Ext derivations: all resolutions produced by the library are minimal, and
//! `Hom_A(P_v, S_j) = δ_{vj}·k`, so the induced cochain differentials into a simple
//! vanish and `dim Ext^k(S_i, S_j)` is the multiplicity of `P_j` in the `k`-th term of
//! the minimal resolution of `S_i`. In particular `Ext^0(S_i, S_j) = δ_{ij}`,
//! `Ext^1(S_i, S_j)` counts arrows `i → j`, and `Ext^2(S_i, S_j)` counts minimal
//! relations from `i` to `j` (Bongartz, "Algebras and quadratic forms", 1983).
//!
//! Convention note against the frozen archive repo: the old code computed with LEFT
//! modules (column convention), so its nonzero Ext pairs are the transposes of ours.
//! For example, its `verify_ext_manual.rs` expected `Ext¹(S_sink, S_source) = 1` for A_2,
//! while for right modules the extension realized by an arrow sits on
//! `(source, sink)`. Where such a swap occurs we trust the right-module derivation.

use std::env;
use std::io::Read;
use std::process::{Command, Stdio};
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

use auslander::algebra::{
    MonomialAlgebra, an_with_relations, cyclic_nakayama, dual_numbers, kronecker, linear_an,
    linear_nakayama, radical_square_zero_cycle, truncated_poly,
};
use auslander::ext::{ext_table, global_dimension};
use auslander::field::PrimeField;
use auslander::module::Module;
use auslander::quiver::{ArrowId, Quiver};
use auslander::radical::radical_series;
use auslander::resolution::{Bounded, projective_dimension};

const EXT_DEGREE: usize = 4;
const PD_BOUND: usize = 8;

fn fields() -> [PrimeField; 2] {
    [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()]
}

struct Expected {
    dim: usize,
    /// `cartan[i][j] = dim e_i A e_j`; row `i` is the dimension vector of `P_i`,
    /// column `j` the dimension vector of `I_j`.
    cartan: Vec<Vec<usize>>,
    /// `ext[i][j][k] = dim Ext^k(S_i, S_j)` for `k = 0..=EXT_DEGREE`.
    ext: Vec<Vec<Vec<usize>>>,
    /// `pd[v] = projective_dimension(S_v, PD_BOUND)`.
    pd: Vec<Bounded<usize>>,
    gldim: Bounded<usize>,
    /// `rad_series[v]`: dimension vectors of `P_v ⊇ rad P_v ⊇ … ⊇ 0`.
    rad_series: Vec<Vec<Vec<usize>>>,
}

/// `Ext^0 = δ_{ij}` plus the listed `(i, j, k, dim)` entries.
fn ext_expected(n: usize, entries: &[(usize, usize, usize, usize)]) -> Vec<Vec<Vec<usize>>> {
    let mut table = vec![vec![vec![0; EXT_DEGREE + 1]; n]; n];
    for (i, row) in table.iter_mut().enumerate() {
        row[i][0] = 1;
    }
    for &(i, j, k, d) in entries {
        table[i][j][k] = d;
    }
    table
}

fn check(algebra: &Arc<MonomialAlgebra>, expected: &Expected) {
    assert_eq!(algebra.dim(), expected.dim, "algebra dimension");
    assert_eq!(algebra.cartan_matrix(), expected.cartan, "Cartan matrix");
    let n = algebra.quiver().num_vertices();
    for field in fields() {
        let p = field.modulus();
        for v in 0..n {
            let proj = Module::projective(algebra, field, v);
            assert_eq!(
                proj.dim_vector(),
                expected.cartan[v as usize].as_slice(),
                "dim P_{v} = Cartan row {v} over F_{p}"
            );
            let inj = Module::injective(algebra, field, v);
            let column: Vec<usize> = expected.cartan.iter().map(|row| row[v as usize]).collect();
            assert_eq!(
                inj.dim_vector(),
                column.as_slice(),
                "dim I_{v} = Cartan column {v} over F_{p}"
            );
            let series: Vec<Vec<usize>> = radical_series(&proj)
                .iter()
                .map(|m| m.dim_vector().to_vec())
                .collect();
            assert_eq!(
                series, expected.rad_series[v as usize],
                "radical series of P_{v} over F_{p}"
            );
        }
        let simples: Vec<Module> = (0..n).map(|v| Module::simple(algebra, field, v)).collect();
        for (i, si) in simples.iter().enumerate() {
            for (j, sj) in simples.iter().enumerate() {
                assert_eq!(
                    ext_table(si, sj, EXT_DEGREE).unwrap(),
                    expected.ext[i][j],
                    "Ext table of (S_{i}, S_{j}) over F_{p}"
                );
            }
            assert_eq!(
                projective_dimension(si, PD_BOUND),
                expected.pd[i],
                "pd S_{i} over F_{p}"
            );
        }
        assert_eq!(
            global_dimension(algebra, field, PD_BOUND),
            expected.gldim,
            "global dimension over F_{p}"
        );
    }
}

fn a3_expected() -> Expected {
    Expected {
        dim: 6,
        cartan: vec![vec![1, 1, 1], vec![0, 1, 1], vec![0, 0, 1]],
        ext: ext_expected(3, &[(0, 1, 1, 1), (1, 2, 1, 1)]),
        pd: vec![Bounded::Exact(1), Bounded::Exact(1), Bounded::Exact(0)],
        gldim: Bounded::Exact(1),
        rad_series: vec![
            vec![vec![1, 1, 1], vec![0, 1, 1], vec![0, 0, 1], vec![0, 0, 0]],
            vec![vec![0, 1, 1], vec![0, 0, 1], vec![0, 0, 0]],
            vec![vec![0, 0, 1], vec![0, 0, 0]],
        ],
    }
}

fn a3_mod_ab_expected() -> Expected {
    // 0 → P_2 → P_1 → P_0 → S_0 → 0 gives pd S_0 = 2 and Ext²(S_0, S_2) = 1, the
    // QPA-verified facts from the archive (P_0 = (1, 1, 0), Ext²(S_0, S_2) = 1);
    // the ordered pairs already agree with the right-module derivation.
    Expected {
        dim: 5,
        cartan: vec![vec![1, 1, 0], vec![0, 1, 1], vec![0, 0, 1]],
        ext: ext_expected(3, &[(0, 1, 1, 1), (1, 2, 1, 1), (0, 2, 2, 1)]),
        pd: vec![Bounded::Exact(2), Bounded::Exact(1), Bounded::Exact(0)],
        gldim: Bounded::Exact(2),
        rad_series: vec![
            vec![vec![1, 1, 0], vec![0, 1, 0], vec![0, 0, 0]],
            vec![vec![0, 1, 1], vec![0, 0, 1], vec![0, 0, 0]],
            vec![vec![0, 0, 1], vec![0, 0, 0]],
        ],
    }
}

/// `k[x]/(xⁿ)`: uniserial regular module, `Ω S = rad^{n-1} P ≅ S` up to the shift in
/// the uniserial chain, so the minimal resolution `… → P → P → S` is periodic and
/// `Ext^k(S, S) = 1` for every `k`.
fn truncated_expected(n: usize) -> Expected {
    Expected {
        dim: n,
        cartan: vec![vec![n]],
        ext: ext_expected(1, &[(0, 0, 1, 1), (0, 0, 2, 1), (0, 0, 3, 1), (0, 0, 4, 1)]),
        pd: vec![Bounded::AtLeast(PD_BOUND + 1)],
        gldim: Bounded::AtLeast(PD_BOUND + 1),
        rad_series: vec![(0..=n).rev().map(|d| vec![d]).collect()],
    }
}

#[test]
fn linear_a2() {
    check(
        &linear_an(2),
        &Expected {
            dim: 3,
            cartan: vec![vec![1, 1], vec![0, 1]],
            ext: ext_expected(2, &[(0, 1, 1, 1)]),
            pd: vec![Bounded::Exact(1), Bounded::Exact(0)],
            gldim: Bounded::Exact(1),
            rad_series: vec![
                vec![vec![1, 1], vec![0, 1], vec![0, 0]],
                vec![vec![0, 1], vec![0, 0]],
            ],
        },
    );
}

#[test]
fn linear_a3() {
    check(&linear_an(3), &a3_expected());
}

// The archive's PRODUCTION_READINESS_ASSESSMENT claimed gldim kA_3 = 2; the path
// algebra of A_3 is hereditary, so a3_expected() asserting Exact(1) is a regression
// test against that error.
#[test]
fn linear_a3_is_hereditary() {
    let algebra = linear_an(3);
    for field in fields() {
        assert_eq!(
            global_dimension(&algebra, field, PD_BOUND),
            Bounded::Exact(1)
        );
    }
}

// D_4 as a subspace quiver: arrows 0 → 3, 1 → 3, 2 → 3 into the center. Hereditary;
// P_i = (e_i, path to center) for i < 3 and P_3 = S_3, I_3 = D(A e_3) has dimension
// vector (1, 1, 1, 1).
#[test]
fn d4_three_arrows_into_a_center() {
    let quiver = Quiver::new(4, &[(0, 3), (1, 3), (2, 3)]).unwrap();
    let algebra = MonomialAlgebra::new(quiver, Vec::new()).unwrap();
    check(
        &algebra,
        &Expected {
            dim: 7,
            cartan: vec![
                vec![1, 0, 0, 1],
                vec![0, 1, 0, 1],
                vec![0, 0, 1, 1],
                vec![0, 0, 0, 1],
            ],
            ext: ext_expected(4, &[(0, 3, 1, 1), (1, 3, 1, 1), (2, 3, 1, 1)]),
            pd: vec![
                Bounded::Exact(1),
                Bounded::Exact(1),
                Bounded::Exact(1),
                Bounded::Exact(0),
            ],
            gldim: Bounded::Exact(1),
            rad_series: vec![
                vec![vec![1, 0, 0, 1], vec![0, 0, 0, 1], vec![0, 0, 0, 0]],
                vec![vec![0, 1, 0, 1], vec![0, 0, 0, 1], vec![0, 0, 0, 0]],
                vec![vec![0, 0, 1, 1], vec![0, 0, 0, 1], vec![0, 0, 0, 0]],
                vec![vec![0, 0, 0, 1], vec![0, 0, 0, 0]],
            ],
        },
    );
}

#[test]
fn dual_numbers_k_x_mod_x_squared() {
    check(&dual_numbers(), &truncated_expected(2));
}

#[test]
fn truncated_poly_k_x_mod_x_cubed() {
    check(&truncated_poly(3).unwrap(), &truncated_expected(3));
}

#[test]
fn a3_mod_ab() {
    check(
        &an_with_relations(3, &[(0, 2)]).unwrap(),
        &a3_mod_ab_expected(),
    );
}

// Regression against the archive's examples-db, which listed hereditary Kronecker
// algebras with infinite global dimension; a hereditary algebra that is not
// semisimple has gldim exactly 1.
#[test]
fn kronecker_2_is_hereditary() {
    check(
        &kronecker(2),
        &Expected {
            dim: 4,
            cartan: vec![vec![1, 2], vec![0, 1]],
            ext: ext_expected(2, &[(0, 1, 1, 2)]),
            pd: vec![Bounded::Exact(1), Bounded::Exact(0)],
            gldim: Bounded::Exact(1),
            rad_series: vec![
                vec![vec![1, 2], vec![0, 2], vec![0, 0]],
                vec![vec![0, 1], vec![0, 0]],
            ],
        },
    );
}

// Cycle 0 → 1 → 2 → 0 with rad² = 0: Ω S_i = S_{i+1}, so the minimal resolution of
// S_i has k-th term P_{i+k} and Ext^k(S_i, S_j) = 1 exactly when j ≡ i + k (mod 3).
#[test]
fn radical_square_zero_cycle_3() {
    let mut entries = Vec::new();
    for i in 0..3 {
        for k in 1..=EXT_DEGREE {
            entries.push((i, (i + k) % 3, k, 1));
        }
    }
    check(
        &radical_square_zero_cycle(3),
        &Expected {
            dim: 6,
            cartan: vec![vec![1, 1, 0], vec![0, 1, 1], vec![1, 0, 1]],
            ext: ext_expected(3, &entries),
            pd: vec![Bounded::AtLeast(PD_BOUND + 1); 3],
            gldim: Bounded::AtLeast(PD_BOUND + 1),
            rad_series: vec![
                vec![vec![1, 1, 0], vec![0, 1, 0], vec![0, 0, 0]],
                vec![vec![0, 1, 1], vec![0, 0, 1], vec![0, 0, 0]],
                vec![vec![1, 0, 1], vec![1, 0, 0], vec![0, 0, 0]],
            ],
        },
    );
}

// Kupisch series [3, 2, 1] admits no relations: the algebra is the path algebra of
// linearly oriented A_3 and every A_3 expectation applies verbatim.
#[test]
fn linear_nakayama_3_2_1() {
    let algebra = linear_nakayama(&[3, 2, 1]).unwrap();
    assert!(algebra.forbidden().is_empty());
    check(&algebra, &a3_expected());
}

// Regression: the old library hung on the Kupisch series [2, 2, 1]. The algebra is
// kA_3/(ab), so the full kA_3/(ab) expectations apply. This test only runs the
// assertions when spawned by the watchdog below; a hang here would stall the whole
// in-process test run, so the watchdog moves it into a killable subprocess.
#[test]
fn linear_nakayama_2_2_1_child() {
    if env::var("AUSLANDER_WATCHDOG_CHILD").is_err() {
        return;
    }
    let algebra = linear_nakayama(&[2, 2, 1]).unwrap();
    assert_eq!(algebra.dim(), 5);
    check(&algebra, &a3_mod_ab_expected());
}

// Spawns the current test binary on the child test alone, polls it, and kills it
// after 10 seconds; the bound is enormous compared to the milliseconds the child
// takes, and exists to turn the old hang back into a test failure.
#[test]
fn linear_nakayama_2_2_1_completes_under_watchdog() {
    let exe = env::current_exe().expect("path of the running test binary");
    let mut child = Command::new(exe)
        .args(["--exact", "linear_nakayama_2_2_1_child"])
        .env("AUSLANDER_WATCHDOG_CHILD", "1")
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("spawn the child test process");
    let deadline = Instant::now() + Duration::from_secs(10);
    let status = loop {
        match child.try_wait().expect("poll the child test process") {
            Some(status) => break status,
            None if Instant::now() >= deadline => {
                child.kill().ok();
                child.wait().ok();
                panic!("Kupisch [2, 2, 1] ran past 10s; the old library hung here");
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
        "child ran zero tests; was linear_nakayama_2_2_1_child renamed?\n{stdout}"
    );
}

// Cyclic Nakayama with Kupisch series [3, 3, 3], i.e. kC_3/J³: P_i is uniserial with
// socle S_{i+2}, and rad P_i ≅ P_{i+1}/soc P_{i+1} gives Ω²S_i ≅ S_i. The minimal
// resolution of S_i alternates P_i, P_{i+1}, P_i, …, so Ext^k(S_i, S_j) = 1 exactly
// when j = i for even k and j ≡ i + 1 (mod 3) for odd k.
#[test]
fn cyclic_nakayama_3_3_3() {
    let mut entries = Vec::new();
    for i in 0..3 {
        for k in 1..=EXT_DEGREE {
            let j = if k % 2 == 1 { (i + 1) % 3 } else { i };
            entries.push((i, j, k, 1));
        }
    }
    check(
        &cyclic_nakayama(&[3, 3, 3]).unwrap(),
        &Expected {
            dim: 9,
            cartan: vec![vec![1, 1, 1]; 3],
            ext: ext_expected(3, &entries),
            pd: vec![Bounded::AtLeast(PD_BOUND + 1); 3],
            gldim: Bounded::AtLeast(PD_BOUND + 1),
            rad_series: vec![
                vec![vec![1, 1, 1], vec![0, 1, 1], vec![0, 0, 1], vec![0, 0, 0]],
                vec![vec![1, 1, 1], vec![1, 0, 1], vec![1, 0, 0], vec![0, 0, 0]],
                vec![vec![1, 1, 1], vec![1, 1, 0], vec![0, 1, 0], vec![0, 0, 0]],
            ],
        },
    );
}

// A representation-finite gentle algebra that is not a Nakayama algebra: quiver
// a: 0 → 1, b: 1 → 2, c: 1 → 3 with the single relation ab = 0. The gentleness
// conditions of Assem–Skowroński ("Iterated tilted algebras of type Ã_n", Math. Z.
// 195, 1987) hold: at most two arrows in and out of every vertex, relations are paths
// of length two, and for each arrow at most one continuation lies in the ideal (b
// after a) and at most one outside it (c after a). The quiver is a tree, so there are
// no band modules and the algebra is representation-finite (Butler–Ringel,
// "Auslander-Reiten sequences with few middle terms", Comm. Algebra 15, 1987).
//
// Resolutions: rad P_0 = span{a, ac} is uniserial with top S_1 and socle S_3; its
// cover P_1 has kernel S_2 = P_2 (b dies in rad P_0 because ab = 0), so
// 0 → P_2 → P_1 → P_0 → S_0 → 0 and pd S_0 = 2. rad P_1 = S_2 ⊕ S_3 is projective,
// so pd S_1 = 1; S_2 and S_3 are projective.
#[test]
fn gentle_branch_a_0_1_b_1_2_c_1_3_with_ab_zero() {
    let quiver = Quiver::new(4, &[(0, 1), (1, 2), (1, 3)]).unwrap();
    let algebra = MonomialAlgebra::new(quiver, vec![vec![ArrowId(0), ArrowId(1)]]).unwrap();
    check(
        &algebra,
        &Expected {
            dim: 8,
            cartan: vec![
                vec![1, 1, 0, 1],
                vec![0, 1, 1, 1],
                vec![0, 0, 1, 0],
                vec![0, 0, 0, 1],
            ],
            ext: ext_expected(4, &[(0, 1, 1, 1), (1, 2, 1, 1), (1, 3, 1, 1), (0, 2, 2, 1)]),
            pd: vec![
                Bounded::Exact(2),
                Bounded::Exact(1),
                Bounded::Exact(0),
                Bounded::Exact(0),
            ],
            gldim: Bounded::Exact(2),
            rad_series: vec![
                vec![
                    vec![1, 1, 0, 1],
                    vec![0, 1, 0, 1],
                    vec![0, 0, 0, 1],
                    vec![0, 0, 0, 0],
                ],
                vec![vec![0, 1, 1, 1], vec![0, 0, 1, 1], vec![0, 0, 0, 0]],
                vec![vec![0, 0, 1, 0], vec![0, 0, 0, 0]],
                vec![vec![0, 0, 0, 1], vec![0, 0, 0, 0]],
            ],
        },
    );
}

// Mirrors the quick-start example in the repo README; keep the two in sync.
#[test]
fn readme_quick_start_example() {
    let algebra = an_with_relations(3, &[(0, 2)]).unwrap();
    let field = PrimeField::new(5).unwrap();
    let s0 = Module::simple(&algebra, field, 0);
    let s2 = Module::simple(&algebra, field, 2);
    assert_eq!(ext_table(&s0, &s2, 4).unwrap(), vec![0, 0, 1, 0, 0]);
}

//! Decomposition and isomorphism testing across the v0.1 fixtures.
//!
//! Most checks run over F_2 and F_5. The facts are characteristic-free, so
//! disagreement between the two runs is a bug. Repeated summands are checked
//! over F_32003 as well, because the small fields cannot see the failure mode
//! they guard against: see
//! `decompose_splits_repeated_summands_over_a_large_field`. The twelve-module
//! iso matrix uses dimension vectors as its oracle: within each fixture's
//! simples and projectives, two modules are isomorphic exactly when their
//! dimension vectors agree (sinks make some P_v equal to S_v, which the oracle
//! covers).

use std::sync::Arc;

use auslander::algebra::{
    Algebra, commutative_square, cyclic_nakayama, dual_numbers, kronecker, linear_an,
    radical_square_zero_cycle, truncated_poly,
};
use auslander::ar::tau;
use auslander::decompose::{Certificate, KrullSchmidtOutcome, decompose, krull_schmidt};
use auslander::endo::EndoAlgebra;
use auslander::field::PrimeField;
use auslander::iso::{IsoOutcome, is_isomorphic};
use auslander::linalg::DenseMat;
use auslander::module::{Module, direct_sum};

fn fields() -> [PrimeField; 2] {
    [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()]
}

fn fixtures(field: PrimeField) -> Vec<Arc<Algebra>> {
    vec![
        linear_an(3, field),
        kronecker(2, field),
        dual_numbers(field),
        truncated_poly(3, field).unwrap(),
        cyclic_nakayama(&[3, 3, 3], field).unwrap(),
        radical_square_zero_cycle(3, field),
        commutative_square(field),
    ]
}

fn assert_isomorphic(m: &Module, n: &Module, context: &str) {
    match is_isomorphic(m, n).unwrap() {
        IsoOutcome::Isomorphic(w) => {
            assert!(w.is_isomorphism(), "{context}: witness not invertible")
        }
        other => panic!("{context}: expected an isomorphism, got {other:?}"),
    }
}

#[test]
fn decompose_of_p_plus_s_plus_p_finds_three_certified_summands_and_reassembles() {
    for field in fields() {
        for algebra in fixtures(field) {
            let last = algebra.quiver().num_vertices() - 1;
            let p = Module::projective(&algebra, 0);
            let s = Module::simple(&algebra, last);
            let (sum, _, _) = direct_sum(&[&p, &s, &p]);
            let d = decompose(&sum);
            let context = format!(
                "P_0 ⊕ S_{last} ⊕ P_0 over F_{} for dim-{} algebra",
                field.modulus(),
                algebra.dim()
            );
            assert_eq!(d.summands().len(), 3, "{context}");
            assert!(
                d.certificates()
                    .iter()
                    .all(|c| *c == Certificate::Indecomposable),
                "{context}"
            );
            let mut dims: Vec<Vec<usize>> = d
                .summands()
                .iter()
                .map(|m| m.dim_vector().to_vec())
                .collect();
            dims.sort();
            let mut expected = vec![
                p.dim_vector().to_vec(),
                p.dim_vector().to_vec(),
                s.dim_vector().to_vec(),
            ];
            expected.sort();
            assert_eq!(dims, expected, "{context}");
            let parts: Vec<&Module> = d.summands().iter().collect();
            let (reassembled, _, _) = direct_sum(&parts);
            assert_isomorphic(&reassembled, &sum, &context);
        }
    }
}

/// `P^n ⊕ S` must split into `n` copies of `P` and one `S`, every summand
/// certified, for every fixture and every `n` up to four.
///
/// The field matters. `End(P^n)` is a matrix algebra over a local ring, so a
/// uniform element is invertible with probability `1 - O(1/p)`. Over F_2 a
/// random endomorphism is a non-unit often enough that the random Fitting
/// fallback finds a split by chance. Over F_32003 it almost never does. Before
/// `EndoAlgebra::singular_element` existed, this test passed over F_2 and F_5
/// and returned `Undetermined` for the whole `P^n` block at F_32003.
#[test]
fn decompose_splits_repeated_summands_over_a_large_field() {
    let field = PrimeField::new(32003).unwrap();
    for algebra in fixtures(field) {
        let last = algebra.quiver().num_vertices() - 1;
        let p = Module::projective(&algebra, 0);
        let s = Module::simple(&algebra, last);
        for n in 2..=4usize {
            let mut parts: Vec<&Module> = (0..n).map(|_| &p).collect();
            parts.push(&s);
            let (sum, _, _) = direct_sum(&parts);
            let d = decompose(&sum);
            let context = format!(
                "P_0^{n} ⊕ S_{last} over F_32003 for dim-{} algebra",
                algebra.dim()
            );
            assert!(
                d.certificates()
                    .iter()
                    .all(|c| *c == Certificate::Indecomposable),
                "{context}: {:?}",
                d.certificates()
            );
            let mut dims: Vec<Vec<usize>> = d
                .summands()
                .iter()
                .map(|m| m.dim_vector().to_vec())
                .collect();
            dims.sort();
            let mut expected: Vec<Vec<usize>> = (0..n).map(|_| p.dim_vector().to_vec()).collect();
            expected.push(s.dim_vector().to_vec());
            expected.sort();
            assert_eq!(dims, expected, "{context}");
            let summands: Vec<&Module> = d.summands().iter().collect();
            let (reassembled, _, _) = direct_sum(&summands);
            assert_isomorphic(&reassembled, &sum, &context);
        }
    }
}

/// A repeated summand whose endomorphism algebra is a proper extension field
/// must still split.
///
/// `W` is the Kronecker representation `(I_3, C)` for `C` the companion matrix
/// of `x³ + x + 5`, irreducible over F_32003 because it is a cubic with no
/// root there. Then `End(W)` is the field `F_{32003³}` and
/// `End(W ⊕ W) = M_2(F_{32003³})`: one Wedderburn factor, zero radical, and
/// noncommutative, so no central idempotent exists to split it. Searching for
/// a base-field eigenvalue does not find a splitting element either, since a
/// drawn element of `M_2(F_{p³})` has one with probability `O(p^{-2})`. Only
/// coprime factorization of the minimal polynomial reaches this case.
#[test]
fn decompose_splits_a_repeated_summand_with_an_extension_endomorphism_field() {
    let field = PrimeField::new(32003).unwrap();
    let algebra = kronecker(2, field);
    let mut identity = DenseMat::zero(3, 3);
    for i in 0..3 {
        identity.set(i, i, field.elem(1));
    }
    let mut companion = DenseMat::zero(3, 3);
    companion.set(1, 0, field.elem(1));
    companion.set(2, 1, field.elem(1));
    companion.set(0, 2, field.elem(-5));
    companion.set(1, 2, field.elem(-1));
    let w = Module::new(algebra, vec![3, 3], vec![identity, companion]).unwrap();

    let endo_w = EndoAlgebra::new(&w);
    assert!(endo_w.is_local(), "End(W) should be the field F_{{p³}}");
    assert_eq!(endo_w.dim(), 3);

    let (m, _, _) = direct_sum(&[&w, &w]);
    let endo_m = EndoAlgebra::new(&m);
    assert_eq!(endo_m.dim(), 12);
    assert_eq!(endo_m.radical_dim(), 0);
    assert_eq!(endo_m.semisimple_factor_count(), 1);
    assert!(!endo_m.quotient_is_commutative());

    let d = decompose(&m);
    assert_eq!(d.summands().len(), 2, "{:?}", d.certificates());
    assert!(
        d.certificates()
            .iter()
            .all(|c| *c == Certificate::Indecomposable),
        "{:?}",
        d.certificates()
    );
    for summand in d.summands() {
        assert_eq!(summand.dim_vector(), w.dim_vector());
    }
    match krull_schmidt(&m) {
        KrullSchmidtOutcome::Classes(classes) => {
            assert_eq!(classes.len(), 1);
            assert_eq!(classes[0].multiplicity, 2);
        }
        other => panic!("expected one class of multiplicity two, got {other:?}"),
    }
    assert_isomorphic(&m, &m, "W ⊕ W against itself");
    // Before decompose split this case, tau failed on the same module: the
    // cross-check could not certify the routes equal and reported a disagreement.
    assert!(tau(&m).is_ok(), "tau must not report a false disagreement");
}

/// Krull-Schmidt must report `P` with multiplicity `n` in `P^n ⊕ S`, and the
/// multiplicities must account for every summand.
#[test]
fn krull_schmidt_reports_the_multiplicity_of_a_repeated_summand() {
    let field = PrimeField::new(32003).unwrap();
    for algebra in fixtures(field) {
        let last = algebra.quiver().num_vertices() - 1;
        let p = Module::projective(&algebra, 0);
        let s = Module::simple(&algebra, last);
        for n in 2..=4usize {
            let mut parts: Vec<&Module> = (0..n).map(|_| &p).collect();
            parts.push(&s);
            let (sum, _, _) = direct_sum(&parts);
            let context = format!(
                "P_0^{n} ⊕ S_{last} over F_32003 for dim-{} algebra",
                algebra.dim()
            );
            match krull_schmidt(&sum) {
                KrullSchmidtOutcome::Classes(classes) => {
                    let total: usize = classes.iter().map(|c| c.multiplicity).sum();
                    assert_eq!(total, n + 1, "{context}: multiplicities do not add up");
                    let for_p = classes
                        .iter()
                        .find(|c| c.representative.dim_vector() == p.dim_vector())
                        .unwrap_or_else(|| panic!("{context}: no class matches P_0"));
                    // S_last is P_0 itself when vertex 0 is a sink.
                    let expected = if s.dim_vector() == p.dim_vector() {
                        n + 1
                    } else {
                        n
                    };
                    assert_eq!(for_p.multiplicity, expected, "{context}");
                }
                other => panic!("{context}: {other:?}"),
            }
        }
    }
}

#[test]
fn is_isomorphic_distinguishes_the_twelve_fixture_simples_and_projectives() {
    for field in fields() {
        let mut count = 0;
        for algebra in [
            linear_an(3, field),
            kronecker(2, field),
            dual_numbers(field),
        ] {
            let n = algebra.quiver().num_vertices();
            let mut modules = Vec::new();
            for v in 0..n {
                modules.push(Module::simple(&algebra, v));
                modules.push(Module::projective(&algebra, v));
            }
            count += modules.len();
            for (i, m) in modules.iter().enumerate() {
                for (j, other) in modules.iter().enumerate() {
                    let context = format!(
                        "modules {i} and {j} over F_{} for dim-{} algebra",
                        field.modulus(),
                        algebra.dim()
                    );
                    if m.dim_vector() == other.dim_vector() {
                        assert_isomorphic(m, other, &context);
                    } else {
                        assert!(
                            matches!(
                                is_isomorphic(m, other).unwrap(),
                                IsoOutcome::NotIsomorphic(_)
                            ),
                            "{context}: expected an obstruction"
                        );
                    }
                }
            }
        }
        assert_eq!(count, 12);
    }
}

#[test]
fn krull_schmidt_is_permutation_invariant_on_shuffled_fixture_sums() {
    for field in fields() {
        for algebra in fixtures(field) {
            let last = algebra.quiver().num_vertices() - 1;
            let s = Module::simple(&algebra, 0);
            let p = Module::projective(&algebra, last);
            let (shuffled, _, _) = direct_sum(&[&s, &p, &s, &p]);
            let (reordered, _, _) = direct_sum(&[&p, &s, &p, &s]);
            let classes = |m: &Module| -> Vec<(Vec<usize>, usize)> {
                match krull_schmidt(m) {
                    KrullSchmidtOutcome::Classes(classes) => {
                        let mut dims: Vec<(Vec<usize>, usize)> = classes
                            .iter()
                            .map(|c| (c.representative.dim_vector().to_vec(), c.multiplicity))
                            .collect();
                        dims.sort();
                        dims
                    }
                    KrullSchmidtOutcome::Unknown { reason } => {
                        panic!("unexpected Unknown: {reason}")
                    }
                }
            };
            let left = classes(&shuffled);
            assert_eq!(left, classes(&reordered), "F_{}", field.modulus());
            assert_eq!(left.iter().map(|(_, m)| m).sum::<usize>(), 4);
            let mut expected = vec![
                (s.dim_vector().to_vec(), 2usize),
                (p.dim_vector().to_vec(), 2usize),
            ];
            expected.sort();
            assert_eq!(left, expected, "F_{}", field.modulus());
        }
    }
}

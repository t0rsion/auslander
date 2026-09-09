use auslander::algebra::{Algebra, AlgebraBuildError, linear_an};
use auslander::certificate::FinitenessData;
use auslander::completion::{CompletionLimits, TruncationReason};
use auslander::ext::ext_dim;
use auslander::field::PrimeField;
use auslander::iso::{IsoOutcome, Obstruction, is_isomorphic};
use auslander::linalg::DenseMat;
use auslander::module::{Module, ModuleError, direct_sum};
use auslander::quiver::Quiver;
use auslander::relation::{Presentation, Relation, RelationError};
use auslander::verify::{VerifyError, verify};

use super::common::{self, f5, ids, inhomogeneous_quiver};
use super::fixtures::square;

/// Row 11. Over `kA_2` the sequence `0 → S_1 → P_0 → S_0 → 0` does not
/// split. `Ext¹(S_0, S_1) = 1`, and the middle term `P_0` is not isomorphic
/// to `S_0 ⊕ S_1`. That second fact is the witness the public API certifies.
///
/// The obstruction is the radical series. `rad P_0 = S_1 = [0, 1]` and
/// `rad² P_0 = 0`, so `P_0` has the one-entry series `[[0, 1]]`, while
/// `S_0 ⊕ S_1` is semisimple and its series is empty.
#[test]
fn ka2_nonsplit_extension_witnessed_by_the_middle_term() {
    let a2 = linear_an(2, f5());
    let s0 = Module::simple(&a2, 0);
    let s1 = Module::simple(&a2, 1);
    assert_eq!(ext_dim(&s0, &s1, 1).unwrap(), 1);
    let p0 = Module::projective(&a2, 0);
    let (split_sum, _, _) = direct_sum(&[&s0, &s1]);
    assert_eq!(p0.dim_vector(), split_sum.dim_vector());
    match is_isomorphic(&p0, &split_sum).unwrap() {
        IsoOutcome::NotIsomorphic(Obstruction::LoewySeries { source, target }) => {
            assert_eq!(source, vec![vec![0, 1]]);
            assert_eq!(target, Vec::<Vec<usize>>::new());
        }
        other => panic!("expected a Loewy-series obstruction, got {other:?}"),
    }
}

/// Row 11 over A. `Ext¹(S_0, S_1) = 1`; the extension is realized by the
/// module `M = [1, 1, 0, 0]` with `a` acting as the identity (the relation
/// holds because `b` and `d` act on zero spaces). `M` is not isomorphic to
/// `S_0 ⊕ S_1` because `rad M ≠ 0`.
///
/// The obstruction is the radical series. `rad M` is the image of `a`, so
/// `rad M = [0, 1, 0, 0]` and `rad² M = 0`, giving the one-entry series
/// `[[0, 1, 0, 0]]`, while the semisimple `S_0 ⊕ S_1` has an empty series.
#[test]
fn square_nonsplit_extension_of_s0_by_s1() {
    let a = square();
    let s0 = Module::simple(&a, 0);
    let s1 = Module::simple(&a, 1);
    assert_eq!(ext_dim(&s0, &s1, 1).unwrap(), 1);
    let one = f5().one();
    let middle = Module::new(
        a.clone(),
        vec![1, 1, 0, 0],
        vec![
            DenseMat::from_rows(&[vec![one]]),
            DenseMat::zero(1, 0),
            DenseMat::zero(1, 0),
            DenseMat::zero(0, 0),
        ],
    )
    .unwrap();
    let (split_sum, _, _) = direct_sum(&[&s0, &s1]);
    assert_eq!(middle.dim_vector(), split_sum.dim_vector());
    match is_isomorphic(&middle, &split_sum).unwrap() {
        IsoOutcome::NotIsomorphic(Obstruction::LoewySeries { source, target }) => {
            assert_eq!(source, vec![vec![0, 1, 0, 0]]);
            assert_eq!(target, Vec::<Vec<usize>>::new());
        }
        other => panic!("expected a Loewy-series obstruction, got {other:?}"),
    }
}

/// Row 12. Dump the certificate, verify the bytes independently, rebuild
/// the algebra from the verified token, and compare the invariants.
#[test]
fn square_certificate_dump_verify_rebuild_round_trip() {
    let a = square();
    let bytes = a.certificate().to_canonical_json();
    let verified = verify(&bytes).unwrap();
    let rebuilt = Algebra::from_verified(verified).unwrap();
    assert_eq!(rebuilt.dim(), a.dim());
    assert_eq!(rebuilt.basis(), a.basis());
    assert_eq!(rebuilt.cartan_matrix(), a.cartan_matrix());
    assert_eq!(rebuilt.certificate().to_canonical_json(), bytes);
}

/// Row 13. A tight step budget, a tight basis budget, and a tight word-length
/// budget on B's presentation each surface `Truncated` carrying the matching
/// `TruncationReason`, never a silent partial answer. Every relation of B is a
/// combination of paths of length 2, so `max_word_len: 1` rejects the input
/// words themselves.
#[test]
fn preprojective_with_tight_limits_is_truncated_with_diagnostics() {
    let presentation = common::preprojective_a3_presentation();
    for (limits, reason) in [
        (
            CompletionLimits {
                max_steps: 5,
                ..CompletionLimits::default()
            },
            TruncationReason::StepBudget,
        ),
        (
            CompletionLimits {
                max_basis: 1,
                ..CompletionLimits::default()
            },
            TruncationReason::BasisBudget,
        ),
        (
            CompletionLimits {
                max_word_len: 1,
                ..CompletionLimits::default()
            },
            TruncationReason::WordLenBudget,
        ),
    ] {
        match Algebra::new(presentation.clone(), &limits) {
            Err(AlgebraBuildError::Truncated(diagnostics)) => {
                assert_eq!(diagnostics.reason, reason);
                assert!(diagnostics.steps_used <= limits.max_steps);
            }
            other => panic!("expected Truncated with {reason:?}, got {other:?}"),
        }
    }
}

/// Row 13. The free loop has infinitely many normal words. The error
/// carries the completed certificate plus a cycle witness, and re-verifying
/// the certificate bytes reproduces the same proof.
#[test]
fn free_loop_presentation_is_infinite_dimensional_with_a_witness() {
    let field = f5();
    let quiver = Quiver::new(1, &[(0, 0)]).unwrap();
    let presentation = Presentation::new(quiver, field, Vec::new()).unwrap();
    match Algebra::new(presentation, &CompletionLimits::default()) {
        Err(AlgebraBuildError::InfiniteDimensional {
            certificate,
            witness,
        }) => {
            assert!(!witness.cycle.is_empty(), "the witness names a cycle");
            assert_eq!(
                certificate.finiteness,
                FinitenessData::Infinite {
                    prefix: witness.prefix.clone(),
                    cycle: witness.cycle.clone(),
                },
                "the error's witness is the certificate's finiteness witness"
            );
            match verify(&certificate.to_canonical_json()) {
                Err(VerifyError::InfiniteDimensional { witness: again }) => {
                    assert_eq!(again, witness);
                }
                other => panic!("expected InfiniteDimensional from verify, got {other:?}"),
            }
        }
        other => panic!("expected InfiniteDimensional, got {other:?}"),
    }
}

/// Row 13. Rejected relation input keeps its typed errors: mixed targets,
/// a length-1 word, a coefficient made for another field.
#[test]
fn relation_errors_are_typed() {
    let quiver = inhomogeneous_quiver();
    let field = f5();
    assert_eq!(
        Relation::new(
            &quiver,
            field,
            vec![(field.one(), ids(&[0, 1])), (field.one(), ids(&[2, 3]))],
        ),
        Err(RelationError::MixedTarget { index: 1 })
    );
    assert_eq!(
        Relation::new(&quiver, field, vec![(field.one(), ids(&[0]))]),
        Err(RelationError::WordTooShort { index: 0, len: 1 })
    );
    let foreign = PrimeField::new(7).unwrap().elem(6);
    assert_eq!(
        Relation::new(&quiver, field, vec![(foreign, ids(&[0, 1]))]),
        Err(RelationError::NonCanonicalCoefficient { index: 0 })
    );
}

/// Row 13. A representation with `M(a)M(b) ≠ M(c)M(d)` is a `kQ`-
/// representation but not a module over A, and construction says which
/// relation acts nonzero.
#[test]
fn square_module_validation_rejects_a_relation_violation() {
    let a = square();
    let one = f5().one();
    let zero = f5().zero();
    let result = Module::new(
        a.clone(),
        vec![1, 1, 1, 1],
        vec![
            DenseMat::from_rows(&[vec![one]]),
            DenseMat::from_rows(&[vec![one]]),
            DenseMat::from_rows(&[vec![one]]),
            DenseMat::from_rows(&[vec![zero]]),
        ],
    );
    assert_eq!(
        result.unwrap_err(),
        ModuleError::RelationActsNonzero { index: 0 }
    );
}

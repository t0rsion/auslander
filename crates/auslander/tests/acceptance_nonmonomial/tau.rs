use auslander::algebra::{linear_an, linear_nakayama};
use auslander::ar::tau;
use auslander::decompose::Certificate;
use auslander::dynkin::{DynkinError, dynkin_indecomposables};
use auslander::enumerate::nakayama_indecomposables;
use auslander::module::Module;

use super::common::{f5, preprojective_a3};
use super::fixtures::square;

/// Row 9. Hand derivation of `τS_0` over A via the AR formula: the minimal
/// presentation is `P_1 ⊕ P_2 → P_0`, and `ν` turns it into
/// `I_1 ⊕ I_2 → I_0`. `Hom(S_0, A) = 0` because every `soc P_v = S_3`, so
/// `νS_0 = 0`, the map is surjective, and
/// `τS_0 = [2, 1, 1, 0] - [1, 0, 0, 0] = [1, 1, 1, 0]`. The other values
/// are the oracle's `tau` entries. `tau` itself cross-checks the Nakayama
/// kernel against the transpose dual, so `Ok` certifies both routes.
#[test]
fn square_tau_of_simples_matches_the_hand_and_oracle_values() {
    let a = square();
    let expected: [&[usize]; 3] = [&[1, 1, 1, 0], &[0, 0, 1, 1], &[0, 1, 0, 1]];
    for (v, dims) in expected.iter().enumerate() {
        let t = tau(&Module::simple(&a, v as u32)).unwrap();
        assert_eq!(t.dim_vector(), *dims, "τS_{v}");
    }
    assert!(tau(&Module::simple(&a, 3)).unwrap().is_zero());
}

/// Row 9. Over the self-injective B no simple is projective; the dimension
/// vectors are the oracle's `tau` entries.
#[test]
fn preprojective_tau_of_simples_matches_the_oracle() {
    let b = preprojective_a3();
    let expected: [&[usize]; 3] = [&[0, 1, 1], &[1, 1, 1], &[1, 1, 0]];
    for (v, dims) in expected.iter().enumerate() {
        let t = tau(&Module::simple(&b, v as u32)).unwrap();
        assert_eq!(t.dim_vector(), *dims, "τS_{v}");
    }
}

/// The Nakayama and Dynkin enumerator counts agree. The Dynkin enumerator
/// rejects a nonzero ideal with the typed error.
#[test]
fn enumerators_agree_and_reject_the_square() {
    let nakayama = linear_nakayama(&[3, 2, 1], f5()).unwrap();
    let modules = nakayama_indecomposables(&nakayama).unwrap();
    assert_eq!(modules.len(), 6);
    assert!(
        modules
            .iter()
            .all(|(_, c)| *c == Certificate::Indecomposable)
    );
    let a3 = linear_an(3, f5());
    let modules = dynkin_indecomposables(&a3).unwrap();
    assert_eq!(modules.len(), 6);
    assert!(
        modules
            .iter()
            .all(|(_, c)| *c == Certificate::Indecomposable)
    );
    match dynkin_indecomposables(&square()) {
        Err(DynkinError::NonzeroIdeal { relations }) => assert_eq!(relations, 1),
        other => panic!("expected NonzeroIdeal, got {other:?}"),
    }
}

use super::super::common::{find_factor, ids};
use super::super::{VerifyError, verify, verify_certificate};
use super::check;
use super::fixtures::{loop_certificate, square_certificate, x3_certificate};
use crate::quiver::{ArrowId, PathWord, Quiver};

#[test]
fn truncated_polynomial_certificate_accepted() {
    let verified = check(&x3_certificate()).unwrap();
    assert_eq!(verified.field().modulus(), 5);
    assert_eq!(verified.quiver().num_arrows(), 1);
    assert_eq!(verified.basis().len(), 1);
    assert_eq!(verified.basis()[0].len(), 1);
    let lengths: Vec<usize> = verified.normal_words().iter().map(PathWord::len).collect();
    assert_eq!(lengths, [0, 1, 2]);
    assert!(verified.normal_words()[0].is_trivial());
    assert_eq!(verified.certificate(), &x3_certificate());
}

#[test]
fn commutative_square_certificate_accepted() {
    let verified = check(&square_certificate()).unwrap();
    assert_eq!(verified.quiver().num_vertices(), 4);
    assert_eq!(verified.normal_words().len(), 9);
    assert!(
        verified.normal_words()[..4]
            .iter()
            .all(PathWord::is_trivial)
    );
    assert_eq!(
        verified.normal_words()[8].arrows(),
        &[ArrowId(0), ArrowId(1)][..]
    );
    assert_eq!(verified.basis()[0][0].0, verified.field().one());
}

#[test]
fn one_loop_without_relations_is_infinite_dimensional() {
    let certificate = loop_certificate();
    let witness = match check(&certificate) {
        Err(VerifyError::InfiniteDimensional { witness }) => witness,
        other => panic!("expected InfiniteDimensional, got {other:?}"),
    };
    assert!(!witness.cycle.is_empty());
    let mut word = witness.prefix.clone();
    word.extend_from_slice(&witness.cycle);
    word.extend_from_slice(&witness.cycle);
    let quiver = Quiver::new(1, &[(0, 0)]).unwrap();
    assert!(PathWord::from_arrows(&quiver, &ids(&word)).is_ok());
    for element in &certificate.basis {
        assert!(find_factor(&word, &element[0].1).is_none());
    }
}

#[test]
fn unparsable_bytes_rejected() {
    assert!(matches!(
        verify("not a certificate"),
        Err(VerifyError::Parse(_))
    ));
}

/// The two entry points differ only in transport. The byte path adds the
/// strict parse and nothing else. It accepts and rejects exactly what
/// the typed path does.
#[test]
fn the_typed_entry_and_the_byte_entry_agree() {
    for certificate in [x3_certificate(), square_certificate()] {
        let bytes = certificate.to_canonical_json();
        let typed = verify_certificate(certificate.clone()).expect("the certificate verifies");
        assert_eq!(verify(&bytes).unwrap().normal_words(), typed.normal_words());
        let mut tampered = certificate;
        tampered.order = "wrong".to_string();
        assert_eq!(
            verify(&tampered.to_canonical_json()).unwrap_err(),
            verify_certificate(tampered).unwrap_err()
        );
    }
}

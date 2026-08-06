//! Engine-to-verifier integration: the independent verifier must accept
//! every certificate the completion engine emits, from its serialized bytes
//! alone.

use auslander::completion::{CompletionLimits, Outcome, complete};
use auslander::field::PrimeField;
use auslander::quiver::{ArrowId, Quiver};
use auslander::relation::{Presentation, Relation};
use auslander::verify::{VerifyError, verify};

fn presentation(quiver: Quiver, p: u64, relations: &[&[(i64, &[u32])]]) -> Presentation {
    let field = PrimeField::new(p).unwrap();
    let relations: Vec<Relation> = relations
        .iter()
        .map(|terms| {
            let terms: Vec<(auslander::field::Fp, Vec<ArrowId>)> = terms
                .iter()
                .map(|&(c, word)| (field.elem(c), word.iter().copied().map(ArrowId).collect()))
                .collect();
            Relation::new(&quiver, field, terms).unwrap()
        })
        .collect();
    Presentation::new(quiver, field, relations).unwrap()
}

fn complete_and_verify(p: Presentation) -> Result<(), VerifyError> {
    let outcome = complete(&p, &CompletionLimits::default());
    let Outcome::Complete(cert) = outcome else {
        panic!("completion truncated on a test presentation");
    };
    verify(&cert.to_canonical_json()).map(|_| ())
}

#[test]
fn monomial_x_cubed_certificate_verifies() {
    let quiver = Quiver::new(1, &[(0, 0)]).unwrap();
    let p = presentation(quiver, 5, &[&[(1, &[0, 0, 0])]]);
    assert_eq!(complete_and_verify(p), Ok(()));
}

#[test]
fn commutative_square_certificate_verifies() {
    let quiver = Quiver::new(4, &[(0, 1), (1, 3), (0, 2), (2, 3)]).unwrap();
    let p = presentation(quiver, 5, &[&[(1, &[0, 1]), (-1, &[2, 3])]]);
    assert_eq!(complete_and_verify(p), Ok(()));
}

#[test]
fn overlap_completion_certificate_verifies() {
    let quiver = Quiver::new(1, &[(0, 0), (0, 0)]).unwrap();
    let p = presentation(quiver, 2, &[&[(1, &[1, 0]), (1, &[0, 0])], &[(1, &[1, 1])]]);
    assert_eq!(complete_and_verify(p), Ok(()));
}

#[test]
fn inclusion_completion_certificate_verifies() {
    let quiver = Quiver::new(1, &[(0, 0)]).unwrap();
    let p = presentation(
        quiver,
        2,
        &[
            &[(1, &[0, 0, 0, 0, 0])],
            &[(1, &[0, 0, 0, 0]), (1, &[0, 0])],
        ],
    );
    assert_eq!(complete_and_verify(p), Ok(()));
}

#[test]
fn inhomogeneous_certificate_verifies() {
    let quiver = Quiver::new(5, &[(0, 1), (1, 4), (0, 2), (2, 3), (3, 4)]).unwrap();
    let p = presentation(quiver, 5, &[&[(1, &[2, 3, 4]), (-1, &[0, 1])]]);
    assert_eq!(complete_and_verify(p), Ok(()));
}

#[test]
fn characteristic_two_diamond_certificate_verifies() {
    let quiver = Quiver::new(4, &[(0, 1), (1, 3), (0, 2), (2, 3)]).unwrap();
    let p = presentation(quiver, 2, &[&[(1, &[0, 1]), (1, &[2, 3])]]);
    assert_eq!(complete_and_verify(p), Ok(()));
}

#[test]
fn free_loop_certificate_is_rejected_as_infinite() {
    let quiver = Quiver::new(1, &[(0, 0)]).unwrap();
    let field = PrimeField::new(5).unwrap();
    let p = Presentation::new(quiver, field, Vec::new()).unwrap();
    let outcome = complete(&p, &CompletionLimits::default());
    let Outcome::Complete(cert) = outcome else {
        panic!("empty presentation must complete");
    };
    let result = verify(&cert.to_canonical_json());
    assert!(matches!(
        result,
        Err(VerifyError::InfiniteDimensional { .. })
    ));
}

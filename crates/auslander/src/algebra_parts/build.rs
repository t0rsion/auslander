use std::sync::Arc;

use crate::certificate::FinitenessData;
use crate::completion::{CompletionLimits, Outcome, complete};
use crate::profile::{Site, hit};
use crate::relation::{Presentation, Relation};
use crate::verify::{VerifiedCompletion, VerifyError, verify_certificate};

use super::types::{Algebra, AlgebraBuildError, check_input_relations, index_basis};

impl Algebra {
    /// Completes `presentation`, verifies the emitted certificate, and builds
    /// the tables from the verified data.
    pub fn new(
        presentation: Presentation,
        limits: &CompletionLimits,
    ) -> Result<Arc<Algebra>, AlgebraBuildError> {
        hit(Site::AlgebraNew);
        let certificate = match complete(&presentation, limits) {
            Outcome::Complete(certificate) => certificate,
            Outcome::Truncated(diagnostics) => {
                return Err(AlgebraBuildError::Truncated(diagnostics));
            }
        };
        // verify_certificate consumes the certificate, and the infinite case
        // has to hand it back. The verifier returns InfiniteDimensional only
        // for a certificate whose own finiteness claim is Infinite, so a copy
        // taken in exactly that case covers the error path and the finite path
        // copies nothing.
        let spare = match certificate.finiteness {
            FinitenessData::Infinite { .. } => Some(certificate.clone()),
            FinitenessData::Finite => None,
        };
        match verify_certificate(certificate) {
            Ok(verified) => {
                check_input_relations(&presentation, verified.certificate())?;
                Algebra::from_verified_with_limits(verified, limits)
            }
            Err(VerifyError::InfiniteDimensional { witness }) => {
                Err(AlgebraBuildError::InfiniteDimensional {
                    certificate: Box::new(
                        spare.expect("only an infinite finiteness claim yields this error"),
                    ),
                    witness,
                })
            }
            Err(error) => Err(AlgebraBuildError::Verification(error)),
        }
    }

    /// Builds the algebra from an already verified completion.
    ///
    /// This is the dump, reload, and reverify path: serialize with
    /// [`Algebra::certificate`], later call [`crate::verify::verify`] on the
    /// bytes, and rebuild from the token.
    ///
    /// Errors with [`AlgebraBuildError::NonAdmissible`] when the arrow ideal
    /// of the verified quotient is not nilpotent. Verification proves the
    /// quotient finite dimensional, which is weaker: it decides that from
    /// the leading words alone.
    ///
    /// The rebuilt algebra uses [`CompletionLimits::default`] as its
    /// effective limits. Certificate bytes are untrusted input, and untrusted
    /// input must never carry or select downstream resource budgets. Use
    /// [`Algebra::from_verified_with_limits`] to preserve the budgets of the
    /// original build.
    pub fn from_verified(verified: VerifiedCompletion) -> Result<Arc<Algebra>, AlgebraBuildError> {
        Algebra::from_verified_with_limits(verified, &CompletionLimits::default())
    }

    /// [`Algebra::from_verified`] with caller-supplied completion limits.
    ///
    /// The limits come from the caller, never from the certificate bytes.
    /// Downstream completions such as [`crate::opposite::opposite`] run with
    /// them.
    pub fn from_verified_with_limits(
        verified: VerifiedCompletion,
        limits: &CompletionLimits,
    ) -> Result<Arc<Algebra>, AlgebraBuildError> {
        hit(Site::AlgebraFromVerified);
        let quiver = verified.quiver().clone();
        let field = verified.field();
        let relations: Vec<Relation> = verified
            .basis()
            .iter()
            .map(|element| {
                let terms = element
                    .iter()
                    .map(|(coeff, word)| (*coeff, word.arrows().to_vec()))
                    .collect();
                Relation::new(&quiver, field, terms)
                    .expect("a verified basis element is a valid relation")
            })
            .collect();
        let basis = verified.normal_words().to_vec();
        let (index_of, from, to, between) = index_basis(&quiver, &basis);
        let mut algebra = Algebra {
            quiver,
            field,
            relations,
            certificate: verified.certificate().clone(),
            limits: limits.clone(),
            basis,
            index_of,
            from,
            to,
            between,
            right_mul: Vec::new(),
            left_mul: Vec::new(),
            radical_powers: Vec::new(),
        };
        let num_arrows = algebra.quiver.num_arrows();
        let mut right_mul = vec![vec![Vec::new(); num_arrows]; algebra.basis.len()];
        let mut left_mul = vec![vec![Vec::new(); algebra.basis.len()]; num_arrows];
        for (i, p) in algebra.basis.iter().enumerate() {
            for &a in algebra.quiver.arrows_from(p.target()) {
                let mut word = p.arrows().to_vec();
                word.push(a);
                right_mul[i][a.index()] = algebra.nf_arrow_word(word);
            }
            for &a in algebra.quiver.arrows_to(p.source()) {
                let mut word = vec![a];
                word.extend_from_slice(p.arrows());
                left_mul[a.index()][i] = algebra.nf_arrow_word(word);
            }
        }
        algebra.right_mul = right_mul;
        algebra.left_mul = left_mul;
        // radical_chain needs right_mul and between, and nothing after it, so
        // it is the last field filled.
        algebra.radical_powers = algebra.radical_chain()?;
        Ok(Arc::new(algebra))
    }
}

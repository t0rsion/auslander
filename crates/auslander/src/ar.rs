//! The AR translate τ, computed two independent ways with an automatic
//! cross-check.
//!
//! Both routes start from the minimal presentation `P_1 -d1-> P_0 → M → 0` in
//! element-matrix form. Route 1 applies the Nakayama functor and takes a kernel:
//! `τM = ker(ν(d1): νP_1 → νP_0)`, from the exact sequence
//! `0 → τM → νP_1 → νP_0 → νM → 0` (see
//! [`crate::opposite::nu_of_presentation_map`]). Route 2 applies `Hom_A(−, A)` to
//! `d1`, which is the element-matrix transpose over the opposite algebra, takes
//! the cokernel to get `Tr M`, and dualizes back: `τM = D(Tr M)`.
//!
//! Running both routes is a cross-check, and the cross-check has a limit. The
//! routes share two things: the checked minimal presentation, and the
//! [`crate::opposite::ElementMatrix`] path-coefficient encoding. Everything after
//! that is independent: injectives plus kernel on one side, opposite-side
//! projectives plus cokernel plus dual on the other. Agreement therefore tests
//! every step below the shared encoding, and it tests nothing inside it.
//!
//! [`tau`] always runs both routes and answers only when
//! [`crate::iso::is_isomorphic`] certifies the two results isomorphic.

use std::fmt;

use crate::algebra::AlgebraBuildError;
use crate::hom::{cokernel, kernel};
use crate::iso::{IsoOutcome, Obstruction, is_isomorphic};
use crate::module::Module;
use crate::opposite::{ElementMatrix, OppositeMap, dual, nu_of_presentation_map, opposite};
use crate::resolution::minimal_presentation_matrix;

/// A [`tau`] cross-check that did not end in agreement.
///
/// The two failure variants are different claims. Do not conflate them.
/// [`TauError::RoutesDisagree`] carries a proof that the two routes produced
/// non-isomorphic modules; that is a bug in this library, and one of the two
/// results is wrong. [`TauError::AgreementUnknown`] means the isomorphism test
/// reached no verdict. It says nothing about whether the routes agree, so it is
/// evidence about the test, not about `τM`.
#[derive(Clone, Debug)]
pub enum TauError {
    /// Building the opposite algebra failed, so the transpose-dual route
    /// could not run. This is an engine limit or defect, not a statement
    /// about the module.
    Opposite(AlgebraBuildError),
    /// [`crate::iso::is_isomorphic`] proved the two routes non-isomorphic.
    RoutesDisagree {
        /// `ker(ν(d1))`.
        nakayama_kernel: Module,
        /// `D(Tr M)`.
        transpose_dual: Module,
        /// The proof of non-isomorphism.
        obstruction: Obstruction,
    },
    /// [`crate::iso::is_isomorphic`] certified neither an isomorphism nor an
    /// obstruction, so the cross-check is undecided.
    AgreementUnknown {
        /// `ker(ν(d1))`.
        nakayama_kernel: Module,
        /// `D(Tr M)`.
        transpose_dual: Module,
        /// Why the isomorphism test could not certify either answer.
        reason: String,
    },
}

impl fmt::Display for TauError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Opposite(error) => {
                write!(f, "building the opposite algebra failed: {error}")
            }
            Self::RoutesDisagree {
                nakayama_kernel,
                transpose_dual,
                obstruction,
            } => write!(
                f,
                "τ routes disagree: Nakayama kernel has dimension vector {:?}, transpose dual {:?} ({obstruction:?})",
                nakayama_kernel.dim_vector(),
                transpose_dual.dim_vector()
            ),
            Self::AgreementUnknown {
                nakayama_kernel,
                transpose_dual,
                reason,
            } => write!(
                f,
                "τ routes not certified isomorphic: Nakayama kernel has dimension vector {:?}, \
                 transpose dual {:?} ({reason})",
                nakayama_kernel.dim_vector(),
                transpose_dual.dim_vector()
            ),
        }
    }
}

impl std::error::Error for TauError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Opposite(error) => Some(error),
            _ => None,
        }
    }
}

/// Route 1: `τM = ker(ν(d1))` for the minimal presentation `P_1 -d1-> P_0`.
/// Zero exactly when `m` is projective.
pub fn tau_via_nakayama_kernel(m: &Module) -> Module {
    nakayama_kernel_route(&minimal_presentation_matrix(m))
}

fn nakayama_kernel_route(d1: &ElementMatrix) -> Module {
    kernel(&nu_of_presentation_map(d1)).0
}

/// Route 2: `τM = D(Tr M)` with `Tr M = coker(Hom_A(d1, A))`, the transposed
/// element matrix realized between opposite-side projectives.
///
/// Zero exactly when `m` is projective. The result lives over the same algebra
/// [`std::sync::Arc`] as `m`. Errors with [`TauError::Opposite`] when building the
/// opposite algebra fails.
pub fn tau_via_transpose_dual(m: &Module) -> Result<Module, TauError> {
    let op = opposite(m.algebra()).map_err(TauError::Opposite)?;
    Ok(transpose_dual_route(&minimal_presentation_matrix(m), &op))
}

fn transpose_dual_route(d1: &ElementMatrix, op: &OppositeMap) -> Module {
    let transposed = d1
        .transpose_over(op)
        .expect("the presentation matrix lives over the algebra side of its own opposite pair");
    let (tr, _) = cokernel(&transposed.morphism());
    dual(&tr, op).expect("Tr M lives over the opposite side of the pair")
}

/// The AR translate `τM`, as the Nakayama-kernel result over `m`'s algebra.
///
/// The result is the zero module exactly when `m` is projective, because a
/// projective has an empty `P_1` in its minimal presentation and both routes
/// then land on the zero module. Test that case with [`Module::is_zero`].
///
/// The presentation is computed once and both routes always run on it. An answer
/// comes back only when [`is_isomorphic`] certifies the two results isomorphic. A
/// certified disagreement is [`TauError::RoutesDisagree`]. An undecided
/// cross-check is [`TauError::AgreementUnknown`], a limit of the isomorphism test
/// rather than evidence about the routes.
pub fn tau(m: &Module) -> Result<Module, TauError> {
    let d1 = minimal_presentation_matrix(m);
    let nakayama_kernel = nakayama_kernel_route(&d1);
    let op = opposite(m.algebra()).map_err(TauError::Opposite)?;
    let transpose_dual = transpose_dual_route(&d1, &op);
    let outcome = is_isomorphic(&nakayama_kernel, &transpose_dual)
        .expect("both routes land over m's algebra Arc");
    match outcome {
        IsoOutcome::Isomorphic(_) => {}
        IsoOutcome::NotIsomorphic(obstruction) => {
            return Err(TauError::RoutesDisagree {
                nakayama_kernel,
                transpose_dual,
                obstruction,
            });
        }
        IsoOutcome::Unknown { reason } => {
            return Err(TauError::AgreementUnknown {
                nakayama_kernel,
                transpose_dual,
                reason,
            });
        }
    }
    Ok(nakayama_kernel)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{cyclic_nakayama, dual_numbers, kronecker, linear_an};
    use crate::field::PrimeField;

    fn fields() -> [PrimeField; 2] {
        [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()]
    }

    #[test]
    fn nakayama_kernel_route_recovers_hand_derived_translates() {
        for field in fields() {
            let a3 = linear_an(3, field);
            assert_eq!(
                tau_via_nakayama_kernel(&Module::simple(&a3, 0)).dim_vector(),
                &[0, 1, 0]
            );
            assert_eq!(
                tau_via_nakayama_kernel(&Module::simple(&a3, 1)).dim_vector(),
                &[0, 0, 1]
            );
            let kron = kronecker(2, field);
            assert_eq!(
                tau_via_nakayama_kernel(&Module::simple(&kron, 0)).dim_vector(),
                &[3, 2]
            );
        }
    }

    #[test]
    fn nakayama_kernel_route_is_zero_on_projectives() {
        for field in fields() {
            for algebra in [
                linear_an(3, field),
                dual_numbers(field),
                cyclic_nakayama(&[3, 3, 3], field).unwrap(),
            ] {
                for v in 0..algebra.quiver().num_vertices() {
                    let p = Module::projective(&algebra, v);
                    assert!(tau_via_nakayama_kernel(&p).is_zero(), "τ P_{v}");
                }
            }
        }
    }

    #[test]
    fn transpose_dual_route_lands_over_the_same_algebra_arc() {
        for field in fields() {
            let a3 = linear_an(3, field);
            let s0 = Module::simple(&a3, 0);
            let t = tau_via_transpose_dual(&s0).unwrap();
            assert!(std::sync::Arc::ptr_eq(t.algebra(), &a3));
            assert_eq!(t.dim_vector(), &[0, 1, 0]);
        }
    }

    #[test]
    fn tau_is_zero_exactly_on_projectives() {
        for field in fields() {
            for algebra in [
                linear_an(3, field),
                dual_numbers(field),
                cyclic_nakayama(&[3, 3, 3], field).unwrap(),
            ] {
                for v in 0..algebra.quiver().num_vertices() {
                    let p = Module::projective(&algebra, v);
                    assert!(tau(&p).unwrap().is_zero(), "τ P_{v}");
                    let s = Module::simple(&algebra, v);
                    if s.dim_vector() == p.dim_vector() {
                        continue;
                    }
                    assert!(!tau(&s).unwrap().is_zero(), "τ S_{v}");
                }
            }
        }
    }

    #[test]
    fn tau_of_the_zero_module_is_zero() {
        let a = linear_an(3, PrimeField::new(5).unwrap());
        let z = Module::zero(&a);
        assert!(tau(&z).unwrap().is_zero());
    }

    #[test]
    fn both_routes_agree_on_every_simple_of_the_fixtures() {
        for field in fields() {
            for algebra in [
                linear_an(3, field),
                kronecker(2, field),
                dual_numbers(field),
                cyclic_nakayama(&[3, 3, 3], field).unwrap(),
            ] {
                for v in 0..algebra.quiver().num_vertices() {
                    let s = Module::simple(&algebra, v);
                    let left = tau_via_nakayama_kernel(&s);
                    let right = tau_via_transpose_dual(&s).unwrap();
                    assert!(
                        matches!(
                            is_isomorphic(&left, &right).unwrap(),
                            IsoOutcome::Isomorphic(_)
                        ),
                        "routes for S_{v} over F_{}",
                        field.modulus()
                    );
                    assert!(tau(&s).is_ok());
                }
            }
        }
    }
}

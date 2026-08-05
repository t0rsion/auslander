//! The AR translate τ, computed two independent ways with an automatic
//! cross-check.
//!
//! Both routes start from the minimal presentation `P_1 -d1-> P_0 → M → 0` in
//! element-matrix form. Route 1 applies the Nakayama functor and takes a
//! kernel: `τM = ker(ν(d1): νP_1 → νP_0)`, from the exact sequence
//! `0 → τM → νP_1 → νP_0 → νM → 0` (see
//! [`crate::opposite::nu_of_presentation_map`]). Route 2 applies
//! `Hom_A(−, A)` to `d1` (the element-matrix transpose over the opposite
//! algebra), takes the cokernel to get `Tr M`, and dualizes back:
//! `τM = D(Tr M)`. The routes share the checked minimal presentation and the
//! [`crate::opposite::ElementMatrix`] path-coefficient encoding. Their back
//! ends are independent (injectives plus kernel versus opposite-side
//! projectives plus cokernel plus dual), so agreement cross-checks everything
//! downstream of the shared encoding. [`tau`] always runs both routes and
//! refuses to answer when [`crate::iso::is_isomorphic`] does not certify the
//! results isomorphic.

use std::fmt;

use crate::hom::{cokernel, kernel};
use crate::iso::{IsoOutcome, Obstruction, is_isomorphic};
use crate::module::Module;
use crate::opposite::{ElementMatrix, OppositeMap, dual, nu_of_presentation_map, opposite};
use crate::resolution::minimal_presentation_matrix;

/// The AR translate of a module.
#[derive(Clone, Debug)]
pub enum Tau {
    /// The module is projective (zero `P_1` in its minimal presentation).
    Zero,
    /// `τM` for non-projective `M`, as computed by the Nakayama-kernel route
    /// and certified isomorphic to the transpose-dual result.
    Module(Module),
}

/// A [`tau`] cross-check that did not end in agreement.
///
/// The two variants are different claims and must not be conflated.
/// [`TauError::RoutesDisagree`] carries a proof that the routes produced
/// non-isomorphic modules, which is a library bug.
/// [`TauError::AgreementUnknown`] means the isomorphism test could not decide.
/// It says nothing about whether the routes agree.
#[derive(Clone, Debug)]
pub enum TauError {
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
                "τ routes not certified equal: Nakayama kernel has dimension vector {:?}, \
                 transpose dual {:?} ({reason})",
                nakayama_kernel.dim_vector(),
                transpose_dual.dim_vector()
            ),
        }
    }
}

impl std::error::Error for TauError {}

/// Route 1: `τM = ker(ν(d1))` for the minimal presentation `P_1 -d1-> P_0`.
/// Zero exactly when `m` is projective.
pub fn tau_via_nakayama_kernel(m: &Module) -> Module {
    nakayama_kernel_route(&minimal_presentation_matrix(m))
}

fn nakayama_kernel_route(d1: &ElementMatrix) -> Module {
    kernel(&nu_of_presentation_map(d1)).0
}

/// Route 2: `τM = D(Tr M)` with `Tr M = coker(Hom_A(d1, A))`, the transposed
/// element matrix realized between opposite-side projectives. Zero exactly
/// when `m` is projective. The result lives over the same algebra [`std::sync::Arc`]
/// as `m`.
pub fn tau_via_transpose_dual(m: &Module) -> Module {
    transpose_dual_route(&minimal_presentation_matrix(m), &opposite(m.algebra()))
}

fn transpose_dual_route(d1: &ElementMatrix, op: &OppositeMap) -> Module {
    let transposed = d1
        .transpose_over(op)
        .expect("the presentation matrix lives over the algebra side of its own opposite pair");
    let (tr, _) = cokernel(&transposed.morphism());
    dual(&tr, op).expect("Tr M lives over the opposite side of the pair")
}

/// The AR translate: [`Tau::Zero`] exactly when `m` is projective (zero `P_1`
/// in the minimal presentation), otherwise [`Tau::Module`] with the
/// Nakayama-kernel result. The presentation is computed once and both routes
/// always run on it. A result is returned only when [`is_isomorphic`]
/// certifies the two results isomorphic. A certified disagreement is
/// [`TauError::RoutesDisagree`]. An undecided cross-check is
/// [`TauError::AgreementUnknown`], which is a limit of the isomorphism test
/// rather than evidence about the routes.
pub fn tau(m: &Module) -> Result<Tau, TauError> {
    let d1 = minimal_presentation_matrix(m);
    let nakayama_kernel = nakayama_kernel_route(&d1);
    let transpose_dual = transpose_dual_route(&d1, &opposite(m.algebra()));
    let outcome = is_isomorphic(&nakayama_kernel, &transpose_dual)
        .expect("both routes land over m's algebra Arc and field");
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
    if d1.sources().is_empty() {
        Ok(Tau::Zero)
    } else {
        Ok(Tau::Module(nakayama_kernel))
    }
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
            let a3 = linear_an(3);
            assert_eq!(
                tau_via_nakayama_kernel(&Module::simple(&a3, field, 0)).dim_vector(),
                &[0, 1, 0]
            );
            assert_eq!(
                tau_via_nakayama_kernel(&Module::simple(&a3, field, 1)).dim_vector(),
                &[0, 0, 1]
            );
            let kron = kronecker(2);
            assert_eq!(
                tau_via_nakayama_kernel(&Module::simple(&kron, field, 0)).dim_vector(),
                &[3, 2]
            );
        }
    }

    #[test]
    fn nakayama_kernel_route_is_zero_on_projectives() {
        for field in fields() {
            for algebra in [
                linear_an(3),
                dual_numbers(),
                cyclic_nakayama(&[3, 3, 3]).unwrap(),
            ] {
                for v in 0..algebra.quiver().num_vertices() {
                    let p = Module::projective(&algebra, field, v);
                    assert!(tau_via_nakayama_kernel(&p).is_zero(), "τ P_{v}");
                }
            }
        }
    }

    #[test]
    fn transpose_dual_route_lands_over_the_same_algebra_arc() {
        for field in fields() {
            let a3 = linear_an(3);
            let s0 = Module::simple(&a3, field, 0);
            let t = tau_via_transpose_dual(&s0);
            assert!(std::sync::Arc::ptr_eq(t.algebra(), &a3));
            assert_eq!(t.dim_vector(), &[0, 1, 0]);
        }
    }

    #[test]
    fn tau_is_zero_exactly_on_projectives() {
        for field in fields() {
            for algebra in [
                linear_an(3),
                dual_numbers(),
                cyclic_nakayama(&[3, 3, 3]).unwrap(),
            ] {
                for v in 0..algebra.quiver().num_vertices() {
                    let p = Module::projective(&algebra, field, v);
                    assert!(matches!(tau(&p).unwrap(), Tau::Zero), "τ P_{v}");
                    let s = Module::simple(&algebra, field, v);
                    if s.dim_vector() == p.dim_vector() {
                        continue;
                    }
                    match tau(&s).unwrap() {
                        Tau::Module(t) => assert!(!t.is_zero(), "τ S_{v}"),
                        Tau::Zero => panic!("τ S_{v} claimed projective"),
                    }
                }
            }
        }
    }

    #[test]
    fn tau_of_the_zero_module_is_zero() {
        let a = linear_an(3);
        let z = Module::zero(&a, PrimeField::new(5).unwrap());
        assert!(matches!(tau(&z).unwrap(), Tau::Zero));
    }

    #[test]
    fn both_routes_agree_on_every_simple_of_the_fixtures() {
        for field in fields() {
            for algebra in [
                linear_an(3),
                kronecker(2),
                dual_numbers(),
                cyclic_nakayama(&[3, 3, 3]).unwrap(),
            ] {
                for v in 0..algebra.quiver().num_vertices() {
                    let s = Module::simple(&algebra, field, v);
                    let left = tau_via_nakayama_kernel(&s);
                    let right = tau_via_transpose_dual(&s);
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

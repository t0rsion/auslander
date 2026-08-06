//! Modules certified indecomposable by a local endomorphism algebra.
//!
//! [`IndecomposableModule::new`] builds the [`EndoAlgebra`] of the module and
//! accepts exactly when the algebra is local. Locality is exact, so a value
//! of this type proves indecomposability. Rejections are typed: the zero
//! module, a verified split with its summand count, or an honest
//! [`IndecError::Undetermined`] after every splitting route failed.

use std::fmt;

use crate::algebra::AlgebraBuildError;
use crate::decompose::{Certificate, decompose};
use crate::endo::EndoAlgebra;
use crate::injective::injective_dimension;
use crate::module::Module;
use crate::resolution::{Bounded, projective_dimension};

/// Why a module failed the indecomposability gate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IndecError {
    /// The zero module is not indecomposable.
    Zero,
    /// The module splits into this many certified summands of a verified
    /// [`crate::decompose::Split`].
    Decomposable { summands: usize },
    /// The endomorphism algebra is not local, and no splitting route
    /// succeeded within this Fitting retry budget. The module may or may not
    /// be indecomposable.
    Undetermined { attempts: u32 },
}

impl fmt::Display for IndecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Zero => f.write_str("the zero module is not indecomposable"),
            Self::Decomposable { summands } => {
                write!(f, "the module splits into {summands} summands")
            }
            Self::Undetermined { attempts } => write!(
                f,
                "the endomorphism algebra is not local and {attempts} split attempts failed"
            ),
        }
    }
}

impl std::error::Error for IndecError {}

/// A module together with the locality proof of its endomorphism algebra.
///
/// Fields are private; construction goes through [`IndecomposableModule::new`],
/// so a value of this type exists only when [`EndoAlgebra::is_local`] holds
/// for the stored algebra, which proves the module indecomposable.
pub struct IndecomposableModule {
    module: Module,
    endo: EndoAlgebra,
}

impl fmt::Debug for IndecomposableModule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IndecomposableModule")
            .field("dim_vector", &self.module.dim_vector())
            .field("endo_dim", &self.endo.dim())
            .field("radical_dim", &self.endo.radical_dim())
            .finish()
    }
}

impl IndecomposableModule {
    /// Certifies `m` indecomposable: builds [`EndoAlgebra`] and requires
    /// [`EndoAlgebra::is_local`].
    ///
    /// The zero module is [`IndecError::Zero`]. When the algebra is not
    /// local, [`decompose`] runs: a verified split into two or more summands
    /// is [`IndecError::Decomposable`] with the summand count, and an
    /// exhausted split search is [`IndecError::Undetermined`] with the
    /// Fitting retry budget from [`Certificate::Undetermined`].
    pub fn new(m: &Module) -> Result<IndecomposableModule, IndecError> {
        if m.is_zero() {
            return Err(IndecError::Zero);
        }
        let endo = EndoAlgebra::new(m);
        if endo.is_local() {
            return Ok(IndecomposableModule {
                module: m.clone(),
                endo,
            });
        }
        let decomposition = decompose(m);
        let summands = decomposition.summands().len();
        if summands >= 2 {
            return Err(IndecError::Decomposable { summands });
        }
        let attempts = decomposition
            .certificates()
            .iter()
            .find_map(|c| match c {
                Certificate::Undetermined { attempts } => Some(*attempts),
                Certificate::Indecomposable => None,
            })
            .expect("a non-local unsplit module carries an Undetermined certificate");
        Err(IndecError::Undetermined { attempts })
    }

    /// The certified module.
    #[inline]
    pub fn module(&self) -> &Module {
        &self.module
    }

    /// The endomorphism algebra whose locality certifies the module.
    #[inline]
    pub fn endo(&self) -> &EndoAlgebra {
        &self.endo
    }

    /// The degree `d` of the residue field of the local endomorphism
    /// algebra: `endo.dim() - endo.radical_dim()`. The quotient by the
    /// radical is a finite division ring, so a field `F_{p^d}` by
    /// Wedderburn.
    pub fn residue_degree(&self) -> usize {
        self.endo.dim() - self.endo.radical_dim()
    }

    /// Whether the module is projective: its minimal resolution ends at the
    /// cover, `projective_dimension(m, 0) == Exact(0)`.
    pub fn is_projective(&self) -> bool {
        projective_dimension(&self.module, 0) == Bounded::Exact(0)
    }

    /// Whether the module is injective: its minimal coresolution ends at the
    /// envelope, `injective_dimension(m, 0) == Exact(0)`. Errors when
    /// building the opposite algebra fails, as [`injective_dimension`].
    pub fn is_injective(&self) -> Result<bool, AlgebraBuildError> {
        Ok(injective_dimension(&self.module, 0)? == Bounded::Exact(0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{commutative_square, dual_numbers, kronecker, linear_an};
    use crate::field::PrimeField;
    use crate::linalg::DenseMat;
    use crate::module::direct_sum;
    use std::sync::Arc;

    fn fields() -> [PrimeField; 2] {
        [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()]
    }

    fn fixtures(field: PrimeField) -> Vec<Arc<crate::algebra::Algebra>> {
        vec![
            linear_an(3, field),
            dual_numbers(field),
            commutative_square(field),
        ]
    }

    #[test]
    fn simples_are_accepted_with_residue_degree_1() {
        for field in fields() {
            for algebra in fixtures(field) {
                for v in 0..algebra.quiver().num_vertices() {
                    let s = Module::simple(&algebra, v);
                    let ind = IndecomposableModule::new(&s).unwrap();
                    assert!(ind.module().ptr_eq(&s));
                    assert!(ind.endo().is_local());
                    assert_eq!(ind.residue_degree(), 1, "S_{v} over F_{}", field.modulus());
                }
            }
        }
    }

    #[test]
    fn projectives_are_accepted_and_report_projectivity() {
        for field in fields() {
            for algebra in fixtures(field) {
                for v in 0..algebra.quiver().num_vertices() {
                    let p = Module::projective(&algebra, v);
                    let ind = IndecomposableModule::new(&p).unwrap();
                    assert!(ind.is_projective(), "P_{v} over F_{}", field.modulus());
                    assert_eq!(ind.residue_degree(), 1);
                }
            }
        }
    }

    #[test]
    fn the_zero_module_is_rejected() {
        let algebra = linear_an(3, PrimeField::new(5).unwrap());
        assert_eq!(
            IndecomposableModule::new(&Module::zero(&algebra)).unwrap_err(),
            IndecError::Zero
        );
    }

    #[test]
    fn direct_sums_are_rejected_with_the_summand_count() {
        for field in fields() {
            for algebra in fixtures(field) {
                let last = algebra.quiver().num_vertices() - 1;
                let p = Module::projective(&algebra, 0);
                let s = Module::simple(&algebra, last);
                let (pair, _, _) = direct_sum(&[&p, &s]);
                assert_eq!(
                    IndecomposableModule::new(&pair).unwrap_err(),
                    IndecError::Decomposable { summands: 2 },
                    "P_0 + S_{last} over F_{}",
                    field.modulus()
                );
                let (triple, _, _) = direct_sum(&[&p, &s, &p]);
                assert_eq!(
                    IndecomposableModule::new(&triple).unwrap_err(),
                    IndecError::Decomposable { summands: 3 },
                    "P_0 + S_{last} + P_0 over F_{}",
                    field.modulus()
                );
            }
        }
    }

    // Over linearly oriented A_3: P_0 has dimension vector (1, 1, 1) and
    // equals I_2, S_0 equals I_0, and S_1 is neither projective nor
    // injective.
    #[test]
    fn projectivity_and_injectivity_match_known_a3_facts() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let p0 = IndecomposableModule::new(&Module::projective(&algebra, 0)).unwrap();
            assert!(p0.is_projective());
            assert!(p0.is_injective().unwrap());
            let s0 = IndecomposableModule::new(&Module::simple(&algebra, 0)).unwrap();
            assert!(!s0.is_projective());
            assert!(s0.is_injective().unwrap());
            let s1 = IndecomposableModule::new(&Module::simple(&algebra, 1)).unwrap();
            assert!(!s1.is_projective());
            assert!(!s1.is_injective().unwrap());
            let s2 = IndecomposableModule::new(&Module::simple(&algebra, 2)).unwrap();
            assert!(s2.is_projective());
            assert!(!s2.is_injective().unwrap());
        }
    }

    // The construction of tests/decompose_iso.rs over F_2: the Kronecker
    // representation (I_3, C) for C the companion matrix of x^3 + x + 1,
    // irreducible over F_2, so End(W) is the field F_8.
    #[test]
    fn the_f8_endomorphism_kronecker_module_has_residue_degree_3() {
        let field = PrimeField::new(2).unwrap();
        let algebra = kronecker(2, field);
        let identity3 = DenseMat::identity(3);
        let mut companion = DenseMat::zero(3, 3);
        companion.set(0, 1, field.one());
        companion.set(1, 2, field.one());
        companion.set(2, 0, field.one());
        companion.set(2, 1, field.one());
        let w = Module::new(algebra, vec![3, 3], vec![identity3, companion]).unwrap();
        let ind = IndecomposableModule::new(&w).unwrap();
        assert_eq!(ind.endo().dim(), 3);
        assert_eq!(ind.endo().radical_dim(), 0);
        assert_eq!(ind.residue_degree(), 3);
        let (doubled, _, _) = direct_sum(&[&w, &w]);
        assert_eq!(
            IndecomposableModule::new(&doubled).unwrap_err(),
            IndecError::Decomposable { summands: 2 }
        );
    }
}

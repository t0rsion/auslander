//! Indecomposable enumeration for Nakayama algebras.
//!
//! An algebra here is Nakayama exactly when every vertex of its quiver has at
//! most one incoming and at most one outgoing arrow (linear or cyclic Kupisch
//! series). Its indecomposables are precisely the uniserial quotients
//! `P_i / rad^l P_i` for `1 ≤ l ≤ c_i`, where `c_i = dim_k P_i` is the Kupisch
//! entry. Their number is `Σ_i c_i = dim_k A`.

use std::fmt;
use std::sync::Arc;

use crate::algebra::Algebra;
use crate::decompose::{Certificate, decompose};
use crate::hom::cokernel;
use crate::module::Module;
use crate::radical::radical;

/// Rejected enumeration input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EnumerateError {
    /// A vertex with more than one incoming or outgoing arrow: the algebra is
    /// not Nakayama, so `P_i / rad^l P_i` does not exhaust its
    /// indecomposables.
    NotNakayama {
        vertex: u32,
        incoming: usize,
        outgoing: usize,
    },
}

impl fmt::Display for EnumerateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotNakayama {
                vertex,
                incoming,
                outgoing,
            } => write!(
                f,
                "vertex {vertex} has {incoming} incoming and {outgoing} outgoing arrows; \
                 a Nakayama quiver allows at most one of each"
            ),
        }
    }
}

impl std::error::Error for EnumerateError {}

/// Every indecomposable right module of a Nakayama algebra: `P_i / rad^l P_i`
/// for `1 ≤ l ≤ c_i`, ordered by vertex then by length `l`. Each quotient is
/// the cokernel of the composed inclusion `rad^l P_i ↪ P_i`. Each comes with the
/// certificate from [`decompose`], always [`Certificate::Indecomposable`]. The
/// exact local-endomorphism computation must certify a uniserial module, so any
/// other outcome is an upstream bug.
pub fn nakayama_indecomposables(
    algebra: &Arc<Algebra>,
) -> Result<Vec<(Module, Certificate)>, EnumerateError> {
    let quiver = algebra.quiver();
    for v in 0..quiver.num_vertices() {
        let incoming = quiver.arrows_to(v).len();
        let outgoing = quiver.arrows_from(v).len();
        if incoming > 1 || outgoing > 1 {
            return Err(EnumerateError::NotNakayama {
                vertex: v,
                incoming,
                outgoing,
            });
        }
    }
    let mut modules = Vec::with_capacity(algebra.dim());
    for v in 0..quiver.num_vertices() {
        let p = Module::projective(algebra, v);
        let (mut rad_power, mut inclusion) = radical(&p);
        loop {
            modules.push(certified(cokernel(&inclusion).0));
            if rad_power.is_zero() {
                break;
            }
            let (next, next_inclusion) = radical(&rad_power);
            inclusion = next_inclusion
                .then(&inclusion)
                .expect("radical inclusions chain into the projective");
            rad_power = next;
        }
    }
    Ok(modules)
}

fn certified(m: Module) -> (Module, Certificate) {
    let d = decompose(&m);
    assert_eq!(
        d.summands().len(),
        1,
        "uniserial quotient split into {} summands; library bug",
        d.summands().len()
    );
    assert_eq!(
        d.certificates(),
        [Certificate::Indecomposable],
        "uniserial quotient not certified indecomposable; library bug"
    );
    (m, Certificate::Indecomposable)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{
        cyclic_nakayama, dual_numbers, kronecker, linear_nakayama, radical_square_zero_cycle,
        truncated_poly,
    };
    use crate::field::PrimeField;

    fn fields() -> [PrimeField; 2] {
        [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()]
    }

    #[test]
    fn count_equals_the_sum_of_the_kupisch_series() {
        for field in fields() {
            for algebra in [
                linear_nakayama(&[3, 2, 1], field).unwrap(),
                linear_nakayama(&[2, 2, 1], field).unwrap(),
                cyclic_nakayama(&[3, 3, 3], field).unwrap(),
                radical_square_zero_cycle(3, field),
                dual_numbers(field),
                truncated_poly(4, field).unwrap(),
            ] {
                let modules = nakayama_indecomposables(&algebra).unwrap();
                assert_eq!(modules.len(), algebra.dim());
                assert!(
                    modules
                        .iter()
                        .all(|(_, c)| *c == Certificate::Indecomposable)
                );
            }
        }
    }

    #[test]
    fn linear_3_2_1_lists_the_six_uniserial_dimension_vectors() {
        for field in fields() {
            let algebra = linear_nakayama(&[3, 2, 1], field).unwrap();
            let dims: Vec<Vec<usize>> = nakayama_indecomposables(&algebra)
                .unwrap()
                .iter()
                .map(|(m, _)| m.dim_vector().to_vec())
                .collect();
            assert_eq!(
                dims,
                vec![
                    vec![1, 0, 0],
                    vec![1, 1, 0],
                    vec![1, 1, 1],
                    vec![0, 1, 0],
                    vec![0, 1, 1],
                    vec![0, 0, 1],
                ]
            );
        }
    }

    #[test]
    fn truncated_poly_lists_every_jordan_block_dimension() {
        for field in fields() {
            let algebra = truncated_poly(4, field).unwrap();
            let dims: Vec<usize> = nakayama_indecomposables(&algebra)
                .unwrap()
                .iter()
                .map(|(m, _)| m.total_dim())
                .collect();
            assert_eq!(dims, vec![1, 2, 3, 4]);
        }
    }

    #[test]
    fn a_vertex_with_two_outgoing_arrows_is_rejected() {
        let algebra = kronecker(2, PrimeField::new(5).unwrap());
        assert_eq!(
            nakayama_indecomposables(&algebra).unwrap_err(),
            EnumerateError::NotNakayama {
                vertex: 0,
                incoming: 0,
                outgoing: 2,
            }
        );
    }
}

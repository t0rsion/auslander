use std::sync::Arc;

use crate::completion::CompletionLimits;
use crate::field::PrimeField;
use crate::monomial::{
    MonomialIdeal, an_with_relations_ideal, cyclic_nakayama_ideal, kronecker_ideal,
    linear_an_ideal, linear_nakayama_ideal, radical_square_zero_cycle_ideal, truncated_poly_ideal,
};
use crate::quiver::{ArrowId, Quiver};
use crate::relation::{Presentation, Relation};

use super::types::{Algebra, AlgebraBuildError};

/// `ideal` as a [`Presentation`] over `field`: one monic one-term relation
/// per forbidden word, in the ideal's own order.
///
/// [`MonomialIdeal::new`] already checked that every forbidden word is a path
/// of length >= 2, which is what [`Relation::new`] asks for, so nothing here
/// can be rejected.
pub fn monomial_presentation(ideal: &MonomialIdeal, field: PrimeField) -> Presentation {
    let quiver = ideal.quiver().clone();
    let relations = ideal
        .forbidden()
        .iter()
        .map(|word| {
            Relation::new(&quiver, field, vec![(field.one(), word.clone())])
                .expect("a forbidden word is a path of length >= 2")
        })
        .collect();
    Presentation::new(quiver, field, relations).expect("the relations were built over this quiver")
}

/// Completion limits adequate for `ideal`: each entry is the default or a
/// bound derived from the forbidden words, whichever is larger.
///
/// `max_word_len` covers the longest self-overlap superposition, `2·L - 1`
/// for the longest forbidden word length `L`. `max_basis` covers the
/// forbidden words. `max_ambiguities` covers `2·L` keys for each ordered pair
/// of forbidden words. `max_origin_terms` keeps the default: a monomial
/// completion never combines provenance, because every composition reduces to
/// zero, so each origin keeps the one term its forbidden word started with.
///
/// `max_steps` keeps the default, and that is the one budget these limits do
/// not derive. Each emitted normal word costs one step, so a monomial algebra
/// of dimension above `max_steps` truncates.
pub fn monomial_limits(ideal: &MonomialIdeal) -> CompletionLimits {
    let defaults = CompletionLimits::default();
    let words = ideal.forbidden().len();
    let longest = ideal.forbidden().iter().map(Vec::len).max().unwrap_or(0);
    CompletionLimits {
        max_basis: defaults.max_basis.max(words),
        max_word_len: defaults
            .max_word_len
            .max(longest.saturating_mul(2).saturating_sub(1)),
        max_steps: defaults.max_steps,
        max_origin_terms: defaults.max_origin_terms,
        max_ambiguities: defaults.max_ambiguities.max(
            words
                .saturating_mul(words)
                .saturating_mul(longest.saturating_mul(2)),
        ),
    }
}

/// The runtime algebra of `ideal` over `field`, built with
/// [`monomial_limits`].
pub fn monomial_algebra(
    ideal: &MonomialIdeal,
    field: PrimeField,
) -> Result<Arc<Algebra>, AlgebraBuildError> {
    Algebra::new(monomial_presentation(ideal, field), &monomial_limits(ideal))
}

/// The path algebra `kQ` over `field`, with no relations.
///
/// Errors with [`AlgebraBuildError::InfiniteDimensional`] when `quiver` has a
/// cycle, since then `kQ` has infinitely many paths. The default completion
/// limits are adequate: with no relation there is no superposition word.
pub fn path_algebra(quiver: Quiver, field: PrimeField) -> Result<Arc<Algebra>, AlgebraBuildError> {
    let presentation =
        Presentation::new(quiver, field, Vec::new()).expect("there is no relation to reject");
    Algebra::new(presentation, &CompletionLimits::default())
}

/// Path algebra of linearly oriented `A_n` over `field`.
pub fn linear_an(n: usize, field: PrimeField) -> Arc<Algebra> {
    monomial_algebra(&linear_an_ideal(n), field)
        .expect("the zero ideal over an acyclic quiver completes")
}

/// Kronecker-type algebra over `field`: vertices `0, 1` and `m` parallel
/// arrows `0 → 1`. Hereditary; `dim = m + 2`.
pub fn kronecker(m: usize, field: PrimeField) -> Arc<Algebra> {
    monomial_algebra(&kronecker_ideal(m), field)
        .expect("the zero ideal over an acyclic quiver completes")
}

/// `k[x]/(x²)` over `field`: one vertex, one loop `x`, forbidden word `xx`.
pub fn dual_numbers(field: PrimeField) -> Arc<Algebra> {
    truncated_poly(2, field).expect("x² is an admissible relation")
}

/// `k[x]/(xⁿ)` over `field`, as [`crate::monomial::truncated_poly_ideal`].
pub fn truncated_poly(n: usize, field: PrimeField) -> Result<Arc<Algebra>, AlgebraBuildError> {
    let ideal = truncated_poly_ideal(n).map_err(AlgebraBuildError::Monomial)?;
    monomial_algebra(&ideal, field)
}

/// Linear Nakayama algebra over `field`, as
/// [`crate::monomial::linear_nakayama_ideal`].
pub fn linear_nakayama(
    kupisch: &[usize],
    field: PrimeField,
) -> Result<Arc<Algebra>, AlgebraBuildError> {
    let ideal = linear_nakayama_ideal(kupisch).map_err(AlgebraBuildError::Monomial)?;
    monomial_algebra(&ideal, field)
}

/// Cyclic Nakayama algebra over `field`, as
/// [`crate::monomial::cyclic_nakayama_ideal`].
pub fn cyclic_nakayama(
    kupisch: &[usize],
    field: PrimeField,
) -> Result<Arc<Algebra>, AlgebraBuildError> {
    let ideal = cyclic_nakayama_ideal(kupisch).map_err(AlgebraBuildError::Monomial)?;
    monomial_algebra(&ideal, field)
}

/// Cyclic quiver on `n` vertices with `rad² = 0` over `field`, as
/// [`crate::monomial::radical_square_zero_cycle_ideal`]. `dim = 2n`.
pub fn radical_square_zero_cycle(n: usize, field: PrimeField) -> Arc<Algebra> {
    monomial_algebra(&radical_square_zero_cycle_ideal(n), field)
        .expect("rad² = 0 leaves only vertices and arrows")
}

/// Linearly oriented `A_n` with zero relations over `field`, as
/// [`crate::monomial::an_with_relations_ideal`].
pub fn an_with_relations(
    n: usize,
    zero_paths: &[(usize, usize)],
    field: PrimeField,
) -> Result<Arc<Algebra>, AlgebraBuildError> {
    let ideal = an_with_relations_ideal(n, zero_paths).map_err(AlgebraBuildError::Monomial)?;
    monomial_algebra(&ideal, field)
}

/// The commutative square over `field`: vertices `0..4`, arrows `a: 0 → 1`,
/// `b: 1 → 3`, `c: 0 → 2`, `d: 2 → 3`, and the relation `ab - cd`.
/// `dim = 9`; the two length-2 paths share one basis class.
pub fn commutative_square(field: PrimeField) -> Arc<Algebra> {
    let quiver = Quiver::new(4, &[(0, 1), (1, 3), (0, 2), (2, 3)]).expect("endpoints in range");
    let relation = Relation::new(
        &quiver,
        field,
        vec![
            (field.one(), vec![ArrowId(0), ArrowId(1)]),
            (field.elem(-1), vec![ArrowId(2), ArrowId(3)]),
        ],
    )
    .expect("ab - cd is a valid uniform relation");
    let presentation = Presentation::new(quiver, field, vec![relation])
        .expect("the relation was built over this quiver and field");
    // The one relation has length 2, so completion needs word length 3 at
    // most. The defaults cover that.
    Algebra::new(presentation, &CompletionLimits::default())
        .expect("the commutative square is finite dimensional")
}

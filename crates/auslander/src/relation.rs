//! Uniform relations and presentations for bound quiver algebras kQ/I.
//!
//! A relation is a k-linear combination of parallel paths: every word has the
//! same source and the same target. Non-uniform input is rejected, not
//! decomposed. Terms are stored in strictly descending order under the sealed
//! order of [`crate::order`], so the leading term is always `terms[0]`.

use std::fmt;

use crate::field::{Fp, PrimeField};
use crate::order::word_cmp;
use crate::quiver::{ArrowId, PathWord, Quiver, QuiverError};

/// Rejected relation input. Where a variant carries `index`, it is the
/// position of the offending term: in the list passed to [`Relation::new`],
/// or in the stored terms of the relation that [`Presentation::new`]
/// rejected.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RelationError {
    /// A relation needs at least one term.
    Empty,
    /// The relation was built over a field with modulus `found`, and the
    /// presentation has modulus `expected`. Coefficients are canonical
    /// representatives, so the same raw value means different elements in
    /// the two fields.
    FieldMismatch { expected: u64, found: u64 },
    /// Term `index` has coefficient zero.
    ZeroCoefficient { index: usize },
    /// Term `index` has a coefficient outside `0..p`, so it comes from a
    /// field with a larger modulus.
    NonCanonicalCoefficient { index: usize },
    /// Term `index` repeats the word of an earlier term.
    DuplicateWord { index: usize },
    /// The word of term `index` is not a path in the quiver.
    InvalidWord { index: usize, error: QuiverError },
    /// The word of term `index` has length < 2. Admissibility needs `I ⊆ J²`.
    WordTooShort { index: usize, len: usize },
    /// The word of term `index` starts at a different vertex than the word of
    /// term 0.
    MixedSource { index: usize },
    /// The word of term `index` ends at a different vertex than the word of
    /// term 0.
    MixedTarget { index: usize },
}

impl fmt::Display for RelationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => f.write_str("relation needs at least one term"),
            Self::FieldMismatch { expected, found } => write!(
                f,
                "relation is over the field with modulus {found}, the presentation over {expected}"
            ),
            Self::ZeroCoefficient { index } => {
                write!(f, "term {index} has coefficient zero")
            }
            Self::NonCanonicalCoefficient { index } => write!(
                f,
                "term {index} has a coefficient outside 0..p; its field has a larger modulus"
            ),
            Self::DuplicateWord { index } => {
                write!(f, "term {index} repeats the word of an earlier term")
            }
            Self::InvalidWord { index, error } => {
                write!(f, "term {index} is not a path: {error}")
            }
            Self::WordTooShort { index, len } => write!(
                f,
                "term {index} has length {len}; admissibility needs length >= 2"
            ),
            Self::MixedSource { index } => {
                write!(f, "term {index} starts at a different vertex than term 0")
            }
            Self::MixedTarget { index } => {
                write!(f, "term {index} ends at a different vertex than term 0")
            }
        }
    }
}

impl std::error::Error for RelationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::InvalidWord { error, .. } => Some(error),
            _ => None,
        }
    }
}

/// A uniform relation: a nonzero k-combination of distinct parallel paths of
/// length >= 2.
///
/// Terms are in strictly descending order under [`crate::order::word_cmp`];
/// coefficients are nonzero and canonical for [`Relation::field`], the field
/// the relation was built over. The relation carries that field so a later
/// [`Presentation`] cannot reinterpret the coefficients over another one.
///
/// Length >= 2 gives `I ⊆ J²`, one half of admissibility. The other half,
/// nilpotence of `J`, depends on the whole ideal and is decided when
/// [`crate::algebra::Algebra`] is built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Relation {
    field: PrimeField,
    terms: Vec<(Fp, PathWord)>,
}

impl Relation {
    /// Validates `terms` and sorts them into a relation over `quiver` and
    /// `field`.
    ///
    /// Rejects an empty term list, zero or non-canonical coefficients,
    /// duplicate words, non-path words, words of length < 2, and mixed
    /// sources or targets. Sorts the terms in strictly descending order.
    /// Coefficients are kept as given: nothing here scales the relation to a
    /// monic leading term.
    pub fn new(
        quiver: &Quiver,
        field: PrimeField,
        terms: Vec<(Fp, Vec<ArrowId>)>,
    ) -> Result<Relation, RelationError> {
        if terms.is_empty() {
            return Err(RelationError::Empty);
        }
        let mut checked: Vec<(Fp, PathWord)> = Vec::with_capacity(terms.len());
        let mut seen = std::collections::BTreeSet::new();
        for (index, (coeff, arrows)) in terms.into_iter().enumerate() {
            if coeff.is_zero() {
                return Err(RelationError::ZeroCoefficient { index });
            }
            if coeff.raw() >= field.modulus() {
                return Err(RelationError::NonCanonicalCoefficient { index });
            }
            if arrows.len() < 2 {
                return Err(RelationError::WordTooShort {
                    index,
                    len: arrows.len(),
                });
            }
            let word = PathWord::from_arrows(quiver, &arrows)
                .map_err(|error| RelationError::InvalidWord { index, error })?;
            if let Some((_, first)) = checked.first() {
                if word.source() != first.source() {
                    return Err(RelationError::MixedSource { index });
                }
                if word.target() != first.target() {
                    return Err(RelationError::MixedTarget { index });
                }
            }
            if !seen.insert(arrows) {
                return Err(RelationError::DuplicateWord { index });
            }
            checked.push((coeff, word));
        }
        checked.sort_by(|(_, a), (_, b)| word_cmp(b.arrows(), a.arrows()));
        Ok(Relation {
            field,
            terms: checked,
        })
    }

    /// The field the relation was built over. Its coefficients are canonical
    /// representatives for this field and mean something else in any other.
    #[inline]
    pub fn field(&self) -> PrimeField {
        self.field
    }

    /// Terms in strictly descending order under the sealed order.
    #[inline]
    pub fn terms(&self) -> &[(Fp, PathWord)] {
        &self.terms
    }

    /// The term with the largest word, `terms[0]`.
    #[inline]
    pub fn leading(&self) -> (&Fp, &PathWord) {
        let (coeff, word) = &self.terms[0];
        (coeff, word)
    }

    /// The common source vertex of all words.
    #[inline]
    pub fn source(&self) -> u32 {
        self.terms[0].1.source()
    }

    /// The common target vertex of all words.
    #[inline]
    pub fn target(&self) -> u32 {
        self.terms[0].1.target()
    }
}

/// A bound quiver algebra presentation: a quiver, a prime field, and a list
/// of uniform relations over both.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Presentation {
    quiver: Quiver,
    field: PrimeField,
    relations: Vec<Relation>,
}

impl Presentation {
    /// Bundles relations with the quiver and field they were built over.
    ///
    /// Each relation must already be a [`Relation`] over this quiver and
    /// field. Two things are checked: [`Relation::field`] must equal `field`,
    /// and every word must be a path of `quiver`. Coefficients, uniformity,
    /// word length, and term order are not rechecked; [`Relation::new`]
    /// established them over the field the relation carries, and that is now
    /// this field. A rejected word names its term index inside the offending
    /// relation, never which relation failed.
    pub fn new(
        quiver: Quiver,
        field: PrimeField,
        relations: Vec<Relation>,
    ) -> Result<Presentation, RelationError> {
        for relation in &relations {
            if relation.field != field {
                return Err(RelationError::FieldMismatch {
                    expected: field.modulus(),
                    found: relation.field.modulus(),
                });
            }
            for (index, (_, word)) in relation.terms.iter().enumerate() {
                word.validate_in(&quiver)
                    .map_err(|error| RelationError::InvalidWord { index, error })?;
            }
        }
        Ok(Presentation {
            quiver,
            field,
            relations,
        })
    }

    #[inline]
    pub fn quiver(&self) -> &Quiver {
        &self.quiver
    }

    #[inline]
    pub fn field(&self) -> PrimeField {
        self.field
    }

    #[inline]
    pub fn relations(&self) -> &[Relation] {
        &self.relations
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn commutative_square() -> Quiver {
        Quiver::new(4, &[(0, 1), (1, 3), (0, 2), (2, 3)]).unwrap()
    }

    fn f5() -> PrimeField {
        PrimeField::new(5).unwrap()
    }

    fn ids(raw: &[u32]) -> Vec<ArrowId> {
        raw.iter().copied().map(ArrowId).collect()
    }

    #[test]
    fn terms_sort_strictly_descending() {
        let q = commutative_square();
        let f = f5();
        let r = Relation::new(
            &q,
            f,
            vec![(f.elem(1), ids(&[0, 1])), (f.elem(-1), ids(&[2, 3]))],
        )
        .unwrap();
        assert_eq!(r.terms().len(), 2);
        assert_eq!(r.terms()[0].1.arrows(), ids(&[2, 3]).as_slice());
        assert_eq!(r.terms()[1].1.arrows(), ids(&[0, 1]).as_slice());
        let (lead_coeff, lead_word) = r.leading();
        assert_eq!(*lead_coeff, f.elem(-1));
        assert_eq!(lead_word.arrows(), ids(&[2, 3]).as_slice());
        assert_eq!((r.source(), r.target()), (0, 3));
    }

    #[test]
    fn empty_relation_rejected() {
        assert_eq!(
            Relation::new(&commutative_square(), f5(), Vec::new()),
            Err(RelationError::Empty)
        );
    }

    #[test]
    fn zero_coefficient_rejected() {
        let q = commutative_square();
        let f = f5();
        assert_eq!(
            Relation::new(
                &q,
                f,
                vec![(f.elem(1), ids(&[0, 1])), (f.zero(), ids(&[2, 3]))]
            ),
            Err(RelationError::ZeroCoefficient { index: 1 })
        );
    }

    #[test]
    fn non_canonical_coefficient_rejected() {
        let q = commutative_square();
        let foreign = PrimeField::new(7).unwrap().elem(6);
        assert_eq!(
            Relation::new(&q, f5(), vec![(foreign, ids(&[0, 1]))]),
            Err(RelationError::NonCanonicalCoefficient { index: 0 })
        );
    }

    #[test]
    fn duplicate_word_rejected() {
        let q = commutative_square();
        let f = f5();
        assert_eq!(
            Relation::new(
                &q,
                f,
                vec![(f.elem(1), ids(&[0, 1])), (f.elem(2), ids(&[0, 1]))]
            ),
            Err(RelationError::DuplicateWord { index: 1 })
        );
    }

    #[test]
    fn non_composable_word_rejected() {
        let q = commutative_square();
        let f = f5();
        assert_eq!(
            Relation::new(&q, f, vec![(f.elem(1), ids(&[0, 3]))]),
            Err(RelationError::InvalidWord {
                index: 0,
                error: QuiverError::NotComposable { position: 0 },
            })
        );
    }

    #[test]
    fn short_words_rejected() {
        let q = commutative_square();
        let f = f5();
        assert_eq!(
            Relation::new(&q, f, vec![(f.elem(1), ids(&[0]))]),
            Err(RelationError::WordTooShort { index: 0, len: 1 })
        );
        assert_eq!(
            Relation::new(&q, f, vec![(f.elem(1), Vec::new())]),
            Err(RelationError::WordTooShort { index: 0, len: 0 })
        );
    }

    #[test]
    fn mixed_source_rejected() {
        let q = Quiver::new(4, &[(0, 1), (1, 3), (2, 1), (1, 3)]).unwrap();
        let f = f5();
        assert_eq!(
            Relation::new(
                &q,
                f,
                vec![(f.elem(1), ids(&[0, 1])), (f.elem(1), ids(&[2, 3]))]
            ),
            Err(RelationError::MixedSource { index: 1 })
        );
    }

    #[test]
    fn mixed_target_rejected() {
        let q = Quiver::new(4, &[(0, 1), (1, 3), (0, 1), (1, 2)]).unwrap();
        let f = f5();
        assert_eq!(
            Relation::new(
                &q,
                f,
                vec![(f.elem(1), ids(&[0, 1])), (f.elem(1), ids(&[2, 3]))]
            ),
            Err(RelationError::MixedTarget { index: 1 })
        );
    }

    #[test]
    fn presentation_accepts_its_own_relations() {
        let q = commutative_square();
        let f = f5();
        let r = Relation::new(
            &q,
            f,
            vec![(f.elem(1), ids(&[0, 1])), (f.elem(-1), ids(&[2, 3]))],
        )
        .unwrap();
        let p = Presentation::new(q.clone(), f, vec![r.clone()]).unwrap();
        assert_eq!(p.quiver(), &q);
        assert_eq!(p.field(), f);
        assert_eq!(p.relations(), &[r]);
    }

    #[test]
    fn presentation_rejects_relations_over_another_quiver() {
        let f = f5();
        let other = Quiver::new(3, &[(0, 1), (1, 2)]).unwrap();
        let r = Relation::new(&other, f, vec![(f.elem(1), ids(&[0, 1]))]).unwrap();
        assert!(matches!(
            Presentation::new(commutative_square(), f, vec![r]),
            Err(RelationError::InvalidWord { index: 0, .. })
        ));
    }

    #[test]
    fn presentation_rejects_relations_over_another_field() {
        let q = commutative_square();
        let f7 = PrimeField::new(7).unwrap();
        let r = Relation::new(&q, f7, vec![(f7.elem(6), ids(&[0, 1]))]).unwrap();
        assert_eq!(
            Presentation::new(q, f5(), vec![r]),
            Err(RelationError::FieldMismatch {
                expected: 5,
                found: 7,
            })
        );
    }

    /// Over F_5 the coefficient -1 is the raw value 4, which is canonical for
    /// F_7 too and means +4 there. Only the stored field separates the two.
    #[test]
    fn presentation_rejects_a_relation_whose_coefficient_fits_the_other_field() {
        let q = commutative_square();
        let f5 = f5();
        let r = Relation::new(&q, f5, vec![(f5.elem(-1), ids(&[0, 1]))]).unwrap();
        assert_eq!(r.terms()[0].0, f5.elem(4));
        assert_eq!(r.field(), f5);
        assert_eq!(
            Presentation::new(q, PrimeField::new(7).unwrap(), vec![r]),
            Err(RelationError::FieldMismatch {
                expected: 7,
                found: 5,
            })
        );
    }
}

use std::sync::Arc;

use crate::algebra::{Algebra, AlgebraBuildError};
use crate::profile::{Site, hit};
use crate::quiver::{ArrowId, Quiver};
use crate::relation::{Presentation, Relation};

use super::types::OppositeMap;

/// The opposite algebra of `algebra` with its arrow/word correspondence: same
/// vertices, arrows reversed keeping their ids, every relation word reversed.
/// The reversed relations run through the full completion and verification
/// pipeline, with the completion limits stored on `algebra`. Reversal bijects
/// paths, so the opposite has the same dimension. An error is a budget or
/// engine failure, not an infinite dimension.
///
/// ```
/// use auslander::algebra::an_with_relations;
/// use auslander::field::PrimeField;
/// use auslander::opposite::opposite;
/// let field = PrimeField::new(5).unwrap();
/// let a = an_with_relations(3, &[(0, 2)], field).unwrap();
/// let op = opposite(&a).unwrap();
/// assert_eq!(op.opposite().dim(), a.dim());
/// ```
pub fn opposite(algebra: &Arc<Algebra>) -> Result<OppositeMap, AlgebraBuildError> {
    hit(Site::Opposite);
    let quiver = algebra.quiver();
    let field = algebra.field();
    let arrows: Vec<(u32, u32)> = quiver.arrows().iter().map(|&(s, t)| (t, s)).collect();
    let reversed_quiver = Quiver::new(quiver.num_vertices(), &arrows)
        .expect("reversing endpoints keeps them in range");
    let relations = algebra
        .relations()
        .iter()
        .map(|relation| {
            let terms = relation
                .terms()
                .iter()
                .map(|(coeff, word)| {
                    let reversed: Vec<ArrowId> = word.arrows().iter().rev().copied().collect();
                    (*coeff, reversed)
                })
                .collect();
            Relation::new(&reversed_quiver, field, terms)
        })
        .collect::<Result<Vec<Relation>, _>>()
        .map_err(AlgebraBuildError::Relation)?;
    let presentation = Presentation::new(reversed_quiver, field, relations)
        .map_err(AlgebraBuildError::Relation)?;
    let opposite = Algebra::new(presentation, algebra.completion_limits())?;
    Ok(OppositeMap {
        algebra: algebra.clone(),
        opposite,
    })
}

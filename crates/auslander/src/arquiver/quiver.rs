use std::sync::Arc;

use crate::algebra::Algebra;
use crate::field::unit_vector;
use crate::hom::Morphism;
use crate::homspace::{HomQuotient, HomSubspace};
use crate::indec::IndecomposableModule;
use crate::module::Module;

use super::radical::{category_radical, quotient_or_defect, span_of_composites};
use super::{ArQuiverError, CatalogError, IndecomposableCatalog};

/// One vertex of an [`ArQuiver`]: a certified indecomposable with the data
/// the AR quiver labels it by.
#[derive(Debug)]
pub struct ArVertex {
    id: usize,
    // The catalog entry itself, shared with the catalog.
    module: Arc<IndecomposableModule>,
    residue_degree: usize,
    projective: bool,
    injective: bool,
}

impl ArVertex {
    accessor_methods! {
        /// The identifier of the vertex: its index in the catalog and in
        /// [`ArQuiver::vertices`].
        pub id() -> usize = |this| this.id;
        /// The module at the vertex.
        pub module() -> &IndecomposableModule = |this| &this.module;
        /// The residue degree `d` of the module: the residue field of its local
        /// endomorphism algebra is `F_{p^d}`.
        pub residue_degree() -> usize = |this| this.residue_degree;
        /// Whether the module is projective.
        pub projective() -> bool = |this| this.projective;
        /// Whether the module is injective.
        pub injective() -> bool = |this| this.injective;
    }
}

/// The valuation of an [`ArArrow`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ArrowValuation {
    /// Both endpoints have residue degree 1, so `dim_Fp Irr(X, Y)` is the whole
    /// valuation.
    Plain(usize),
    /// At least one endpoint has residue degree above 1, so the dimension of
    /// `Irr(X, Y)` over that residue field is smaller than its dimension over
    /// the prime field, and both numbers are needed.
    Valued {
        /// `dim_Fp Irr(X, Y)`.
        base_dim: usize,
        /// The dimension of `Irr(X, Y)` over the residue field of the source.
        over_source: usize,
        /// The dimension of `Irr(X, Y)` over the residue field of the target.
        over_target: usize,
    },
}

/// One arrow of an [`ArQuiver`]: a pair of vertices with a nonzero
/// `Irr(X, Y)`, its dimensions, and representatives of its classes.
#[derive(Debug)]
pub struct ArArrow {
    pub(super) source: usize,
    pub(super) target: usize,
    pub(super) base_dim: usize,
    pub(super) over_source_residue: usize,
    pub(super) over_target_residue: usize,
    pub(super) representatives: Vec<Morphism>,
}

impl ArArrow {
    accessor_methods! {
        /// The identifier of the source vertex.
        pub source() -> usize = |this| this.source;
        /// The identifier of the target vertex.
        pub target() -> usize = |this| this.target;
        /// `dim_Fp Irr(X, Y)`, always positive.
        pub base_dim() -> usize = |this| this.base_dim;
        /// The dimension of `Irr(X, Y)` over the residue field of the source.
        pub over_source_residue() -> usize = |this| this.over_source_residue;
        /// The dimension of `Irr(X, Y)` over the residue field of the target.
        pub over_target_residue() -> usize = |this| this.over_target_residue;
        /// One irreducible map per complement basis row of `Irr(X, Y)`, in the
        /// order of that basis.
        pub representatives() -> &[Morphism] = |this| &this.representatives;
    }

    /// The valuation: [`ArrowValuation::Plain`] when both endpoints have
    /// residue degree 1, and [`ArrowValuation::Valued`] otherwise. The test is
    /// on the stored quotients, which equal the base dimension exactly when the
    /// matching residue degree is 1.
    pub fn valuation(&self) -> ArrowValuation {
        if self.base_dim == self.over_source_residue && self.base_dim == self.over_target_residue {
            ArrowValuation::Plain(self.base_dim)
        } else {
            ArrowValuation::Valued {
                base_dim: self.base_dim,
                over_source: self.over_source_residue,
                over_target: self.over_target_residue,
            }
        }
    }
}

/// The valued Auslander-Reiten quiver of one algebra: every indecomposable as
/// a vertex, every nonzero `Irr(X, Y)` as an arrow.
///
/// The quiver is complete for its domain. The catalog behind it is a complete
/// enumeration, and no work budget cuts the pair loop off, so there is no
/// partial AR quiver.
#[derive(Debug)]
pub struct ArQuiver {
    catalog: IndecomposableCatalog,
    vertices: Vec<ArVertex>,
    arrows: Vec<ArArrow>,
}

impl ArQuiver {
    accessor_methods! {
        /// The catalog the vertices come from. Vertex `i` carries the same module
        /// as catalog entry `i`.
        pub catalog() -> &IndecomposableCatalog = |this| &this.catalog;
        /// The vertices in catalog order.
        pub vertices() -> &[ArVertex] = |this| &this.vertices;
        /// The arrows, ordered by source identifier then target identifier.
        pub arrows() -> &[ArArrow] = |this| &this.arrows;
    }
}

/// `base_dim / residue_degree`: the dimension of a space of prime-field
/// dimension `base_dim` over a residue field of degree `residue_degree`.
/// `module` names the module whose residue degree this is, for the error.
///
/// # Errors
/// [`ArQuiverError::ResidueDegreeDoesNotDivide`] when the division leaves a
/// remainder or the degree is 0, which is a crate defect.
pub(crate) fn over_residue(
    base_dim: usize,
    residue_degree: usize,
    module: &Module,
) -> Result<usize, ArQuiverError> {
    if residue_degree == 0 || !base_dim.is_multiple_of(residue_degree) {
        return Err(ArQuiverError::ResidueDegreeDoesNotDivide {
            dim_vector: module.dim_vector().to_vec(),
            base_dim,
            residue_degree,
        });
    }
    Ok(base_dim / residue_degree)
}

fn vertices_of(catalog: &IndecomposableCatalog) -> Result<Vec<ArVertex>, ArQuiverError> {
    let mut vertices = Vec::with_capacity(catalog.len());
    for (id, entry) in catalog.entries().iter().enumerate() {
        vertices.push(ArVertex {
            id,
            residue_degree: entry.residue_degree(),
            projective: entry.is_projective(),
            injective: entry.is_injective().map_err(ArQuiverError::Injective)?,
            module: entry.clone(),
        })
    }
    Ok(vertices)
}

fn radicals_of(catalog: &IndecomposableCatalog) -> Result<Vec<HomSubspace>, ArQuiverError> {
    let n = catalog.len();
    let mut radicals = Vec::with_capacity(n * n);
    for x in catalog.entries() {
        for y in catalog.entries() {
            radicals.push(category_radical(x, y)?);
        }
    }
    Ok(radicals)
}

fn quotient_for_pair(
    catalog: &IndecomposableCatalog,
    radicals: &[HomSubspace],
    source: usize,
    target: usize,
) -> Result<Option<HomQuotient>, ArQuiverError> {
    let n = catalog.len();
    let (x, y) = (
        catalog.entries()[source].module(),
        catalog.entries()[target].module(),
    );
    let square = span_of_composites(
        x,
        y,
        (0..n).map(|k| (&radicals[source * n + k], &radicals[k * n + target])),
    )?;
    let quotient = quotient_or_defect(&radicals[source * n + target], &square)?;
    if quotient.dim() == 0 {
        return Ok(None);
    }
    Ok(Some(quotient))
}

fn arrow_for_pair(
    catalog: &IndecomposableCatalog,
    vertices: &[ArVertex],
    radicals: &[HomSubspace],
    source: usize,
    target: usize,
) -> Result<Option<ArArrow>, ArQuiverError> {
    let Some(quotient) = quotient_for_pair(catalog, radicals, source, target)? else {
        return Ok(None);
    };
    let base_dim = quotient.dim();
    let (x, y) = (
        catalog.entries()[source].module(),
        catalog.entries()[target].module(),
    );
    Ok(Some(ArArrow {
        source,
        target,
        base_dim,
        over_source_residue: over_residue(base_dim, vertices[source].residue_degree, x)?,
        over_target_residue: over_residue(base_dim, vertices[target].residue_degree, y)?,
        representatives: (0..base_dim)
            .map(|index| quotient.representative(&unit_vector(base_dim, index)))
            .collect(),
    }))
}

fn arrows_of_catalog(
    catalog: &IndecomposableCatalog,
    vertices: &[ArVertex],
    radicals: &[HomSubspace],
) -> Result<Vec<ArArrow>, ArQuiverError> {
    let mut arrows = Vec::new();
    for source in 0..catalog.len() {
        for target in 0..catalog.len() {
            if let Some(arrow) = arrow_for_pair(catalog, vertices, radicals, source, target)? {
                arrows.push(arrow);
            }
        }
    }
    Ok(arrows)
}

fn quiver_of(catalog: IndecomposableCatalog) -> Result<ArQuiver, ArQuiverError> {
    let vertices = vertices_of(&catalog)?;
    let radicals = radicals_of(&catalog)?;
    let arrows = arrows_of_catalog(&catalog, &vertices, &radicals)?;
    Ok(ArQuiver {
        catalog,
        vertices,
        arrows,
    })
}

/// The valued AR quiver of `algebra`.
///
/// The dispatch is deterministic: Dynkin, Nakayama, then gentle tree.
///
/// # Errors
/// [`ArQuiverError::UnsupportedDomain`], carrying all route rejections, when
/// no complete enumeration applies. [`ArQuiverError::Injective`] when the
/// opposite algebra needed for the injectivity flags fails to build.
pub fn ar_quiver(algebra: &Arc<Algebra>) -> Result<ArQuiver, ArQuiverError> {
    let catalog = IndecomposableCatalog::complete(algebra).map_err(catalog_error)?;
    quiver_of(catalog)
}

/// Builds the valued AR quiver from an existing complete catalog.
///
/// The catalog is cloned, so the caller keeps ownership and classification is
/// not run again. The quiver still computes all radicals and irreducible
/// quotients from the certified entries.
pub fn ar_quiver_from_catalog(catalog: &IndecomposableCatalog) -> Result<ArQuiver, ArQuiverError> {
    quiver_of(catalog.clone())
}

fn catalog_error(error: CatalogError) -> ArQuiverError {
    match error {
        CatalogError::UnsupportedDomain {
            dynkin,
            nakayama,
            gentle,
        } => ArQuiverError::UnsupportedDomain {
            dynkin,
            nakayama,
            gentle,
        },
    }
}

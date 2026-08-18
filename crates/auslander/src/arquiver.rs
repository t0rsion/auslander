//! The category radical of certified indecomposables, exhaustive
//! indecomposable catalogs, and the valued Auslander-Reiten quiver.
//!
//! For certified indecomposables `X` and `Y`, the radical of the module
//! category is exact and needs no catalog. Two cases:
//!
//! - `X` and `Y` are not isomorphic. Then no map `X -> Y` is invertible, so
//!   `rad(X, Y) = Hom(X, Y)`.
//! - `X` and `Y` are isomorphic. Fix one isomorphism `u: Y -> X`. Then
//!   `rad(X, Y) = { f : f.then(u) in rad End(X) }`. The condition is linear
//!   in `f`, so the result is a [`HomSubspace`]. The subspace does not depend
//!   on the choice of `u`: a second isomorphism is `u.then(a)` for an
//!   automorphism `a` of `X`, and `rad End(X)` is a two-sided ideal, so
//!   `f.then(u).then(a)` lies in the radical exactly when `f.then(u)` does.
//!
//! The square of the radical needs a catalog. Through a list `C` of
//! indecomposables,
//!
//! ```text
//! rad2(X, Y) = sum over Z in C of span{ f.then(g) :
//!     f in basis rad(X, Z), g in basis rad(Z, Y) }
//! ```
//!
//! The composite `f.then(g)` is first `f`, then `g`, the crate-wide
//! left-to-right order. The sum runs over `C` in catalog order; it is a span,
//! so the order does not change it.
//!
//! Lemma: when `C` is exhaustive, this is the true `rad^2(X, Y)`. Any element
//! of `rad^2(X, Y)` factors as `X -> M -> Y` through some module `M` with both
//! legs in the radical. Krull-Schmidt splits `M` into indecomposables, each
//! isomorphic to a catalog member, and the radical is an ideal, so every
//! component of the factorization stays a radical map. With less than an
//! exhaustive catalog the same sum is only a subspace of `rad^2`. The API
//! keeps the two apart by construction: [`radical_square_through_catalog`]
//! and everything built on it take an [`IndecomposableCatalog`], and a
//! catalog is built only from a complete enumeration.
//!
//! `Irr(X, Y) = rad(X, Y) / rad^2(X, Y)` is [`irreducible_quotient`]. Its
//! nonzero elements are the classes of the irreducible maps `X -> Y`. Its
//! dimension is the base dimension of the arrow `X -> Y` of the AR quiver,
//! and the arrow exists exactly when that dimension is positive.
//!
//! `Irr(X, Y)` is a vector space over the residue field of `End(X)` and over
//! the residue field of `End(Y)`, so both residue degrees divide the base
//! dimension, and [`ArArrow`] stores the two quotients. When both residue
//! degrees are 1 the three numbers agree, the base dimension says everything
//! about the arrow, and [`ArArrow::valuation`] reports
//! [`ArrowValuation::Plain`]. When a residue degree `d` exceeds 1, the base
//! dimension counts `d` prime-field dimensions per dimension over that residue
//! field, so no single integer is the multiplicity of the arrow. In that case
//! `valuation` reports [`ArrowValuation::Valued`] with all three numbers. The
//! crate offers no bare multiplicity accessor, so no caller can read one
//! number where two are needed.

use std::fmt;
use std::sync::Arc;

use crate::algebra::{Algebra, AlgebraBuildError};
use crate::decompose::{Certificate, matrix_inverse};
use crate::dynkin::{DynkinError, dynkin_indecomposables};
use crate::endo::EndoAlgebra;
use crate::enumerate::{EnumerateError, nakayama_indecomposables};
use crate::field::{Fp, PrimeField};
use crate::hom::{HomError, Morphism};
use crate::homspace::{HomQuotient, HomSpace, HomSpaceError, HomSubspace};
use crate::indec::IndecomposableModule;
use crate::iso::indecomposable_iso;
use crate::linalg::DenseMat;
use crate::module::Module;

/// Rejected input, or a failed internal cross-check, of the AR-quiver layer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArQuiverError {
    /// Two modules do not share one algebra, or a composite was formed from
    /// mismatched endpoints.
    Hom(HomError),
    /// A morphism or subspace did not match the endpoints of its Hom space.
    Space(HomSpaceError),
    /// Deciding injectivity needs the opposite algebra, and building it
    /// failed.
    Injective(AlgebraBuildError),
    /// The algebra is neither a path algebra of Dynkin type nor a Nakayama
    /// algebra, so no complete enumeration of its indecomposables exists in
    /// this release. Both rejections are carried.
    UnsupportedDomain {
        /// Why the Dynkin route rejected the algebra.
        dynkin: DynkinError,
        /// Why the Nakayama route rejected the algebra.
        nakayama: EnumerateError,
    },
    /// `rad^2(X, Y)` came out with a member outside `rad(X, Y)`. The radical
    /// is an ideal, so this is a crate defect. The dimension vectors of `X`
    /// and `Y` are carried.
    RadicalSquareNotContained {
        /// Dimension vector of `X`.
        source: Vec<usize>,
        /// Dimension vector of `Y`.
        target: Vec<usize>,
    },
    /// A residue degree does not divide the base dimension of an arrow.
    /// `Irr(X, Y)` is a vector space over each residue field, so this is a
    /// crate defect. The dimension vector of the module whose residue degree
    /// failed is carried.
    ResidueDegreeDoesNotDivide {
        /// Dimension vector of the module whose residue degree failed.
        dim_vector: Vec<usize>,
        /// `dim_Fp Irr(X, Y)`.
        base_dim: usize,
        /// The residue degree that does not divide it.
        residue_degree: usize,
    },
}

impl fmt::Display for ArQuiverError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Hom(error) => write!(f, "morphism rejected: {error}"),
            Self::Space(error) => write!(f, "hom space rejected the input: {error}"),
            Self::Injective(error) => {
                write!(f, "the opposite algebra could not be built: {error}")
            }
            Self::UnsupportedDomain { dynkin, nakayama } => write!(
                f,
                "no complete enumeration applies: the Dynkin route reports {dynkin}, \
                 the Nakayama route reports {nakayama}"
            ),
            Self::RadicalSquareNotContained { source, target } => write!(
                f,
                "the radical square of ({source:?}, {target:?}) left the radical; crate defect"
            ),
            Self::ResidueDegreeDoesNotDivide {
                dim_vector,
                base_dim,
                residue_degree,
            } => write!(
                f,
                "residue degree {residue_degree} of {dim_vector:?} does not divide \
                 the base dimension {base_dim}; crate defect"
            ),
        }
    }
}

impl std::error::Error for ArQuiverError {}

impl From<HomError> for ArQuiverError {
    fn from(error: HomError) -> ArQuiverError {
        ArQuiverError::Hom(error)
    }
}

impl From<HomSpaceError> for ArQuiverError {
    fn from(error: HomSpaceError) -> ArQuiverError {
        ArQuiverError::Space(error)
    }
}

/// The inverse of an isomorphism, vertex by vertex.
fn inverse_of(f: &Morphism) -> Option<Morphism> {
    let field = f.source().field();
    let mut maps = Vec::new();
    for v in 0..f.source().algebra().quiver().num_vertices() {
        maps.push(matrix_inverse(f.map_at(v), &field)?);
    }
    Morphism::new(f.target(), f.source(), maps).ok()
}

/// The morphisms `f` in `space` with `f.then(u)` in the radical of `endo`.
///
/// `endo` must be the endomorphism algebra of the source module of `space`,
/// and `u` must run from the target module of `space` to that same source
/// module.
fn radical_against_iso(
    space: &HomSpace,
    endo: &EndoAlgebra,
    u: &Morphism,
) -> Result<HomSubspace, ArQuiverError> {
    let field = space.source().field();
    let radical = endo.radical_basis();
    let mut rows: Vec<Vec<Fp>> = Vec::with_capacity(space.dim() + radical.rows());
    for f in space.basis() {
        rows.push(endo.coords(&f.then(u)?));
    }
    for r in 0..radical.rows() {
        rows.push(radical.row(r).to_vec());
    }
    let stacked = if rows.is_empty() {
        DenseMat::zero(0, endo.dim())
    } else {
        DenseMat::from_rows(&rows)
    };
    // The stacked matrix holds one row per composite and then the radical
    // basis. A row (l | m) of its left null space says that the composite
    // combined by l equals the radical element combined by -m, so l runs
    // over the solutions of the radical condition.
    let kernel = stacked.left_kernel_basis(&field);
    let spanning: Vec<Morphism> = (0..kernel.rows())
        .map(|k| space.morphism(&kernel.row(k)[..space.dim()]))
        .collect();
    Ok(space.subspace(&spanning)?)
}

/// The radical `rad(X, Y)` of the module category between two certified
/// indecomposables, as a subspace of `Hom(X, Y)`.
///
/// Non-isomorphic endpoints give the whole Hom space. Isomorphic endpoints
/// give the maps `f` with `f.then(u)` in `rad End(X)`, where `u: Y -> X` is the
/// inverse of the first isomorphism `X -> Y` found by the deterministic scan of
/// the radical criterion. The subspace does not depend on that choice, as the
/// module documentation explains.
///
/// # Errors
/// [`ArQuiverError::Hom`] when the two modules do not share one algebra.
pub fn category_radical(
    x: &IndecomposableModule,
    y: &IndecomposableModule,
) -> Result<HomSubspace, ArQuiverError> {
    let space = HomSpace::new(x.module(), y.module())?;
    let Some(h) = indecomposable_iso(x.module(), y.module(), x.endo()) else {
        return Ok(space.full_subspace());
    };
    let u = inverse_of(&h).expect("the radical criterion returns an isomorphism");
    radical_against_iso(&space, x.endo(), &u)
}

/// Which classification theorem lists the entries of a catalog.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CatalogProvenance {
    /// The Nakayama classification: the indecomposables of a Nakayama algebra
    /// are the uniserial quotients `P_i / rad^l P_i`.
    Nakayama,
    /// Gabriel's theorem: the indecomposables of a path algebra of Dynkin
    /// type are one per positive root of the underlying graph.
    DynkinZeroIdeal,
}

impl fmt::Display for CatalogProvenance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Nakayama => f.write_str("Nakayama classification"),
            Self::DynkinZeroIdeal => f.write_str("Gabriel's theorem"),
        }
    }
}

/// A complete list of the indecomposable modules of one algebra, each
/// certified by its local endomorphism algebra.
///
/// Fields are private, and the only constructors are
/// [`IndecomposableCatalog::nakayama`] and [`IndecomposableCatalog::dynkin`],
/// which wrap the two complete enumerations of the crate. A plain list of
/// modules never becomes a catalog, so a value of this type carries the
/// completeness of its [`CatalogProvenance`].
///
/// Entry order is enumerator order. The stable identifier of an entry is its
/// index.
pub struct IndecomposableCatalog {
    algebra: Arc<Algebra>,
    provenance: CatalogProvenance,
    // Shared, so an AR vertex can hold its entry without running the
    // locality gate a second time.
    entries: Vec<Arc<IndecomposableModule>>,
}

impl fmt::Debug for IndecomposableCatalog {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IndecomposableCatalog")
            .field("provenance", &self.provenance)
            .field("entries", &self.entries.len())
            .finish()
    }
}

/// Puts every listed module through the indecomposability gate.
///
/// # Panics
/// Panics when the gate rejects a module the enumerator listed. Both
/// enumerators list only modules their classification theorem proves
/// indecomposable, and both attach a [`Certificate`], so a rejection is a
/// crate defect.
fn certified_entries(listed: Vec<(Module, Certificate)>) -> Vec<Arc<IndecomposableModule>> {
    listed
        .into_iter()
        .map(|(m, certificate)| {
            Arc::new(IndecomposableModule::new(&m).unwrap_or_else(|error| {
                panic!(
                    "the enumerator listed the module {:?} with certificate {certificate:?}, \
                     and the locality gate rejected it: {error}; crate defect",
                    m.dim_vector()
                )
            }))
        })
        .collect()
}

impl IndecomposableCatalog {
    /// The indecomposables of a Nakayama algebra, in the order of
    /// [`nakayama_indecomposables`].
    ///
    /// # Errors
    /// [`EnumerateError`] when the algebra is not Nakayama.
    pub fn nakayama(algebra: &Arc<Algebra>) -> Result<IndecomposableCatalog, EnumerateError> {
        let listed = nakayama_indecomposables(algebra)?;
        Ok(IndecomposableCatalog {
            algebra: algebra.clone(),
            provenance: CatalogProvenance::Nakayama,
            entries: certified_entries(listed),
        })
    }

    /// The indecomposables of a path algebra of Dynkin type, in the order of
    /// [`dynkin_indecomposables`].
    ///
    /// # Errors
    /// [`DynkinError`] when the algebra has relations or the underlying graph
    /// of its quiver is no Dynkin diagram.
    pub fn dynkin(algebra: &Arc<Algebra>) -> Result<IndecomposableCatalog, DynkinError> {
        let listed = dynkin_indecomposables(algebra)?;
        Ok(IndecomposableCatalog {
            algebra: algebra.clone(),
            provenance: CatalogProvenance::DynkinZeroIdeal,
            entries: certified_entries(listed),
        })
    }

    /// The algebra the entries are modules over.
    #[inline]
    pub fn algebra(&self) -> &Arc<Algebra> {
        &self.algebra
    }

    /// The classification theorem that makes the list complete.
    #[inline]
    pub fn provenance(&self) -> CatalogProvenance {
        self.provenance
    }

    /// The entries in enumerator order. An entry's index is its identifier.
    #[inline]
    pub fn entries(&self) -> &[Arc<IndecomposableModule>] {
        &self.entries
    }

    /// The number of entries.
    #[inline]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the catalog has no entries. An algebra with at least one
    /// vertex has at least one simple module, so both enumerators return a
    /// nonempty list.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

/// The span of the composites `f.then(g)` over the given pairs of subspaces,
/// as a subspace of `Hom(source, target)`.
fn span_of_composites<'a>(
    source: &Module,
    target: &Module,
    factorizations: impl Iterator<Item = (&'a HomSubspace, &'a HomSubspace)>,
) -> Result<HomSubspace, ArQuiverError> {
    let mut composites = Vec::new();
    for (left, right) in factorizations {
        for i in 0..left.dim() {
            let f = left.basis_morphism(i);
            for j in 0..right.dim() {
                composites.push(f.then(&right.basis_morphism(j))?);
            }
        }
    }
    Ok(HomSubspace::spanned_by(source, target, &composites)?)
}

/// `rad^2(X, Y)`: the sum over the catalog entries `Z` of the composites of
/// `rad(X, Z)` with `rad(Z, Y)`, as a subspace of `Hom(X, Y)`.
///
/// The catalog is complete, so the sum is the whole square of the radical,
/// not a lower bound. The summation runs in catalog order; the result is a
/// span, so the order does not change it.
///
/// # Errors
/// [`ArQuiverError::Hom`] when `x`, `y` and the catalog do not share one
/// algebra.
pub fn radical_square_through_catalog(
    catalog: &IndecomposableCatalog,
    x: &IndecomposableModule,
    y: &IndecomposableModule,
) -> Result<HomSubspace, ArQuiverError> {
    let mut legs = Vec::with_capacity(catalog.len());
    for z in catalog.entries() {
        legs.push((category_radical(x, z)?, category_radical(z, y)?));
    }
    span_of_composites(
        x.module(),
        y.module(),
        legs.iter().map(|(left, right)| (left, right)),
    )
}

/// `Irr(X, Y) = rad(X, Y) / rad^2(X, Y)`, with the deterministic complement
/// representatives of [`HomQuotient`]. The nonzero elements are the classes
/// of the irreducible maps `X -> Y`.
///
/// # Errors
/// [`ArQuiverError::Hom`] when `x`, `y` and the catalog do not share one
/// algebra, and [`ArQuiverError::RadicalSquareNotContained`] when the square
/// leaves the radical, which is a crate defect.
pub fn irreducible_quotient(
    catalog: &IndecomposableCatalog,
    x: &IndecomposableModule,
    y: &IndecomposableModule,
) -> Result<HomQuotient, ArQuiverError> {
    let radical = category_radical(x, y)?;
    let square = radical_square_through_catalog(catalog, x, y)?;
    quotient_or_defect(&radical, &square)
}

fn quotient_or_defect(
    radical: &HomSubspace,
    square: &HomSubspace,
) -> Result<HomQuotient, ArQuiverError> {
    radical.quotient_by(square).map_err(|error| match error {
        HomSpaceError::NotContained => ArQuiverError::RadicalSquareNotContained {
            source: radical.source().dim_vector().to_vec(),
            target: radical.target().dim_vector().to_vec(),
        },
        other => ArQuiverError::Space(other),
    })
}

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
    /// The identifier of the vertex: its index in the catalog and in
    /// [`ArQuiver::vertices`].
    #[inline]
    pub fn id(&self) -> usize {
        self.id
    }

    /// The module at the vertex.
    #[inline]
    pub fn module(&self) -> &IndecomposableModule {
        &self.module
    }

    /// The residue degree `d` of the module: the residue field of its local
    /// endomorphism algebra is `F_{p^d}`.
    #[inline]
    pub fn residue_degree(&self) -> usize {
        self.residue_degree
    }

    /// Whether the module is projective.
    #[inline]
    pub fn projective(&self) -> bool {
        self.projective
    }

    /// Whether the module is injective.
    #[inline]
    pub fn injective(&self) -> bool {
        self.injective
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
    source: usize,
    target: usize,
    base_dim: usize,
    over_source_residue: usize,
    over_target_residue: usize,
    representatives: Vec<Morphism>,
}

impl ArArrow {
    /// The identifier of the source vertex.
    #[inline]
    pub fn source(&self) -> usize {
        self.source
    }

    /// The identifier of the target vertex.
    #[inline]
    pub fn target(&self) -> usize {
        self.target
    }

    /// `dim_Fp Irr(X, Y)`, always positive.
    #[inline]
    pub fn base_dim(&self) -> usize {
        self.base_dim
    }

    /// The dimension of `Irr(X, Y)` over the residue field of the source.
    #[inline]
    pub fn over_source_residue(&self) -> usize {
        self.over_source_residue
    }

    /// The dimension of `Irr(X, Y)` over the residue field of the target.
    #[inline]
    pub fn over_target_residue(&self) -> usize {
        self.over_target_residue
    }

    /// One irreducible map per complement basis row of `Irr(X, Y)`, in the
    /// order of that basis.
    #[inline]
    pub fn representatives(&self) -> &[Morphism] {
        &self.representatives
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
    /// The catalog the vertices come from. Vertex `i` carries the same module
    /// as catalog entry `i`.
    #[inline]
    pub fn catalog(&self) -> &IndecomposableCatalog {
        &self.catalog
    }

    /// The vertices in catalog order.
    #[inline]
    pub fn vertices(&self) -> &[ArVertex] {
        &self.vertices
    }

    /// The arrows, ordered by source identifier then target identifier.
    #[inline]
    pub fn arrows(&self) -> &[ArArrow] {
        &self.arrows
    }
}

/// `base_dim / residue_degree`: the dimension of a space of prime-field
/// dimension `base_dim` over a residue field of degree `residue_degree`.
/// `module` names the module whose residue degree this is, for the error.
///
/// # Errors
/// [`ArQuiverError::ResidueDegreeDoesNotDivide`] when the division leaves a
/// remainder or the degree is 0, which is a crate defect.
fn over_residue(
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

fn unit(dim: usize, k: usize, field: &PrimeField) -> Vec<Fp> {
    let mut coords = vec![field.zero(); dim];
    coords[k] = field.one();
    coords
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
        });
    }
    Ok(vertices)
}

fn quiver_of(catalog: IndecomposableCatalog) -> Result<ArQuiver, ArQuiverError> {
    let vertices = vertices_of(&catalog)?;
    let n = catalog.len();
    let mut radicals = Vec::with_capacity(n * n);
    for x in catalog.entries() {
        for y in catalog.entries() {
            radicals.push(category_radical(x, y)?);
        }
    }
    let mut arrows = Vec::new();
    for i in 0..n {
        for j in 0..n {
            let (x, y) = (catalog.entries()[i].module(), catalog.entries()[j].module());
            let square = span_of_composites(
                x,
                y,
                (0..n).map(|k| (&radicals[i * n + k], &radicals[k * n + j])),
            )?;
            let quotient = quotient_or_defect(&radicals[i * n + j], &square)?;
            let base_dim = quotient.dim();
            if base_dim == 0 {
                continue;
            }
            let field = x.field();
            arrows.push(ArArrow {
                source: i,
                target: j,
                base_dim,
                over_source_residue: over_residue(base_dim, vertices[i].residue_degree, x)?,
                over_target_residue: over_residue(base_dim, vertices[j].residue_degree, y)?,
                representatives: (0..base_dim)
                    .map(|k| quotient.representative(&unit(base_dim, k, &field)))
                    .collect(),
            });
        }
    }
    Ok(ArQuiver {
        catalog,
        vertices,
        arrows,
    })
}

/// The valued AR quiver of `algebra`.
///
/// The dispatch is deterministic: a zero ideal over a quiver of Dynkin shape
/// takes the Gabriel enumeration, any other Nakayama algebra takes the
/// Nakayama enumeration, and anything else is rejected.
///
/// # Errors
/// [`ArQuiverError::UnsupportedDomain`], carrying both rejections, when
/// neither enumeration applies. [`ArQuiverError::Injective`] when the
/// opposite algebra needed for the injectivity flags fails to build.
pub fn ar_quiver(algebra: &Arc<Algebra>) -> Result<ArQuiver, ArQuiverError> {
    let catalog = match IndecomposableCatalog::dynkin(algebra) {
        Ok(catalog) => catalog,
        Err(dynkin) => match IndecomposableCatalog::nakayama(algebra) {
            Ok(catalog) => catalog,
            Err(nakayama) => return Err(ArQuiverError::UnsupportedDomain { dynkin, nakayama }),
        },
    };
    quiver_of(catalog)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{
        commutative_square, cyclic_nakayama, kronecker, linear_an, radical_square_zero_cycle,
        truncated_poly,
    };
    use crate::dynkin::{DynkinType, dynkin_quiver};
    use crate::hom::hom;
    use crate::module::Module;
    use crate::quiver::Quiver;

    fn f2() -> PrimeField {
        PrimeField::new(2).unwrap()
    }

    fn f5() -> PrimeField {
        PrimeField::new(5).unwrap()
    }

    fn path_algebra(quiver: Quiver, field: PrimeField) -> Arc<Algebra> {
        crate::algebra::path_algebra(quiver, field)
            .expect("the zero ideal over an acyclic quiver completes")
    }

    fn d4(field: PrimeField) -> Arc<Algebra> {
        path_algebra(
            dynkin_quiver(DynkinType::D(4)).expect("D_4 has a quiver"),
            field,
        )
    }

    fn indec(m: &Module) -> IndecomposableModule {
        IndecomposableModule::new(m).expect("the fixture module is indecomposable")
    }

    fn dim_vectors(quiver: &ArQuiver) -> Vec<Vec<usize>> {
        quiver
            .vertices()
            .iter()
            .map(|v| v.module().module().dim_vector().to_vec())
            .collect()
    }

    fn arrow_triples(quiver: &ArQuiver) -> Vec<(usize, usize, usize)> {
        quiver
            .arrows()
            .iter()
            .map(|a| (a.source(), a.target(), a.base_dim()))
            .collect()
    }

    fn flags(quiver: &ArQuiver) -> Vec<(bool, bool)> {
        quiver
            .vertices()
            .iter()
            .map(|v| (v.projective(), v.injective()))
            .collect()
    }

    // The F_8-endomorphism module of tests/decompose_iso.rs: the Kronecker
    // representation (I_3, C) over F_2 for C the companion matrix of
    // x^3 + x + 1, irreducible over F_2, so End(W) is the field F_8.
    fn f8_module() -> Module {
        let field = f2();
        let algebra = kronecker(2, field);
        let mut companion = DenseMat::zero(3, 3);
        companion.set(0, 1, field.one());
        companion.set(1, 2, field.one());
        companion.set(2, 0, field.one());
        companion.set(2, 1, field.one());
        Module::new(algebra, vec![3, 3], vec![DenseMat::identity(3), companion])
            .expect("the Kronecker representation is a module")
    }

    #[test]
    fn the_radical_between_distinct_simples_is_the_whole_hom_space() {
        for field in [f2(), f5()] {
            let algebra = linear_an(3, field);
            let simples: Vec<IndecomposableModule> = (0..3)
                .map(|v| indec(&Module::simple(&algebra, v)))
                .collect();
            for x in &simples {
                for y in &simples {
                    let space = HomSpace::new(x.module(), y.module()).unwrap();
                    let radical = category_radical(x, y).unwrap();
                    if x.module().ptr_eq(y.module()) {
                        // End(S) = k, so rad End(S) = 0 while Hom is a line.
                        assert_eq!(space.dim(), 1);
                        assert_eq!(radical.dim(), 0);
                    } else {
                        // Distinct simples over linearly oriented A_3 admit no
                        // nonzero map, so Hom and its radical are both zero.
                        assert_eq!(space.dim(), 0);
                        assert_eq!(radical, space.full_subspace());
                    }
                }
            }
        }
    }

    // Over linearly oriented A_3 the projective P_0 has dimension vector
    // (1, 1, 1) and S_0 is its top, so Hom(P_0, S_0) is the line spanned by
    // the top projection. The two modules are not isomorphic, so the whole
    // line is radical.
    #[test]
    fn the_radical_from_a_projective_onto_its_top_is_the_whole_hom_line() {
        for field in [f2(), f5()] {
            let algebra = linear_an(3, field);
            let p0 = indec(&Module::projective(&algebra, 0));
            let s0 = indec(&Module::simple(&algebra, 0));
            let space = HomSpace::new(p0.module(), s0.module()).unwrap();
            assert_eq!(space.dim(), 1);
            let radical = category_radical(&p0, &s0).unwrap();
            assert_eq!(radical.dim(), 1);
            assert_eq!(radical, space.full_subspace());
            assert!(radical.contains(&space.basis()[0]).unwrap());
        }
    }

    // The isomorphic case, on two separately built copies of the projective
    // of k[x]/(x^3): the catalog entry P/rad^3 is a cokernel, the projective
    // is built directly, and the two are isomorphic. A second isomorphism is
    // the first composed with the automorphism 1 + n for n a radical basis
    // element of End(X); 1 + n is a unit because n is nilpotent.
    #[test]
    fn the_radical_does_not_depend_on_the_chosen_isomorphism() {
        for field in [f2(), f5()] {
            let algebra = truncated_poly(3, field).unwrap();
            let catalog = IndecomposableCatalog::nakayama(&algebra).unwrap();
            let x = indec(&Module::projective(&algebra, 0));
            let y = &catalog.entries()[2];
            assert_eq!(y.module().total_dim(), 3);
            assert!(!x.module().ptr_eq(y.module()));
            let space = HomSpace::new(x.module(), y.module()).unwrap();
            assert_eq!(space.dim(), 3);

            let first = inverse_of(
                &indecomposable_iso(x.module(), y.module(), x.endo())
                    .expect("the two copies are isomorphic"),
            )
            .unwrap();
            let endo = x.endo();
            assert_eq!(endo.radical_dim(), 2);
            let mut automorphism = endo.one().to_vec();
            for (c, entry) in automorphism.iter_mut().enumerate() {
                *entry = field.add(*entry, endo.radical_basis().get(0, c));
            }
            let second = first.then(&endo.morphism(&automorphism)).unwrap();
            assert!(second.is_isomorphism());
            assert_ne!(first, second);

            let by_first = radical_against_iso(&space, endo, &first).unwrap();
            let by_second = radical_against_iso(&space, endo, &second).unwrap();
            assert_eq!(by_first.dim(), 2);
            assert_eq!(by_first, by_second);
            assert_eq!(by_first, category_radical(&x, y).unwrap());
        }
    }

    // End(W) = F_8 is a field, so rad End(W) = 0 and the radical of the
    // category between W and itself is zero, while Hom(W, W) has F_2
    // dimension 3. Hom(W, W) and its radical are F_8 spaces, so both
    // dimensions are multiples of the residue degree 3.
    #[test]
    fn the_radical_of_the_f8_module_is_zero_with_residue_degree_3_bookkeeping() {
        let w = indec(&f8_module());
        assert_eq!(w.residue_degree(), 3);
        assert_eq!(w.endo().radical_dim(), 0);
        let space = HomSpace::new(w.module(), w.module()).unwrap();
        assert_eq!(space.dim(), 3);
        let radical = category_radical(&w, &w).unwrap();
        assert_eq!(radical.dim(), 0);
        assert_eq!(over_residue(space.dim(), 3, w.module()).unwrap(), 1);
        assert_eq!(over_residue(radical.dim(), 3, w.module()).unwrap(), 0);
    }

    #[test]
    fn a_residue_degree_that_does_not_divide_is_a_typed_defect() {
        let w = f8_module();
        assert_eq!(
            over_residue(2, 3, &w).unwrap_err(),
            ArQuiverError::ResidueDegreeDoesNotDivide {
                dim_vector: vec![3, 3],
                base_dim: 2,
                residue_degree: 3,
            }
        );
        assert_eq!(
            over_residue(1, 0, &w).unwrap_err(),
            ArQuiverError::ResidueDegreeDoesNotDivide {
                dim_vector: vec![3, 3],
                base_dim: 1,
                residue_degree: 0,
            }
        );
    }

    // No cheap fixture yields a nonzero valued Irr, and the two catalog
    // domains provably cannot (every entry has residue degree 1), so the
    // Valued arithmetic is pinned here on directly built arrows through
    // the same division routine `quiver_of` calls.
    #[test]
    fn valued_arrow_arithmetic_and_the_division_gate_are_pinned() {
        let w = f8_module();
        let valued = ArArrow {
            source: 0,
            target: 1,
            base_dim: 6,
            over_source_residue: over_residue(6, 2, &w).unwrap(),
            over_target_residue: over_residue(6, 3, &w).unwrap(),
            representatives: Vec::new(),
        };
        assert_eq!(
            valued.valuation(),
            ArrowValuation::Valued {
                base_dim: 6,
                over_source: 3,
                over_target: 2,
            }
        );
        let one_sided = ArArrow {
            source: 0,
            target: 1,
            base_dim: 6,
            over_source_residue: over_residue(6, 1, &w).unwrap(),
            over_target_residue: over_residue(6, 3, &w).unwrap(),
            representatives: Vec::new(),
        };
        assert_eq!(
            one_sided.valuation(),
            ArrowValuation::Valued {
                base_dim: 6,
                over_source: 6,
                over_target: 2,
            }
        );
        let plain = ArArrow {
            source: 0,
            target: 1,
            base_dim: 6,
            over_source_residue: over_residue(6, 1, &w).unwrap(),
            over_target_residue: over_residue(6, 1, &w).unwrap(),
            representatives: Vec::new(),
        };
        assert_eq!(plain.valuation(), ArrowValuation::Plain(6));
        assert_eq!(
            over_residue(5, 3, &w).unwrap_err(),
            ArQuiverError::ResidueDegreeDoesNotDivide {
                dim_vector: vec![3, 3],
                base_dim: 5,
                residue_degree: 3,
            }
        );
    }

    // Over linearly oriented A_3 write M[i, j] for the module supported on
    // the interval i..=j. Then dim Hom(M[i, j], M[k, l]) is 1 when
    // k <= i <= l <= j and 0 otherwise, and every nonzero map is the identity
    // on the overlap. Two hand-checked consequences:
    //
    // - The top projection P_0 = M[0, 2] -> S_0 = M[0, 0] is the composite of
    //   the two surjections M[0, 2] -> M[0, 1] -> M[0, 0], so it lies in
    //   rad^2 and Irr(P_0, S_0) is zero.
    // - The surjection M[0, 2] -> M[0, 1] does not factor: the only modules Z
    //   with rad(M[0, 2], Z) and rad(Z, M[0, 1]) both nonzero are M[0, 1]
    //   itself and M[0, 0], and both routes compose to zero, so
    //   Irr(P_0, M[0, 1]) is a line.
    #[test]
    fn the_radical_square_on_linear_a3_matches_the_hand_checked_factorizations() {
        for field in [f2(), f5()] {
            let algebra = linear_an(3, field);
            let catalog = IndecomposableCatalog::dynkin(&algebra).unwrap();
            let p0 = indec(&Module::projective(&algebra, 0));
            let s0 = indec(&Module::simple(&algebra, 0));
            let m01 = indec(&Module::injective(&algebra, 1));
            assert_eq!(m01.module().dim_vector(), [1, 1, 0]);

            assert_eq!(category_radical(&p0, &s0).unwrap().dim(), 1);
            assert_eq!(
                radical_square_through_catalog(&catalog, &p0, &s0)
                    .unwrap()
                    .dim(),
                1
            );
            assert_eq!(irreducible_quotient(&catalog, &p0, &s0).unwrap().dim(), 0);

            assert_eq!(category_radical(&p0, &m01).unwrap().dim(), 1);
            assert_eq!(
                radical_square_through_catalog(&catalog, &p0, &m01)
                    .unwrap()
                    .dim(),
                0
            );
            assert_eq!(irreducible_quotient(&catalog, &p0, &m01).unwrap().dim(), 1);
        }
    }

    // Linearly oriented A_3 with the zero ideal, hand-derived from the Hom
    // rule above. The six indecomposables are the interval modules, and the
    // catalog lists them by root height then lexicographically:
    //
    //   0: (0,0,1) = S_2 = P_2   3: (0,1,1) = P_1
    //   1: (0,1,0) = S_1         4: (1,1,0) = I_1
    //   2: (1,0,0) = S_0 = I_0   5: (1,1,1) = P_0 = I_2
    //
    // Deleting from each nonzero rad(X, Y) the ones that factor leaves six
    // arrows, the classical zigzag: P_2 -> P_1 -> P_0 along the projectives,
    // P_1 -> S_1 -> I_1 and P_0 -> I_1 -> S_0. The meshes confirm it:
    // 0 -> S_2 -> P_1 -> S_1 -> 0, 0 -> P_1 -> S_1 + P_0 -> I_1 -> 0 and
    // 0 -> S_1 -> I_1 -> S_0 -> 0 are the three almost-split sequences, and
    // the three projectives receive one arrow each from their radical.
    #[test]
    fn linear_a3_has_the_hand_derived_zigzag_ar_quiver() {
        for field in [f2(), f5()] {
            let algebra = linear_an(3, field);
            let quiver = ar_quiver(&algebra).unwrap();
            assert_eq!(
                quiver.catalog().provenance(),
                CatalogProvenance::DynkinZeroIdeal
            );
            assert_eq!(
                dim_vectors(&quiver),
                vec![
                    vec![0, 0, 1],
                    vec![0, 1, 0],
                    vec![1, 0, 0],
                    vec![0, 1, 1],
                    vec![1, 1, 0],
                    vec![1, 1, 1],
                ]
            );
            assert_eq!(
                flags(&quiver),
                vec![
                    (true, false),
                    (false, false),
                    (false, true),
                    (true, false),
                    (false, true),
                    (true, true),
                ]
            );
            assert_eq!(
                arrow_triples(&quiver),
                vec![
                    (0, 3, 1),
                    (1, 4, 1),
                    (3, 1, 1),
                    (3, 5, 1),
                    (4, 2, 1),
                    (5, 4, 1),
                ]
            );
        }
    }

    // k[x]/(x^3) is Nakayama with one vertex, so the catalog is
    // M_1, M_2, M_3 by length. Hom(M_i, M_j) has dimension min(i, j), the
    // radical of End(M_i) is multiplication by x, and every map M_i -> M_j
    // sends 1 to an element killed by x^i. Hand-checking the four candidate
    // arrows: M_1 -> M_2 and M_2 -> M_1 do not factor, M_2 -> M_3 has
    // rad(M_2, M_3) of dimension 2 with a one-dimensional square, and
    // M_1 -> M_3 factors through M_2, so its Irr is zero. The AR sequences
    // are 0 -> M_1 -> M_2 -> M_1 -> 0 and 0 -> M_2 -> M_1 + M_3 -> M_2 -> 0,
    // and M_3 is projective-injective.
    #[test]
    fn truncated_poly_3_has_the_ar_quiver_of_k_x_mod_x_cubed() {
        for field in [f2(), f5()] {
            let algebra = truncated_poly(3, field).unwrap();
            let quiver = ar_quiver(&algebra).unwrap();
            assert_eq!(quiver.catalog().provenance(), CatalogProvenance::Nakayama);
            assert_eq!(dim_vectors(&quiver), vec![vec![1], vec![2], vec![3]]);
            assert_eq!(
                flags(&quiver),
                vec![(false, false), (false, false), (true, true)]
            );
            assert_eq!(
                arrow_triples(&quiver),
                vec![(0, 1, 1), (1, 0, 1), (1, 2, 1), (2, 1, 1)]
            );
        }
    }

    // The cyclic quiver on three vertices with rad^2 = 0 is a self-injective
    // Nakayama algebra of dimension 6. Every projective P_i has top S_i and
    // socle S_{i+1}, so the six indecomposables are the three simples and the
    // three projectives, listed by the enumerator as S_0, P_0, S_1, P_1,
    // S_2, P_2. The Loewy length is 2, so the only almost-split sequences are
    // 0 -> S_{i+1} -> P_i -> S_i -> 0, giving the arrows S_{i+1} -> P_i and
    // P_i -> S_i, six in all: a hexagon.
    #[test]
    fn the_radical_square_zero_3_cycle_has_a_hexagonal_ar_quiver() {
        for field in [f2(), f5()] {
            let algebra = radical_square_zero_cycle(3, field);
            let quiver = ar_quiver(&algebra).unwrap();
            assert_eq!(quiver.catalog().provenance(), CatalogProvenance::Nakayama);
            assert_eq!(
                dim_vectors(&quiver),
                vec![
                    vec![1, 0, 0],
                    vec![1, 1, 0],
                    vec![0, 1, 0],
                    vec![0, 1, 1],
                    vec![0, 0, 1],
                    vec![1, 0, 1],
                ]
            );
            assert_eq!(
                flags(&quiver),
                vec![
                    (false, false),
                    (true, true),
                    (false, false),
                    (true, true),
                    (false, false),
                    (true, true),
                ]
            );
            assert_eq!(
                arrow_triples(&quiver),
                vec![
                    (0, 5, 1),
                    (1, 0, 1),
                    (2, 1, 1),
                    (3, 2, 1),
                    (4, 3, 1),
                    (5, 4, 1),
                ]
            );
        }
    }

    // D_4 oriented away from the branch vertex 0: arrows 0 -> 1, 0 -> 2,
    // 0 -> 3. Then P_0 = (1,1,1,1) with rad P_0 = S_1 + S_2 + S_3, the
    // leaves are simple projective, and the injectives are S_0 and the three
    // (1, ..., 1, ...) modules. Knitting from the three simple projectives:
    //
    //   S_i -> P_0 (three arrows into the projective from its radical),
    //   0 -> S_i -> P_0 -> (1,1,1,1) - S_i -> 0,
    //   0 -> P_0 -> sum of those three -> (2,1,1,1) -> 0,
    //   0 -> (1,1,1,1) - S_i -> (2,1,1,1) -> I_i -> 0,
    //   0 -> (2,1,1,1) -> I_1 + I_2 + I_3 -> S_0 -> 0.
    //
    // That is 12 vertices and 15 arrows, with a three-arrow star in and a
    // three-arrow star out at both (1,1,1,1) and (2,1,1,1).
    #[test]
    fn d4_oriented_away_from_the_branch_vertex_has_15_arrows_and_two_stars() {
        let algebra = d4(f2());
        let quiver = ar_quiver(&algebra).unwrap();
        assert_eq!(quiver.vertices().len(), 12);
        assert_eq!(quiver.arrows().len(), 15);
        assert_eq!(
            dim_vectors(&quiver),
            vec![
                vec![0, 0, 0, 1],
                vec![0, 0, 1, 0],
                vec![0, 1, 0, 0],
                vec![1, 0, 0, 0],
                vec![1, 0, 0, 1],
                vec![1, 0, 1, 0],
                vec![1, 1, 0, 0],
                vec![1, 0, 1, 1],
                vec![1, 1, 0, 1],
                vec![1, 1, 1, 0],
                vec![1, 1, 1, 1],
                vec![2, 1, 1, 1],
            ]
        );
        assert_eq!(
            arrow_triples(&quiver),
            vec![
                (0, 10, 1),
                (1, 10, 1),
                (2, 10, 1),
                (4, 3, 1),
                (5, 3, 1),
                (6, 3, 1),
                (7, 11, 1),
                (8, 11, 1),
                (9, 11, 1),
                (10, 7, 1),
                (10, 8, 1),
                (10, 9, 1),
                (11, 4, 1),
                (11, 5, 1),
                (11, 6, 1),
            ]
        );
        let star_in = |id: usize| -> Vec<usize> {
            quiver
                .arrows()
                .iter()
                .filter(|a| a.target() == id)
                .map(|a| a.source())
                .collect()
        };
        let star_out = |id: usize| -> Vec<usize> {
            quiver
                .arrows()
                .iter()
                .filter(|a| a.source() == id)
                .map(|a| a.target())
                .collect()
        };
        assert_eq!(star_in(10), vec![0, 1, 2]);
        assert_eq!(star_out(10), vec![7, 8, 9]);
        assert_eq!(star_in(11), vec![7, 8, 9]);
        assert_eq!(star_out(11), vec![4, 5, 6]);
        assert!(quiver.vertices()[10].projective());
        assert!(!quiver.vertices()[11].projective());
        assert!(!quiver.vertices()[11].injective());
    }

    fn catalog_fixtures() -> Vec<Arc<Algebra>> {
        vec![
            linear_an(3, f5()),
            linear_an(4, f2()),
            truncated_poly(3, f2()).unwrap(),
            truncated_poly(4, f5()).unwrap(),
            radical_square_zero_cycle(3, f5()),
            cyclic_nakayama(&[3, 3, 3], f2()).unwrap(),
            d4(f2()),
        ]
    }

    // Every indecomposable over these algebras is a brick or a uniserial
    // module with endomorphism algebra local of residue degree 1, so every
    // arrow valuation is plain.
    #[test]
    fn every_arrow_on_the_catalog_domains_is_plain() {
        for algebra in catalog_fixtures() {
            let quiver = ar_quiver(&algebra).unwrap();
            for vertex in quiver.vertices() {
                assert_eq!(
                    vertex.residue_degree(),
                    1,
                    "vertex {} of a catalog domain",
                    vertex.id()
                );
            }
            for arrow in quiver.arrows() {
                assert!(arrow.base_dim() > 0);
                assert_eq!(arrow.over_source_residue(), arrow.base_dim());
                assert_eq!(arrow.over_target_residue(), arrow.base_dim());
                assert_eq!(arrow.valuation(), ArrowValuation::Plain(arrow.base_dim()));
                assert_eq!(arrow.representatives().len(), arrow.base_dim());
            }
        }
    }

    #[test]
    fn arrow_representatives_are_radical_maps_outside_the_radical_square() {
        for algebra in [linear_an(3, f5()), truncated_poly(3, f2()).unwrap()] {
            let quiver = ar_quiver(&algebra).unwrap();
            let catalog = quiver.catalog();
            for arrow in quiver.arrows() {
                let x = &catalog.entries()[arrow.source()];
                let y = &catalog.entries()[arrow.target()];
                let radical = category_radical(x, y).unwrap();
                let square = radical_square_through_catalog(catalog, x, y).unwrap();
                for f in arrow.representatives() {
                    assert!(radical.contains(f).unwrap());
                    assert!(!square.contains(f).unwrap());
                }
            }
        }
    }

    // A positive-dimensional algebra has one simple module per vertex, and
    // both enumerations list all of them, so no catalog is ever empty.
    #[test]
    fn every_catalog_has_at_least_one_entry_per_vertex() {
        for algebra in catalog_fixtures() {
            let quiver = ar_quiver(&algebra).unwrap();
            let vertices = algebra.quiver().num_vertices() as usize;
            assert!(quiver.catalog().len() >= vertices);
            assert!(!quiver.catalog().is_empty());
            assert_eq!(quiver.vertices().len(), quiver.catalog().len());
            assert!(Arc::ptr_eq(quiver.catalog().algebra(), &algebra));
            for (id, vertex) in quiver.vertices().iter().enumerate() {
                assert_eq!(vertex.id(), id);
                assert!(
                    vertex
                        .module()
                        .module()
                        .ptr_eq(quiver.catalog().entries()[id].module())
                );
            }
        }
    }

    #[test]
    fn the_catalog_constructors_reject_the_other_route() {
        let nakayama = truncated_poly(3, f5()).unwrap();
        assert_eq!(
            IndecomposableCatalog::dynkin(&nakayama).unwrap_err(),
            DynkinError::NonzeroIdeal { relations: 1 }
        );
        let dynkin = d4(f5());
        assert_eq!(
            IndecomposableCatalog::nakayama(&dynkin).unwrap_err(),
            EnumerateError::NotNakayama {
                vertex: 0,
                incoming: 0,
                outgoing: 3,
            }
        );
    }

    // The commutative square has one relation, so Gabriel's theorem does not
    // apply, and vertex 0 has two outgoing arrows, so it is not Nakayama.
    #[test]
    fn an_unsupported_domain_carries_both_rejections() {
        let algebra = commutative_square(f5());
        assert_eq!(
            ar_quiver(&algebra).unwrap_err(),
            ArQuiverError::UnsupportedDomain {
                dynkin: DynkinError::NonzeroIdeal { relations: 1 },
                nakayama: EnumerateError::NotNakayama {
                    vertex: 0,
                    incoming: 0,
                    outgoing: 2,
                },
            }
        );
    }

    #[test]
    fn the_radical_needs_one_algebra() {
        let first = linear_an(3, f5());
        let second = linear_an(3, f5());
        let x = indec(&Module::simple(&first, 0));
        let y = indec(&Module::simple(&second, 0));
        assert_eq!(
            category_radical(&x, &y).unwrap_err(),
            ArQuiverError::Hom(HomError::DifferentAlgebras)
        );
    }

    // The radical of a Hom space between certified indecomposables misses
    // exactly the isomorphisms, so a nonzero map outside the radical is one.
    #[test]
    fn maps_outside_the_radical_are_isomorphisms() {
        for algebra in [linear_an(3, f5()), truncated_poly(3, f2()).unwrap()] {
            let catalog = ar_quiver(&algebra).unwrap();
            let catalog = catalog.catalog();
            for x in catalog.entries() {
                for y in catalog.entries() {
                    let radical = category_radical(x, y).unwrap();
                    for f in hom(x.module(), y.module()).unwrap() {
                        if !radical.contains(&f).unwrap() {
                            assert!(f.is_isomorphism());
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn the_ar_quiver_is_the_same_on_a_second_run() {
        for algebra in [linear_an(3, f2()), radical_square_zero_cycle(3, f5())] {
            let first = ar_quiver(&algebra).unwrap();
            let second = ar_quiver(&algebra).unwrap();
            assert_eq!(dim_vectors(&first), dim_vectors(&second));
            assert_eq!(arrow_triples(&first), arrow_triples(&second));
            for (a, b) in first.arrows().iter().zip(second.arrows()) {
                for (f, g) in a.representatives().iter().zip(b.representatives()) {
                    assert_eq!(f.map_at(0).entries_u64(), g.map_at(0).entries_u64());
                }
            }
        }
    }
}

//! Ext dimensions and global dimension via minimal resolutions and Yoneda bases.
//!
//! `Ext^k(M, N)` is the cohomology of `Hom_A(P_•, N)` for a projective resolution
//! `P_• → M`. Every term produced by [`projective_cover`](crate::resolution::projective_cover) is `⊕_v P_v^{t_v}` in a
//! canonical layout, and Yoneda gives `Hom_A(e_v A, N) ≅ N_v`. So `Hom_A(P, N)` has
//! an explicit basis indexed by (generator, basis vector of `N` at its vertex). The
//! element for generator `g` at `v` and index `j` sends the summand basis path
//! `p: v → w` to the `j`-th row of `N(p)`. Coordinates of any morphism in this basis
//! are read off its generator rows. No linear system is solved.
//!
//! Sign convention: the induced cochain maps are `δ^i(f) = f ∘ d_{i+1}` with no
//! signs. Alternating signs only normalize `δ² = 0` under other differentials'
//! conventions. Here `δ² = 0` follows from `d² = 0`. Any sign choice rescales basis
//! vectors without changing ranks, so dimension computations are sign-free.
//!
//! Exactness: [`ext_dim`]`(m, n, k)` resolves `m` for `k + 1` steps. The result is
//! either a complete finite resolution or a prefix with differentials
//! `d_1, …, d_{k+1}`. Cohomology at position `k` needs only `d_k` and `d_{k+1}`,
//! so the answer is exact for every `k`, even when the projective dimension is
//! unknown.

use std::fmt;
use std::sync::Arc;

use crate::algebra::Algebra;
use crate::field::{Fp, PrimeField};
use crate::hom::Morphism;
use crate::homspace::deterministic_complement;
use crate::linalg::DenseMat;
use crate::module::Module;
use crate::radical::top;
use crate::resolution::{Bounded, ProjectiveResolution, projective_dimension, resolve};

/// Rejected Ext input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExtError {
    /// The modules live over different algebras (distinct [`Arc`]s). The
    /// field comes from the algebra, so a shared algebra implies a shared
    /// field.
    DifferentAlgebras,
}

impl fmt::Display for ExtError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DifferentAlgebras => f.write_str("modules live over different algebras"),
        }
    }
}

impl std::error::Error for ExtError {}

/// Summand layout of a projective term `⊕_v P_v^{t_v}` built by [`projective_cover`](crate::resolution::projective_cover):
/// generators are ordered by vertex then copy. At each vertex the term's basis is the
/// concatenation of the summands' path bases in generator order.
struct Layout {
    /// Vertex of each generator, in canonical order.
    gen_vertex: Vec<u32>,
    /// `offsets[w][g]`: first row of generator `g`'s block in the term at vertex `w`.
    offsets: Vec<Vec<usize>>,
}

/// Recovers the layout from the term alone: `t_v = dim (top P)_v` because
/// `top P_v = S_v`. The block-total assertion fails only if the term is not built
/// by [`projective_cover`](crate::resolution::projective_cover), which never happens inside this module.
fn layout(term: &Module) -> Layout {
    let algebra = term.algebra();
    let n = algebra.quiver().num_vertices();
    let (t, _) = top(term);
    let mut gen_vertex = Vec::new();
    for v in 0..n {
        for _ in 0..t.dim_at(v) {
            gen_vertex.push(v);
        }
    }
    let mut offsets = vec![Vec::with_capacity(gen_vertex.len()); n as usize];
    for w in 0..n {
        let mut off = 0;
        for &v in &gen_vertex {
            offsets[w as usize].push(off);
            off += algebra.paths_between(v, w).len();
        }
        assert_eq!(
            off,
            term.dim_at(w),
            "resolution term is not a canonical projective sum at vertex {w}; \
             this is a bug in auslander"
        );
    }
    Layout {
        gen_vertex,
        offsets,
    }
}

/// `dim Hom_A(term, n) = Σ_g dim N_{v_g}` by Yoneda.
fn hom_space_dim(lay: &Layout, n: &Module) -> usize {
    lay.gen_vertex.iter().map(|&v| n.dim_at(v)).sum()
}

/// The Yoneda basis of `Hom_A(term, n)`, in canonical (generator, index) order.
fn yoneda_basis(term: &Module, lay: &Layout, n: &Module) -> Vec<Morphism> {
    let algebra = term.algebra();
    let nv = algebra.quiver().num_vertices();
    let mut basis = Vec::new();
    for (g, &v) in lay.gen_vertex.iter().enumerate() {
        for j in 0..n.dim_at(v) {
            let mut maps: Vec<DenseMat> = (0..nv)
                .map(|w| DenseMat::zero(term.dim_at(w), n.dim_at(w)))
                .collect();
            for w in 0..nv {
                for (r, &b) in algebra.paths_between(v, w).iter().enumerate() {
                    let action = n
                        .word_action(&algebra.basis()[b])
                        .expect("algebra basis words are valid in their own quiver");
                    for c in 0..n.dim_at(w) {
                        maps[w as usize].set(lay.offsets[w as usize][g] + r, c, action.get(j, c));
                    }
                }
            }
            basis.push(Morphism::new(term, n, maps).expect("Yoneda basis element is A-linear"));
        }
    }
    basis
}

/// Coordinates of `f: term → n` in the Yoneda basis: the trivial path `e_v` is the
/// first basis path of every `(v, v)` block, so the coordinate block of generator `g`
/// is row `offsets[v_g][g]` of `f` at `v_g`.
fn coordinates(f: &Morphism, lay: &Layout, n: &Module) -> Vec<Fp> {
    let mut coords = Vec::new();
    for (g, &v) in lay.gen_vertex.iter().enumerate() {
        let row = lay.offsets[v as usize][g];
        for j in 0..n.dim_at(v) {
            coords.push(f.map_at(v).get(row, j));
        }
    }
    coords
}

/// Rank of `δ^i: Hom(P_i, N) → Hom(P_{i+1}, N)`, `f ↦ d.then(f)`, in Yoneda bases.
fn delta_rank(d: &Morphism, term: &Module, lay: &Layout, next_lay: &Layout, n: &Module) -> usize {
    let field = term.field();
    if hom_space_dim(next_lay, n) == 0 {
        return 0;
    }
    let rows: Vec<Vec<Fp>> = yoneda_basis(term, lay, n)
        .iter()
        .map(|f| {
            let composite = d
                .then(f)
                .expect("internal endpoint invariant: d targets the term f leaves");
            coordinates(&composite, next_lay, n)
        })
        .collect();
    if rows.is_empty() {
        return 0;
    }
    DenseMat::from_rows(&rows).rank(&field)
}

fn check_pair(m: &Module, n: &Module) -> Result<(), ExtError> {
    if !Arc::ptr_eq(m.algebra(), n.algebra()) {
        return Err(ExtError::DifferentAlgebras);
    }
    Ok(())
}

/// `[dim Ext^0(m, n), …, dim Ext^max_k(m, n)]`, each entry exact (see the module
/// docs: the resolution prefix is always long enough). Errors when the modules
/// do not share one algebra.
pub fn ext_table(m: &Module, n: &Module, max_k: usize) -> Result<Vec<usize>, ExtError> {
    check_pair(m, n)?;
    let res = resolve(m, max_k + 1);
    let layouts: Vec<Layout> = res.terms.iter().map(layout).collect();
    // A finite resolution continues with zero terms: Hom = 0 and δ = 0 beyond it.
    let h: Vec<usize> = (0..=max_k)
        .map(|i| layouts.get(i).map_or(0, |lay| hom_space_dim(lay, n)))
        .collect();
    let ranks: Vec<usize> = (0..=max_k)
        .map(|i| {
            if i + 1 < res.terms.len() {
                delta_rank(&res.maps[i], &res.terms[i], &layouts[i], &layouts[i + 1], n)
            } else {
                0
            }
        })
        .collect();
    Ok((0..=max_k)
        .map(|k| {
            let kernel_dim = h[k] - ranks[k];
            let boundary = if k == 0 { 0 } else { ranks[k - 1] };
            assert!(
                kernel_dim >= boundary,
                "im δ^{} ⊄ ker δ^{k}; this is a bug in auslander",
                k.wrapping_sub(1)
            );
            kernel_dim - boundary
        })
        .collect())
}

/// `dim Ext^k_A(m, n)`, exact for every `k`. `Ext^0` is `dim Hom_A(m, n)`.
/// Errors when the modules do not share one algebra.
pub fn ext_dim(m: &Module, n: &Module, k: usize) -> Result<usize, ExtError> {
    Ok(ext_table(m, n, k)?[k])
}

/// The global dimension of the algebra, resolved up to `bound` differentials.
///
/// Infallible on valid input: the simples it resolves are constructed here over
/// the given algebra, so no endpoint mismatch can arise.
/// For a finite-dimensional algebra `gldim A = pd (A/rad A) = max_v pd S_v`: every
/// module has a finite composition series with simple factors, so the supremum of
/// projective dimensions is attained on the simples. Returns `Exact` when every
/// simple resolves within `bound`, otherwise `AtLeast(bound + 1)` (the minimal
/// resolution of some simple has a nonzero syzygy past the bound).
pub fn global_dimension(algebra: &Arc<Algebra>, bound: usize) -> Bounded<usize> {
    let mut max = 0usize;
    let mut cut = false;
    for v in 0..algebra.quiver().num_vertices() {
        match projective_dimension(&Module::simple(algebra, v), bound) {
            Bounded::Exact(d) => max = max.max(d),
            Bounded::AtLeast(_) => cut = true,
        }
    }
    if cut {
        Bounded::AtLeast(bound + 1)
    } else {
        Bounded::Exact(max)
    }
}

/// The cochain morphism `term -> n` whose canonical coordinates are `coords`:
/// generator `g` at vertex `v` takes the coordinate block of length
/// `dim N_v`, and the basis path `p: v -> w` of its summand maps to that
/// block times `N(p)`.
///
/// # Panics
/// Panics unless `coords` has one entry per (generator, basis vector) pair.
fn cochain_from_coordinates(term: &Module, lay: &Layout, n: &Module, coords: &[Fp]) -> Morphism {
    let algebra = term.algebra();
    let field = term.field();
    let nv = algebra.quiver().num_vertices();
    let mut maps: Vec<DenseMat> = (0..nv)
        .map(|w| DenseMat::zero(term.dim_at(w), n.dim_at(w)))
        .collect();
    let mut offset = 0;
    for (g, &v) in lay.gen_vertex.iter().enumerate() {
        let block = &coords[offset..offset + n.dim_at(v)];
        offset += n.dim_at(v);
        for w in 0..nv {
            for (r, &b) in algebra.paths_between(v, w).iter().enumerate() {
                let action = n
                    .word_action(&algebra.basis()[b])
                    .expect("algebra basis words are valid in their own quiver");
                for c in 0..n.dim_at(w) {
                    let mut acc = Fp::ZERO;
                    for (j, &x) in block.iter().enumerate() {
                        acc = field.add(acc, field.mul(x, action.get(j, c)));
                    }
                    maps[w as usize].set(lay.offsets[w as usize][g] + r, c, acc);
                }
            }
        }
    }
    assert_eq!(
        offset,
        coords.len(),
        "cochain_from_coordinates: coordinate count"
    );
    Morphism::new(term, n, maps).expect("generator images extend to an A-linear map")
}

/// The matrix of `delta: Hom(term, N) -> Hom(next, N)`, `f -> d.then(f)`, in
/// Yoneda bases: one row per basis element of the source cochain space.
fn delta_matrix(
    d: &Morphism,
    term: &Module,
    lay: &Layout,
    next_lay: &Layout,
    n: &Module,
) -> DenseMat {
    let mut out = DenseMat::zero(hom_space_dim(lay, n), hom_space_dim(next_lay, n));
    for (i, f) in yoneda_basis(term, lay, n).iter().enumerate() {
        let composite = d
            .then(f)
            .expect("internal endpoint invariant: d targets the term f leaves");
        for (j, &v) in coordinates(&composite, next_lay, n).iter().enumerate() {
            out.set(i, j, v);
        }
    }
    out
}

/// `coords * rows` as a vector of length `rows.cols()`.
fn combine_rows(rows: &DenseMat, coords: &[Fp], field: &PrimeField) -> Vec<Fp> {
    let mut out = vec![Fp::ZERO; rows.cols()];
    for (k, &c) in coords.iter().enumerate() {
        if c.is_zero() {
            continue;
        }
        for (j, out_j) in out.iter_mut().enumerate() {
            *out_j = field.add(*out_j, field.mul(c, rows.get(k, j)));
        }
    }
    out
}

/// `top` stacked above `bottom`; both must share a column count.
fn stack_rows(top: &DenseMat, bottom: &DenseMat) -> DenseMat {
    let rows: Vec<Vec<Fp>> = (0..top.rows())
        .map(|r| top.row(r).to_vec())
        .chain((0..bottom.rows()).map(|r| bottom.row(r).to_vec()))
        .collect();
    if rows.is_empty() {
        DenseMat::zero(0, top.cols())
    } else {
        DenseMat::from_rows(&rows)
    }
}

/// The lift `phi: term -> T` with `phi.then(through) = rhs`, for `through: T -> B`
/// and `rhs: term -> B` with `term` a canonical projective sum. Each generator
/// image solves one linear system with free variables zeroed, so the lift is
/// deterministic.
///
/// # Panics
/// Panics when a generator image of `rhs` lies outside the image of `through`;
/// callers only lift maps that land there.
pub(crate) fn lift_through(term: &Module, through: &Morphism, rhs: &Morphism) -> Morphism {
    debug_assert!(rhs.source().ptr_eq(term));
    debug_assert!(rhs.target().ptr_eq(through.target()));
    let field = term.field();
    let lay = layout(term);
    let mut coords = Vec::new();
    for (g, &v) in lay.gen_vertex.iter().enumerate() {
        let row = lay.offsets[v as usize][g];
        let x = through
            .map_at(v)
            .transpose()
            .solve(rhs.map_at(v).row(row), &field)
            .expect("lift_through: the right side lands in the image of the lifted-through map");
        coords.extend(x);
    }
    cochain_from_coordinates(term, &lay, through.source(), &coords)
}

/// Rejected Ext class input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExtClassError {
    /// The operands' spaces are not compatible: compatibility needs
    /// pointer-equal sources, pointer-equal targets, and equal degrees.
    IncompatibleSpaces,
    /// The left class's target module is not the right class's source module
    /// (by [`Module::ptr_eq`]), so the Yoneda product is undefined.
    MiddleMismatch,
    /// The cochain's source is not the space's cochain term (by
    /// [`Module::ptr_eq`]).
    SourceMismatch,
    /// The cochain's target is not the space's target module (by
    /// [`Module::ptr_eq`]).
    TargetMismatch,
    /// The cochain is not a cocycle: `d_{k+1}.then(f)` is nonzero. The field
    /// holds the composite's coordinates in the degree `k + 1` cochain basis.
    NotCocycle { composite: Vec<Fp> },
    /// The coordinate vector's length is not the space's dimension.
    CoordinateCountMismatch { expected: usize, got: usize },
    /// The coordinate at this index is not a canonical element of the
    /// modules' field.
    NonCanonicalCoordinate { index: usize },
    /// The identity class lives only in `Ext^0(M, M)`: degree 0 with
    /// pointer-equal endpoints.
    NotDegreeZeroEndo,
}

impl fmt::Display for ExtClassError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IncompatibleSpaces => f.write_str("the classes live in incompatible Ext spaces"),
            Self::MiddleMismatch => {
                f.write_str("the left class's target module is not the right class's source module")
            }
            Self::SourceMismatch => {
                f.write_str("the cochain's source is not the space's cochain term")
            }
            Self::TargetMismatch => {
                f.write_str("the cochain's target is not the space's target module")
            }
            Self::NotCocycle { .. } => f.write_str("the cochain is not a cocycle"),
            Self::CoordinateCountMismatch { expected, got } => write!(
                f,
                "coordinate vector has {got} entries, the space has dimension {expected}"
            ),
            Self::NonCanonicalCoordinate { index } => write!(
                f,
                "coordinate {index} is not a canonical element of the modules' field"
            ),
            Self::NotDegreeZeroEndo => f.write_str("the identity class lives only in Ext^0(M, M)"),
        }
    }
}

impl std::error::Error for ExtClassError {}

struct ExtSpaceInner {
    source: Module,
    target: Module,
    degree: usize,
    // resolve(source, degree + 1); minimal, so recomputation gives the same
    // matrices.
    resolution: ProjectiveResolution,
    // P_k, or the zero module when the finite resolution ends before k.
    term: Module,
    // RREF basis of Z^k = ker delta^k in generator-block coordinates.
    cocycles: DenseMat,
    // RREF basis of B^k = im delta^{k-1}; zero rows at degree 0.
    coboundaries: DenseMat,
    // Deterministic complement of B^k in Z^k by the crate-wide rule.
    complement: DenseMat,
    // One cocycle morphism P_k -> N per complement row.
    reps: Vec<Morphism>,
}

/// `Ext^k(M, N)` as an explicit vector space: the resolution prefix, RREF
/// cocycle and coboundary bases in generator-block coordinates, the
/// deterministic complement of the coboundaries inside the cocycles, and one
/// representative cocycle per complement row.
///
/// Two spaces are compatible when their sources are [`Module::ptr_eq`], their
/// targets are [`Module::ptr_eq`], and their degrees are equal. Every stored
/// matrix is deterministic, so recomputed compatible spaces carry identical
/// bases and class coordinates transport verbatim.
///
/// Cloning is cheap (a reference count bump).
#[derive(Clone)]
pub struct ExtSpace(Arc<ExtSpaceInner>);

impl fmt::Debug for ExtSpace {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ExtSpace")
            .field("source_dim", &self.0.source.dim_vector())
            .field("target_dim", &self.0.target.dim_vector())
            .field("degree", &self.0.degree)
            .field("dim", &self.dim())
            .finish()
    }
}

impl ExtSpace {
    /// Builds `Ext^k(m, n)` from the minimal resolution prefix
    /// `resolve(m, k + 1)`. Zero modules give zero spaces. A finite resolution
    /// that ends before degree `k` gives the zero space with the zero module
    /// as cochain term. Errors when the modules do not share one algebra.
    pub fn new(m: &Module, n: &Module, k: usize) -> Result<ExtSpace, ExtError> {
        check_pair(m, n)?;
        let field = m.field();
        let resolution = resolve(m, k + 1);
        let (term, cocycles, coboundaries) = if k < resolution.terms.len() {
            let term = resolution.terms[k].clone();
            let lay = layout(&term);
            let width = hom_space_dim(&lay, n);
            let cocycles = if k + 1 < resolution.terms.len() {
                let next_lay = layout(&resolution.terms[k + 1]);
                let delta = delta_matrix(&resolution.maps[k], &term, &lay, &next_lay, n);
                delta
                    .transpose()
                    .kernel_basis(&field)
                    .row_space_basis(&field)
            } else {
                DenseMat::identity(width)
            };
            let coboundaries = if k == 0 {
                DenseMat::zero(0, width)
            } else {
                let prev = &resolution.terms[k - 1];
                let prev_lay = layout(prev);
                delta_matrix(&resolution.maps[k - 1], prev, &prev_lay, &lay, n)
                    .row_space_basis(&field)
            };
            (term, cocycles, coboundaries)
        } else {
            (
                Module::zero(m.algebra()),
                DenseMat::zero(0, 0),
                DenseMat::zero(0, 0),
            )
        };
        let cocycles_t = cocycles.transpose();
        for r in 0..coboundaries.rows() {
            assert!(
                cocycles_t.solve(coboundaries.row(r), &field).is_some(),
                "im delta^{} is not contained in ker delta^{k}; this is a bug in auslander",
                k.wrapping_sub(1)
            );
        }
        let complement = deterministic_complement(&cocycles, &coboundaries, &field);
        let lay = layout(&term);
        let reps = (0..complement.rows())
            .map(|r| cochain_from_coordinates(&term, &lay, n, complement.row(r)))
            .collect();
        Ok(ExtSpace(Arc::new(ExtSpaceInner {
            source: m.clone(),
            target: n.clone(),
            degree: k,
            resolution,
            term,
            cocycles,
            coboundaries,
            complement,
            reps,
        })))
    }

    /// `dim_k Ext^k(M, N)`: the number of complement rows. Equals
    /// [`ext_dim`]`(m, n, k)`.
    #[inline]
    pub fn dim(&self) -> usize {
        self.0.complement.rows()
    }

    /// The source module `M`.
    #[inline]
    pub fn source(&self) -> &Module {
        &self.0.source
    }

    /// The target module `N`.
    #[inline]
    pub fn target(&self) -> &Module {
        &self.0.target
    }

    /// The cohomological degree `k`.
    #[inline]
    pub fn degree(&self) -> usize {
        self.0.degree
    }

    /// The source of degree-`k` cochains: `P_k` of the minimal resolution, or
    /// the zero module when the finite resolution ends before `k`.
    #[inline]
    pub fn cochain_term(&self) -> &Module {
        &self.0.term
    }

    /// One representative cocycle `P_k -> N` per complement row, in row order.
    #[inline]
    pub fn representatives(&self) -> &[Morphism] {
        &self.0.reps
    }

    /// The RREF basis of `Z^k = ker delta^k` in generator-block coordinates,
    /// one vector per row.
    #[inline]
    pub fn cocycle_basis(&self) -> &DenseMat {
        &self.0.cocycles
    }

    /// The RREF basis of `B^k = im delta^{k-1}` in generator-block
    /// coordinates, one vector per row; no rows at degree 0.
    #[inline]
    pub fn coboundary_basis(&self) -> &DenseMat {
        &self.0.coboundaries
    }

    /// The complement rows kept by the crate-wide rule, in scan order; class
    /// coordinates index these rows.
    #[inline]
    pub fn complement_basis(&self) -> &DenseMat {
        &self.0.complement
    }

    /// The stored resolution prefix `resolve(source, degree + 1)`.
    #[inline]
    pub(crate) fn resolution(&self) -> &ProjectiveResolution {
        &self.0.resolution
    }

    /// Whether class coordinates transport verbatim between the two spaces:
    /// sources pointer-equal, targets pointer-equal, degrees equal.
    pub fn is_compatible(&self, other: &ExtSpace) -> bool {
        self.0.source.ptr_eq(&other.0.source)
            && self.0.target.ptr_eq(&other.0.target)
            && self.0.degree == other.0.degree
    }

    /// The zero class of this space.
    pub fn zero_class(&self) -> ExtClass {
        ExtClass {
            space: self.clone(),
            coords: vec![Fp::ZERO; self.dim()],
        }
    }

    /// The Yoneda unit: the class of the augmentation in `Ext^0(M, M)`.
    /// Errors unless the space has degree 0 and pointer-equal endpoints.
    pub fn identity_class(&self) -> Result<ExtClass, ExtClassError> {
        if self.0.degree != 0 || !self.0.source.ptr_eq(&self.0.target) {
            return Err(ExtClassError::NotDegreeZeroEndo);
        }
        self.class_from_cocycle(&self.0.resolution.augmentation)
    }

    /// The class of the cocycle `f: P_k -> N`: checks both endpoints by
    /// [`Module::ptr_eq`], checks `d_{k+1}.then(f) = 0`, and reduces modulo
    /// the coboundaries against the stacked complement-plus-RREF system.
    pub fn class_from_cocycle(&self, f: &Morphism) -> Result<ExtClass, ExtClassError> {
        let inner = &self.0;
        if !f.source().ptr_eq(&inner.term) {
            return Err(ExtClassError::SourceMismatch);
        }
        if !f.target().ptr_eq(&inner.target) {
            return Err(ExtClassError::TargetMismatch);
        }
        let field = inner.source.field();
        if inner.degree + 1 < inner.resolution.terms.len() {
            let composite = inner.resolution.maps[inner.degree]
                .then(f)
                .expect("d_{k+1} targets the cochain term");
            if !composite.is_zero() {
                let next_lay = layout(&inner.resolution.terms[inner.degree + 1]);
                return Err(ExtClassError::NotCocycle {
                    composite: coordinates(&composite, &next_lay, &inner.target),
                });
            }
        }
        let lay = layout(&inner.term);
        let f_coords = coordinates(f, &lay, &inner.target);
        let stacked = stack_rows(&inner.complement, &inner.coboundaries);
        let x = stacked
            .transpose()
            .solve(&f_coords, &field)
            .expect("a cocycle lies in the span of complement plus coboundaries; this is a bug in auslander");
        Ok(ExtClass {
            space: self.clone(),
            coords: x[..inner.complement.rows()].to_vec(),
        })
    }

    /// The class with the given coordinates over the complement basis.
    /// Errors on a wrong length and on entries that are not canonical
    /// elements of the modules' field.
    pub fn class_from_coordinates(&self, coords: &[Fp]) -> Result<ExtClass, ExtClassError> {
        if coords.len() != self.dim() {
            return Err(ExtClassError::CoordinateCountMismatch {
                expected: self.dim(),
                got: coords.len(),
            });
        }
        let modulus = self.0.source.field().modulus();
        for (index, c) in coords.iter().enumerate() {
            if c.raw() >= modulus {
                return Err(ExtClassError::NonCanonicalCoordinate { index });
            }
        }
        Ok(ExtClass {
            space: self.clone(),
            coords: coords.to_vec(),
        })
    }
}

/// An element of an [`ExtSpace`]: coordinates over the complement basis.
///
/// Equality and arithmetic require compatible spaces (see
/// [`ExtSpace::is_compatible`]); incompatible operands are a typed
/// [`ExtClassError`], never `false`.
#[derive(Clone, Debug)]
pub struct ExtClass {
    space: ExtSpace,
    coords: Vec<Fp>,
}

impl ExtClass {
    /// The space the class lives in.
    #[inline]
    pub fn space(&self) -> &ExtSpace {
        &self.space
    }

    /// The coordinates over the complement basis.
    #[inline]
    pub fn coordinates(&self) -> &[Fp] {
        &self.coords
    }

    /// Whether every coordinate is zero.
    pub fn is_zero(&self) -> bool {
        self.coords.iter().all(|c| c.is_zero())
    }

    fn require_compatible(&self, other: &ExtClass) -> Result<(), ExtClassError> {
        if !self.space.is_compatible(&other.space) {
            return Err(ExtClassError::IncompatibleSpaces);
        }
        Ok(())
    }

    /// The sum of two classes. Errors unless the spaces are compatible.
    pub fn add(&self, other: &ExtClass) -> Result<ExtClass, ExtClassError> {
        self.require_compatible(other)?;
        let field = self.space.0.source.field();
        let coords = self
            .coords
            .iter()
            .zip(&other.coords)
            .map(|(&a, &b)| field.add(a, b))
            .collect();
        Ok(ExtClass {
            space: self.space.clone(),
            coords,
        })
    }

    /// The additive inverse.
    pub fn neg(&self) -> ExtClass {
        let field = self.space.0.source.field();
        ExtClass {
            space: self.space.clone(),
            coords: self.coords.iter().map(|&c| field.neg(c)).collect(),
        }
    }

    /// The scalar multiple. The scalar must be a canonical element of the
    /// modules' field.
    pub fn scale(&self, c: Fp) -> ExtClass {
        let field = self.space.0.source.field();
        ExtClass {
            space: self.space.clone(),
            coords: self.coords.iter().map(|&x| field.mul(c, x)).collect(),
        }
    }

    /// Whether the classes are equal. Errors unless the spaces are
    /// compatible, so incompatible operands never read as unequal.
    pub fn equals(&self, other: &ExtClass) -> Result<bool, ExtClassError> {
        self.require_compatible(other)?;
        Ok(self.coords == other.coords)
    }

    /// The representative cocycle `P_k -> N`: the complement-row combination
    /// of the coordinates.
    pub fn representative(&self) -> Morphism {
        let inner = &self.space.0;
        let field = inner.source.field();
        let row = combine_rows(&inner.complement, &self.coords, &field);
        let lay = layout(&inner.term);
        cochain_from_coordinates(&inner.term, &lay, &inner.target, &row)
    }

    /// The Yoneda product `Ext^m(M, N) x Ext^n(N, L) -> Ext^{m+n}(M, L)`,
    /// matching the endpoint order of [`Morphism::then`]. Errors when the
    /// middle modules disagree (by [`Module::ptr_eq`]).
    pub fn then(&self, other: &ExtClass) -> Result<ExtClass, ExtClassError> {
        self.then_with_witness(other).map(|(class, _)| class)
    }

    /// The Yoneda product together with the chain lifts that computed it.
    /// Errors when the middle modules disagree (by [`Module::ptr_eq`]).
    pub fn then_with_witness(
        &self,
        other: &ExtClass,
    ) -> Result<(ExtClass, ProductWitness), ExtClassError> {
        if !self.space.0.target.ptr_eq(&other.space.0.source) {
            return Err(ExtClassError::MiddleMismatch);
        }
        let n = other.space.0.degree;
        let product_space = ExtSpace::new(
            &self.space.0.source,
            &other.space.0.target,
            self.space.0.degree + n,
        )
        .expect("the product endpoints share one algebra through the middle module");
        let lifts = chain_lifts(self, other, &product_space);
        let g = other.representative();
        let h = lifts[n]
            .then(&g)
            .expect("the last lift targets the right class's cochain term");
        let class = product_space
            .class_from_cocycle(&h)
            .expect("a Yoneda product of cocycles is a cocycle");
        Ok((class, ProductWitness { lifts }))
    }
}

/// The chain terms `P^M_m, ..., P^M_{m+n}` and `P^N_0, ..., P^N_n` with their
/// differentials, extended by zero modules and zero maps past a finite
/// resolution, and the lifts `phi_i: P^M_{m+i} -> P^N_i` with
/// `phi_0.then(aug_N) = f` and `d^M_{m+i+1}.then(phi_i) = phi_{i+1}.then(d^N_{i+1})`.
/// Every lift solves per-generator systems with zeroed free variables, so the
/// family is deterministic.
fn chain_lifts(alpha: &ExtClass, beta: &ExtClass, product_space: &ExtSpace) -> Vec<Morphism> {
    let m = alpha.space.0.degree;
    let n = beta.space.0.degree;
    let deep = &product_space.0.resolution;
    debug_assert!(
        alpha
            .space
            .0
            .resolution
            .terms
            .iter()
            .zip(&deep.terms)
            .all(|(a, b)| a.dim_vector() == b.dim_vector()),
        "recomputed minimal resolution prefix disagrees; this is a bug in auslander"
    );
    let algebra = alpha.space.0.source.algebra();
    let chain_m: Vec<Module> = (m..=m + n)
        .map(|j| {
            if j < deep.terms.len() {
                deep.terms[j].clone()
            } else if j == m + n {
                product_space.0.term.clone()
            } else {
                Module::zero(algebra)
            }
        })
        .collect();
    let chain_dm: Vec<Morphism> = (0..n)
        .map(|i| {
            if m + i < deep.maps.len() {
                deep.maps[m + i].clone()
            } else {
                crate::hom::zero_morphism(&chain_m[i + 1], &chain_m[i])
                    .expect("chain terms share one algebra")
            }
        })
        .collect();
    let res_n = &beta.space.0.resolution;
    let chain_n: Vec<Module> = (0..=n)
        .map(|i| {
            if i < res_n.terms.len() {
                res_n.terms[i].clone()
            } else if i == n {
                beta.space.0.term.clone()
            } else {
                Module::zero(algebra)
            }
        })
        .collect();
    let chain_dn: Vec<Morphism> = (0..n)
        .map(|i| {
            if i < res_n.maps.len() {
                res_n.maps[i].clone()
            } else {
                crate::hom::zero_morphism(&chain_n[i + 1], &chain_n[i])
                    .expect("chain terms share one algebra")
            }
        })
        .collect();
    let rep = alpha.representative();
    let nv = algebra.quiver().num_vertices();
    let rep_maps: Vec<DenseMat> = (0..nv).map(|v| rep.map_at(v).clone()).collect();
    let f = Morphism::new(&chain_m[0], &beta.space.0.source, rep_maps)
        .expect("the recomputed resolution prefix matches, so the representative transports");
    let mut lifts = vec![lift_through(&chain_m[0], &res_n.augmentation, &f)];
    for i in 1..=n {
        let rhs = chain_dm[i - 1]
            .then(&lifts[i - 1])
            .expect("chain endpoints line up by construction");
        lifts.push(lift_through(&chain_m[i], &chain_dn[i - 1], &rhs));
    }
    lifts
}

/// The chain lifts behind one Yoneda product, `phi_i: P^M_{m+i} -> P^N_i` in
/// degree order.
#[derive(Clone, Debug)]
pub struct ProductWitness {
    lifts: Vec<Morphism>,
}

impl ProductWitness {
    /// The lifts in degree order, `phi_0` first.
    #[inline]
    pub fn lifts(&self) -> &[Morphism] {
        &self.lifts
    }

    /// Rechecks that the lifts tie `alpha` and `beta` to `product`: the two
    /// lift identity families, the reduction of `phi_n.then(g)` to the
    /// product coordinates by multiplication and coboundary membership, and
    /// that the product space's stored bases equal a fresh recomputation
    /// from the live endpoint modules, so a tampered complement or
    /// coboundary basis is rejected even when the reduction is trivial.
    pub fn verify(&self, alpha: &ExtClass, beta: &ExtClass, product: &ExtClass) -> bool {
        let m = alpha.space.0.degree;
        let n = beta.space.0.degree;
        if product.space.0.degree != m + n
            || !beta.space.0.source.ptr_eq(&alpha.space.0.target)
            || !product.space.0.source.ptr_eq(&alpha.space.0.source)
            || !product.space.0.target.ptr_eq(&beta.space.0.target)
            || self.lifts.len() != n + 1
            || product.coords.len() != product.space.dim()
        {
            return false;
        }
        let Ok(recomputed) = ExtSpace::new(&product.space.0.source, &product.space.0.target, m + n)
        else {
            return false;
        };
        if product.space.0.cocycles != recomputed.0.cocycles
            || product.space.0.coboundaries != recomputed.0.coboundaries
            || product.space.0.complement != recomputed.0.complement
        {
            return false;
        }
        let deep = &product.space.0.resolution;
        let res_n = &beta.space.0.resolution;
        let field = alpha.space.0.source.field();
        let nv = alpha.space.0.source.algebra().quiver().num_vertices();
        let rep = alpha.representative();
        let rep_maps: Vec<DenseMat> = (0..nv).map(|v| rep.map_at(v).clone()).collect();
        let Ok(f) = Morphism::new(self.lifts[0].source(), &beta.space.0.source, rep_maps) else {
            return false;
        };
        let Ok(lhs) = self.lifts[0].then(&res_n.augmentation) else {
            return false;
        };
        if lhs != f {
            return false;
        }
        for i in 0..n {
            let left = if m + i < deep.maps.len() {
                match deep.maps[m + i].then(&self.lifts[i]) {
                    Ok(x) => Some(x),
                    Err(_) => return false,
                }
            } else {
                None
            };
            let right = if i < res_n.maps.len() {
                match self.lifts[i + 1].then(&res_n.maps[i]) {
                    Ok(x) => Some(x),
                    Err(_) => return false,
                }
            } else {
                None
            };
            let ok = match (left, right) {
                (Some(l), Some(r)) => l == r,
                (Some(l), None) => l.is_zero(),
                (None, Some(r)) => r.is_zero(),
                (None, None) => true,
            };
            if !ok {
                return false;
            }
        }
        let g = beta.representative();
        let Ok(h) = self.lifts[n].then(&g) else {
            return false;
        };
        if !h.source().ptr_eq(&product.space.0.term) {
            return false;
        }
        let lay = layout(&product.space.0.term);
        let h_coords = coordinates(&h, &lay, &product.space.0.target);
        let expected = combine_rows(&product.space.0.complement, &product.coords, &field);
        let diff: Vec<Fp> = h_coords
            .iter()
            .zip(&expected)
            .map(|(&a, &b)| field.sub(a, b))
            .collect();
        let cob = &product.space.0.coboundaries;
        let Some(x) = cob.transpose().solve(&diff, &field) else {
            return false;
        };
        combine_rows(cob, &x, &field) == diff
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{
        an_with_relations, dual_numbers, kronecker, linear_an, radical_square_zero_cycle,
        truncated_poly,
    };
    use crate::field::PrimeField;
    use crate::hom::hom_dim;
    use crate::module::direct_sum;

    fn f5() -> PrimeField {
        PrimeField::new(5).unwrap()
    }

    // Right modules over linearly oriented A_3 (arrows a: 0 → 1, b: 1 → 2). The
    // nonsplit extension realized by arrow a is 0 → S_1 → M → S_0 → 0 with
    // M = P_0/rad² of dimension vector (1, 1, 0), top S_0 and socle S_1, so the
    // nonzero Ext group is Ext¹(S_0, S_1). In general dim Ext¹(S_i, S_j) equals
    // the number of arrows i → j (same pairing as for left modules over A^op read
    // backwards; ASS III.2.12 states it for right modules).
    #[test]
    fn a3_ext_1_between_simples_counts_arrows_source_to_target() {
        let field = f5();
        let algebra = linear_an(3, field);
        let simples: Vec<Module> = (0..3).map(|v| Module::simple(&algebra, v)).collect();
        for i in 0..3 {
            for j in 0..3 {
                let expected = usize::from(j == i + 1);
                assert_eq!(
                    ext_dim(&simples[i], &simples[j], 1).unwrap(),
                    expected,
                    "Ext¹(S_{i}, S_{j})"
                );
                for k in 2..=4 {
                    assert_eq!(
                        ext_dim(&simples[i], &simples[j], k).unwrap(),
                        0,
                        "Ext^{k}(S_{i}, S_{j}) over a gldim-1 algebra"
                    );
                }
            }
        }
        assert_eq!(ext_dim(&simples[1], &simples[0], 1).unwrap(), 0);
        assert_eq!(global_dimension(&algebra, 5), Bounded::Exact(1));
    }

    // kA_3/(ab), right modules: pd S_0 = 2 via 0 → P_2 → P_1 → P_0 → S_0 → 0.
    // Ext¹(S_i, S_j) = #arrows i → j gives Ext¹(S_0, S_1) = Ext¹(S_1, S_2) = 1;
    // Ext² is detected by the relation, on the ordered pair (source, target) of the
    // forbidden path: Hom(P_2, S_2) = k sits in degree 2 of the resolution of S_0
    // with zero δ on both sides, so Ext²(S_0, S_2) = 1. These values match the
    // QPA-verified facts (Ext¹(S_0, S_1) = 1, Ext²(S_0, S_2) = 1) on the same
    // ordered pairs, with no right-vs-left discrepancy.
    #[test]
    fn a3_mod_ab_ext_1_and_2_among_simples() {
        let field = f5();
        let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
        let simples: Vec<Module> = (0..3).map(|v| Module::simple(&algebra, v)).collect();
        for i in 0..3 {
            for j in 0..3 {
                let ext1 = usize::from(j == i + 1);
                let ext2 = usize::from(i == 0 && j == 2);
                assert_eq!(
                    ext_dim(&simples[i], &simples[j], 1).unwrap(),
                    ext1,
                    "Ext¹(S_{i}, S_{j})"
                );
                assert_eq!(
                    ext_dim(&simples[i], &simples[j], 2).unwrap(),
                    ext2,
                    "Ext²(S_{i}, S_{j})"
                );
                assert_eq!(ext_dim(&simples[i], &simples[j], 3).unwrap(), 0);
            }
        }
        assert_eq!(global_dimension(&algebra, 5), Bounded::Exact(2));
    }

    #[test]
    fn dual_numbers_ext_table_of_the_simple_is_all_ones() {
        let field = f5();
        let algebra = dual_numbers(field);
        let s = Module::simple(&algebra, 0);
        assert_eq!(ext_table(&s, &s, 4).unwrap(), vec![1, 1, 1, 1, 1]);
        assert_eq!(global_dimension(&algebra, 6), Bounded::AtLeast(7));
    }

    // k[x]/(x³) over F_3: the minimal resolution of S is Ω-periodic with period 2
    // (Ω S = rad P has dimension 2, Ω² S = soc P ≅ S), every term is P, and
    // Hom(P, S) = k with zero differentials throughout.
    #[test]
    fn truncated_poly_3_ext_table_of_the_simple_is_all_ones() {
        let field = PrimeField::new(3).unwrap();
        let algebra = truncated_poly(3, field).unwrap();
        let s = Module::simple(&algebra, 0);
        let res = resolve(&s, 5);
        for term in &res.terms {
            assert_eq!(term.dim_vector(), &[3]);
        }
        assert_eq!(ext_table(&s, &s, 4).unwrap(), vec![1, 1, 1, 1, 1]);
    }

    // Cycle 0 → 1 → 2 → 0 with rad² = 0, right modules: rad P_i = S_{i+1}, so
    // Ω S_i = S_{i+1} and the extension realized by the arrow i → i+1 gives
    // Ext¹(S_i, S_{i+1}) = 1 while Ext¹(S_i, S_{i-1}) = 0: the pairing again runs
    // from arrow source to arrow target.
    #[test]
    fn radical_square_zero_cycle_ext_1_follows_the_arrows() {
        let field = f5();
        let algebra = radical_square_zero_cycle(3, field);
        let simples: Vec<Module> = (0..3).map(|v| Module::simple(&algebra, v)).collect();
        for i in 0..3 {
            for j in 0..3 {
                let expected = usize::from(j == (i + 1) % 3);
                assert_eq!(
                    ext_dim(&simples[i], &simples[j], 1).unwrap(),
                    expected,
                    "Ext¹(S_{i}, S_{j})"
                );
            }
        }
        assert_eq!(global_dimension(&algebra, 4), Bounded::AtLeast(5));
    }

    // Regression against the old examples-db, which listed hereditary Kronecker
    // algebras as having infinite global dimension.
    #[test]
    fn kronecker_2_is_hereditary_with_global_dimension_1() {
        let algebra = kronecker(2, f5());
        assert_eq!(global_dimension(&algebra, 5), Bounded::Exact(1));
    }

    fn assorted_pairs() -> Vec<(Module, Module)> {
        let field = f5();
        let mut pairs = Vec::new();
        for algebra in [
            linear_an(3, field),
            an_with_relations(3, &[(0, 2)], field).unwrap(),
            dual_numbers(field),
            radical_square_zero_cycle(3, field),
        ] {
            let n = algebra.quiver().num_vertices();
            for v in 0..n {
                let s = Module::simple(&algebra, v);
                let p = Module::projective(&algebra, v);
                let i = Module::injective(&algebra, v);
                pairs.push((s.clone(), i.clone()));
                pairs.push((i, s.clone()));
                pairs.push((s.clone(), p.clone()));
                pairs.push((p, s));
            }
            let s0 = Module::simple(&algebra, 0);
            let i_last = Module::injective(&algebra, n - 1);
            let (sum, _, _) = direct_sum(&[&s0, &i_last]);
            pairs.push((sum.clone(), s0));
            pairs.push((sum.clone(), sum));
        }
        pairs
    }

    #[test]
    fn ext_0_equals_hom_dim() {
        for (m, n) in assorted_pairs() {
            assert_eq!(
                ext_dim(&m, &n, 0).unwrap(),
                hom_dim(&m, &n).unwrap(),
                "Ext⁰ with dim m = {:?}, dim n = {:?}",
                m.dim_vector(),
                n.dim_vector()
            );
        }
    }

    // The Yoneda basis must agree with the generic commuting-square solver: same
    // dimension for Hom(P, N) on every resolution term, and the canonical
    // coordinates of the Yoneda basis form the identity matrix.
    #[test]
    fn yoneda_basis_agrees_with_generic_hom_on_resolution_terms() {
        let field = f5();
        for (m, n) in assorted_pairs() {
            let res = resolve(&m, 2);
            for term in &res.terms {
                let lay = layout(term);
                assert_eq!(hom_space_dim(&lay, &n), hom_dim(term, &n).unwrap());
                let basis = yoneda_basis(term, &lay, &n);
                for (i, f) in basis.iter().enumerate() {
                    let coords = coordinates(f, &lay, &n);
                    for (c, &val) in coords.iter().enumerate() {
                        let expected = if c == i { field.one() } else { field.zero() };
                        assert_eq!(val, expected, "coordinate {c} of basis element {i}");
                    }
                }
            }
        }
    }

    #[test]
    fn ext_beyond_a_finite_resolution_is_zero() {
        let field = f5();
        let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
        let s0 = Module::simple(&algebra, 0);
        let s2 = Module::simple(&algebra, 2);
        assert_eq!(ext_table(&s0, &s2, 6).unwrap(), vec![0, 0, 1, 0, 0, 0, 0]);
    }
}

#[cfg(test)]
mod ext_class_tests {
    use super::*;
    use crate::algebra::{
        an_with_relations, commutative_square, dual_numbers, linear_an, truncated_poly,
    };
    use crate::decompose::add_morphisms;
    use crate::field::PrimeField;
    use crate::hom::{hom_dim, zero_morphism};
    use crate::module::direct_sum;

    fn f5() -> PrimeField {
        PrimeField::new(5).unwrap()
    }

    fn f2() -> PrimeField {
        PrimeField::new(2).unwrap()
    }

    fn unit(dim: usize, k: usize, field: &PrimeField) -> Vec<Fp> {
        let mut v = vec![field.zero(); dim];
        v[k] = field.one();
        v
    }

    fn basis_class(space: &ExtSpace, k: usize) -> ExtClass {
        let field = space.source().field();
        space
            .class_from_coordinates(&unit(space.dim(), k, &field))
            .unwrap()
    }

    #[test]
    fn ext_space_dim_matches_ext_dim_and_hom_dim_on_fixtures() {
        let field = f5();
        for algebra in [
            truncated_poly(3, field).unwrap(),
            commutative_square(field),
            linear_an(3, field),
            an_with_relations(3, &[(0, 2)], field).unwrap(),
            dual_numbers(field),
        ] {
            let nv = algebra.quiver().num_vertices();
            let mut modules: Vec<Module> = (0..nv).map(|v| Module::simple(&algebra, v)).collect();
            modules.push(Module::projective(&algebra, 0));
            modules.push(Module::injective(&algebra, nv - 1));
            let s0 = Module::simple(&algebra, 0);
            let i_last = Module::injective(&algebra, nv - 1);
            modules.push(direct_sum(&[&s0, &i_last]).0);
            for m in &modules {
                for n in &modules {
                    for k in 0..=3 {
                        let space = ExtSpace::new(m, n, k).unwrap();
                        assert_eq!(
                            space.dim(),
                            ext_dim(m, n, k).unwrap(),
                            "dim m = {:?}, dim n = {:?}, k = {k}",
                            m.dim_vector(),
                            n.dim_vector()
                        );
                        if k == 0 {
                            assert_eq!(space.dim(), hom_dim(m, n).unwrap());
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn truncated_poly_3_ext_spaces_are_one_dimensional_over_f5_and_f2() {
        for field in [f5(), f2()] {
            let algebra = truncated_poly(3, field).unwrap();
            let s = Module::simple(&algebra, 0);
            for k in 0..=4 {
                let space = ExtSpace::new(&s, &s, k).unwrap();
                assert_eq!(space.dim(), 1, "Ext^{k}(S, S) over F_{}", field.modulus());
                assert_eq!(space.dim(), ext_dim(&s, &s, k).unwrap());
            }
        }
    }

    #[test]
    fn identity_classes_are_yoneda_units() {
        let field = f5();
        let x3 = truncated_poly(3, field).unwrap();
        let s = Module::simple(&x3, 0);
        let a3 = an_with_relations(3, &[(0, 2)], field).unwrap();
        let s0 = Module::simple(&a3, 0);
        let s1 = Module::simple(&a3, 1);
        let s2 = Module::simple(&a3, 2);
        let cases: Vec<(Module, Module, usize)> = vec![
            (s.clone(), s.clone(), 0),
            (s.clone(), s.clone(), 1),
            (s.clone(), s.clone(), 2),
            (s0.clone(), s1.clone(), 1),
            (s0.clone(), s2.clone(), 2),
            (s1.clone(), s2.clone(), 1),
        ];
        for (m, n, k) in cases {
            let space = ExtSpace::new(&m, &n, k).unwrap();
            assert!(space.dim() > 0, "fixture case has a nonzero space");
            let alpha = basis_class(&space, 0);
            let id_m = ExtSpace::new(&m, &m, 0).unwrap().identity_class().unwrap();
            let id_n = ExtSpace::new(&n, &n, 0).unwrap().identity_class().unwrap();
            let left = id_m.then(&alpha).unwrap();
            let right = alpha.then(&id_n).unwrap();
            assert!(left.equals(&alpha).unwrap(), "left unit at degree {k}");
            assert!(right.equals(&alpha).unwrap(), "right unit at degree {k}");
        }
    }

    // Over k[x]/(x^3) the differentials of the minimal resolution of S
    // alternate right multiplication by x and by x^2. The degree-1 lift of
    // the Ext^1 generator sends the generator of P_2 into the radical, so
    // composing with a cocycle P_1 -> S kills it: the Yoneda square of the
    // degree-1 class is zero in every characteristic. The Ext algebra is
    // k[z] tensor the exterior algebra on y, so every product involving the
    // degree-2 generator z is nonzero.
    #[test]
    fn truncated_poly_3_yoneda_products_match_the_ext_algebra() {
        for field in [f5(), f2()] {
            let algebra = truncated_poly(3, field).unwrap();
            let s = Module::simple(&algebra, 0);
            let ext1 = ExtSpace::new(&s, &s, 1).unwrap();
            let ext2 = ExtSpace::new(&s, &s, 2).unwrap();
            let xi = basis_class(&ext1, 0);
            let chi = basis_class(&ext2, 0);
            assert!(
                xi.then(&xi).unwrap().is_zero(),
                "y^2 = 0 over F_{}",
                field.modulus()
            );
            assert!(!xi.then(&chi).unwrap().is_zero(), "y z is nonzero");
            assert!(!chi.then(&xi).unwrap().is_zero(), "z y is nonzero");
            assert!(!chi.then(&chi).unwrap().is_zero(), "z^2 is nonzero");
            let (product, witness) = xi.then_with_witness(&chi).unwrap();
            assert!(witness.verify(&xi, &chi, &product));
        }
    }

    // Over k[x]/(x^2) the Ext algebra of the simple is the polynomial ring
    // on the degree-1 class, so every Yoneda power is nonzero.
    #[test]
    fn dual_numbers_yoneda_powers_of_the_degree_one_class_are_nonzero() {
        let algebra = dual_numbers(f5());
        let s = Module::simple(&algebra, 0);
        let ext1 = ExtSpace::new(&s, &s, 1).unwrap();
        let xi = basis_class(&ext1, 0);
        let square = xi.then(&xi).unwrap();
        assert!(!square.is_zero(), "y^2 is nonzero over k[x]/(x^2)");
        assert!(!square.then(&xi).unwrap().is_zero(), "y^3 is nonzero");
    }

    // Ext^1(S_0, S_1) x Ext^1(S_1, S_2) -> Ext^2(S_0, S_2) over kA_3/(ab):
    // both lifts are identities on the shared projective terms, so the
    // product is the Ext^2 generator detected by the relation. On the
    // commutative square the product Ext^1(S_0, S_1) x Ext^1(S_1, S_3) ->
    // Ext^2(S_0, S_3) has rank 1 (QPA-verified).
    #[test]
    fn ext1_times_ext1_is_nonzero_on_relation_detected_pairs() {
        let field = f5();
        let a3 = an_with_relations(3, &[(0, 2)], field).unwrap();
        let s0 = Module::simple(&a3, 0);
        let s1 = Module::simple(&a3, 1);
        let s2 = Module::simple(&a3, 2);
        let alpha = basis_class(&ExtSpace::new(&s0, &s1, 1).unwrap(), 0);
        let beta = basis_class(&ExtSpace::new(&s1, &s2, 1).unwrap(), 0);
        let product = alpha.then(&beta).unwrap();
        assert_eq!(product.space().dim(), 1);
        assert!(!product.is_zero(), "Ext^1 . Ext^1 -> Ext^2 over kA_3/(ab)");
        let square = commutative_square(field);
        let t0 = Module::simple(&square, 0);
        let t1 = Module::simple(&square, 1);
        let t3 = Module::simple(&square, 3);
        let a = basis_class(&ExtSpace::new(&t0, &t1, 1).unwrap(), 0);
        let b = basis_class(&ExtSpace::new(&t1, &t3, 1).unwrap(), 0);
        let ab = a.then(&b).unwrap();
        assert_eq!(ab.space().dim(), 1);
        assert!(
            !ab.is_zero(),
            "the commutative square relation pairs 0 -> 3"
        );
    }

    #[test]
    fn yoneda_products_are_bilinear_on_small_cases() {
        let field = f5();
        let a3 = an_with_relations(3, &[(0, 2)], field).unwrap();
        let dn = dual_numbers(field);
        let cases: Vec<(ExtClass, ExtClass)> = {
            let s0 = Module::simple(&a3, 0);
            let s1 = Module::simple(&a3, 1);
            let s2 = Module::simple(&a3, 2);
            let s = Module::simple(&dn, 0);
            vec![
                (
                    basis_class(&ExtSpace::new(&s0, &s1, 1).unwrap(), 0),
                    basis_class(&ExtSpace::new(&s1, &s2, 1).unwrap(), 0),
                ),
                (
                    basis_class(&ExtSpace::new(&s, &s, 1).unwrap(), 0),
                    basis_class(&ExtSpace::new(&s, &s, 1).unwrap(), 0),
                ),
            ]
        };
        for (alpha, beta) in cases {
            let two = field.elem(2);
            let three = field.elem(3);
            let product = alpha.then(&beta).unwrap();
            let doubled = alpha.scale(two);
            let sum = alpha.add(&doubled).unwrap();
            let left = sum.then(&beta).unwrap();
            let right = product.add(&doubled.then(&beta).unwrap()).unwrap();
            assert!(left.equals(&right).unwrap(), "additivity on the left");
            let scaled_left = alpha.scale(three).then(&beta).unwrap();
            assert!(scaled_left.equals(&product.scale(three)).unwrap());
            let scaled_right = alpha.then(&beta.scale(three)).unwrap();
            assert!(scaled_right.equals(&product.scale(three)).unwrap());
            let negated = alpha.neg().then(&beta).unwrap();
            assert!(negated.equals(&product.neg()).unwrap());
            let zero = alpha.space().zero_class().then(&beta).unwrap();
            assert!(zero.is_zero(), "the zero class annihilates products");
        }
    }

    #[test]
    fn adding_a_coboundary_does_not_change_the_class() {
        let field = f5();
        let mut saw_nonzero_coboundary = false;
        for algebra in [
            truncated_poly(3, field).unwrap(),
            an_with_relations(3, &[(0, 2)], field).unwrap(),
            commutative_square(field),
        ] {
            let nv = algebra.quiver().num_vertices();
            for v in 0..nv {
                let s = Module::simple(&algebra, v);
                for w in 0..nv {
                    for n in [
                        Module::projective(&algebra, w),
                        Module::injective(&algebra, w),
                    ] {
                        for k in 1..=2 {
                            let space = ExtSpace::new(&s, &n, k).unwrap();
                            let cob = space.coboundary_basis();
                            if cob.rows() == 0 {
                                continue;
                            }
                            saw_nonzero_coboundary = true;
                            let lay = layout(space.cochain_term());
                            let mut classes = vec![space.zero_class()];
                            for i in 0..space.dim() {
                                classes.push(basis_class(&space, i));
                            }
                            for class in &classes {
                                let rep = class.representative();
                                for r in 0..cob.rows() {
                                    let boundary = cochain_from_coordinates(
                                        space.cochain_term(),
                                        &lay,
                                        space.target(),
                                        cob.row(r),
                                    );
                                    let shifted = add_morphisms(&rep, &boundary);
                                    let recovered = space.class_from_cocycle(&shifted).unwrap();
                                    assert!(recovered.equals(class).unwrap());
                                }
                            }
                        }
                    }
                }
            }
        }
        assert!(saw_nonzero_coboundary, "the fixtures exercise nonzero B^k");
    }

    #[test]
    fn class_from_cocycle_rejects_wrong_endpoints_and_non_cocycles() {
        let field = f5();
        let algebra = truncated_poly(3, field).unwrap();
        let s = Module::simple(&algebra, 0);
        let p = Module::projective(&algebra, 0);
        let space = ExtSpace::new(&s, &p, 1).unwrap();
        let other = ExtSpace::new(&s, &p, 1).unwrap();
        let wrong_source = zero_morphism(other.cochain_term(), &p).unwrap();
        assert_eq!(
            space.class_from_cocycle(&wrong_source).unwrap_err(),
            ExtClassError::SourceMismatch
        );
        let p_copy = Module::projective(&algebra, 0);
        let wrong_target = zero_morphism(space.cochain_term(), &p_copy).unwrap();
        assert_eq!(
            space.class_from_cocycle(&wrong_target).unwrap_err(),
            ExtClassError::TargetMismatch
        );
        let lay = layout(space.cochain_term());
        let non_cocycle = yoneda_basis(space.cochain_term(), &lay, &p).remove(0);
        match space.class_from_cocycle(&non_cocycle).unwrap_err() {
            ExtClassError::NotCocycle { composite } => {
                assert!(composite.iter().any(|c| !c.is_zero()));
            }
            other => panic!("expected NotCocycle, got {other:?}"),
        }
    }

    #[test]
    fn class_from_coordinates_rejects_wrong_length_and_non_canonical_entries() {
        let algebra = truncated_poly(3, f2()).unwrap();
        let s = Module::simple(&algebra, 0);
        let space = ExtSpace::new(&s, &s, 1).unwrap();
        assert_eq!(space.dim(), 1);
        assert_eq!(
            space.class_from_coordinates(&[]).unwrap_err(),
            ExtClassError::CoordinateCountMismatch {
                expected: 1,
                got: 0
            }
        );
        let one = f2().one();
        assert_eq!(
            space.class_from_coordinates(&[one, one]).unwrap_err(),
            ExtClassError::CoordinateCountMismatch {
                expected: 1,
                got: 2
            }
        );
        // The entry 3 comes from F_5; it is not a canonical F_2 representative.
        assert_eq!(
            space.class_from_coordinates(&[f5().elem(3)]).unwrap_err(),
            ExtClassError::NonCanonicalCoordinate { index: 0 }
        );
    }

    #[test]
    fn arithmetic_rejects_incompatible_spaces_and_products_reject_bad_middles() {
        let field = f5();
        let algebra = truncated_poly(3, field).unwrap();
        let s = Module::simple(&algebra, 0);
        let s_copy = Module::simple(&algebra, 0);
        let deg1 = ExtSpace::new(&s, &s, 1).unwrap();
        let deg2 = ExtSpace::new(&s, &s, 2).unwrap();
        let copied = ExtSpace::new(&s_copy, &s_copy, 1).unwrap();
        let a = basis_class(&deg1, 0);
        let b = basis_class(&deg2, 0);
        let c = basis_class(&copied, 0);
        assert_eq!(a.add(&b).unwrap_err(), ExtClassError::IncompatibleSpaces);
        assert_eq!(a.equals(&b).unwrap_err(), ExtClassError::IncompatibleSpaces);
        assert_eq!(a.add(&c).unwrap_err(), ExtClassError::IncompatibleSpaces);
        assert_eq!(a.equals(&c).unwrap_err(), ExtClassError::IncompatibleSpaces);
        assert_eq!(a.then(&c).unwrap_err(), ExtClassError::MiddleMismatch);
    }

    #[test]
    fn identity_class_needs_degree_zero_and_equal_endpoints() {
        let field = f5();
        let algebra = truncated_poly(3, field).unwrap();
        let s = Module::simple(&algebra, 0);
        let p = Module::projective(&algebra, 0);
        assert_eq!(
            ExtSpace::new(&s, &s, 1)
                .unwrap()
                .identity_class()
                .unwrap_err(),
            ExtClassError::NotDegreeZeroEndo
        );
        assert_eq!(
            ExtSpace::new(&s, &p, 0)
                .unwrap()
                .identity_class()
                .unwrap_err(),
            ExtClassError::NotDegreeZeroEndo
        );
    }

    #[test]
    fn zero_modules_give_zero_spaces() {
        let field = f5();
        let algebra = truncated_poly(3, field).unwrap();
        let s = Module::simple(&algebra, 0);
        let z = Module::zero(&algebra);
        for k in 0..=2 {
            let left = ExtSpace::new(&z, &s, k).unwrap();
            let right = ExtSpace::new(&s, &z, k).unwrap();
            assert_eq!(left.dim(), 0);
            assert_eq!(right.dim(), 0);
            assert!(left.zero_class().is_zero());
            assert!(right.zero_class().representative().is_zero());
        }
    }

    #[test]
    fn a_finite_resolution_ending_before_the_degree_gives_the_zero_space() {
        let field = f5();
        let algebra = linear_an(3, field);
        let s0 = Module::simple(&algebra, 0);
        let s1 = Module::simple(&algebra, 1);
        let space = ExtSpace::new(&s0, &s1, 3).unwrap();
        assert_eq!(space.dim(), 0);
        assert!(space.cochain_term().is_zero());
        assert!(space.zero_class().representative().is_zero());
        let empty = space.class_from_coordinates(&[]).unwrap();
        assert!(empty.is_zero());
        let zero = zero_morphism(space.cochain_term(), space.target()).unwrap();
        assert!(space.class_from_cocycle(&zero).unwrap().is_zero());
    }

    #[test]
    fn product_witness_accepts_the_genuine_triple_and_rejects_tampering() {
        let field = f5();
        let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
        let s0 = Module::simple(&algebra, 0);
        let s1 = Module::simple(&algebra, 1);
        let s2 = Module::simple(&algebra, 2);
        let alpha = basis_class(&ExtSpace::new(&s0, &s1, 1).unwrap(), 0);
        let beta = basis_class(&ExtSpace::new(&s1, &s2, 1).unwrap(), 0);
        let (product, witness) = alpha.then_with_witness(&beta).unwrap();
        assert!(witness.verify(&alpha, &beta, &product));
        // A Morphism is checked at construction, so the tamper scales one
        // lift: every nonzero entry changes and one lift identity breaks.
        assert!(!witness.lifts()[0].is_zero());
        let nv = algebra.quiver().num_vertices();
        let scaled_maps: Vec<DenseMat> = (0..nv)
            .map(|v| {
                let m = witness.lifts()[0].map_at(v);
                let mut out = DenseMat::zero(m.rows(), m.cols());
                for r in 0..m.rows() {
                    for c in 0..m.cols() {
                        out.set(r, c, field.mul(field.elem(2), m.get(r, c)));
                    }
                }
                out
            })
            .collect();
        let scaled = Morphism::new(
            witness.lifts()[0].source(),
            witness.lifts()[0].target(),
            scaled_maps,
        )
        .unwrap();
        let mut tampered_lifts = witness.lifts().to_vec();
        tampered_lifts[0] = scaled;
        let tampered = ProductWitness {
            lifts: tampered_lifts,
        };
        assert!(!tampered.verify(&alpha, &beta, &product));
        let wrong_product = ExtClass {
            space: product.space().clone(),
            coords: vec![field.elem(2)],
        };
        assert!(!witness.verify(&alpha, &beta, &wrong_product));
        assert!(!witness.verify(&alpha.scale(field.elem(2)), &beta, &product));
    }

    #[test]
    fn recomputed_spaces_carry_identical_bases_and_representatives() {
        let field = f5();
        let algebra = commutative_square(field);
        let s0 = Module::simple(&algebra, 0);
        let p0 = Module::projective(&algebra, 0);
        for (m, n, k) in [(&s0, &p0, 1), (&s0, &p0, 2), (&s0, &s0, 0)] {
            let first = ExtSpace::new(m, n, k).unwrap();
            let second = ExtSpace::new(m, n, k).unwrap();
            assert!(first.is_compatible(&second));
            assert_eq!(
                first.cocycle_basis().entries_u64(),
                second.cocycle_basis().entries_u64()
            );
            assert_eq!(
                first.coboundary_basis().entries_u64(),
                second.coboundary_basis().entries_u64()
            );
            assert_eq!(
                first.complement_basis().entries_u64(),
                second.complement_basis().entries_u64()
            );
            for (a, b) in first.representatives().iter().zip(second.representatives()) {
                for v in 0..algebra.quiver().num_vertices() {
                    assert_eq!(a.map_at(v), b.map_at(v));
                }
            }
        }
    }

    #[test]
    fn ext_space_new_rejects_modules_over_different_algebras() {
        let a = linear_an(3, f5());
        let b = linear_an(3, f5());
        let m = Module::simple(&a, 0);
        let n = Module::simple(&b, 0);
        assert_eq!(
            ExtSpace::new(&m, &n, 1).unwrap_err(),
            ExtError::DifferentAlgebras
        );
    }
}

/// Representative-level product gates. The acceptance suite pins the
/// class-level product laws; the tests here drive the lift construction on
/// altered cocycle morphisms and on cocycles re-solved from realized
/// extensions, which needs the crate-internal lift machinery.
#[cfg(test)]
mod product_representative_tests {
    use super::*;
    use crate::algebra::{an_with_relations, dual_numbers, truncated_poly};
    use crate::decompose::add_morphisms;
    use crate::field::PrimeField;
    use crate::radical::radical;
    use crate::sequence::ShortExactSequence;

    fn f5() -> PrimeField {
        PrimeField::new(5).unwrap()
    }

    fn f2() -> PrimeField {
        PrimeField::new(2).unwrap()
    }

    fn basis_class(space: &ExtSpace, k: usize) -> ExtClass {
        let field = space.source().field();
        let mut coords = vec![field.zero(); space.dim()];
        coords[k] = field.one();
        space.class_from_coordinates(&coords).unwrap()
    }

    /// The cochain morphism of `row` over the cochain term of `space`.
    fn cocycle_of_row(space: &ExtSpace, row: &[Fp]) -> Morphism {
        let inner = &space.0;
        let lay = layout(&inner.term);
        cochain_from_coordinates(&inner.term, &lay, &inner.target, row)
    }

    /// The degree 1 x degree 1 product class computed by the lift
    /// construction from an arbitrary left cocycle `P^M_1 -> N`, not from
    /// the canonical representative: transport the cocycle onto the product
    /// resolution, lift it through the augmentation of N's resolution, push
    /// one differential further, compose with the right cocycle, and
    /// reduce.
    fn product_from_cocycles(
        left_cocycle: &Morphism,
        beta: &ExtClass,
        right_cocycle: &Morphism,
        product_space: &ExtSpace,
    ) -> ExtClass {
        let deep = &product_space.0.resolution;
        let res_n = &beta.space().0.resolution;
        let nv = product_space.0.source.algebra().quiver().num_vertices();
        let maps: Vec<DenseMat> = (0..nv).map(|v| left_cocycle.map_at(v).clone()).collect();
        let f = Morphism::new(&deep.terms[1], &beta.space().0.source, maps)
            .expect("the recomputed resolution prefix matches, so the cocycle transports");
        let phi0 = lift_through(&deep.terms[1], &res_n.augmentation, &f);
        let rhs = deep.maps[1].then(&phi0).unwrap();
        let phi1 = lift_through(&deep.terms[2], &res_n.maps[0], &rhs);
        let h = phi1.then(right_cocycle).unwrap();
        product_space.class_from_cocycle(&h).unwrap()
    }

    /// Over A = k[x]/(x^3) with S the simple and R = rad P = A/(x^2): the
    /// resolution of S has d_1 = x and d_2 = x^2, so B^1(S, R) is the line
    /// spanned by 1 -> x while B^1 into any simple target vanishes. The
    /// products Ext^1(S, R) x Ext^1(R, S) -> Ext^2(S, S) and
    /// Ext^1(R, S) x Ext^1(S, R) -> Ext^2(R, R) are both nonzero: the
    /// spliced 2-extensions 0 -> S -> P -> P -> S -> 0 (middle map x) and
    /// 0 -> R -> P -> P -> R -> 0 (middle map x^2) have nonzero connecting
    /// cocycles against the minimal resolutions.
    fn x3_pairs(field: PrimeField) -> Vec<(ExtSpace, ExtSpace)> {
        let algebra = truncated_poly(3, field).unwrap();
        let s = Module::simple(&algebra, 0);
        let r = radical(&Module::projective(&algebra, 0)).0;
        vec![
            (
                ExtSpace::new(&s, &r, 1).unwrap(),
                ExtSpace::new(&r, &s, 1).unwrap(),
            ),
            (
                ExtSpace::new(&r, &s, 1).unwrap(),
                ExtSpace::new(&s, &r, 1).unwrap(),
            ),
        ]
    }

    #[test]
    fn a_left_cocycle_shifted_by_a_coboundary_lifts_to_the_same_product() {
        for field in [f5(), f2()] {
            let mut shifted_cases = 0usize;
            for (left, right) in x3_pairs(field) {
                let alpha = basis_class(&left, 0);
                let beta = basis_class(&right, 0);
                let canonical = alpha.then(&beta).unwrap();
                assert!(!canonical.is_zero(), "the fixture products are nonzero");
                let cob = left.coboundary_basis();
                if cob.rows() == 0 {
                    continue;
                }
                let rep = alpha.representative();
                let g = beta.representative();
                let product_space = canonical.space();
                for k in 0..cob.rows() {
                    let boundary = cocycle_of_row(&left, cob.row(k));
                    assert!(!boundary.is_zero());
                    let shifted = add_morphisms(&rep, &boundary);
                    assert!(shifted != rep, "the altered representative differs");
                    let from_shifted = product_from_cocycles(&shifted, &beta, &g, product_space);
                    assert!(from_shifted.equals(&canonical).unwrap());
                    shifted_cases += 1;
                }
            }
            assert!(
                shifted_cases > 0,
                "some left factor space has nonzero coboundaries"
            );
        }
    }

    #[test]
    fn a_right_cocycle_shifted_by_a_coboundary_composes_to_the_same_product() {
        for field in [f5(), f2()] {
            let mut shifted_cases = 0usize;
            for (left, right) in x3_pairs(field) {
                let alpha = basis_class(&left, 0);
                let beta = basis_class(&right, 0);
                let (canonical, witness) = alpha.then_with_witness(&beta).unwrap();
                assert!(!canonical.is_zero(), "the fixture products are nonzero");
                let cob = right.coboundary_basis();
                if cob.rows() == 0 {
                    continue;
                }
                let g = beta.representative();
                for k in 0..cob.rows() {
                    let boundary = cocycle_of_row(&right, cob.row(k));
                    assert!(!boundary.is_zero());
                    let shifted = add_morphisms(&g, &boundary);
                    assert!(shifted != g, "the altered representative differs");
                    let h = witness.lifts()[1].then(&shifted).unwrap();
                    let reduced = canonical.space().class_from_cocycle(&h).unwrap();
                    assert!(reduced.equals(&canonical).unwrap());
                    shifted_cases += 1;
                }
            }
            assert!(
                shifted_cases > 0,
                "some right factor space has nonzero coboundaries"
            );
        }
    }

    /// Re-solves the connecting cocycle of `alpha`'s realized extension,
    /// the pre-reduction morphism of the `ext1_class` recovery: lift the
    /// augmentation through the projection, push it one differential
    /// further, and pull the result back through the inclusion.
    fn recovered_cocycle(alpha: &ExtClass) -> Morphism {
        let ses = ShortExactSequence::from_ext1(alpha).unwrap();
        let res = &alpha.space().0.resolution;
        let h = lift_through(&res.terms[0], ses.projection(), &res.augmentation);
        let d1h = res.maps[0].then(&h).unwrap();
        lift_through(&res.terms[1], ses.inclusion(), &d1h)
    }

    #[test]
    fn the_cocycle_recovered_from_the_extension_splices_to_the_product() {
        let field = f5();
        let a3 = an_with_relations(3, &[(0, 2)], field).unwrap();
        let s0 = Module::simple(&a3, 0);
        let s1 = Module::simple(&a3, 1);
        let s2 = Module::simple(&a3, 2);
        let dn = dual_numbers(field);
        let ds = Module::simple(&dn, 0);
        let mut pairs = vec![
            (
                ExtSpace::new(&s0, &s1, 1).unwrap(),
                ExtSpace::new(&s1, &s2, 1).unwrap(),
            ),
            (
                ExtSpace::new(&ds, &ds, 1).unwrap(),
                ExtSpace::new(&ds, &ds, 1).unwrap(),
            ),
        ];
        pairs.extend(x3_pairs(field));
        let mut perturbed_cases = 0usize;
        for (left, right) in pairs {
            let alpha = basis_class(&left, 0);
            let beta = basis_class(&right, 0);
            let canonical = alpha.then(&beta).unwrap();
            assert!(!canonical.is_zero(), "the fixture products are nonzero");
            let recovered = recovered_cocycle(&alpha);
            assert!(
                left.class_from_cocycle(&recovered)
                    .unwrap()
                    .equals(&alpha)
                    .unwrap()
            );
            let rep = alpha.representative();
            let cocycle = if recovered == rep {
                // A route through the same morphism proves nothing, so
                // perturb by a coboundary. When B^1 is zero every class
                // has one cocycle and the coincidence is forced.
                let cob = left.coboundary_basis();
                if cob.rows() == 0 {
                    recovered
                } else {
                    let shifted = add_morphisms(&recovered, &cocycle_of_row(&left, cob.row(0)));
                    assert!(shifted != rep, "the perturbed cocycle differs");
                    perturbed_cases += 1;
                    shifted
                }
            } else {
                perturbed_cases += 1;
                recovered
            };
            let g = beta.representative();
            let spliced = product_from_cocycles(&cocycle, &beta, &g, canonical.space());
            assert!(spliced.equals(&canonical).unwrap());
        }
        assert!(
            perturbed_cases > 0,
            "some case runs the splice on a cocycle other than the canonical representative"
        );
    }

    /// A copy of `space` whose stored complement and coboundary matrices
    /// are replaced; the reduction paths consume exactly these fields.
    fn space_with(space: &ExtSpace, complement: DenseMat, coboundaries: DenseMat) -> ExtSpace {
        let inner = &space.0;
        let lay = layout(&inner.term);
        let reps = (0..complement.rows())
            .map(|r| cochain_from_coordinates(&inner.term, &lay, &inner.target, complement.row(r)))
            .collect();
        ExtSpace(Arc::new(ExtSpaceInner {
            source: inner.source.clone(),
            target: inner.target.clone(),
            degree: inner.degree,
            resolution: ProjectiveResolution {
                terms: inner.resolution.terms.clone(),
                maps: inner.resolution.maps.clone(),
                augmentation: inner.resolution.augmentation.clone(),
                end: inner.resolution.end,
            },
            term: inner.term.clone(),
            cocycles: inner.cocycles.clone(),
            coboundaries,
            complement,
            reps,
        }))
    }

    fn rows_of(mat: &DenseMat) -> Vec<Vec<Fp>> {
        (0..mat.rows()).map(|r| mat.row(r).to_vec()).collect()
    }

    // Section 15 of the design: a complement row replaced by a coboundary.
    // The genuine witness reduces the product cocycle against the tampered
    // complement, and the mismatch is not a coboundary, so verify rejects.
    #[test]
    fn a_complement_row_replaced_by_a_coboundary_fails_product_verification() {
        let field = f5();
        let mut pairs = x3_pairs(field);
        let (left, right) = pairs.remove(1);
        let alpha = basis_class(&left, 0);
        let beta = basis_class(&right, 0);
        let (product, witness) = alpha.then_with_witness(&beta).unwrap();
        assert!(!product.is_zero());
        assert!(witness.verify(&alpha, &beta, &product));
        let inner = &product.space().0;
        assert!(
            inner.coboundaries.rows() > 0,
            "Ext^2(R, R) has nonzero coboundaries"
        );
        let mut rows = rows_of(&inner.complement);
        rows[0] = inner.coboundaries.row(0).to_vec();
        let tampered = space_with(
            product.space(),
            DenseMat::from_rows(&rows),
            inner.coboundaries.clone(),
        );
        let bad = ExtClass {
            space: tampered,
            coords: product.coordinates().to_vec(),
        };
        assert!(!witness.verify(&alpha, &beta, &bad));
    }

    // Section 15 of the design: a product reduced against a tampered
    // coboundary basis. A basis grown by a cocycle outside B^2 would let
    // any class label pass the membership solve, so verify must compare
    // the stored basis against the recomputation and reject.
    #[test]
    fn a_tampered_coboundary_basis_fails_product_verification() {
        let field = f5();
        let mut pairs = x3_pairs(field);
        let (left, right) = pairs.remove(1);
        let alpha = basis_class(&left, 0);
        let beta = basis_class(&right, 0);
        let (product, witness) = alpha.then_with_witness(&beta).unwrap();
        assert!(witness.verify(&alpha, &beta, &product));
        let inner = &product.space().0;
        assert!(
            inner.coboundaries.rows() > 0,
            "Ext^2(R, R) has nonzero coboundaries"
        );
        let mut rows = rows_of(&inner.coboundaries);
        rows.push(inner.complement.row(0).to_vec());
        let grown = DenseMat::from_rows(&rows).row_space_basis(&field);
        assert_ne!(grown, inner.coboundaries);
        let tampered = space_with(product.space(), inner.complement.clone(), grown);
        let bad = ExtClass {
            space: tampered,
            coords: product.coordinates().to_vec(),
        };
        assert!(!witness.verify(&alpha, &beta, &bad));
        let wrong_label = ExtClass {
            space: bad.space.clone(),
            coords: vec![field.zero(); product.coordinates().len()],
        };
        assert!(!witness.verify(&alpha, &beta, &wrong_label));
    }
}

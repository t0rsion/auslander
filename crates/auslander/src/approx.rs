//! Minimal left `add(N)`-approximations, with factorization data and a
//! radical-containment minimality witness.
//!
//! Give `N` by its indecomposable summands `N_1, ..., N_k`, one module per
//! isomorphism class. A map `f: X -> B` with `B` in `add(N)` is a left
//! `add(N)`-approximation when every map `X -> N'` with `N'` in `add(N)`
//! factors through `f`. Testing the `N_i` is enough, since a map into a sum is
//! its components, and testing an `F_p` basis of each `Hom(X, N_i)` is enough,
//! since factorization through `f` is linear in the target map. The witness
//! stores the factorization coordinates of every basis map.
//!
//! `f` is left minimal exactly when `K_f = ker(End(B) -> Hom(X, B))` under
//! `h |-> f.then(h)` lies inside `rad End(B)`. `K_f` is a right ideal, so
//! `K_f` inside the radical says every `1 - u` with `u` in `K_f` is invertible,
//! which is the usual statement: `f.then(h) = f` forces `h` invertible. The
//! witness stores the RREF basis of `K_f` in `End(B)` coordinates together with
//! the coordinates that place each basis row inside `rad End(B)`.
//!
//! [`crate::arquiver::category_radical`] does not settle minimality when `B` is
//! decomposable. It is defined between two certified indecomposables, and the
//! criterion needs `rad End(B)` for the whole middle term. [`EndoAlgebra`]
//! supplies that radical exactly, over any prime field.
//!
//! # Multiplicities are dimensions over a division ring
//!
//! The number of copies of `N_i` in `B` is not `dim_{F_p} Hom(X, N_i)`. Write
//! `L = End(N)` and read `Hom(X, N)` as a right `L`-module. A map `f: X -> B`
//! with `B` in `add(N)` is a left approximation exactly when
//! `Hom(B, N) -> Hom(X, N)`, `h |-> f.then(h)`, is onto, and `f` is minimal
//! exactly when that map is a projective cover, because `Hom(-, N)` is a
//! duality from `add(N)` onto the projective right `L`-modules. So the
//! multiplicity of `N_i` is the multiplicity of the `i`-th simple in the top
//! `Hom(X, N) / Hom(X, N) rad L`, counted over the residue division ring
//! `D_i = End(N_i) / rad End(N_i)`. With `d_i = dim_{F_p} D_i` the residue
//! degree of `N_i`, an `F_p` basis of `Hom(X, N_i)` gives `d_i` times too many
//! copies. Over an algebraically closed field every `d_i` is 1 and the two
//! counts agree, which is where that assumption hides. The prime fields here
//! have `d_i > 1`: the Kronecker module `(I_3, C)` over `F_2` for `C` the
//! companion matrix of `x^3 + x + 1` has `End = F_8` and `d = 3`.
//!
//! [`left_approximation`] therefore picks generators over `D_i`, not over
//! `F_p`. See its docstring for the loop.

use std::fmt;

use crate::decompose::add_morphisms;
use crate::endo::EndoAlgebra;
use crate::field::{Fp, PrimeField};
use crate::hom::{HomError, Morphism, hom, identity, zero_morphism};
use crate::homspace::{HomSpace, HomSpaceError};
use crate::indec::{IndecError, IndecomposableModule};
use crate::iso::indecomposable_iso;
use crate::linalg::{DenseMat, RowReducer};
use crate::module::{Module, direct_sum};

/// A failed internal cross-check of the approximation layer. Every variant
/// signals a crate defect: the construction checked a consequence of a theorem
/// whose hypotheses hold, and the check failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ApproxDefect {
    /// Accepting one generator for `summand` moved the `F_p` dimension of the
    /// generated span by `growth` instead of by the residue degree. The
    /// generator lies outside the span and the span already holds
    /// `generator . rad End(N_i)`, so the step must add exactly one `D_i` line.
    GeneratorGrowth {
        /// Index of the add-generator in the given list.
        summand: usize,
        /// The observed rise in `F_p` dimension.
        growth: usize,
        /// The residue degree of the add-generator.
        residue_degree: usize,
    },
    /// A basis map of `Hom(X, N_i)` does not factor through the built map, so
    /// the generators failed to generate.
    FactorizationMissing {
        /// Index of the add-generator in the given list.
        summand: usize,
        /// Position of the map in the [`HomSpace`] basis.
        basis_index: usize,
    },
    /// A basis row of `K_f` lies outside `rad End(B)`, so the built map is not
    /// minimal. The generator loop returns a projective cover, so this cannot
    /// happen.
    KernelOutsideRadical {
        /// Position of the row in the RREF basis of `K_f`.
        row: usize,
        /// `dim_k K_f`.
        kernel_dim: usize,
        /// `dim_k rad End(B)`.
        radical_dim: usize,
    },
}

impl fmt::Display for ApproxDefect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::GeneratorGrowth {
                summand,
                growth,
                residue_degree,
            } => write!(
                f,
                "a generator for summand {summand} raised the span by {growth}, not by the \
                 residue degree {residue_degree}; crate defect"
            ),
            Self::FactorizationMissing {
                summand,
                basis_index,
            } => write!(
                f,
                "basis map {basis_index} for summand {summand} does not factor through the \
                 built map; crate defect"
            ),
            Self::KernelOutsideRadical {
                row,
                kernel_dim,
                radical_dim,
            } => write!(
                f,
                "row {row} of the {kernel_dim}-dimensional kernel lies outside the \
                 {radical_dim}-dimensional radical; crate defect"
            ),
        }
    }
}

impl std::error::Error for ApproxDefect {}

/// Rejected approximation input, or a failed internal cross-check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ApproxError {
    /// An add-generator failed the indecomposability gate.
    SummandNotIndecomposable {
        /// Position in the given list.
        index: usize,
        /// Why the gate rejected it.
        reason: IndecError,
    },
    /// Two add-generators are isomorphic. The list holds one module per
    /// isomorphism class, because `rad(N_j, N_i)` for `j != i` is all of
    /// `Hom(N_j, N_i)` only when the two are not isomorphic.
    RepeatedSummand {
        /// Position of the earlier module.
        first: usize,
        /// Position of the later module.
        second: usize,
    },
    /// A Hom computation rejected its input, usually two different algebras.
    Hom(HomError),
    /// A Hom-space coordinate call rejected its input.
    HomSpace(HomSpaceError),
    /// An internal cross-check failed.
    Defect(ApproxDefect),
}

impl fmt::Display for ApproxError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SummandNotIndecomposable { index, reason } => {
                write!(f, "add-generator {index} is not indecomposable: {reason}")
            }
            Self::RepeatedSummand { first, second } => write!(
                f,
                "add-generators {first} and {second} are isomorphic; give one module per class"
            ),
            Self::Hom(error) => write!(f, "hom: {error}"),
            Self::HomSpace(error) => write!(f, "hom space: {error}"),
            Self::Defect(defect) => write!(f, "{defect}"),
        }
    }
}

impl std::error::Error for ApproxError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::SummandNotIndecomposable { reason, .. } => Some(reason),
            Self::Hom(error) => Some(error),
            Self::HomSpace(error) => Some(error),
            Self::Defect(defect) => Some(defect),
            Self::RepeatedSummand { .. } => None,
        }
    }
}

/// The `k`-th unit vector of length `dim`.
fn unit(dim: usize, k: usize, field: &PrimeField) -> Vec<Fp> {
    let mut v = vec![Fp::ZERO; dim];
    v[k] = field.one();
    v
}

/// Certifies each add-generator indecomposable and the list free of repeats.
fn certify(n_summands: &[Module]) -> Result<Vec<IndecomposableModule>, ApproxError> {
    let mut certified = Vec::with_capacity(n_summands.len());
    for (index, n) in n_summands.iter().enumerate() {
        let ind = IndecomposableModule::new(n)
            .map_err(|reason| ApproxError::SummandNotIndecomposable { index, reason })?;
        certified.push(ind);
    }
    for second in 0..certified.len() {
        for first in 0..second {
            let iso = indecomposable_iso(
                certified[first].module(),
                certified[second].module(),
                certified[first].endo(),
            );
            if iso.is_some() {
                return Err(ApproxError::RepeatedSummand { first, second });
            }
        }
    }
    Ok(certified)
}

/// The direct sum of the slot modules with its inclusions and projections. An
/// empty slot list gives the zero module and no maps, which [`direct_sum`]
/// itself rejects.
fn slot_sum(
    algebra_source: &Module,
    summands: &[IndecomposableModule],
    slots: &[usize],
) -> (Module, Vec<Morphism>, Vec<Morphism>) {
    if slots.is_empty() {
        return (
            Module::zero(algebra_source.algebra()),
            Vec::new(),
            Vec::new(),
        );
    }
    let parts: Vec<&Module> = slots.iter().map(|&i| summands[i].module()).collect();
    direct_sum(&parts)
}

/// The RREF basis of `{y : sum_t y_t rows[t] = 0}`, one vector per row.
///
/// The caller passes `rows[t]` as the image of the `t`-th basis endomorphism
/// of `End(B)`, so a result row is a `K_f` element in `End(B)` coordinates. `width` sizes the coordinate system of the images,
/// which `DenseMat::from_rows` cannot recover when it is zero.
fn row_relations(rows: &[Vec<Fp>], width: usize, field: &PrimeField) -> DenseMat {
    if rows.is_empty() {
        return DenseMat::zero(0, 0);
    }
    let stacked = if width == 0 {
        DenseMat::zero(rows.len(), 0)
    } else {
        DenseMat::from_rows(rows)
    };
    stacked
        .transpose()
        .into_kernel_basis(field)
        .into_row_space_basis(field)
}

/// Coordinates placing each row of `kernel` inside `rad End(B)`, or the index
/// of the first row that lies outside.
///
/// One [`DenseMat::solve_many`] serves every row. Only the failure path needs
/// the index, so it alone repeats the solve row by row.
fn radical_coordinates(endo: &EndoAlgebra, kernel: &DenseMat) -> Result<Vec<Vec<Fp>>, usize> {
    let field = endo.field();
    if kernel.rows() == 0 {
        return Ok(Vec::new());
    }
    let radical = endo.radical_basis().transpose();
    let Some(x) = radical.solve_many(&kernel.transpose(), &field) else {
        return Err((0..kernel.rows())
            .position(|r| radical.solve(kernel.row(r), &field).is_none())
            .expect("solve_many rejects only when some row lies outside"));
    };
    Ok(columns_of(&x))
}

/// The columns of `x`, one vector per column. [`DenseMat::solve_many`] puts
/// one solution in each column, and both callers want one solution per row.
fn columns_of(x: &DenseMat) -> Vec<Vec<Fp>> {
    (0..x.cols())
        .map(|j| (0..x.rows()).map(|i| x.get(i, j)).collect())
        .collect()
}

/// Coordinates writing each unit vector over the columns of `system`, or the
/// index of the first unit that lies outside the column space.
///
/// The unit vectors are the identity matrix, so one [`DenseMat::solve_many`]
/// replaces one `solve` per unit. Only the failure path needs the index, so it
/// alone repeats the solve unit by unit.
fn unit_factorizations(system: &DenseMat, field: &PrimeField) -> Result<Vec<Vec<Fp>>, usize> {
    let dim = system.rows();
    if dim == 0 {
        return Ok(Vec::new());
    }
    let Some(x) = system.solve_many(&DenseMat::identity(dim), field) else {
        return Err((0..dim)
            .position(|j| system.solve(&unit(dim, j, field), field).is_none())
            .expect("solve_many rejects only when some unit lies outside"));
    };
    Ok(columns_of(&x))
}

/// Whether `coords` against the radical basis reproduces `row`.
fn radical_combination_matches(endo: &EndoAlgebra, coords: &[Fp], row: &[Fp]) -> bool {
    let field = endo.field();
    let radical = endo.radical_basis();
    if coords.len() != radical.rows() || row.len() != endo.dim() {
        return false;
    }
    for (c, &want) in row.iter().enumerate() {
        let mut acc = Fp::ZERO;
        for (t, &x) in coords.iter().enumerate() {
            acc = field.add(acc, field.mul(x, radical.get(t, c)));
        }
        if acc != want {
            return false;
        }
    }
    true
}

/// Whether the stored maps decompose `total` as the sum of the slot modules.
fn decomposition_holds(
    total: &Module,
    summands: &[IndecomposableModule],
    slots: &[usize],
    inclusions: &[Morphism],
    projections: &[Morphism],
) -> bool {
    if inclusions.len() != slots.len() || projections.len() != slots.len() {
        return false;
    }
    let mut sum = match zero_morphism(total, total) {
        Ok(z) => z,
        Err(_) => return false,
    };
    for (c, &i) in slots.iter().enumerate() {
        let part = summands[i].module();
        if !inclusions[c].source().ptr_eq(part) || !inclusions[c].target().ptr_eq(total) {
            return false;
        }
        if !projections[c].source().ptr_eq(total) || !projections[c].target().ptr_eq(part) {
            return false;
        }
        for (d, incl) in inclusions.iter().enumerate() {
            let Ok(composite) = incl.then(&projections[c]) else {
                return false;
            };
            if c == d {
                if composite != identity(part) {
                    return false;
                }
            } else if !composite.is_zero() {
                return false;
            }
        }
        let Ok(idempotent) = projections[c].then(&inclusions[c]) else {
            return false;
        };
        sum = add_morphisms(&sum, &idempotent);
    }
    sum == identity(total)
}

/// A left `add(N)`-approximation `f: X -> B` that is left minimal, with the
/// data that proves both properties.
///
/// Fields are private and the only public constructor is
/// [`left_approximation`], so every value carries checked factorization
/// coordinates and a checked radical containment. [`MinimalLeftApproximation::verify`]
/// recomputes all of it from the stored maps.
#[derive(Debug)]
pub struct MinimalLeftApproximation {
    // f: X -> B. The endpoints are `map.source()` and `map.target()`.
    map: Morphism,
    summands: Vec<IndecomposableModule>,
    // B is the direct sum of `summands[slots[c]]`, in slot order.
    slots: Vec<usize>,
    inclusions: Vec<Morphism>,
    projections: Vec<Morphism>,
    // factorizations[i][j]: coordinates in Hom(B, N_i) of an h with
    // f.then(h) equal to basis map j of Hom(X, N_i).
    factorizations: Vec<Vec<Vec<Fp>>>,
    // RREF basis of K_f in End(B) coordinates.
    kernel: DenseMat,
    // One row per kernel row: its coordinates over the RREF basis of rad End(B).
    radical: Vec<Vec<Fp>>,
}

impl MinimalLeftApproximation {
    /// The approximation `f: X -> B`.
    #[inline]
    pub fn map(&self) -> &Morphism {
        &self.map
    }

    /// The certified add-generators `N_1, ..., N_k`, in the given order.
    #[inline]
    pub fn summands(&self) -> &[IndecomposableModule] {
        &self.summands
    }

    /// The slot list: `B` is the direct sum of `summands()[slots()[c]]`.
    #[inline]
    pub fn slots(&self) -> &[usize] {
        &self.slots
    }

    /// The block inclusions `N_{slots[c]} -> B`, in slot order.
    #[inline]
    pub fn inclusions(&self) -> &[Morphism] {
        &self.inclusions
    }

    /// The block projections `B -> N_{slots[c]}`, in slot order.
    #[inline]
    pub fn projections(&self) -> &[Morphism] {
        &self.projections
    }

    /// How many copies of add-generator `summand` occur in `B`.
    pub fn multiplicity(&self, summand: usize) -> usize {
        self.slots.iter().filter(|&&i| i == summand).count()
    }

    /// Coordinates in `Hom(B, N_i)` of an `h` with `f.then(h)` equal to basis
    /// map `basis_index` of `Hom(X, N_i)`, for `i` equal to `summand`.
    ///
    /// # Panics
    /// Panics if either index is out of range.
    pub fn factorization(&self, summand: usize, basis_index: usize) -> &[Fp] {
        &self.factorizations[summand][basis_index]
    }

    /// The RREF basis of `K_f = ker(End(B) -> Hom(X, B))` in `End(B)`
    /// coordinates, one vector per row.
    #[inline]
    pub fn kernel_basis(&self) -> &DenseMat {
        &self.kernel
    }

    /// Coordinates of kernel basis row `row` over the RREF basis of
    /// `rad End(B)`.
    ///
    /// # Panics
    /// Panics if `row` is out of range.
    pub fn radical_coordinates(&self, row: usize) -> &[Fp] {
        &self.radical[row]
    }

    /// Recomputes every stored claim from the stored maps and reports whether
    /// all of it holds.
    ///
    /// The checks: the stored inclusions and projections decompose `B` into the
    /// slot modules; `Hom(X, N_i)` and `Hom(B, N_i)` rebuild and every stored
    /// factorization reproduces its basis map under `f.then(h)`; `End(B)`
    /// rebuilds and its recomputed `K_f` equals the stored RREF basis; each
    /// stored radical coordinate vector reproduces its kernel row against
    /// `rad End(B)`. Nothing is replayed from the build.
    pub fn verify(&self) -> bool {
        let x = self.map.source();
        let b = self.map.target();
        if self.factorizations.len() != self.summands.len() {
            return false;
        }
        if self.slots.iter().any(|&i| i >= self.summands.len()) {
            return false;
        }
        if !decomposition_holds(
            b,
            &self.summands,
            &self.slots,
            &self.inclusions,
            &self.projections,
        ) {
            return false;
        }
        for (i, n) in self.summands.iter().enumerate() {
            let (Ok(target_space), Ok(source_space)) =
                (HomSpace::new(x, n.module()), HomSpace::new(b, n.module()))
            else {
                return false;
            };
            if self.factorizations[i].len() != target_space.dim() {
                return false;
            }
            for (j, coords) in self.factorizations[i].iter().enumerate() {
                if coords.len() != source_space.dim() {
                    return false;
                }
                let Ok(composite) = self.map.then(&source_space.morphism(coords)) else {
                    return false;
                };
                if composite != target_space.basis()[j] {
                    return false;
                }
            }
        }
        let endo = EndoAlgebra::new(b);
        let Ok(space) = HomSpace::new(x, b) else {
            return false;
        };
        let field = x.field();
        let mut rows = Vec::with_capacity(endo.dim());
        for e in endo.basis() {
            let Ok(composite) = self.map.then(e) else {
                return false;
            };
            match space.coords(&composite) {
                Ok(c) => rows.push(c),
                Err(_) => return false,
            }
        }
        let kernel = row_relations(&rows, space.dim(), &field);
        if kernel != self.kernel || self.radical.len() != kernel.rows() {
            return false;
        }
        (0..kernel.rows())
            .all(|r| radical_combination_matches(&endo, &self.radical[r], kernel.row(r)))
    }
}

/// The minimal left `add(N)`-approximation of `x`, with `N` given by its
/// indecomposable summands `n_summands`, one module per isomorphism class.
///
/// # Algorithm
///
/// Write `M_i` for `Hom(x, N_i)` and `R_i` for the `i`-th component of
/// `Hom(x, N) rad End(N)`, namely
/// `sum_{j != i} M_j . Hom(N_j, N_i) + M_i . rad End(N_i)`. The sum over
/// `j != i` uses all of `Hom(N_j, N_i)`, which is the categorical radical
/// exactly because `N_j` and `N_i` are non-isomorphic indecomposables; the
/// constructor rejects a repeated class for that reason.
///
/// For each `i`, start the span at `R_i` and scan the `F_p` basis of `M_i` in
/// its [`HomSpace`] order. Accept a basis map `g` as a generator when it lies
/// outside the span, then add `g . End(N_i)` to the span. Each accepted
/// generator contributes one copy of `N_i` to `B`, and `f` is the map whose
/// component into that copy is `g`.
///
/// Acceptance raises the `F_p` dimension of the span by exactly the residue
/// degree `d_i`. The span already holds `g . rad End(N_i)`, so the new part is
/// the image of `D_i = End(N_i) / rad End(N_i)`, a right `D_i`-line because
/// `g` itself is outside the span. The constructor asserts that rise and
/// reports [`ApproxDefect::GeneratorGrowth`] otherwise. The scan visits each of
/// the `dim_{F_p} M_i` basis maps once, so the loop is finite and accepts at
/// most `dim_{F_p} M_i / d_i` generators.
///
/// The accepted generators are a minimal generating set of `Hom(x, N)` as a
/// right `End(N)`-module, by Nakayama, so `Hom(B, N) -> Hom(x, N)` is a
/// projective cover and `f` is a minimal left approximation. No reduction pass
/// follows: the constructor checks both properties and reports a defect rather
/// than repairing the result.
///
/// # Errors
/// [`ApproxError::SummandNotIndecomposable`] when an add-generator fails the
/// indecomposability gate, [`ApproxError::RepeatedSummand`] when two are
/// isomorphic, [`ApproxError::Hom`] when the modules do not share one algebra,
/// and [`ApproxError::Defect`] on a failed internal cross-check.
pub fn left_approximation(
    x: &Module,
    n_summands: &[Module],
) -> Result<MinimalLeftApproximation, ApproxError> {
    let summands = certify(n_summands)?;
    let field = x.field();
    let mut spaces = Vec::with_capacity(summands.len());
    for n in &summands {
        spaces.push(HomSpace::new(x, n.module()).map_err(ApproxError::Hom)?);
    }

    let mut slots: Vec<usize> = Vec::new();
    let mut components: Vec<Morphism> = Vec::new();
    for (i, n) in summands.iter().enumerate() {
        let width = spaces[i].dim();
        let mut rows: Vec<Vec<Fp>> = Vec::new();
        for (j, other) in summands.iter().enumerate() {
            if j == i {
                let radical = n.endo().radical_basis();
                for r in 0..radical.rows() {
                    let step = n.endo().morphism(radical.row(r));
                    for g in spaces[i].basis() {
                        rows.push(compose_into(&spaces[i], g, &step)?);
                    }
                }
            } else {
                let between = hom(other.module(), n.module()).map_err(ApproxError::Hom)?;
                for step in &between {
                    for g in spaces[j].basis() {
                        rows.push(compose_into(&spaces[i], g, step)?);
                    }
                }
            }
        }
        let mut span = RowReducer::new(width);
        for row in &rows {
            span.push(row, &field);
        }
        for t in 0..width {
            // A push raises the rank exactly when the unit was outside the
            // span. The unit is `g` composed with the identity of End(N_i),
            // one of the rows pushed below, so keeping it here leaves the
            // span that `growth` measures unchanged.
            if !span.push(&unit(width, t, &field), &field) {
                continue;
            }
            let before = span.rank() - 1;
            let g = &spaces[i].basis()[t];
            for e in n.endo().basis() {
                span.push(&compose_into(&spaces[i], g, e)?, &field);
            }
            let growth = span.rank() - before;
            if growth != n.residue_degree() {
                return Err(ApproxError::Defect(ApproxDefect::GeneratorGrowth {
                    summand: i,
                    growth,
                    residue_degree: n.residue_degree(),
                }));
            }
            slots.push(i);
            components.push(g.clone());
        }
    }

    let (b, inclusions, projections) = slot_sum(x, &summands, &slots);
    let mut map = zero_morphism(x, &b).map_err(ApproxError::Hom)?;
    for (c, component) in components.iter().enumerate() {
        let block = component
            .then(&inclusions[c])
            .expect("a component lands in its own block");
        map = add_morphisms(&map, &block);
    }

    let mut factorizations = Vec::with_capacity(summands.len());
    for (i, n) in summands.iter().enumerate() {
        let source_space = HomSpace::new(&b, n.module()).map_err(ApproxError::Hom)?;
        let mut images = Vec::with_capacity(source_space.dim());
        for h in source_space.basis() {
            let composite = map.then(h).expect("f composes with a map out of B");
            images.push(
                spaces[i]
                    .coords(&composite)
                    .map_err(ApproxError::HomSpace)?,
            );
        }
        let system = if images.is_empty() {
            DenseMat::zero(spaces[i].dim(), 0)
        } else {
            DenseMat::from_rows(&images).transpose()
        };
        factorizations.push(unit_factorizations(&system, &field).map_err(|basis_index| {
            ApproxError::Defect(ApproxDefect::FactorizationMissing {
                summand: i,
                basis_index,
            })
        })?);
    }

    let endo = EndoAlgebra::new(&b);
    let space = HomSpace::new(x, &b).map_err(ApproxError::Hom)?;
    let mut rows = Vec::with_capacity(endo.dim());
    for e in endo.basis() {
        let composite = map.then(e).expect("f composes with an endomorphism of B");
        rows.push(space.coords(&composite).map_err(ApproxError::HomSpace)?);
    }
    let kernel = row_relations(&rows, space.dim(), &field);
    let radical = radical_coordinates(&endo, &kernel).map_err(|row| {
        ApproxError::Defect(ApproxDefect::KernelOutsideRadical {
            row,
            kernel_dim: kernel.rows(),
            radical_dim: endo.radical_dim(),
        })
    })?;

    Ok(MinimalLeftApproximation {
        map,
        summands,
        slots,
        inclusions,
        projections,
        factorizations,
        kernel,
        radical,
    })
}

/// The coordinates of `first.then(second)` in `space`.
fn compose_into(
    space: &HomSpace,
    first: &Morphism,
    second: &Morphism,
) -> Result<Vec<Fp>, ApproxError> {
    let composite = first.then(second).map_err(ApproxError::Hom)?;
    space.coords(&composite).map_err(ApproxError::HomSpace)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{Algebra, commutative_square, kronecker, linear_an, truncated_poly};
    use crate::dynkin::{DynkinType, dynkin_quiver};
    use crate::field::PrimeField;
    use crate::hom::kernel;
    use crate::quiver::Quiver;
    use std::sync::Arc;

    fn f2() -> PrimeField {
        PrimeField::new(2).unwrap()
    }

    fn f5() -> PrimeField {
        PrimeField::new(5).unwrap()
    }

    fn fields() -> [PrimeField; 2] {
        [f2(), f5()]
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

    fn fixtures(field: PrimeField) -> Vec<(&'static str, Arc<Algebra>)> {
        vec![
            ("A_2", linear_an(2, field)),
            ("A_3", linear_an(3, field)),
            ("k[x]/x^3", truncated_poly(3, field).unwrap()),
            ("D_4", d4(field)),
            ("commutative square", commutative_square(field)),
        ]
    }

    fn projectives(algebra: &Arc<Algebra>) -> Vec<Module> {
        (0..algebra.quiver().num_vertices())
            .map(|v| Module::projective(algebra, v))
            .collect()
    }

    fn injectives(algebra: &Arc<Algebra>) -> Vec<Module> {
        (0..algebra.quiver().num_vertices())
            .map(|v| Module::injective(algebra, v))
            .collect()
    }

    fn test_modules(algebra: &Arc<Algebra>) -> Vec<Module> {
        let mut out: Vec<Module> = (0..algebra.quiver().num_vertices())
            .map(|v| Module::simple(algebra, v))
            .collect();
        out.extend(projectives(algebra));
        out.extend(injectives(algebra));
        out
    }

    // The approximation property, re-solved from scratch rather than read off
    // the witness: every basis map of Hom(X, N_i) is f.then(h) for some h.
    fn left_property_holds(a: &MinimalLeftApproximation) -> bool {
        let x = a.map().source();
        let b = a.map().target();
        let field = x.field();
        for n in a.summands() {
            let target_space = HomSpace::new(x, n.module()).unwrap();
            let source_space = HomSpace::new(b, n.module()).unwrap();
            let images: Vec<Vec<Fp>> = source_space
                .basis()
                .iter()
                .map(|h| target_space.coords(&a.map().then(h).unwrap()).unwrap())
                .collect();
            let system = if images.is_empty() {
                DenseMat::zero(target_space.dim(), 0)
            } else {
                DenseMat::from_rows(&images).transpose()
            };
            if unit_factorizations(&system, &field).is_err() {
                return false;
            }
        }
        true
    }

    // Factorization coordinates for a map that is known to approximate, in the
    // layout MinimalLeftApproximation stores.
    fn left_factorizations(f: &Morphism, summands: &[IndecomposableModule]) -> Vec<Vec<Vec<Fp>>> {
        let field = f.source().field();
        summands
            .iter()
            .map(|n| {
                let target_space = HomSpace::new(f.source(), n.module()).unwrap();
                let source_space = HomSpace::new(f.target(), n.module()).unwrap();
                let images: Vec<Vec<Fp>> = source_space
                    .basis()
                    .iter()
                    .map(|h| target_space.coords(&f.then(h).unwrap()).unwrap())
                    .collect();
                let system = if images.is_empty() {
                    DenseMat::zero(target_space.dim(), 0)
                } else {
                    DenseMat::from_rows(&images).transpose()
                };
                unit_factorizations(&system, &field).expect("the map approximates")
            })
            .collect()
    }

    // K_f of a left approximation, recomputed outside the witness.
    fn left_kernel_of(f: &Morphism, endo: &EndoAlgebra) -> DenseMat {
        let space = HomSpace::new(f.source(), f.target()).unwrap();
        let field = f.source().field();
        let rows: Vec<Vec<Fp>> = endo
            .basis()
            .iter()
            .map(|e| space.coords(&f.then(e).unwrap()).unwrap())
            .collect();
        row_relations(&rows, space.dim(), &field)
    }

    #[test]
    fn left_approximations_by_the_projectives_verify_on_every_fixture() {
        let mut checked = 0;
        for field in fields() {
            for (name, algebra) in fixtures(field) {
                let generators = projectives(&algebra);
                for x in test_modules(&algebra) {
                    let context = format!("{name} over F_{}", field.modulus());
                    let left = left_approximation(&x, &generators)
                        .unwrap_or_else(|e| panic!("{context}: left: {e}"));
                    assert!(left.verify(), "{context}: left verify");
                    assert!(left_property_holds(&left), "{context}: left property");
                    checked += 1;
                }
            }
        }
        assert_eq!(checked, 84);
    }

    #[test]
    fn left_approximations_by_the_injectives_verify_on_every_fixture() {
        for field in fields() {
            for (name, algebra) in fixtures(field) {
                let generators = injectives(&algebra);
                for x in test_modules(&algebra) {
                    let context = format!("{name} over F_{}", field.modulus());
                    let left = left_approximation(&x, &generators)
                        .unwrap_or_else(|e| panic!("{context}: left: {e}"));
                    assert!(left.verify(), "{context}: left verify");
                    assert!(left_property_holds(&left), "{context}: left property");
                }
            }
        }
    }

    #[test]
    fn every_kernel_row_sits_inside_the_radical_of_the_endomorphism_algebra() {
        for field in fields() {
            for (name, algebra) in fixtures(field) {
                let generators = projectives(&algebra);
                for x in test_modules(&algebra) {
                    let left = left_approximation(&x, &generators).unwrap();
                    let endo = EndoAlgebra::new(left.map().target());
                    let kernel = left_kernel_of(left.map(), &endo);
                    assert_eq!(&kernel, left.kernel_basis(), "{name}: recomputed K_f");
                    for r in 0..kernel.rows() {
                        assert!(
                            endo.in_radical(kernel.row(r)),
                            "{name} over F_{}: row {r} outside rad End(B)",
                            field.modulus()
                        );
                    }
                }
            }
        }
    }

    // Over linearly oriented A_2 (0 -> a -> 1), P_0 has dimension vector (1, 1)
    // and P_1 = S_1 has (0, 1). A map f: S_0 -> P_0 has f_1 = 0 and must satisfy
    // f_0 . P_0(a) = S_0(a) . f_1 = 0 with P_0(a) invertible, so f_0 = 0. A map
    // S_0 -> P_1 is zero at vertex 0 for lack of room. So Hom(S_0, P_v) = 0 for
    // both v, and the minimal left approximation of S_0 by add(P) is the zero
    // map into the zero module.
    #[test]
    fn a_left_approximation_with_no_maps_available_is_the_zero_map_into_zero() {
        for field in fields() {
            let algebra = linear_an(2, field);
            let s0 = Module::simple(&algebra, 0);
            let generators = projectives(&algebra);
            for n in &generators {
                assert_eq!(HomSpace::new(&s0, n).unwrap().dim(), 0);
            }
            let a = left_approximation(&s0, &generators).unwrap();
            assert!(a.slots().is_empty());
            assert!(a.map().target().is_zero());
            assert!(a.map().is_zero());
            assert_eq!(a.kernel_basis().rows(), 0);
            assert!(a.verify());
            assert!(left_property_holds(&a));
        }
    }

    // X in add(N) gives a split monomorphism. Over A_2 take X = S_1 = P_1.
    // Hom(S_1, P_1) = End(S_1) is one-dimensional; Hom(P_0, P_1) = 0, so the
    // radical part R_1 is zero and the identity is the single generator. The
    // approximation is X -> X, an isomorphism, which is split mono.
    //
    // Hom(S_1, P_0) is one-dimensional too, the socle inclusion, but every map
    // there is the composite S_1 -> P_1 -> P_0 with P_1 and P_0 not isomorphic,
    // so R_0 is all of Hom(S_1, P_0) and P_0 gets no copy. That is the part of
    // the count an F_p basis would get wrong.
    #[test]
    fn a_module_inside_add_n_gets_a_split_monomorphism() {
        for field in fields() {
            let algebra = linear_an(2, field);
            let generators = projectives(&algebra);
            let x = generators[1].clone();
            assert_eq!(HomSpace::new(&x, &generators[0]).unwrap().dim(), 1);
            let a = left_approximation(&x, &generators).unwrap();
            assert_eq!(a.multiplicity(0), 0, "P_0 is redundant here");
            assert_eq!(a.slots(), &[1]);
            assert!(a.map().is_isomorphism());
            assert_eq!(kernel(a.map()).0.total_dim(), 0);

            // The factorization payload by value. B is one copy of P_1 and f
            // is the block inclusion of the generator, which is the identity
            // of End(P_1) = k. Hom(X, N_i) and Hom(B, N_i) are both
            // one-dimensional for each i, and f identifies the two, so every
            // basis map factors with the single coordinate 1.
            for (i, n) in generators.iter().enumerate() {
                assert_eq!(HomSpace::new(&x, n).unwrap().dim(), 1);
                assert_eq!(HomSpace::new(a.map().target(), n).unwrap().dim(), 1);
                assert_eq!(a.factorization(i, 0), &[field.one()], "summand {i}");
            }

            assert!(a.verify());
            assert!(left_property_holds(&a));
        }
    }

    #[test]
    fn an_empty_add_generator_list_gives_the_zero_map_into_zero() {
        for field in fields() {
            for (name, algebra) in fixtures(field) {
                let x = Module::projective(&algebra, 0);
                let left = left_approximation(&x, &[]).unwrap();
                assert!(left.summands().is_empty(), "{name}");
                assert!(left.slots().is_empty(), "{name}");
                assert!(left.map().target().is_zero(), "{name}");
                assert!(left.verify(), "{name}");
            }
        }
    }

    // Over k[x]/x^3 the only indecomposable projective is the regular module P
    // of dimension 3, and the algebra is self-injective, so P is also the
    // injective envelope of every module. For M = k[x]/x^2,
    // Hom(M, P) = {p in P : x^2 p = 0} = span{x, x^2} has F_p dimension 2, and
    // Hom(M, P) . rad End(P) = span{x, x^2} . span{x, x^2} = span{x^2} has
    // dimension 1. The top is one-dimensional over the residue field
    // D = End(P)/rad End(P) = F_p, so the minimal left approximation uses one
    // copy of P: the injective envelope M -> P. The naive F_p count would take
    // two copies.
    #[test]
    fn a_truncated_polynomial_module_needs_one_copy_where_the_fp_count_says_two() {
        for field in fields() {
            let algebra = truncated_poly(3, field).unwrap();
            let p = Module::projective(&algebra, 0);
            let mut action = DenseMat::zero(2, 2);
            action.set(0, 1, field.one());
            let m = Module::new(algebra.clone(), vec![2], vec![action]).unwrap();
            assert_eq!(HomSpace::new(&m, &p).unwrap().dim(), 2);

            let a = left_approximation(&m, std::slice::from_ref(&p)).unwrap();
            assert_eq!(a.slots(), &[0], "one copy of P, not two");
            assert_eq!(a.map().target().dim_vector(), &[3]);
            assert_eq!(
                kernel(a.map()).0.total_dim(),
                0,
                "the envelope is injective"
            );

            // The minimality payload by value. f is mono, so
            // K_f = {h in End(P) : f.then(h) = 0} is the set of h vanishing on
            // the image span{x, x^2}, which is multiplication by x^2 alone: a
            // line. rad End(P) is span{x, x^2}, of dimension 2. The kernel row
            // is the first radical basis row, so its coordinates over that
            // basis are (1, 0).
            let endo = EndoAlgebra::new(a.map().target());
            assert_eq!(endo.dim(), 3);
            assert_eq!(endo.radical_dim(), 2);
            assert_eq!(a.kernel_basis().rows(), 1);
            assert_eq!(a.kernel_basis().row(0), endo.radical_basis().row(0));
            assert_eq!(a.radical_coordinates(0), &[field.one(), Fp::ZERO]);

            assert!(a.verify());
            assert!(left_property_holds(&a));
        }
    }

    // The Kronecker representation (I_3, C) over F_2 with C the companion
    // matrix of x^3 + x + 1, irreducible over F_2, so End(W) is the field F_8
    // and the residue degree is 3. Same module as `indec.rs` and
    // `arquiver.rs`. Hom(W, W) has F_2 dimension 3 and rad End(W) is zero, so
    // the radical part of the span starts at zero and one generator fills the
    // whole space: the multiplicity is 3 / 3 = 1, while an F_2 basis would give
    // 3 copies.
    #[test]
    fn a_residue_degree_three_summand_gets_one_copy_where_an_fp_basis_gives_three() {
        let field = f2();
        let algebra = kronecker(2, field);
        let identity3 = DenseMat::identity(3);
        let mut companion = DenseMat::zero(3, 3);
        companion.set(0, 1, field.one());
        companion.set(1, 2, field.one());
        companion.set(2, 0, field.one());
        companion.set(2, 1, field.one());
        let w = Module::new(algebra, vec![3, 3], vec![identity3, companion]).unwrap();
        let certified = IndecomposableModule::new(&w).unwrap();
        assert_eq!(certified.residue_degree(), 3, "the fixture must have d = 3");

        let fp_dim = HomSpace::new(&w, &w).unwrap().dim();
        assert_eq!(fp_dim, 3);

        let left = left_approximation(&w, std::slice::from_ref(&w)).unwrap();
        assert_eq!(left.multiplicity(0), fp_dim / 3);
        assert_eq!(left.multiplicity(0), 1);
        assert_eq!(left.map().target().dim_vector(), &[3, 3]);
        assert!(left.map().is_isomorphism());
        assert!(left.verify());
        assert!(left_property_holds(&left));
    }

    // The teeth of the minimality check. Take the genuine minimal left
    // approximation f: X -> B and pad it: B~ = B (+) N_k with f~ = f followed
    // by the inclusion of B, so the component into the extra copy is zero. f~ is
    // still a left approximation, since every map that factors through f factors
    // through f~. It is not minimal: the projection-inclusion idempotent of the
    // extra copy kills f~, and an idempotent outside the radical proves
    // K_{f~} leaves rad End(B~).
    #[test]
    fn a_padded_approximation_is_rejected_by_the_minimality_check() {
        let mut cases = 0;
        for field in fields() {
            for (name, algebra) in fixtures(field) {
                let generators = projectives(&algebra);
                for x in test_modules(&algebra) {
                    let a = left_approximation(&x, &generators).unwrap();
                    let context = format!("{name} over F_{}", field.modulus());
                    let endo = EndoAlgebra::new(a.map().target());
                    assert!(
                        radical_coordinates(&endo, a.kernel_basis()).is_ok(),
                        "{context}: the genuine approximation must be minimal"
                    );

                    let extra = &generators[0];
                    let mut parts: Vec<&Module> = a
                        .slots()
                        .iter()
                        .map(|&i| a.summands()[i].module())
                        .collect();
                    parts.push(extra);
                    let (padded, inclusions, projections) = direct_sum(&parts);
                    let mut padded_map = zero_morphism(&x, &padded).unwrap();
                    for (c, &i) in a.slots().iter().enumerate() {
                        let component = a
                            .map()
                            .then(&a.projections()[c])
                            .expect("the block projection follows f");
                        assert_eq!(
                            component.target().dim_vector(),
                            a.summands()[i].module().dim_vector()
                        );
                        let block = component.then(&inclusions[c]).unwrap();
                        padded_map = add_morphisms(&padded_map, &block);
                    }
                    let padded_endo = EndoAlgebra::new(&padded);
                    let padded_kernel = left_kernel_of(&padded_map, &padded_endo);
                    assert!(
                        radical_coordinates(&padded_endo, &padded_kernel).is_err(),
                        "{context}: the padded approximation must fail minimality"
                    );

                    // The padded map still approximates: it is the genuine one
                    // composed with a split monomorphism.
                    let last = projections.len() - 1;
                    assert!(
                        padded_map.then(&projections[last]).unwrap().is_zero(),
                        "{context}: the extra component is zero"
                    );
                    cases += 1;
                }
            }
        }
        assert_eq!(cases, 84);
    }

    // The same padding on one fixture where every number is hand-derivable,
    // so the defect is checked as a value rather than as `is_err()`.
    //
    // Over A_2 the minimal left add(P)-approximation of P_0 is the identity
    // P_0 -> P_0, one copy of P_0. Padding it with a second copy gives
    // B~ = P_0 (+) P_0 and f~ = (id, 0). Hom(P_0, P_0) = e_0 A e_0 = k, so
    // End(B~) is the 2 by 2 matrix algebra over k: dimension 4, semisimple,
    // rad End(B~) = 0. K_{f~} = {h : f~.then(h) = 0} is the set of matrices
    // whose first row is zero, of dimension 2. Nothing but zero fits inside a
    // zero radical, so the first kernel row already fails and the defect is
    // row 0 of a 2-dimensional kernel against a 0-dimensional radical.
    #[test]
    fn a_padded_approximation_reports_the_kernel_row_outside_the_radical() {
        for field in fields() {
            let algebra = linear_an(2, field);
            let x = Module::projective(&algebra, 0);
            let generators = projectives(&algebra);
            let a = left_approximation(&x, &generators).unwrap();
            assert_eq!(a.slots(), &[0], "the fixture uses one copy of P_0");

            let summands = certify(&generators).unwrap();
            let mut slots = a.slots().to_vec();
            slots.push(a.slots()[0]);
            let (padded, inclusions, _) = slot_sum(&x, &summands, &slots);
            let mut padded_map = zero_morphism(&x, &padded).unwrap();
            for (c, block) in inclusions.iter().enumerate().take(a.slots().len()) {
                let component = a.map().then(&a.projections()[c]).unwrap();
                padded_map = add_morphisms(&padded_map, &component.then(block).unwrap());
            }
            let endo = EndoAlgebra::new(&padded);
            assert_eq!(endo.dim(), 4);
            assert_eq!(endo.radical_dim(), 0);
            let kernel = left_kernel_of(&padded_map, &endo);
            assert_eq!(kernel.rows(), 2);
            let defect = radical_coordinates(&endo, &kernel)
                .map_err(|row| ApproxDefect::KernelOutsideRadical {
                    row,
                    kernel_dim: kernel.rows(),
                    radical_dim: endo.radical_dim(),
                })
                .unwrap_err();
            assert_eq!(
                defect,
                ApproxDefect::KernelOutsideRadical {
                    row: 0,
                    kernel_dim: 2,
                    radical_dim: 0,
                },
                "over F_{}",
                field.modulus()
            );
        }
    }

    // The same rejection through the public witness: a hand-built
    // MinimalLeftApproximation carrying the padded map fails verify(), because
    // verify() recomputes K_f and rechecks the radical containment.
    #[test]
    fn verify_rejects_a_witness_built_around_a_padded_map() {
        let field = f5();
        let algebra = linear_an(3, field);
        let x = Module::projective(&algebra, 0);
        let generators = projectives(&algebra);
        let a = left_approximation(&x, &generators).unwrap();
        assert_eq!(a.slots(), &[0], "the fixture uses one copy of P_0");

        let summands = certify(&generators).unwrap();
        let mut slots = a.slots().to_vec();
        slots.push(a.slots()[0]);
        let (padded, inclusions, projections) = slot_sum(&x, &summands, &slots);
        let mut padded_map = zero_morphism(&x, &padded).unwrap();
        for (c, block) in inclusions.iter().enumerate().take(a.slots().len()) {
            let component = a.map().then(&a.projections()[c]).unwrap();
            padded_map = add_morphisms(&padded_map, &component.then(block).unwrap());
        }
        let factorizations = left_factorizations(&padded_map, &summands);
        let endo = EndoAlgebra::new(&padded);
        let kernel = left_kernel_of(&padded_map, &endo);
        // Every row that is inside the radical gets its true coordinates, so
        // the only claim verify() can reject is the containment itself.
        let radical: Vec<Vec<Fp>> = (0..kernel.rows())
            .map(|r| {
                endo.radical_basis()
                    .transpose()
                    .solve(kernel.row(r), &field)
                    .unwrap_or_else(|| vec![Fp::ZERO; endo.radical_dim()])
            })
            .collect();
        let witness = MinimalLeftApproximation {
            map: padded_map,
            summands,
            slots,
            inclusions,
            projections,
            factorizations,
            kernel,
            radical,
        };
        assert!(!witness.verify(), "a padded map must not verify");
    }

    #[test]
    fn a_decomposable_add_generator_is_rejected_with_its_position() {
        let field = f5();
        let algebra = linear_an(3, field);
        let p0 = Module::projective(&algebra, 0);
        let (sum, _, _) = direct_sum(&[&p0, &p0]);
        let x = Module::simple(&algebra, 0);
        assert_eq!(
            left_approximation(&x, &[p0.clone(), sum]).unwrap_err(),
            ApproxError::SummandNotIndecomposable {
                index: 1,
                reason: IndecError::Decomposable { summands: 2 },
            }
        );
        assert_eq!(
            left_approximation(&x, &[Module::zero(&algebra)]).unwrap_err(),
            ApproxError::SummandNotIndecomposable {
                index: 0,
                reason: IndecError::Zero,
            }
        );
    }

    #[test]
    fn an_isomorphic_repeat_in_the_generator_list_is_rejected() {
        let field = f2();
        let algebra = linear_an(3, field);
        let p0 = Module::projective(&algebra, 0);
        let p1 = Module::projective(&algebra, 1);
        let x = Module::simple(&algebra, 2);
        assert_eq!(
            left_approximation(&x, &[p0.clone(), p1, p0]).unwrap_err(),
            ApproxError::RepeatedSummand {
                first: 0,
                second: 2
            }
        );
    }

    #[test]
    fn a_generator_from_another_algebra_is_a_typed_hom_error() {
        let x = Module::simple(&linear_an(2, f5()), 0);
        let other = Module::simple(&linear_an(2, f5()), 0);
        assert_eq!(
            left_approximation(&x, std::slice::from_ref(&other)).unwrap_err(),
            ApproxError::Hom(HomError::DifferentAlgebras)
        );
    }

    #[test]
    fn error_display_names_the_position_and_the_reason() {
        assert_eq!(
            ApproxError::RepeatedSummand {
                first: 0,
                second: 2
            }
            .to_string(),
            "add-generators 0 and 2 are isomorphic; give one module per class"
        );
        assert_eq!(
            ApproxError::Defect(ApproxDefect::GeneratorGrowth {
                summand: 1,
                growth: 2,
                residue_degree: 3,
            })
            .to_string(),
            "a generator for summand 1 raised the span by 2, not by the residue degree 3; \
             crate defect"
        );
    }

    // Over the commutative square the four projectives are pairwise
    // non-isomorphic and P_0 is projective-injective. The left approximation of
    // P_0 by add(P) is the identity, so K_f is zero.
    #[test]
    fn a_projective_approximated_by_the_projectives_gets_the_identity() {
        for field in fields() {
            let algebra = commutative_square(field);
            let p0 = Module::projective(&algebra, 0);
            let a = left_approximation(&p0, &projectives(&algebra)).unwrap();
            assert_eq!(a.slots(), &[0]);
            assert!(a.map().is_isomorphism());
            assert_eq!(a.kernel_basis().rows(), 0);
            assert!(a.verify());
        }
    }
}

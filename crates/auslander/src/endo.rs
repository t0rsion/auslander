//! The endomorphism algebra End(M) as a finite-dimensional algebra over F_p.
//!
//! Elements are coordinate vectors in the [`crate::homspace::HomSpace`] basis
//! of `Hom(M, M)`, read off the flattened vertex matrices of a morphism.
//! Multiplication goes through structure constants, each of them the composite
//! of two basis elements re-expressed in the basis. The table of constants is
//! built by the first [`EndoAlgebra::multiply`]: the radical, the semisimple
//! quotient, and locality read none of it.
//!
//! The Jacobson radical is exact in every characteristic. The Friedl-Rónyai chain
//! (Rónyai, "Computing the structure of finite algebras", J. Symbolic Comput. 9
//! (1990)) refines the trace-form kernel with the characteristic polynomial
//! coefficients `c_{p^i}`, which stay F_p-linear on each ideal of the chain. The
//! trace form alone is not enough in small characteristic, so the chain is run to
//! the end rather than trusted after its first step.

use std::fmt;
use std::sync::OnceLock;

use crate::field::{Fp, PrimeField};
use crate::hom::{Morphism, express_in_row_basis, identity};
use crate::homspace::{HomSpace, flat_row, row_times};
use crate::linalg::{DenseMat, RowReducer};
use crate::module::Module;

/// Columns at which a coordinate row can be read off `flat`, and the inverse of
/// the submatrix there when that submatrix is not the identity.
///
/// The coordinates `x` of `f` are the solution of `x · flat = flat_row(f)`, so
/// for any `dim` columns whose submatrix `S` is invertible, `x` is
/// `flat_row(f)` restricted to those columns times `S⁻¹`. [`crate::hom::hom_rows`]
/// hands back a kernel basis carrying a 1 in its own free column and 0 in every
/// other free column, in the [`flat_row`] layout, so the free columns give
/// `S = I` and reading coordinates off is a selection. The scan finds them
/// without knowing which columns were free: a column that is a unit vector
/// claims its row. The pivot columns are the fallback for a basis without that
/// shape.
fn coordinate_columns(flat: &DenseMat, field: &PrimeField) -> (Vec<usize>, Option<DenseMat>) {
    let unit_column = |c: usize| -> Option<usize> {
        let mut hit = None;
        for r in 0..flat.rows() {
            let v = flat.get(r, c);
            if v.is_zero() {
                continue;
            }
            if hit.is_some() || v != Fp::ONE {
                return None;
            }
            hit = Some(r);
        }
        hit
    };
    let mut cols = vec![usize::MAX; flat.rows()];
    let mut found = 0;
    for c in 0..flat.cols() {
        if let Some(r) = unit_column(c)
            && cols[r] == usize::MAX
        {
            cols[r] = c;
            found += 1;
            if found == flat.rows() {
                return (cols, None);
            }
        }
    }
    let (_, pivots) = flat.rref(field);
    let mut square = DenseMat::zero(flat.rows(), pivots.len());
    for (j, &c) in pivots.iter().enumerate() {
        for r in 0..flat.rows() {
            square.set(r, j, flat.get(r, c));
        }
    }
    let inverse = square
        .inverse(field)
        .expect("pivot columns are independent");
    (pivots, Some(inverse))
}

/// The endomorphism algebra of a fixed module, with its `Hom(M, M)` basis,
/// exact Jacobson radical, and structure constants built on demand.
#[derive(Clone)]
pub struct EndoAlgebra {
    module: Module,
    field: PrimeField,
    basis: Vec<Morphism>,
    // dim × Σ_v (dim M_v)² flattened basis, for expressing endomorphisms.
    flat: DenseMat,
    // One column of `flat` per basis element, and the inverse of the submatrix
    // there; see coordinate_columns.
    coord_cols: Vec<usize>,
    coord_inverse: Option<DenseMat>,
    // table[i * dim + j] = coordinates of basis[i].then(basis[j]), filled by
    // the first `multiply`.
    table: OnceLock<Vec<Vec<Fp>>>,
    one: Vec<Fp>,
    // Rows: coordinates of a radical basis, in reduced row echelon form.
    radical: DenseMat,
    // Pivot column of each radical row, in row order.
    radical_pivots: Vec<usize>,
    // Rows: coset representatives of a basis of End(M)/rad.
    complement: DenseMat,
    // dim × q. Quotient coordinates of an element are its coordinates times
    // this matrix: the last q columns of the inverse of the radical rows
    // stacked over the complement rows.
    quotient: DenseMat,
    // qtable[i * q + j] = quotient coordinates of complement[i] · complement[j].
    qtable: Vec<Vec<Fp>>,
    qone: Vec<Fp>,
    quotient_commutative: bool,
    // Rows: quotient coordinates of a basis of the center of End(M)/rad.
    center: DenseMat,
    // Rows: quotient coordinates of a basis of the Frobenius fixed space of
    // the center; its dimension is the number of Wedderburn factors.
    fixed: DenseMat,
}

impl fmt::Debug for EndoAlgebra {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("EndoAlgebra")
            .field("dim_vector", &self.module.dim_vector())
            .field("dim", &self.dim())
            .field("radical_dim", &self.radical_dim())
            .finish()
    }
}

impl EndoAlgebra {
    /// Builds `End(m)` from the [`HomSpace`] basis and runs the radical chain.
    pub fn new(m: &Module) -> EndoAlgebra {
        let mut endo = EndoAlgebra::over(
            m,
            HomSpace::new(m, m).expect("a module shares its own algebra"),
        );
        endo.radical = ronyai_radical(&endo);
        endo.analyze_quotient();
        endo
    }

    /// `End(s)` for a summand `s` of the module of `parent`, with the radical
    /// inherited instead of recomputed.
    ///
    /// `include: s → M` and `project: M → s` must split, that is
    /// `include.then(project) = id_s`. Write `e = project.then(include)`, an
    /// idempotent of `End(M)`. Then `g ↦ include.then(g).then(project)` is an
    /// algebra isomorphism from `e End(M) e` onto `End(s)`, and
    /// `rad(eAe) = e rad(A) e` (Lam, A First Course in Noncommutative Rings,
    /// 21.10), so the images of a basis of `rad End(M)` span `rad End(s)`.
    ///
    /// The basis stays the `Hom(s, s)` basis and the spanning set is reduced
    /// with `row_space_basis`, the same reduction [`ronyai_radical`] ends with, so
    /// the stored radical is the matrix [`EndoAlgebra::new`] would store.
    pub(crate) fn from_summand(
        s: &Module,
        parent: &EndoAlgebra,
        include: &Morphism,
        project: &Morphism,
    ) -> EndoAlgebra {
        let mut endo = EndoAlgebra::over(
            s,
            HomSpace::new(s, s).expect("a summand shares its algebra"),
        );
        let rows: Vec<Vec<Fp>> = (0..parent.radical_dim())
            .map(|r| {
                let corner = include
                    .then(&parent.morphism(parent.radical.row(r)))
                    .expect("the inclusion lands in the parent")
                    .then(project)
                    .expect("the projection starts at the parent");
                endo.express(&corner)
            })
            .collect();
        endo.radical = if rows.is_empty() {
            DenseMat::zero(0, endo.dim())
        } else {
            DenseMat::from_rows(&rows).row_space_basis(&endo.field)
        };
        endo.analyze_quotient();
        endo
    }

    // Everything the radical does not determine: the flattened basis, the
    // coordinate columns, and the identity.
    //
    // The whole basis is materialized here, unlike elsewhere: `multiply`
    // composes every pair of basis elements, so each one is used `2 dim` times.
    fn over(m: &Module, space: HomSpace) -> EndoAlgebra {
        let field = m.field();
        let (flat, basis) = space.into_parts();
        let (coord_cols, coord_inverse) = coordinate_columns(&flat, &field);
        let dim = basis.len();
        let mut endo = EndoAlgebra {
            module: m.clone(),
            field,
            basis,
            flat,
            coord_cols,
            coord_inverse,
            table: OnceLock::new(),
            one: Vec::new(),
            radical: DenseMat::zero(0, dim),
            radical_pivots: Vec::new(),
            complement: DenseMat::zero(0, dim),
            quotient: DenseMat::zero(0, 0),
            qtable: Vec::new(),
            qone: Vec::new(),
            quotient_commutative: true,
            center: DenseMat::zero(0, 0),
            fixed: DenseMat::zero(0, 0),
        };
        endo.one = endo.express(&identity(m));
        endo
    }

    // Coordinates of an endomorphism of this algebra's module, unchecked.
    fn express(&self, f: &Morphism) -> Vec<Fp> {
        let row = flat_row(f);
        let picked: Vec<Fp> = self.coord_cols.iter().map(|&c| row[c]).collect();
        match &self.coord_inverse {
            None => picked,
            Some(inverse) => row_times(&picked, inverse, &self.field),
        }
    }

    // Fills everything the radical determines: its pivot columns, a complement
    // basis, the quotient change of basis, the quotient structure constants,
    // commutativity, the center, and the Frobenius fixed space of the center.
    fn analyze_quotient(&mut self) {
        let field = self.field;
        let dim = self.dim();
        self.radical_pivots = (0..self.radical.rows())
            .map(|r| {
                (0..dim)
                    .find(|&c| !self.radical.get(r, c).is_zero())
                    .expect("a radical basis row is nonzero")
            })
            .collect();
        // Greedy over the unit vectors in index order: e_i joins the complement
        // when it is independent of the radical and of the earlier picks. This
        // is not the free-column set of the radical (for rad = span{e_0 + e_1}
        // the pick is e_0 and the free column is 1), and every quotient
        // coordinate in the crate is stated in the basis it selects.
        let mut reducer = RowReducer::new(dim);
        for r in 0..self.radical.rows() {
            reducer.push(self.radical.row(r), &field);
        }
        let complement_cols: Vec<usize> = (0..dim)
            .filter(|&i| {
                let mut unit = vec![Fp::ZERO; dim];
                unit[i] = Fp::ONE;
                reducer.push(&unit, &field)
            })
            .collect();
        let complement_rows: Vec<Vec<Fp>> = complement_cols
            .iter()
            .map(|&i| {
                let mut unit = vec![Fp::ZERO; dim];
                unit[i] = Fp::ONE;
                unit
            })
            .collect();
        self.complement = DenseMat::from_rows(&complement_rows);
        let q = complement_cols.len();
        let radical_rows = self.radical.rows();
        self.quotient = if dim == 0 {
            DenseMat::zero(0, 0)
        } else {
            let full: Vec<Vec<Fp>> = (0..radical_rows)
                .map(|r| self.radical.row(r).to_vec())
                .chain(complement_rows)
                .collect();
            let inverse = DenseMat::from_rows(&full)
                .inverse(&field)
                .expect("a complement of the radical completes it to a basis");
            let mut map = DenseMat::zero(dim, q);
            for r in 0..dim {
                for c in 0..q {
                    map.set(r, c, inverse.get(r, radical_rows + c));
                }
            }
            map
        };
        // Each complement row is a unit vector, so its products are single
        // structure constants and the full dim² table stays unbuilt.
        let mut qtable = Vec::with_capacity(q * q);
        for i in 0..q {
            for j in 0..q {
                let product = self.basis[complement_cols[i]]
                    .then(&self.basis[complement_cols[j]])
                    .expect("endomorphisms compose");
                let coords = self.express(&product);
                qtable.push(self.reduce(&coords));
            }
        }
        self.qtable = qtable;
        self.qone = self.reduce(&self.one);
        self.quotient_commutative =
            (0..q).all(|i| (0..i).all(|j| self.qtable[i * q + j] == self.qtable[j * q + i]));
        let mut cond_rows = Vec::new();
        for j in 0..q {
            for comp in 0..q {
                let mut row = vec![Fp::ZERO; q];
                for (i, entry) in row.iter_mut().enumerate() {
                    *entry = field.sub(self.qtable[i * q + j][comp], self.qtable[j * q + i][comp]);
                }
                cond_rows.push(row);
            }
        }
        self.center = if q == 0 {
            DenseMat::zero(0, 0)
        } else {
            DenseMat::from_rows(&cond_rows).kernel_basis(&field)
        };
        let c = self.center.rows();
        let mut frobenius = DenseMat::zero(c, c);
        for r in 0..c {
            let zp = self.qpow(self.center.row(r), field.modulus());
            let mut as_matrix = DenseMat::zero(1, q);
            for (col, &v) in zp.iter().enumerate() {
                as_matrix.set(0, col, v);
            }
            let in_center = express_in_row_basis(&self.center, &as_matrix, &field);
            for col in 0..c {
                frobenius.set(r, col, in_center.get(0, col));
            }
        }
        let mut shifted = frobenius;
        for i in 0..c {
            shifted.set(i, i, field.sub(shifted.get(i, i), Fp::ONE));
        }
        self.fixed = shifted.left_kernel_basis(&field).mul(&self.center, &field);
    }

    // Quotient coordinates of an element given in algebra coordinates: the
    // components along the complement basis after the stored change of basis.
    fn reduce(&self, coords: &[Fp]) -> Vec<Fp> {
        row_times(coords, &self.quotient, &self.field)
    }

    // Product in the quotient, both factors in quotient coordinates.
    fn qmul(&self, a: &[Fp], b: &[Fp]) -> Vec<Fp> {
        let q = self.quotient_dim();
        let mut out = vec![Fp::ZERO; q];
        for (i, &ai) in a.iter().enumerate() {
            if ai.is_zero() {
                continue;
            }
            for (j, &bj) in b.iter().enumerate() {
                if bj.is_zero() {
                    continue;
                }
                let c = self.field.mul(ai, bj);
                for (k, out_k) in out.iter_mut().enumerate() {
                    let t = self.field.mul(c, self.qtable[i * q + j][k]);
                    *out_k = self.field.add(*out_k, t);
                }
            }
        }
        out
    }

    fn qpow(&self, a: &[Fp], mut exp: u64) -> Vec<Fp> {
        let mut base = a.to_vec();
        let mut acc = self.qone.clone();
        while exp > 0 {
            if exp & 1 == 1 {
                acc = self.qmul(&acc, &base);
            }
            base = self.qmul(&base, &base);
            exp >>= 1;
        }
        acc
    }

    /// The module this is the endomorphism algebra of.
    #[inline]
    pub fn module(&self) -> &Module {
        &self.module
    }

    /// The field every coordinate is over: the field of [`EndoAlgebra::module`].
    ///
    /// Coordinates passed to [`EndoAlgebra::morphism`], [`EndoAlgebra::multiply`]
    /// and [`EndoAlgebra::in_radical`] must be canonical elements of this field;
    /// [`Fp`] carries no field identity, so the types do not check this.
    #[inline]
    pub fn field(&self) -> PrimeField {
        self.field
    }

    /// `dim_k End(M)`.
    #[inline]
    pub fn dim(&self) -> usize {
        self.basis.len()
    }

    /// The basis endomorphisms; coordinates index into this list.
    #[inline]
    pub fn basis(&self) -> &[Morphism] {
        &self.basis
    }

    /// Coordinates of the identity endomorphism.
    #[inline]
    pub fn one(&self) -> &[Fp] {
        &self.one
    }

    /// Coordinates of `f` in the basis, read off its flattened row.
    ///
    /// # Panics
    /// Panics unless both endpoints of `f` are this algebra's module in the
    /// sense of [`Module::ptr_eq`].
    pub fn coords(&self, f: &Morphism) -> Vec<Fp> {
        assert!(
            f.source().ptr_eq(&self.module) && f.target().ptr_eq(&self.module),
            "coords: not an endomorphism of this algebra's module"
        );
        self.express(f)
    }

    /// The endomorphism with the given coordinates, which must be canonical
    /// elements of [`EndoAlgebra::field`].
    ///
    /// The result skips the commuting-square check. `maps[v]` is
    /// `Σ_k coords[k] · basis[k]_v`, and each `basis[k]` is A-linear for this
    /// module, so at every arrow `a` the square is the same sum of squares:
    /// `Σ_k c_k (basis[k]_{s(a)} · M(a)) = Σ_k c_k (M(a) · basis[k]_{t(a)})`.
    /// `Hom_A(M, M)` is a subspace of the matrix tuples, so a linear
    /// combination of its elements stays in it. Each `maps[v]` starts as
    /// `DenseMat::zero(dim M_v, dim M_v)`, the right shape, and every entry
    /// comes from this algebra's own field.
    ///
    /// # Panics
    /// Panics unless `coords` has length [`EndoAlgebra::dim`].
    pub fn morphism(&self, coords: &[Fp]) -> Morphism {
        assert_eq!(coords.len(), self.dim(), "morphism: coordinate count");
        let mut maps: Vec<DenseMat> = self
            .module
            .dim_vector()
            .iter()
            .map(|&d| DenseMat::zero(d, d))
            .collect();
        for (k, &c) in coords.iter().enumerate() {
            if c.is_zero() {
                continue;
            }
            for (v, map) in maps.iter_mut().enumerate() {
                let block = self.basis[k].map_at(v as u32);
                for r in 0..map.rows() {
                    for j in 0..map.cols() {
                        let t = self.field.mul(c, block.get(r, j));
                        map.set(r, j, self.field.add(map.get(r, j), t));
                    }
                }
            }
        }
        Morphism::new_unchecked(&self.module, &self.module, maps)
    }

    /// The product `a · b` (first `a`, then `b`, matching [`Morphism::then`])
    /// through the structure constants. Both inputs must be coordinates of
    /// canonical elements of [`EndoAlgebra::field`].
    ///
    /// The first call composes all `dim²` basis pairs and keeps the table; the
    /// radical, the semisimple quotient, and locality need none of it.
    ///
    /// # Panics
    /// Panics unless both inputs have length [`EndoAlgebra::dim`].
    pub fn multiply(&self, a: &[Fp], b: &[Fp]) -> Vec<Fp> {
        let dim = self.dim();
        assert!(
            a.len() == dim && b.len() == dim,
            "multiply: coordinate count"
        );
        let table = self.table.get_or_init(|| {
            let mut table = Vec::with_capacity(dim * dim);
            for i in 0..dim {
                for j in 0..dim {
                    let product = self.basis[i]
                        .then(&self.basis[j])
                        .expect("endomorphisms compose");
                    table.push(self.express(&product));
                }
            }
            table
        });
        let mut out = vec![Fp::ZERO; dim];
        for (i, &ai) in a.iter().enumerate() {
            if ai.is_zero() {
                continue;
            }
            for (j, &bj) in b.iter().enumerate() {
                if bj.is_zero() {
                    continue;
                }
                let c = self.field.mul(ai, bj);
                for (k, out_k) in out.iter_mut().enumerate() {
                    let t = self.field.mul(c, table[i * dim + j][k]);
                    *out_k = self.field.add(*out_k, t);
                }
            }
        }
        out
    }

    /// A basis of the Jacobson radical, one coordinate vector per row, in
    /// reduced row echelon form.
    #[inline]
    pub fn radical_basis(&self) -> &DenseMat {
        &self.radical
    }

    /// `dim_k rad End(M)`.
    #[inline]
    pub fn radical_dim(&self) -> usize {
        self.radical.rows()
    }

    /// `dim_k End(M)/rad End(M)`, the dimension of the semisimple quotient.
    /// This is the residue degree only when `End(M)` is local, which
    /// [`EndoAlgebra::is_local`] decides; see
    /// [`crate::indec::IndecomposableModule::residue_degree`].
    #[inline]
    pub fn quotient_dim(&self) -> usize {
        self.complement.rows()
    }

    /// Whether the element with the given coordinates lies in the radical.
    /// The coordinates must be canonical elements of [`EndoAlgebra::field`].
    ///
    /// One reduction against the radical rows, which are in reduced row echelon
    /// form: `radical_dim · dim` field operations, no rank computation.
    ///
    /// # Panics
    /// Panics unless `coords` has length [`EndoAlgebra::dim`].
    pub fn in_radical(&self, coords: &[Fp]) -> bool {
        assert_eq!(coords.len(), self.dim(), "in_radical: coordinate count");
        let field = self.field;
        let mut v = coords.to_vec();
        for (r, &pivot) in self.radical_pivots.iter().enumerate() {
            let c = v[pivot];
            if c.is_zero() {
                continue;
            }
            for (k, x) in v.iter_mut().enumerate() {
                *x = field.sub(*x, field.mul(c, self.radical.get(r, k)));
            }
        }
        v.iter().all(|x| x.is_zero())
    }

    /// Whether the semisimple quotient `End(M)/rad` is commutative.
    #[inline]
    pub fn quotient_is_commutative(&self) -> bool {
        self.quotient_commutative
    }

    /// The number of Wedderburn factors of `End(M)/rad`: the dimension of the
    /// fixed space of the Frobenius `x ↦ x^p` on the center of the quotient
    /// (Berlekamp-style factor counting).
    #[inline]
    pub fn semisimple_factor_count(&self) -> usize {
        self.fixed.rows()
    }

    /// Whether `End(M)` is local: the quotient by the radical is a division
    /// algebra, which by Wedderburn means commutative with a single factor.
    /// Exact: the radical and the factor count are both exact. The zero algebra
    /// is not local, since `dim() == 0` fails the test outright.
    pub fn is_local(&self) -> bool {
        self.dim() > 0 && self.quotient_commutative && self.semisimple_factor_count() == 1
    }

    /// A nontrivial idempotent when the semisimple quotient has at least two
    /// factors: coordinates with `e² = e` and `e ∉ {0, 1}`, both verified before
    /// the return.
    ///
    /// A Frobenius fixed-space element outside `span{1}` has a squarefree minimal
    /// polynomial that splits over `F_p`, because the fixed space of the center is
    /// `F_p^r`. Its Lagrange projector at one root is a central idempotent of the
    /// quotient, and Newton iteration `e ↦ 3e² − 2e³` lifts that idempotent
    /// through the radical. Such an idempotent exists whenever the factor count is
    /// at least two.
    ///
    /// The Newton lift always converges inside its 64 rounds. With
    /// `δ = e² − e`, the iterate satisfies `f(e)² − f(e) = δ²·(4δ − 3)` in every
    /// characteristic, 2 and 3 included, so the error ideal squares each round;
    /// `δ` starts in the radical, and the radical is nilpotent of index at most
    /// `radical_dim + 1`, so `ceil(log2(radical_dim + 1))` rounds suffice. The
    /// 64 is a defensive stop, not a reachable budget.
    ///
    /// One budget is genuinely probabilistic: for `p > 4096` the seeded
    /// Cantor-Zassenhaus root search gives up after 64 draws (never observed in
    /// the test suite) and this returns `None`. Callers fall back to Fitting
    /// splits and, at worst, an honest `Undetermined`.
    pub(crate) fn split_idempotent(&self, rng: &mut SplitMix64) -> Option<Vec<Fp>> {
        if self.semisimple_factor_count() < 2 {
            return None;
        }
        let field = self.field;
        let q = self.quotient_dim();
        let f = (0..self.fixed.rows())
            .map(|r| self.fixed.row(r))
            .find(|f| {
                let mut stacked = DenseMat::zero(2, q);
                for c in 0..q {
                    stacked.set(0, c, self.qone[c]);
                    stacked.set(1, c, f[c]);
                }
                stacked.rank(&field) == 2
            })?;
        let minpoly = self.quotient_min_poly(f);
        let roots = split_squarefree_roots(&minpoly, &field, rng)?;
        let mut projector = vec![
            field.inv(
                roots[1..]
                    .iter()
                    .fold(Fp::ONE, |acc, &b| field.mul(acc, field.sub(roots[0], b))),
            ),
        ];
        for &b in &roots[1..] {
            let mut next = vec![Fp::ZERO; projector.len() + 1];
            for (k, &c) in projector.iter().enumerate() {
                next[k + 1] = field.add(next[k + 1], c);
                next[k] = field.sub(next[k], field.mul(b, c));
            }
            projector = next;
        }
        let mut ebar = vec![Fp::ZERO; q];
        for &c in projector.iter().rev() {
            ebar = self.qmul(&ebar, f);
            for (k, e_k) in ebar.iter_mut().enumerate() {
                *e_k = field.add(*e_k, field.mul(c, self.qone[k]));
            }
        }
        if self.qmul(&ebar, &ebar) != ebar || ebar.iter().all(|c| c.is_zero()) || ebar == self.qone
        {
            return None;
        }
        let mut e = vec![Fp::ZERO; self.dim()];
        for (i, &c) in ebar.iter().enumerate() {
            for (k, e_k) in e.iter_mut().enumerate() {
                *e_k = field.add(*e_k, field.mul(c, self.complement.get(i, k)));
            }
        }
        for _ in 0..64 {
            let square = self.multiply(&e, &e);
            if square == e {
                if e.iter().all(|c| c.is_zero()) || e == self.one {
                    return None;
                }
                return Some(e);
            }
            let cube = self.multiply(&square, &e);
            for (k, e_k) in e.iter_mut().enumerate() {
                let three = field.add(field.add(square[k], square[k]), square[k]);
                let two = field.add(cube[k], cube[k]);
                *e_k = field.sub(three, two);
            }
        }
        None
    }

    /// Coordinates of an element of `End(M)` that is neither invertible nor
    /// nilpotent, or `None` after `attempts` seeded draws.
    ///
    /// Fitting's lemma splits `M` along exactly such an element. A uniform draw
    /// does not work, because units are dense. A uniform element of
    /// `M_j(F_q)` is invertible with probability `1 - O(1/q)`, so a random
    /// endomorphism is almost always an automorphism and Fitting's lemma
    /// returns the trivial split. Instead draw `a`, split its minimal
    /// polynomial over `F_p` as `m = g·h` with `g` and `h` coprime and
    /// nonconstant, and return `g(a)`. Then `g(a)·h(a) = m(a) = 0` with
    /// `h(a) ≠ 0`, so `g(a)` is a zero divisor and hence a non-unit; and
    /// `g(a)^k = 0` would force `m | g^k`, impossible for a nonconstant `h`
    /// coprime to `g`, so `g(a)` is not nilpotent either.
    ///
    /// Splitting on a root `λ ∈ F_p` alone is not enough. When the residue
    /// field of a Wedderburn factor is a proper extension `F_{p^d}`, a drawn
    /// element of `M_j(F_{p^d})` has a base-field eigenvalue with probability
    /// `O(p^{1-d})`, so a root search almost never succeeds even though the
    /// factor is full of idempotents. Coprime factorization of the minimal
    /// polynomial covers that case: two eigenvalues that are not Frobenius
    /// conjugate contribute distinct irreducible factors, of equal degree when
    /// both generate `F_{p^d}`.
    ///
    /// Radical elements lift both properties: `g(a)` is a unit (nilpotent) in
    /// `End(M)` if and only if its image is a unit (nilpotent) in the
    /// quotient, because the radical is nilpotent.
    ///
    /// Returns `None` when the quotient is a division ring, and may return
    /// `None` after an unlucky streak: every drawn minimal polynomial was a
    /// prime power or not squarefree, or the shifts inside [`coprime_split`]
    /// never separated the factors. Callers treat that as an honest failure to
    /// split.
    pub(crate) fn singular_element(&self, rng: &mut SplitMix64, attempts: u32) -> Option<Vec<Fp>> {
        let field = self.field;
        let p = field.modulus();
        let q = self.quotient_dim();
        if q == 0 {
            return None;
        }
        for _ in 0..attempts {
            let abar: Vec<Fp> = (0..q).map(|_| field.elem(rng.below(p) as i64)).collect();
            let minpoly = self.quotient_min_poly(&abar);
            // Degree below two means the element is a scalar multiple of the
            // identity, whose minimal polynomial admits no coprime split.
            if minpoly.len() < 3 {
                continue;
            }
            let Some((g, _)) = coprime_split(&minpoly, &field, rng) else {
                continue;
            };
            let value = self.qpoly_eval(&g, &abar);
            let mut lifted = vec![Fp::ZERO; self.dim()];
            for (i, &c) in value.iter().enumerate() {
                for (k, out) in lifted.iter_mut().enumerate() {
                    *out = field.add(*out, field.mul(c, self.complement.get(i, k)));
                }
            }
            return Some(lifted);
        }
        None
    }

    /// `poly(f)` in the semisimple quotient, by Horner's rule.
    fn qpoly_eval(&self, poly: &[Fp], f: &[Fp]) -> Vec<Fp> {
        let field = self.field;
        let mut acc = vec![Fp::ZERO; self.quotient_dim()];
        for &c in poly.iter().rev() {
            acc = self.qmul(&acc, f);
            for (k, out) in acc.iter_mut().enumerate() {
                *out = field.add(*out, field.mul(c, self.qone[k]));
            }
        }
        acc
    }

    // The minimal polynomial (ascending, monic) of a quotient element: the
    // first power dependent on the earlier ones.
    fn quotient_min_poly(&self, f: &[Fp]) -> Vec<Fp> {
        let mut powers = vec![self.qone.clone()];
        loop {
            let next = self.qmul(powers.last().expect("powers start at f⁰"), f);
            let stack = DenseMat::from_rows(&powers);
            if let Some(x) = stack.transpose().solve(&next, &self.field) {
                let mut minpoly: Vec<Fp> = x.iter().map(|&c| self.field.neg(c)).collect();
                minpoly.push(Fp::ONE);
                return minpoly;
            }
            powers.push(next);
        }
    }
}

/// Seeded deterministic PRNG (splitmix64). The only randomness in the crate.
pub(crate) struct SplitMix64(pub(crate) u64);

impl SplitMix64 {
    pub(crate) fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    pub(crate) fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
}

fn poly_trim(mut a: Vec<Fp>) -> Vec<Fp> {
    while a.last().is_some_and(|c| c.is_zero()) {
        a.pop();
    }
    a
}

fn poly_eval(a: &[Fp], x: Fp, field: &PrimeField) -> Fp {
    let mut acc = Fp::ZERO;
    for &c in a.iter().rev() {
        acc = field.add(field.mul(acc, x), c);
    }
    acc
}

// Remainder of a modulo monic b (ascending coefficients, b nonempty).
fn poly_rem(a: &[Fp], b: &[Fp], field: &PrimeField) -> Vec<Fp> {
    let mut r = a.to_vec();
    let db = b.len() - 1;
    while r.len() > db {
        let lead = *r.last().expect("r is longer than b");
        let shift = r.len() - 1 - db;
        if !lead.is_zero() {
            for (i, &c) in b.iter().enumerate() {
                let t = field.mul(lead, c);
                r[shift + i] = field.sub(r[shift + i], t);
            }
        }
        r.pop();
    }
    poly_trim(r)
}

// Quotient of a by monic b, assuming b divides a exactly.
fn poly_quotient(a: &[Fp], b: &[Fp], field: &PrimeField) -> Vec<Fp> {
    let db = b.len() - 1;
    let mut r = a.to_vec();
    let mut quot = vec![Fp::ZERO; a.len() - db];
    while r.len() > db {
        let lead = *r.last().expect("r is longer than b");
        let shift = r.len() - 1 - db;
        quot[shift] = lead;
        if !lead.is_zero() {
            for (i, &c) in b.iter().enumerate() {
                let t = field.mul(lead, c);
                r[shift + i] = field.sub(r[shift + i], t);
            }
        }
        r.pop();
    }
    quot
}

// Monic gcd; zero polynomials are empty vectors.
fn poly_gcd(a: &[Fp], b: &[Fp], field: &PrimeField) -> Vec<Fp> {
    let (mut x, mut y) = (poly_trim(a.to_vec()), poly_trim(b.to_vec()));
    while !y.is_empty() {
        let lead_inv = field.inv(*y.last().expect("y is nonzero"));
        let monic: Vec<Fp> = y.iter().map(|&c| field.mul(c, lead_inv)).collect();
        y = poly_rem(&x, &monic, field);
        x = monic;
    }
    let lead_inv = field.inv(*x.last().expect("gcd of nonzero inputs is nonzero"));
    x.iter().map(|&c| field.mul(c, lead_inv)).collect()
}

fn poly_powmod(base: &[Fp], mut exp: u64, modulus: &[Fp], field: &PrimeField) -> Vec<Fp> {
    let mut b = poly_rem(base, modulus, field);
    let mut acc = vec![Fp::ONE];
    while exp > 0 {
        if exp & 1 == 1 {
            acc = poly_rem(&poly_mul(&acc, &b, field), modulus, field);
        }
        b = poly_rem(&poly_mul(&b, &b, field), modulus, field);
        exp >>= 1;
    }
    acc
}

fn poly_derivative(a: &[Fp], field: &PrimeField) -> Vec<Fp> {
    let mut out = Vec::with_capacity(a.len().saturating_sub(1));
    for (k, &c) in a.iter().enumerate().skip(1) {
        out.push(field.mul(c, field.elem(k as i64)));
    }
    poly_trim(out)
}

fn poly_mulmod(a: &[Fp], b: &[Fp], modulus: &[Fp], field: &PrimeField) -> Vec<Fp> {
    poly_rem(&poly_mul(a, b, field), modulus, field)
}

/// A factorization `poly = g·h` into coprime nonconstant factors, or `None`
/// when none was found: `poly` irreducible, `poly` not squarefree, or an
/// unlucky streak in the Berlekamp element search.
///
/// Berlekamp rather than distinct-degree factorization, because the factors
/// that matter here can share a degree. `End(W ⊕ W)` for `End(W) = F_{p^d}` is
/// `M_2(F_{p^d})`. A typical successful draw there has two eigenvalues that are
/// not Frobenius conjugate but both generate `F_{p^d}`. They contribute two
/// distinct irreducible factors of degree `d`. Grouping factors by degree
/// returns the whole polynomial and splits nothing. The Berlekamp subalgebra
/// `{v : v^p ≡ v mod poly}` has dimension equal to the number of distinct
/// irreducible factors, and any non-scalar element of it separates them.
///
/// A non-squarefree argument returns `None` rather than being handled: callers
/// draw again, and a fresh element of a semisimple algebra has a squarefree
/// minimal polynomial with high probability.
fn coprime_split(
    poly: &[Fp],
    field: &PrimeField,
    rng: &mut SplitMix64,
) -> Option<(Vec<Fp>, Vec<Fp>)> {
    let n = poly.len() - 1;
    if n < 2 {
        return None;
    }
    let derivative = poly_derivative(poly, field);
    if derivative.is_empty() || poly_gcd(poly, &derivative, field).len() > 1 {
        return None;
    }
    let p = field.modulus();
    // Row i of `frobenius` is x^{i·p} mod poly, so a coefficient row vector v
    // maps to v^p under multiplication on the right.
    let mut frobenius = DenseMat::zero(n, n);
    let step = poly_powmod(&[Fp::ZERO, Fp::ONE], p, poly, field);
    let mut current = vec![Fp::ONE];
    for i in 0..n {
        for (j, &c) in current.iter().enumerate() {
            frobenius.set(i, j, c);
        }
        current = poly_mulmod(&current, &step, poly, field);
    }
    for i in 0..n {
        frobenius.set(i, i, field.sub(frobenius.get(i, i), Fp::ONE));
    }
    let fixed = frobenius.left_kernel_basis(field);
    // The fixed space is spanned by the constants exactly when poly is
    // irreducible.
    let candidate = (0..fixed.rows())
        .map(|r| poly_trim(fixed.row(r).to_vec()))
        .find(|v| v.len() > 1)?;
    let proper = |g: &Vec<Fp>| g.len() > 1 && g.len() <= n;
    if p <= 4096 {
        for s in 0..p as i64 {
            let mut shifted = candidate.clone();
            shifted[0] = field.sub(shifted[0], field.elem(s));
            let g = poly_gcd(poly, &poly_trim(shifted), field);
            if proper(&g) {
                return Some((g.clone(), poly_quotient(poly, &g, field)));
            }
        }
        return None;
    }
    for _ in 0..64 {
        let mut shifted = candidate.clone();
        shifted[0] = field.sub(shifted[0], field.elem(rng.below(p) as i64));
        let shifted = poly_trim(shifted);
        let g = poly_gcd(poly, &shifted, field);
        if proper(&g) {
            return Some((g.clone(), poly_quotient(poly, &g, field)));
        }
        let mut powered = poly_powmod(&shifted, (p - 1) / 2, poly, field);
        if powered.is_empty() {
            powered.push(Fp::ZERO);
        }
        powered[0] = field.sub(powered[0], Fp::ONE);
        let g = poly_gcd(poly, &poly_trim(powered), field);
        if proper(&g) {
            return Some((g.clone(), poly_quotient(poly, &g, field)));
        }
    }
    None
}

/// The roots of a monic polynomial known to split into distinct linear factors
/// over F_p: a full scan of the field for `p ≤ 4096`, otherwise seeded
/// Cantor-Zassenhaus splitting with `gcd(m, (x + δ)^{(p−1)/2} − 1)` and 64 draws.
///
/// The caller guarantees the input splits, so `None` means a failed coin-flip
/// streak on the large-`p` path, never a wrong answer. The scan path returns
/// `None` only if it finds fewer roots than the degree, which means the
/// guarantee was broken.
fn split_squarefree_roots(
    poly: &[Fp],
    field: &PrimeField,
    rng: &mut SplitMix64,
) -> Option<Vec<Fp>> {
    let degree = poly.len() - 1;
    let p = field.modulus();
    if p <= 4096 {
        let roots: Vec<Fp> = (0..p as i64)
            .map(|a| field.elem(a))
            .filter(|&a| poly_eval(poly, a, field).is_zero())
            .collect();
        return (roots.len() == degree).then_some(roots);
    }
    if degree == 0 {
        return Some(Vec::new());
    }
    if degree == 1 {
        return Some(vec![field.neg(poly[0])]);
    }
    for _ in 0..64 {
        let delta = field.elem(rng.below(p) as i64);
        let base = vec![delta, Fp::ONE];
        let mut shifted = poly_powmod(&base, (p - 1) / 2, poly, field);
        if shifted.is_empty() {
            shifted.push(Fp::ZERO);
        }
        shifted[0] = field.sub(shifted[0], Fp::ONE);
        let shifted = poly_trim(shifted);
        if shifted.is_empty() {
            continue;
        }
        let g = poly_gcd(poly, &shifted, field);
        if g.len() - 1 == 0 || g.len() - 1 == degree {
            continue;
        }
        let h = poly_quotient(poly, &g, field);
        let mut roots = split_squarefree_roots(&g, field, rng)?;
        roots.extend(split_squarefree_roots(&h, field, rng)?);
        return Some(roots);
    }
    None
}

/// Coefficients of `det(X·I − a)` in ascending powers of `X` (length
/// `n + 1`, leading coefficient 1): Hessenberg reduction by similarity, then
/// the leading-minor recurrence, both valid over any field.
fn char_poly(a: &DenseMat, field: &PrimeField) -> Vec<Fp> {
    let n = a.rows();
    assert_eq!(a.cols(), n, "char_poly: matrix is not square");
    let mut h = a.clone();
    for col in 0..n.saturating_sub(2) {
        let Some(t) = ((col + 1)..n).find(|&r| !h.get(r, col).is_zero()) else {
            continue;
        };
        if t != col + 1 {
            for c in 0..n {
                let (x, y) = (h.get(t, c), h.get(col + 1, c));
                h.set(t, c, y);
                h.set(col + 1, c, x);
            }
            for r in 0..n {
                let (x, y) = (h.get(r, t), h.get(r, col + 1));
                h.set(r, t, y);
                h.set(r, col + 1, x);
            }
        }
        let pivinv = field.inv(h.get(col + 1, col));
        for i in (col + 2)..n {
            let u = field.mul(h.get(i, col), pivinv);
            if u.is_zero() {
                continue;
            }
            for c in 0..n {
                let t = field.mul(u, h.get(col + 1, c));
                h.set(i, c, field.sub(h.get(i, c), t));
            }
            for r in 0..n {
                let t = field.mul(u, h.get(r, i));
                h.set(r, col + 1, field.add(h.get(r, col + 1), t));
            }
        }
    }
    let mut polys: Vec<Vec<Fp>> = Vec::with_capacity(n + 1);
    polys.push(vec![Fp::ONE]);
    for m in 1..=n {
        let mut pm = vec![Fp::ZERO; m + 1];
        for (k, &c) in polys[m - 1].iter().enumerate() {
            pm[k + 1] = field.add(pm[k + 1], c);
            let t = field.mul(h.get(m - 1, m - 1), c);
            pm[k] = field.sub(pm[k], t);
        }
        let mut sub = Fp::ONE;
        for i in (1..m).rev() {
            sub = field.mul(sub, h.get(i, i - 1));
            if sub.is_zero() {
                break;
            }
            let coeff = field.mul(h.get(i - 1, m - 1), sub);
            if coeff.is_zero() {
                continue;
            }
            for (k, &c) in polys[i - 1].iter().enumerate() {
                pm[k] = field.sub(pm[k], field.mul(coeff, c));
            }
        }
        polys.push(pm);
    }
    polys.pop().expect("polys holds p_0..p_n")
}

fn poly_mul(a: &[Fp], b: &[Fp], field: &PrimeField) -> Vec<Fp> {
    let mut out = vec![Fp::ZERO; a.len() + b.len() - 1];
    for (i, &x) in a.iter().enumerate() {
        if x.is_zero() {
            continue;
        }
        for (j, &y) in b.iter().enumerate() {
            let t = field.mul(x, y);
            out[i + j] = field.add(out[i + j], t);
        }
    }
    out
}

/// Characteristic polynomial of `f` acting on `⊕_v M_v` (ascending powers):
/// the product of the vertex-block characteristic polynomials.
fn morphism_char_poly(f: &Morphism, field: &PrimeField) -> Vec<Fp> {
    let mut acc = vec![Fp::ONE];
    for v in 0..f.source().algebra().quiver().num_vertices() {
        acc = poly_mul(&acc, &char_poly(f.map_at(v), field), field);
    }
    acc
}

/// The first chain round in closed form: `−tr(b_k·b_j)` over the basis.
///
/// The round starts from the whole algebra, so its generators are the basis
/// itself, and its coefficient `c_1` of a product is minus the trace of that
/// product on `⊕_v M_v`. Since `tr(A·B)` sums `A[r][s]·B[s][r]`, the whole Gram
/// matrix is one product of the flattened basis with its blockwise transpose:
/// no composition, no characteristic polynomial, no `Morphism` allocated.
fn trace_form(e: &EndoAlgebra) -> DenseMat {
    let field = e.field;
    let mut transposed = DenseMat::zero(e.dim(), e.flat.cols());
    let mut offset = 0;
    for &d in e.module.dim_vector() {
        for r in 0..d {
            for c in 0..d {
                for k in 0..e.dim() {
                    transposed.set(k, offset + r * d + c, e.flat.get(k, offset + c * d + r));
                }
            }
        }
        offset += d * d;
    }
    let mut gram = transposed.mul(&e.flat.transpose(), &field);
    for r in 0..gram.rows() {
        for c in 0..gram.cols() {
            gram.set(r, c, field.neg(gram.get(r, c)));
        }
    }
    gram
}

/// The Friedl-Rónyai chain: `B_{-1} = End(M)` and, for `p^i ≤ n = dim_k M`,
/// `B_i = {x ∈ B_{i-1} : c_{p^i}(x·y) = 0 for all y ∈ B_{i-1}}` where `c_j` is
/// the degree-`n − j` characteristic-polynomial coefficient on `⊕_v M_v`. The
/// last chain member is exactly the radical.
///
/// The bound `p^i ≤ dim_k M` is the one for a subalgebra of `End(V)`: Cohen,
/// Ivanyos and Wales, "Finding the radical of an algebra of linear
/// transformations", J. Pure Appl. Algebra 117/118 (1997). Rónyai works from
/// structure constants, so his bound is over `dim_k End(M)`, usually the larger
/// of the two. Running to that bound instead changes nothing: after the rounds
/// below, `x·y` is nilpotent for `x` and `y` in the chain member, so every
/// coefficient a later round reads is zero and every later kernel is the whole
/// member.
fn ronyai_radical(e: &EndoAlgebra) -> DenseMat {
    let field = e.field;
    let n = e.module.total_dim();
    if e.dim() == 0 {
        return DenseMat::zero(0, 0);
    }
    let p = field.modulus();
    let mut cur = trace_form(e).kernel_basis(&field);
    let mut power = 1u64;
    while power * p <= n as u64 && cur.rows() > 0 {
        power *= p;
        let gens: Vec<Morphism> = (0..cur.rows()).map(|r| e.morphism(cur.row(r))).collect();
        let mut cond = DenseMat::zero(gens.len(), gens.len());
        for (j, gj) in gens.iter().enumerate() {
            for (k, gk) in gens.iter().enumerate() {
                let product = gj.then(gk).expect("endomorphisms compose");
                let cp = morphism_char_poly(&product, &field);
                cond.set(k, j, cp[n - power as usize]);
            }
        }
        cur = cond.kernel_basis(&field).mul(&cur, &field);
    }
    cur.row_space_basis(&field)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{
        an_with_relations, cyclic_nakayama, dual_numbers, kronecker, linear_an,
        radical_square_zero_cycle, truncated_poly,
    };
    use crate::module::direct_sum;

    fn f5() -> PrimeField {
        PrimeField::new(5).unwrap()
    }

    fn unit(dim: usize, k: usize, field: &PrimeField) -> Vec<Fp> {
        let mut v = vec![field.zero(); dim];
        v[k] = field.one();
        v
    }

    // Modules with radicals, matrix blocks, and repeated summands, over every
    // field of `fields()`. The endomorphism-algebra fixture set.
    fn fixture_modules() -> Vec<Module> {
        let mut out = Vec::new();
        for field in fields() {
            let a3 = linear_an(3, field);
            let dn = dual_numbers(field);
            let tp = truncated_poly(3, field).unwrap();
            let rel = an_with_relations(3, &[(0, 2)], field).unwrap();
            let singles = [
                Module::projective(&a3, 0),
                Module::simple(&a3, 1),
                Module::projective(&dn, 0),
                Module::projective(&tp, 0),
                Module::projective(&rel, 0),
                Module::projective(&kronecker(2, field), 0),
            ];
            for m in &singles {
                let (double, _, _) = direct_sum(&[m, m]);
                out.push(m.clone());
                out.push(double);
            }
            let (mixed, _, _) = direct_sum(&[
                &Module::projective(&a3, 0),
                &Module::simple(&a3, 0),
                &Module::simple(&a3, 2),
            ]);
            out.push(mixed);
            out.push(kronecker_f4_module());
        }
        out
    }

    #[test]
    fn end_of_a_simple_is_one_dimensional() {
        let a = linear_an(3, f5());
        let e = EndoAlgebra::new(&Module::simple(&a, 0));
        assert_eq!(e.dim(), 1);
        assert_eq!(e.multiply(e.one(), e.one()), e.one().to_vec());
    }

    #[test]
    fn field_is_the_field_of_the_module() {
        let a = linear_an(3, f5());
        let e = EndoAlgebra::new(&Module::simple(&a, 0));
        assert_eq!(e.field(), f5());
    }

    #[test]
    fn end_of_the_zero_module_is_zero_dimensional() {
        let a = linear_an(3, f5());
        let e = EndoAlgebra::new(&Module::zero(&a));
        assert_eq!(e.dim(), 0);
        assert!(e.one().is_empty());
    }

    #[test]
    fn end_of_the_dual_numbers_regular_module_has_dimension_2() {
        let a = dual_numbers(f5());
        let e = EndoAlgebra::new(&Module::projective(&a, 0));
        assert_eq!(e.dim(), 2);
    }

    #[test]
    fn structure_constants_reproduce_composition() {
        let field = f5();
        let a = linear_an(2, field);
        let p0 = Module::projective(&a, 0);
        let p1 = Module::projective(&a, 1);
        let (sum, _, _) = direct_sum(&[&p0, &p1]);
        let e = EndoAlgebra::new(&sum);
        assert_eq!(e.dim(), 3);
        for i in 0..e.dim() {
            for j in 0..e.dim() {
                let product = e.basis()[i].then(&e.basis()[j]).unwrap();
                assert_eq!(
                    e.multiply(&unit(e.dim(), i, &field), &unit(e.dim(), j, &field)),
                    e.coords(&product),
                    "b_{i} · b_{j}"
                );
            }
        }
    }

    #[test]
    fn one_is_neutral_and_multiplication_is_associative_on_basis_triples() {
        let field = f5();
        let a = dual_numbers(field);
        let p = Module::projective(&a, 0);
        let (sum, _, _) = direct_sum(&[&p, &p]);
        let e = EndoAlgebra::new(&sum);
        let units: Vec<Vec<Fp>> = (0..e.dim()).map(|k| unit(e.dim(), k, &field)).collect();
        for x in &units {
            assert_eq!(e.multiply(e.one(), x), *x);
            assert_eq!(e.multiply(x, e.one()), *x);
            for y in &units {
                for z in &units {
                    assert_eq!(
                        e.multiply(&e.multiply(x, y), z),
                        e.multiply(x, &e.multiply(y, z))
                    );
                }
            }
        }
    }

    struct XorShift64(u64);

    impl XorShift64 {
        fn next_u64(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }

        fn below(&mut self, n: u64) -> u64 {
            self.next_u64() % n
        }
    }

    fn fields() -> [PrimeField; 3] {
        [
            PrimeField::new(2).unwrap(),
            PrimeField::new(3).unwrap(),
            PrimeField::new(5).unwrap(),
        ]
    }

    #[test]
    fn char_poly_of_a_companion_matrix_recovers_its_polynomial() {
        let field = f5();
        // Companion matrix of x³ + 2x² + 3x + 4 in the row convention.
        let rows = vec![
            vec![field.elem(0), field.elem(1), field.elem(0)],
            vec![field.elem(0), field.elem(0), field.elem(1)],
            vec![field.elem(-4), field.elem(-3), field.elem(-2)],
        ];
        assert_eq!(
            char_poly(&DenseMat::from_rows(&rows), &field),
            vec![field.elem(4), field.elem(3), field.elem(2), field.elem(1)]
        );
        assert_eq!(char_poly(&DenseMat::zero(0, 0), &field), vec![field.one()]);
    }

    #[test]
    fn char_poly_satisfies_cayley_hamilton_on_random_matrices() {
        let mut rng = XorShift64(0x0005_eed0_c4a1_e401);
        for field in fields() {
            let p = field.modulus();
            for _ in 0..25 {
                let n = 1 + rng.below(6) as usize;
                let mut a = DenseMat::zero(n, n);
                for r in 0..n {
                    for c in 0..n {
                        a.set(r, c, field.elem(rng.below(p) as i64));
                    }
                }
                let cp = char_poly(&a, &field);
                let mut acc = DenseMat::zero(n, n);
                for &coeff in cp.iter().rev() {
                    acc = acc.mul(&a, &field);
                    for i in 0..n {
                        acc.set(i, i, field.add(acc.get(i, i), coeff));
                    }
                }
                assert_eq!(acc, DenseMat::zero(n, n), "p = {p}, n = {n}");
            }
        }
    }

    #[test]
    fn radical_of_end_of_a_simple_is_zero() {
        for field in fields() {
            let a = linear_an(3, field);
            let e = EndoAlgebra::new(&Module::simple(&a, 1));
            assert_eq!(e.radical_dim(), 0, "p = {}", field.modulus());
        }
    }

    // End(P_v) ≅ e_v A e_v; for these fixtures the only path v → v is trivial,
    // so every End(P_v) is k and the radical vanishes.
    #[test]
    fn radical_of_end_of_indecomposable_projectives_matches_path_counts() {
        for field in fields() {
            for algebra in [
                linear_an(3, field),
                kronecker(2, field),
                cyclic_nakayama(&[3, 3, 3], field).unwrap(),
                radical_square_zero_cycle(3, field),
            ] {
                for v in 0..algebra.quiver().num_vertices() {
                    let e = EndoAlgebra::new(&Module::projective(&algebra, v));
                    assert_eq!(e.dim(), 1, "End P_{v} over F_{}", field.modulus());
                    assert_eq!(e.radical_dim(), 0, "rad End P_{v}");
                }
            }
        }
    }

    // End of the regular module k[x]/(xⁿ) is k[x]/(xⁿ) itself: radical (x).
    #[test]
    fn radical_of_end_of_truncated_polynomial_regular_modules_has_codimension_1() {
        for field in fields() {
            for n in 2..=4 {
                let a = truncated_poly(n, field).unwrap();
                let e = EndoAlgebra::new(&Module::projective(&a, 0));
                assert_eq!(e.dim(), n, "p = {}", field.modulus());
                assert_eq!(e.radical_dim(), n - 1, "p = {}", field.modulus());
            }
        }
    }

    // The quotient module k[x]/(x²) over k[x]/(x³) has End = k[x]/(x²).
    #[test]
    fn radical_of_end_of_a_truncated_polynomial_quotient_module_is_known() {
        for field in fields() {
            let a = truncated_poly(3, field).unwrap();
            let x = DenseMat::from_rows(&[
                vec![field.zero(), field.one()],
                vec![field.zero(), field.zero()],
            ]);
            let m = Module::new(a, vec![2], vec![x]).unwrap();
            let e = EndoAlgebra::new(&m);
            assert_eq!(e.dim(), 2);
            assert_eq!(e.radical_dim(), 1);
        }
    }

    #[test]
    fn radical_of_end_of_a_sum_of_distinct_simples_is_zero() {
        for field in fields() {
            let a = linear_an(3, field);
            let s0 = Module::simple(&a, 0);
            let s1 = Module::simple(&a, 1);
            let (sum, _, _) = direct_sum(&[&s0, &s1]);
            let e = EndoAlgebra::new(&sum);
            assert_eq!(e.dim(), 2);
            assert_eq!(e.radical_dim(), 0);
        }
    }

    // End(S ⊕ S) ≅ M_2(F_p) is semisimple. On M_2(F_2) the trace form of the
    // regular representation vanishes identically, because it is twice the matrix
    // trace form. A radical test built on that form would return the whole algebra
    // at p = 2; the chain used here returns 0.
    #[test]
    fn radical_of_a_2x2_matrix_algebra_is_zero() {
        for field in fields() {
            let a = linear_an(3, field);
            let s = Module::simple(&a, 0);
            let (sum, _, _) = direct_sum(&[&s, &s]);
            let e = EndoAlgebra::new(&sum);
            assert_eq!(e.dim(), 4);
            assert_eq!(e.radical_dim(), 0, "p = {}", field.modulus());
        }
    }

    // End(A ⊕ A) ≅ M_2(k[ε]) for the dual numbers: radical M_2(εk).
    #[test]
    fn radical_of_end_of_a_doubled_dual_numbers_module_has_dimension_4() {
        for field in fields() {
            let a = dual_numbers(field);
            let p = Module::projective(&a, 0);
            let (sum, _, _) = direct_sum(&[&p, &p]);
            let e = EndoAlgebra::new(&sum);
            assert_eq!(e.dim(), 8);
            assert_eq!(e.radical_dim(), 4, "p = {}", field.modulus());
        }
    }

    #[test]
    fn radical_elements_are_nilpotent_and_the_radical_is_an_ideal() {
        for field in fields() {
            let a = an_with_relations(3, &[(0, 2)], field).unwrap();
            let p0 = Module::projective(&a, 0);
            let s0 = Module::simple(&a, 0);
            let (sum, _, _) = direct_sum(&[&p0, &s0]);
            let e = EndoAlgebra::new(&sum);
            assert!(e.radical_dim() > 0);
            for r in 0..e.radical_dim() {
                let x = e.morphism(e.radical_basis().row(r));
                let mut power = x.clone();
                for _ in 1..sum.total_dim() {
                    power = power.then(&x).unwrap();
                }
                assert!(power.is_zero(), "radical element is nilpotent");
                for k in 0..e.dim() {
                    let b = &e.basis()[k];
                    assert!(e.in_radical(&e.coords(&b.then(&x).unwrap())));
                    assert!(e.in_radical(&e.coords(&x.then(b).unwrap())));
                }
            }
            assert!(!e.in_radical(e.one()));
        }
    }

    #[test]
    fn end_of_a_simple_and_of_uniserial_projectives_is_local() {
        for field in fields() {
            let a3 = linear_an(3, field);
            assert!(EndoAlgebra::new(&Module::simple(&a3, 0)).is_local());
            assert!(EndoAlgebra::new(&Module::projective(&a3, 0)).is_local());
            for n in 2..=4 {
                let a = truncated_poly(n, field).unwrap();
                let e = EndoAlgebra::new(&Module::projective(&a, 0));
                assert!(e.is_local(), "k[x]/(x^{n}) over F_{}", field.modulus());
                assert!(e.quotient_is_commutative());
                assert_eq!(e.semisimple_factor_count(), 1);
            }
        }
    }

    #[test]
    fn end_of_a_sum_of_distinct_simples_has_two_commutative_factors() {
        for field in fields() {
            let a = linear_an(3, field);
            let s0 = Module::simple(&a, 0);
            let s1 = Module::simple(&a, 1);
            let (sum, _, _) = direct_sum(&[&s0, &s1]);
            let e = EndoAlgebra::new(&sum);
            assert!(e.quotient_is_commutative());
            assert_eq!(e.semisimple_factor_count(), 2);
            assert!(!e.is_local());
        }
    }

    // End(S ⊕ S) ≅ M_2(F_p): radical zero yet neither commutative nor local,
    // and a single Wedderburn factor.
    #[test]
    fn a_2x2_matrix_algebra_is_semisimple_but_neither_commutative_nor_local() {
        for field in fields() {
            let a = linear_an(3, field);
            let s = Module::simple(&a, 0);
            let (sum, _, _) = direct_sum(&[&s, &s]);
            let e = EndoAlgebra::new(&sum);
            assert_eq!(e.radical_dim(), 0);
            assert!(!e.quotient_is_commutative());
            assert_eq!(e.semisimple_factor_count(), 1);
            assert!(!e.is_local());
        }
    }

    #[test]
    fn end_of_p0_plus_s0_has_a_radical_and_two_factors() {
        for field in fields() {
            let a = linear_an(3, field);
            let p0 = Module::projective(&a, 0);
            let s0 = Module::simple(&a, 0);
            let (sum, _, _) = direct_sum(&[&p0, &s0]);
            let e = EndoAlgebra::new(&sum);
            assert_eq!(e.dim(), 3);
            assert_eq!(e.radical_dim(), 1);
            assert!(e.quotient_is_commutative());
            assert_eq!(e.semisimple_factor_count(), 2);
            assert!(!e.is_local());
        }
    }

    #[test]
    fn the_zero_endomorphism_algebra_is_not_local() {
        let a = linear_an(3, f5());
        let e = EndoAlgebra::new(&Module::zero(&a));
        assert!(!e.is_local());
        assert_eq!(e.semisimple_factor_count(), 0);
    }

    #[test]
    fn split_idempotent_is_exact_nontrivial_and_deterministic() {
        for field in fields() {
            let a = linear_an(3, field);
            let p0 = Module::projective(&a, 0);
            let s0 = Module::simple(&a, 0);
            let (sum, _, _) = direct_sum(&[&p0, &s0]);
            let e = EndoAlgebra::new(&sum);
            let first = e.split_idempotent(&mut SplitMix64(7)).unwrap();
            let again = e.split_idempotent(&mut SplitMix64(7)).unwrap();
            assert_eq!(first, again, "seeded run is reproducible");
            assert_eq!(e.multiply(&first, &first), first);
            assert!(first.iter().any(|c| !c.is_zero()));
            assert_ne!(first, e.one().to_vec());
        }
    }

    #[test]
    fn singular_element_is_a_non_unit_that_is_not_nilpotent() {
        // End(P ⊕ P) = M_2(k[x]/(x²)), whose semisimple quotient M_2(k) is a
        // single Wedderburn factor, so split_idempotent declines and this is
        // the only route to a split.
        for field in [f5(), PrimeField::new(32003).unwrap()] {
            let a = dual_numbers(field);
            let p = Module::projective(&a, 0);
            let (sum, _, _) = direct_sum(&[&p, &p]);
            let e = EndoAlgebra::new(&sum);
            assert_eq!(e.semisimple_factor_count(), 1);
            assert!(e.split_idempotent(&mut SplitMix64(7)).is_none());

            let coords = e
                .singular_element(&mut SplitMix64(7), 64)
                .expect("M_2(k) contains non-units that are not nilpotent");
            let phi = e.morphism(&coords);
            assert!(
                !phi.is_isomorphism(),
                "a unit gives the trivial Fitting split"
            );
            let mut power = phi.clone();
            for _ in 0..sum.total_dim() {
                power = power.then(&phi).expect("endomorphisms compose");
            }
            assert!(
                !power.is_zero(),
                "a nilpotent gives the trivial Fitting split"
            );
            let again = e.singular_element(&mut SplitMix64(7), 64).unwrap();
            assert_eq!(coords, again, "seeded run is reproducible");
        }
    }

    #[test]
    fn singular_element_is_none_for_a_local_algebra() {
        for field in fields() {
            let a = dual_numbers(field);
            let p = Module::projective(&a, 0);
            let e = EndoAlgebra::new(&p);
            assert!(e.is_local());
            assert!(e.singular_element(&mut SplitMix64(11), 64).is_none());
        }
    }

    #[test]
    fn split_idempotent_is_none_for_local_and_single_factor_algebras() {
        let field = f5();
        let a = linear_an(3, field);
        let p0 = Module::projective(&a, 0);
        assert!(
            EndoAlgebra::new(&p0)
                .split_idempotent(&mut SplitMix64(7))
                .is_none()
        );
        let s = Module::simple(&a, 0);
        let (sum, _, _) = direct_sum(&[&s, &s]);
        // M_2(F_p) has one factor: the central route cannot split it.
        assert!(
            EndoAlgebra::new(&sum)
                .split_idempotent(&mut SplitMix64(7))
                .is_none()
        );
    }

    // p = 1000003 is past the 4096 scan threshold, so this forces the
    // Cantor-Zassenhaus path through gcd(m, (x + δ)^{(p−1)/2} − 1).
    #[test]
    fn split_idempotent_works_over_a_large_prime_via_cantor_zassenhaus() {
        let field = PrimeField::new(1_000_003).unwrap();
        let a = linear_an(2, field);
        let s0 = Module::simple(&a, 0);
        let s1 = Module::simple(&a, 1);
        let (sum, _, _) = direct_sum(&[&s0, &s1]);
        let e = EndoAlgebra::new(&sum);
        assert_eq!(e.semisimple_factor_count(), 2);
        let idem = e.split_idempotent(&mut SplitMix64(7)).unwrap();
        assert_eq!(e.multiply(&idem, &idem), idem);
        assert!(idem.iter().any(|c| !c.is_zero()));
        assert_ne!(idem, e.one().to_vec());
    }

    #[test]
    fn split_squarefree_roots_recovers_all_roots() {
        let field = f5();
        // (x − 1)(x − 3) = x² − 4x + 3.
        let poly = vec![field.elem(3), field.elem(-4), field.one()];
        let mut roots = split_squarefree_roots(&poly, &field, &mut SplitMix64(1)).unwrap();
        roots.sort_by_key(|r| r.raw());
        assert_eq!(roots, vec![field.elem(1), field.elem(3)]);
        let big = PrimeField::new(1_000_003).unwrap();
        // (x − 2)(x − 123456) over a prime past the scan threshold.
        let c0 = big.mul(big.elem(2), big.elem(123_456));
        let c1 = big.neg(big.add(big.elem(2), big.elem(123_456)));
        let mut roots =
            split_squarefree_roots(&[c0, c1, big.one()], &big, &mut SplitMix64(1)).unwrap();
        roots.sort_by_key(|r| r.raw());
        assert_eq!(roots, vec![big.elem(2), big.elem(123_456)]);
    }

    #[test]
    fn coords_and_morphism_round_trip() {
        let field = f5();
        let a = linear_an(2, field);
        let p0 = Module::projective(&a, 0);
        let p1 = Module::projective(&a, 1);
        let (sum, _, _) = direct_sum(&[&p0, &p1]);
        let e = EndoAlgebra::new(&sum);
        let coords: Vec<Fp> = (0..e.dim() as i64).map(|i| field.elem(i + 1)).collect();
        assert_eq!(e.coords(&e.morphism(&coords)), coords);
        assert_eq!(e.coords(&identity(&sum)), e.one().to_vec());
    }

    /// The Kronecker representation (a, b) ↦ (I₂, C) with C the companion
    /// matrix of x² + x + 1, irreducible over F_2.
    fn kronecker_f4_module() -> Module {
        let field = PrimeField::new(2).unwrap();
        let a = kronecker(2, field);
        let id = DenseMat::from_rows(&[
            vec![field.one(), field.zero()],
            vec![field.zero(), field.one()],
        ]);
        let c = DenseMat::from_rows(&[
            vec![field.zero(), field.one()],
            vec![field.one(), field.one()],
        ]);
        Module::new(a, vec![2, 2], vec![id, c]).unwrap()
    }

    // End(M) ≅ F_4 = F_2[C]: a non-split residue field, so the single
    // Frobenius-fixed factor comes from the extension-field branch of the
    // factor count, not from a copy of F_p.
    #[test]
    fn end_of_the_f4_kronecker_module_is_the_field_with_four_elements() {
        let e = EndoAlgebra::new(&kronecker_f4_module());
        assert_eq!(e.dim(), 2);
        assert_eq!(e.radical_dim(), 0);
        assert_eq!(e.semisimple_factor_count(), 1);
        assert!(e.quotient_is_commutative());
        assert!(e.is_local());
    }

    // The claim `express` rests on: the hom basis carries the identity at its
    // free columns, so no submatrix inverse is ever needed.
    #[test]
    fn the_flattened_basis_carries_the_identity_at_the_coordinate_columns() {
        for m in fixture_modules() {
            let e = EndoAlgebra::new(&m);
            assert!(
                e.coord_inverse.is_none(),
                "dim {} needed a submatrix inverse",
                e.dim()
            );
            for (r, &c) in e.coord_cols.iter().enumerate() {
                for k in 0..e.dim() {
                    let expected = if k == r { Fp::ONE } else { Fp::ZERO };
                    assert_eq!(e.flat.get(k, c), expected, "flat[{k}][{c}]");
                }
            }
        }
    }

    // Selecting coordinates off the flat row must agree with solving for them.
    #[test]
    fn coordinates_agree_with_solving_the_flattened_system() {
        for m in fixture_modules() {
            let e = EndoAlgebra::new(&m);
            let field = e.field();
            let mut targets: Vec<Morphism> = vec![identity(&m)];
            for i in 0..e.dim() {
                for j in 0..e.dim() {
                    targets.push(e.basis[i].then(&e.basis[j]).unwrap());
                }
            }
            for f in &targets {
                let mut row = DenseMat::zero(1, e.flat.cols());
                for (c, &v) in flat_row(f).iter().enumerate() {
                    row.set(0, c, v);
                }
                let solved = express_in_row_basis(&e.flat, &row, &field).row(0).to_vec();
                assert_eq!(e.coords(f), solved);
            }
        }
    }

    // The closed-form first round must reproduce the general
    // characteristic-polynomial round, entry for entry.
    #[test]
    fn the_trace_form_matches_the_characteristic_polynomial_round() {
        for m in fixture_modules() {
            if m.total_dim() == 0 {
                continue;
            }
            let e = EndoAlgebra::new(&m);
            let field = e.field();
            let n = m.total_dim();
            let mut expected = DenseMat::zero(e.dim(), e.dim());
            for j in 0..e.dim() {
                for k in 0..e.dim() {
                    let product = e.basis[j].then(&e.basis[k]).unwrap();
                    let cp = morphism_char_poly(&product, &field);
                    expected.set(k, j, cp[n - 1]);
                }
            }
            assert_eq!(trace_form(&e), expected, "dim vector {:?}", m.dim_vector());
        }
    }

    // Membership by reduction must agree with the rank test.
    #[test]
    fn radical_membership_agrees_with_the_rank_test() {
        let mut rng = XorShift64(0x0005_eed0_c4a1_e402);
        for m in fixture_modules() {
            let e = EndoAlgebra::new(&m);
            let field = e.field();
            let p = field.modulus();
            for _ in 0..8 {
                let coords: Vec<Fp> = (0..e.dim())
                    .map(|_| field.elem(rng.below(p) as i64))
                    .collect();
                let mut stacked = DenseMat::zero(e.radical_dim() + 1, e.dim());
                for r in 0..e.radical_dim() {
                    for c in 0..e.dim() {
                        stacked.set(r, c, e.radical_basis().get(r, c));
                    }
                }
                for (c, &v) in coords.iter().enumerate() {
                    stacked.set(e.radical_dim(), c, v);
                }
                assert_eq!(
                    e.in_radical(&coords),
                    stacked.rank(&field) == e.radical_dim()
                );
            }
        }
    }

    // Quotient coordinates by the stored map must agree with solving against
    // the radical rows stacked over the complement rows.
    #[test]
    fn quotient_coordinates_agree_with_the_change_of_basis() {
        let mut rng = XorShift64(0x0005_eed0_c4a1_e403);
        for m in fixture_modules() {
            let e = EndoAlgebra::new(&m);
            let field = e.field();
            let p = field.modulus();
            let full: Vec<Vec<Fp>> = (0..e.radical_dim())
                .map(|r| e.radical_basis().row(r).to_vec())
                .chain((0..e.quotient_dim()).map(|r| e.complement.row(r).to_vec()))
                .collect();
            if full.is_empty() {
                continue;
            }
            let full = DenseMat::from_rows(&full);
            for _ in 0..8 {
                let coords: Vec<Fp> = (0..e.dim())
                    .map(|_| field.elem(rng.below(p) as i64))
                    .collect();
                let mut row = DenseMat::zero(1, e.dim());
                for (c, &v) in coords.iter().enumerate() {
                    row.set(0, c, v);
                }
                let expressed = express_in_row_basis(&full, &row, &field);
                let expected: Vec<Fp> = (e.radical_dim()..e.dim())
                    .map(|c| expressed.get(0, c))
                    .collect();
                assert_eq!(e.reduce(&coords), expected);
            }
        }
    }

    // The complement is the greedy independent set of unit vectors, not the
    // free columns of the radical: for rad = span{e_0 + e_1} it picks e_0 while
    // column 1 is the free one.
    #[test]
    fn the_complement_search_takes_the_first_independent_unit_vector() {
        let field = f5();
        let mut reducer = RowReducer::new(3);
        reducer.push(&[field.one(), field.one(), field.zero()], &field);
        assert!(reducer.push(&unit(3, 0, &field), &field));
        assert!(!reducer.push(&unit(3, 1, &field), &field));
        assert!(reducer.push(&unit(3, 2, &field), &field));
    }

    #[test]
    fn the_quotient_dimension_is_the_codimension_of_the_radical() {
        for m in fixture_modules() {
            let e = EndoAlgebra::new(&m);
            assert_eq!(e.quotient_dim(), e.dim() - e.radical_dim());
        }
    }

    #[test]
    fn the_endomorphism_algebra_is_sync() {
        fn assert_sync<T: Sync + Send>() {}
        assert_sync::<EndoAlgebra>();
    }

    // End(M ⊕ M) ≅ M_2(F_4): one Wedderburn factor but noncommutative, so not
    // local, and split_idempotent must return None (it needs two factors);
    // only the Fitting fallback can split this sum.
    #[test]
    fn m2_of_f4_has_one_factor_but_is_not_local_and_yields_no_idempotent() {
        let m = kronecker_f4_module();
        let (sum, _, _) = direct_sum(&[&m, &m]);
        let e = EndoAlgebra::new(&sum);
        assert_eq!(e.dim(), 8);
        assert_eq!(e.radical_dim(), 0);
        assert_eq!(e.semisimple_factor_count(), 1);
        assert!(!e.quotient_is_commutative());
        assert!(!e.is_local());
        assert_eq!(e.split_idempotent(&mut SplitMix64(7)), None);
    }
}

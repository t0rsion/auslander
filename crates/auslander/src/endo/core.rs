use std::sync::OnceLock;

use crate::field::{Fp, PrimeField};
use crate::hom::{Morphism, express_in_row_basis, identity};
use crate::homspace::{HomSpace, flat_row, row_times};
use crate::linalg::{DenseMat, RowReducer};
use crate::module::Module;
use crate::profile::{Site, hit, hit_module};

use super::helpers::{SplitMix64, coordinate_columns, coordinate_product, unit_row};
use super::polynomial::{
    coprime_split, independent_fixed_element, lagrange_projector, newton_idempotent_lift,
    split_squarefree_roots, valid_idempotent,
};
use super::radical::ronyai_radical;

/// The endomorphism algebra of a fixed module, with its `Hom(M, M)` basis,
/// exact Jacobson radical, and structure constants built on demand.
#[derive(Clone)]
pub struct EndoAlgebra {
    pub(super) module: Module,
    pub(super) field: PrimeField,
    pub(super) basis: Vec<Morphism>,
    // dim × Σ_v (dim M_v)² flattened basis, for expressing endomorphisms.
    pub(super) flat: DenseMat,
    // One column of `flat` per basis element, and the inverse of the submatrix
    // there; see coordinate_columns.
    pub(super) coord_cols: Vec<usize>,
    pub(super) coord_inverse: Option<DenseMat>,
    // table[i * dim + j] = coordinates of basis[i].then(basis[j]), filled by
    // the first `multiply`.
    table: OnceLock<Vec<Vec<Fp>>>,
    one: Vec<Fp>,
    // Rows: coordinates of a radical basis, in reduced row echelon form.
    radical: DenseMat,
    // Pivot column of each radical row, in row order.
    radical_pivots: Vec<usize>,
    // Rows: coset representatives of a basis of End(M)/rad.
    pub(super) complement: DenseMat,
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

debug_fields!(EndoAlgebra |this| {
    "dim_vector" => this.module.dim_vector();
    "dim" => this.dim();
    "radical_dim" => this.radical_dim();
});

impl EndoAlgebra {
    /// Builds `End(m)` from the [`HomSpace`] basis and runs the radical chain.
    pub fn new(m: &Module) -> EndoAlgebra {
        hit_module(Site::EndoNew, m);
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
        hit(Site::EndoFromSummand);
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
        endo.radical =
            DenseMat::from_rows_with_cols(&rows, endo.dim()).row_space_basis(&endo.field);
        endo.analyze_quotient();
        endo
    }

    // Everything the radical does not determine: the flattened basis, the
    // coordinate columns, and the identity.
    //
    // The whole basis is materialized here, unlike elsewhere: `multiply`
    // composes every pair of basis elements, so each one is used `2 dim` times.
    fn over(m: &Module, space: HomSpace) -> EndoAlgebra {
        hit(Site::EndoOver);
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
            .filter(|&i| reducer.push(&unit_row(dim, i), &field))
            .collect();
        let complement_rows: Vec<Vec<Fp>> =
            complement_cols.iter().map(|&i| unit_row(dim, i)).collect();
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
            let rows: Vec<Vec<Fp>> = (0..dim)
                .map(|r| inverse.row(r)[radical_rows..].to_vec())
                .collect();
            DenseMat::from_rows_with_cols(&rows, q)
        };
        // Each complement row is a unit vector, so its products are single
        // structure constants and the full dim² table stays unbuilt.
        let endo: &EndoAlgebra = &*self;
        let columns = &complement_cols;
        self.qtable = (0..q)
            .flat_map(|i| {
                (0..q).map(move |j| {
                    let product = endo.basis[columns[i]]
                        .then(&endo.basis[columns[j]])
                        .expect("endomorphisms compose");
                    endo.reduce(&endo.express(&product))
                })
            })
            .collect();
        self.qone = self.reduce(&self.one);
        self.quotient_commutative =
            (0..q).all(|i| (0..i).all(|j| self.qtable[i * q + j] == self.qtable[j * q + i]));
        let qtable = &self.qtable;
        let cond_rows: Vec<Vec<Fp>> = (0..q)
            .flat_map(|j| {
                (0..q).map(move |comp| {
                    (0..q)
                        .map(|i| field.sub(qtable[i * q + j][comp], qtable[j * q + i][comp]))
                        .collect()
                })
            })
            .collect();
        self.center = if q == 0 {
            DenseMat::zero(0, 0)
        } else {
            DenseMat::from_rows(&cond_rows).kernel_basis(&field)
        };
        let c = self.center.rows();
        let frobenius_rows: Vec<Vec<Fp>> = (0..c)
            .map(|r| {
                let zp = self.qpow(self.center.row(r), field.modulus());
                let as_matrix = DenseMat::from_rows(std::slice::from_ref(&zp));
                let in_center = express_in_row_basis(&self.center, &as_matrix, &field);
                in_center.row(0).to_vec()
            })
            .collect();
        let mut shifted = DenseMat::from_rows_with_cols(&frobenius_rows, c);
        for i in 0..c {
            shifted.set(i, i, field.sub(shifted.get(i, i), Fp::ONE));
        }
        self.fixed = shifted.left_kernel_basis(&field).mul(&self.center, &field);
    }

    // Quotient coordinates of an element given in algebra coordinates: the
    // components along the complement basis after the stored change of basis.
    pub(super) fn reduce(&self, coords: &[Fp]) -> Vec<Fp> {
        row_times(coords, &self.quotient, &self.field)
    }

    // Product in the quotient, both factors in quotient coordinates.
    fn qmul(&self, a: &[Fp], b: &[Fp]) -> Vec<Fp> {
        coordinate_product(a, b, &self.qtable, self.field)
    }

    fn qpow(&self, a: &[Fp], exp: u64) -> Vec<Fp> {
        binary_power!(a.to_vec(), self.qone.clone(), exp, |left, right| self
            .qmul(left, right))
    }

    accessor_methods! {
        /// The module this is the endomorphism algebra of.
        pub module() -> &Module = |this| &this.module;
        /// The field every coordinate is over: the field of [`EndoAlgebra::module`].
        ///
        /// Coordinates passed to [`EndoAlgebra::morphism`], [`EndoAlgebra::multiply`]
        /// and [`EndoAlgebra::in_radical`] must be canonical elements of this field;
        /// [`Fp`] carries no field identity, so the types do not check this.
        pub field() -> PrimeField = |this| this.field;
        /// `dim_k End(M)`.
        pub dim() -> usize = |this| this.basis.len();
        /// The basis endomorphisms; coordinates index into this list.
        pub basis() -> &[Morphism] = |this| &this.basis;
        /// Coordinates of the identity endomorphism.
        pub one() -> &[Fp] = |this| &this.one;
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
                map.add_scaled_assign(self.basis[k].map_at(v as u32), c, &self.field);
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
        coordinate_product(a, b, table, self.field)
    }

    accessor_methods! {
        /// A basis of the Jacobson radical, one coordinate vector per row, in
        /// reduced row echelon form.
        pub radical_basis() -> &DenseMat = |this| &this.radical;
        /// `dim_k rad End(M)`.
        pub radical_dim() -> usize = |this| this.radical.rows();
        /// `dim_k End(M)/rad End(M)`, the dimension of the semisimple quotient.
        /// This is the residue degree only when `End(M)` is local, which
        /// [`EndoAlgebra::is_local`] decides; see
        /// [`crate::indec::IndecomposableModule::residue_degree`].
        pub quotient_dim() -> usize = |this| this.complement.rows();
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

    accessor_methods! {
        /// Whether the semisimple quotient `End(M)/rad` is commutative.
        pub quotient_is_commutative() -> bool = |this| this.quotient_commutative;
        /// The number of Wedderburn factors of `End(M)/rad`: the dimension of the
        /// fixed space of the Frobenius `x ↦ x^p` on the center of the quotient
        /// (Berlekamp-style factor counting).
        pub semisimple_factor_count() -> usize = |this| this.fixed.rows();
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
    /// One budget is probabilistic: for `p > 4096` the seeded
    /// Cantor-Zassenhaus root search gives up after 64 draws (never observed in
    /// the test suite) and this returns `None`. Callers fall back to Fitting
    /// splits and, at worst, [`crate::decompose::Certificate::Undetermined`].
    pub(crate) fn split_idempotent(&self, rng: &mut SplitMix64) -> Option<Vec<Fp>> {
        if self.semisimple_factor_count() < 2 {
            return None;
        }
        let field = self.field;
        let f = independent_fixed_element(&self.fixed, &self.qone, &field)?;
        let minpoly = self.quotient_min_poly(f);
        let roots = split_squarefree_roots(&minpoly, &field, rng)?;
        let projector = lagrange_projector(&roots, &field);
        let ebar = self.qpoly_eval(&projector, f);
        if !valid_idempotent(&ebar, &self.qone, |value| self.qmul(value, value)) {
            return None;
        }
        newton_idempotent_lift(self, self.lift_quotient(&ebar))
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
    /// never separated the factors. Callers treat that as a failure to split.
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
            return Some(self.lift_quotient(&value));
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

    fn lift_quotient(&self, value: &[Fp]) -> Vec<Fp> {
        row_times(value, &self.complement, &self.field)
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

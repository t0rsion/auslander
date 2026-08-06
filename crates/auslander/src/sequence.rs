//! Checked short exact sequences, their construction from `Ext^1` classes,
//! class recovery, and split status with proof either way.
//!
//! [`ShortExactSequence::new`] verifies exactness per vertex: the inclusion is
//! mono by rank, the projection is epi by rank, the composite is zero, and the
//! dimensions add. Zero composite plus the dimension equality plus mono plus
//! epi force image equals kernel, so no further computation is needed.
//!
//! [`ShortExactSequence::split_status`] solves the retraction linear system in
//! a fixed order: unknowns are the entries of `r: E -> N` vertex-major then
//! row-major; equations are the commuting squares in (arrow, row, column)
//! lexicographic order, then the `iota.then(r) = id` constraints vertex-major
//! then row-major. A solution yields a [`SplitWitness`]. An inconsistent
//! system yields a [`NonSplitWitness`] holding a dual vector `y` with
//! `y A = 0` and `y b = 1`, read off the pivot row of the reduced row echelon
//! form of the augmented system `[A | b | identity]`; that pivot row is
//! normalized with leading entry 1 in the `b` column. Either witness rechecks
//! by multiplication alone.

use std::fmt;

use crate::decompose::add_morphisms;
use crate::ext::{ExtClass, ExtSpace, lift_through};
use crate::field::{Fp, PrimeField};
use crate::hom::{Morphism, cokernel, express_in_row_basis, identity, image, zero_morphism};
use crate::linalg::DenseMat;
use crate::module::{Module, direct_sum};
use crate::quiver::ArrowId;

/// Rejected short exact sequence input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SequenceError {
    /// The inclusion's target is not the projection's source (by
    /// [`Module::ptr_eq`]).
    EndpointMismatch,
    /// The inclusion's rank at this vertex is below the sub dimension, so the
    /// inclusion is not mono.
    NotMono { vertex: u32 },
    /// The projection's rank at this vertex is below the quotient dimension,
    /// so the projection is not epi.
    NotEpi { vertex: u32 },
    /// The composite inclusion-then-projection is nonzero at this vertex.
    CompositeNonzero { vertex: u32 },
    /// `dim middle != dim sub + dim quotient` at this vertex.
    DimensionMismatch { vertex: u32 },
    /// The class or space has the wrong cohomological degree.
    WrongDegree { expected: usize, got: usize },
    /// The space's source module is not this sequence's quotient (by
    /// [`Module::ptr_eq`]).
    SpaceSourceMismatch,
    /// The space's target module is not this sequence's sub (by
    /// [`Module::ptr_eq`]).
    SpaceTargetMismatch,
}

impl fmt::Display for SequenceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EndpointMismatch => {
                f.write_str("the inclusion's target is not the projection's source")
            }
            Self::NotMono { vertex } => {
                write!(f, "the inclusion is not mono at vertex {vertex}")
            }
            Self::NotEpi { vertex } => {
                write!(f, "the projection is not epi at vertex {vertex}")
            }
            Self::CompositeNonzero { vertex } => {
                write!(f, "the composite is nonzero at vertex {vertex}")
            }
            Self::DimensionMismatch { vertex } => write!(
                f,
                "the middle dimension is not sub plus quotient at vertex {vertex}"
            ),
            Self::WrongDegree { expected, got } => {
                write!(f, "degree is {got}, this operation needs degree {expected}")
            }
            Self::SpaceSourceMismatch => {
                f.write_str("the space's source module is not the sequence's quotient")
            }
            Self::SpaceTargetMismatch => {
                f.write_str("the space's target module is not the sequence's sub")
            }
        }
    }
}

impl std::error::Error for SequenceError {}

/// The morphism with every entry negated.
fn negate(f: &Morphism) -> Morphism {
    let field = f.source().field();
    let nv = f.source().algebra().quiver().num_vertices();
    let maps = (0..nv)
        .map(|v| {
            let m = f.map_at(v);
            let mut out = DenseMat::zero(m.rows(), m.cols());
            for r in 0..m.rows() {
                for c in 0..m.cols() {
                    out.set(r, c, field.neg(m.get(r, c)));
                }
            }
            out
        })
        .collect();
    Morphism::new(f.source(), f.target(), maps)
        .expect("the negative of an A-linear map is A-linear")
}

/// The factorization `f: B -> C` with `epi.then(f) = map`, for `epi: A -> B`
/// and `map: A -> C` where `map` kills the kernel of `epi`. Each column
/// solves one linear system with free variables zeroed, so the result is
/// deterministic; it is unique when the vertex matrices of `epi` have full
/// column rank.
///
/// # Panics
/// Panics when a column of `map` lies outside the column space of the
/// matching `epi` matrix; callers only factor maps that kill the kernel.
fn factor_through_epi(epi: &Morphism, map: &Morphism) -> Morphism {
    debug_assert!(epi.source().ptr_eq(map.source()));
    let field = epi.source().field();
    let nv = epi.source().algebra().quiver().num_vertices();
    let maps = (0..nv)
        .map(|v| {
            let e = epi.map_at(v);
            let m = map.map_at(v);
            let mt = m.transpose();
            let mut out = DenseMat::zero(e.cols(), m.cols());
            for j in 0..m.cols() {
                let x = e
                    .solve(mt.row(j), &field)
                    .expect("factor_through_epi: the map kills the kernel of the epimorphism");
                for (i, &val) in x.iter().enumerate() {
                    out.set(i, j, val);
                }
            }
            out
        })
        .collect();
    Morphism::new(epi.target(), map.target(), maps)
        .expect("a factorization through an epimorphism is A-linear")
}

/// The factorization `f: A -> N` with `f.then(mono) = map`, for
/// `mono: N -> B` and `map: A -> B` where `map` lands in the image of `mono`.
/// The vertex matrices of `mono` have full row rank, so `f` is unique.
///
/// # Panics
/// Panics when a row of `map` lies outside the row space of the matching
/// `mono` matrix; callers only factor maps that land in the image.
fn factor_through_mono(mono: &Morphism, map: &Morphism) -> Morphism {
    debug_assert!(mono.target().ptr_eq(map.target()));
    let field = mono.source().field();
    let nv = mono.source().algebra().quiver().num_vertices();
    let maps = (0..nv)
        .map(|v| {
            let mo = mono.map_at(v).transpose();
            let m = map.map_at(v);
            let mut out = DenseMat::zero(m.rows(), mono.map_at(v).rows());
            for r in 0..m.rows() {
                let x = mo
                    .solve(m.row(r), &field)
                    .expect("factor_through_mono: the map lands in the image of the mono");
                for (c, &val) in x.iter().enumerate() {
                    out.set(r, c, val);
                }
            }
            out
        })
        .collect();
    Morphism::new(map.source(), mono.source(), maps)
        .expect("a factorization through a monomorphism is A-linear")
}

/// A short exact sequence `0 -> sub -> middle -> quotient -> 0`, exact per
/// vertex by construction.
///
/// Fields are private; construction goes through [`ShortExactSequence::new`]
/// or [`ShortExactSequence::from_ext1`], so every value is exact.
#[derive(Clone, Debug)]
pub struct ShortExactSequence {
    sub: Module,
    middle: Module,
    quotient: Module,
    inclusion: Morphism,
    projection: Morphism,
}

impl ShortExactSequence {
    /// Builds the sequence after checking, per vertex: the inclusion is mono
    /// by rank, the projection is epi by rank, the composite is zero, and
    /// `dim middle = dim sub + dim quotient`. Together these force exactness.
    pub fn new(
        inclusion: Morphism,
        projection: Morphism,
    ) -> Result<ShortExactSequence, SequenceError> {
        if !inclusion.target().ptr_eq(projection.source()) {
            return Err(SequenceError::EndpointMismatch);
        }
        let sub = inclusion.source().clone();
        let middle = inclusion.target().clone();
        let quotient = projection.target().clone();
        let field = sub.field();
        let nv = sub.algebra().quiver().num_vertices();
        for v in 0..nv {
            if inclusion.map_at(v).rank(&field) < sub.dim_at(v) {
                return Err(SequenceError::NotMono { vertex: v });
            }
        }
        for v in 0..nv {
            if projection.map_at(v).rank(&field) < quotient.dim_at(v) {
                return Err(SequenceError::NotEpi { vertex: v });
            }
        }
        let composite = inclusion.then(&projection).expect("endpoints were checked");
        for v in 0..nv {
            let m = composite.map_at(v);
            if (0..m.rows()).any(|r| m.row(r).iter().any(|c| !c.is_zero())) {
                return Err(SequenceError::CompositeNonzero { vertex: v });
            }
        }
        for v in 0..nv {
            if middle.dim_at(v) != sub.dim_at(v) + quotient.dim_at(v) {
                return Err(SequenceError::DimensionMismatch { vertex: v });
            }
        }
        Ok(ShortExactSequence {
            sub,
            middle,
            quotient,
            inclusion,
            projection,
        })
    }

    /// The sub module `N`.
    #[inline]
    pub fn sub(&self) -> &Module {
        &self.sub
    }

    /// The middle module `E`.
    #[inline]
    pub fn middle(&self) -> &Module {
        &self.middle
    }

    /// The quotient module `M`.
    #[inline]
    pub fn quotient(&self) -> &Module {
        &self.quotient
    }

    /// The inclusion `N -> E`.
    #[inline]
    pub fn inclusion(&self) -> &Morphism {
        &self.inclusion
    }

    /// The projection `E -> M`.
    #[inline]
    pub fn projection(&self) -> &Morphism {
        &self.projection
    }

    /// The extension realizing a class in `Ext^1(M, N)` by pushout: with
    /// `K = im d_1`, `kappa: K -> P_0`, the surjection `s: P_1 -> K`, and the
    /// representative cocycle `c` factored as `s.then(c_bar)`, the middle is
    /// the cokernel of `(c_bar, -kappa): K -> N (+) P_0`. The zero class
    /// yields the split sequence. The result passes through
    /// [`ShortExactSequence::new`]. Errors when the class degree is not 1.
    pub fn from_ext1(class: &ExtClass) -> Result<ShortExactSequence, SequenceError> {
        let space = class.space();
        if space.degree() != 1 {
            return Err(SequenceError::WrongDegree {
                expected: 1,
                got: space.degree(),
            });
        }
        let m = space.source();
        let n = space.target();
        let res = space.resolution();
        let field = m.field();
        let nv = m.algebra().quiver().num_vertices();
        let p0 = &res.terms[0];
        let c = class.representative();
        let (kappa, c_bar) = match res.maps.first() {
            Some(d1) => {
                let (k_mod, kappa) = image(d1);
                let s_maps = (0..nv)
                    .map(|v| express_in_row_basis(kappa.map_at(v), d1.map_at(v), &field))
                    .collect();
                let s = Morphism::new(d1.source(), &k_mod, s_maps)
                    .expect("the corestriction of d_1 to its image is A-linear");
                let c_bar = factor_through_epi(&s, &c);
                (kappa, c_bar)
            }
            None => {
                let k_mod = Module::zero(m.algebra());
                let kappa = zero_morphism(&k_mod, p0).expect("shared algebra");
                let c_bar = zero_morphism(&k_mod, n).expect("shared algebra");
                (kappa, c_bar)
            }
        };
        let (_sum, inclusions, projections) = direct_sum(&[n, p0]);
        let mu = add_morphisms(
            &c_bar
                .then(&inclusions[0])
                .expect("the sum inclusion starts at N"),
            &negate(&kappa)
                .then(&inclusions[1])
                .expect("the sum inclusion starts at P_0"),
        );
        let (_e, q) = cokernel(&mu);
        let iota = inclusions[0]
            .then(&q)
            .expect("the cokernel projection starts at the sum");
        let w = projections[1]
            .then(&res.augmentation)
            .expect("the augmentation starts at P_0");
        let pi = factor_through_epi(&q, &w);
        ShortExactSequence::new(iota, pi)
    }

    /// The class of this extension in `space = Ext^1(quotient, sub)`: lift
    /// the augmentation through the projection, pull `d_1.then(lift)` back
    /// through the inclusion, and reduce the resulting cocycle. Errors when
    /// the space's degree is not 1 or its endpoints are not this sequence's
    /// quotient and sub (by [`Module::ptr_eq`]).
    pub fn ext1_class(&self, space: &ExtSpace) -> Result<ExtClass, SequenceError> {
        if space.degree() != 1 {
            return Err(SequenceError::WrongDegree {
                expected: 1,
                got: space.degree(),
            });
        }
        if !space.source().ptr_eq(&self.quotient) {
            return Err(SequenceError::SpaceSourceMismatch);
        }
        if !space.target().ptr_eq(&self.sub) {
            return Err(SequenceError::SpaceTargetMismatch);
        }
        let res = space.resolution();
        let Some(d1) = res.maps.first() else {
            return Ok(space
                .class_from_coordinates(&[])
                .expect("a projective quotient has the zero Ext^1 space"));
        };
        let h = lift_through(&res.terms[0], &self.projection, &res.augmentation);
        let d1h = d1.then(&h).expect("d_1 targets P_0");
        let c = factor_through_mono(&self.inclusion, &d1h);
        Ok(space
            .class_from_cocycle(&c)
            .expect("the recovered cochain is a cocycle; failure is a bug in auslander"))
    }

    /// Solves the retraction system in the fixed order stated in the module
    /// docs. Both outcomes carry their proof: a retraction and section that
    /// recheck by multiplication, or a dual vector proving the system
    /// inconsistent.
    pub fn split_status(&self) -> SplitStatus {
        let field = self.middle.field();
        let (a, b) = retraction_system(self);
        match a.solve(&b, &field) {
            Some(x) => {
                let retraction = self.retraction_from_solution(&x);
                let e_idem = retraction
                    .then(&self.inclusion)
                    .expect("the retraction ends at the sub");
                let nv = self.middle.algebra().quiver().num_vertices();
                let p_maps = (0..nv)
                    .map(|v| {
                        let id = DenseMat::identity(self.middle.dim_at(v));
                        let neg = e_idem.map_at(v);
                        let mut out = DenseMat::zero(id.rows(), id.cols());
                        for r in 0..id.rows() {
                            for c in 0..id.cols() {
                                out.set(r, c, field.sub(id.get(r, c), neg.get(r, c)));
                            }
                        }
                        out
                    })
                    .collect();
                let p = Morphism::new(&self.middle, &self.middle, p_maps)
                    .expect("a difference of A-linear maps is A-linear");
                let section = factor_through_epi(&self.projection, &p);
                SplitStatus::Split(SplitWitness {
                    retraction,
                    section,
                })
            }
            None => {
                let rows = a.rows();
                let cols = a.cols();
                let mut aug = DenseMat::zero(rows, cols + 1 + rows);
                for (r, &rhs) in b.iter().enumerate() {
                    for c in 0..cols {
                        aug.set(r, c, a.get(r, c));
                    }
                    aug.set(r, cols, rhs);
                    aug.set(r, cols + 1 + r, field.one());
                }
                let (reduced, pivots) = aug.rref(&field);
                let pivot_row = pivots
                    .iter()
                    .position(|&c| c == cols)
                    .expect("an unsolvable system pivots in the right-side column");
                let dual = (0..rows)
                    .map(|r| reduced.get(pivot_row, cols + 1 + r))
                    .collect();
                SplitStatus::NonSplit(NonSplitWitness { dual })
            }
        }
    }

    /// The retraction `E -> N` read off a solution vector of the retraction
    /// system, in the fixed unknown order.
    fn retraction_from_solution(&self, x: &[Fp]) -> Morphism {
        let nv = self.middle.algebra().quiver().num_vertices();
        let mut maps = Vec::with_capacity(nv as usize);
        let mut offset = 0;
        for v in 0..nv {
            let (de, dn) = (self.middle.dim_at(v), self.sub.dim_at(v));
            let mut block = DenseMat::zero(de, dn);
            for r in 0..de {
                for c in 0..dn {
                    block.set(r, c, x[offset + r * dn + c]);
                }
            }
            offset += de * dn;
            maps.push(block);
        }
        Morphism::new(&self.middle, &self.sub, maps)
            .expect("the solved system contains every commuting square")
    }
}

/// The retraction system for `r: E -> N` in the fixed crate order: unknowns
/// vertex-major then row-major; equations are the commuting squares in
/// (arrow, row, column) lexicographic order, then `iota.then(r) = id`
/// vertex-major then row-major.
fn retraction_system(sequence: &ShortExactSequence) -> (DenseMat, Vec<Fp>) {
    let e = &sequence.middle;
    let n = &sequence.sub;
    let field: PrimeField = e.field();
    let quiver = e.algebra().quiver();
    let nv = quiver.num_vertices();
    let mut offsets = vec![0usize; nv as usize];
    let mut total = 0usize;
    for v in 0..nv {
        offsets[v as usize] = total;
        total += e.dim_at(v) * n.dim_at(v);
    }
    let mut rows: Vec<Vec<Fp>> = Vec::new();
    let mut rhs: Vec<Fp> = Vec::new();
    for idx in 0..quiver.num_arrows() {
        let a = ArrowId(idx as u32);
        let (s, t) = (quiver.source(a), quiver.target(a));
        let ea = e.map(a);
        let na = n.map(a);
        for i in 0..e.dim_at(s) {
            for j in 0..n.dim_at(t) {
                let mut row = vec![Fp::ZERO; total];
                for c in 0..n.dim_at(s) {
                    let col = offsets[s as usize] + i * n.dim_at(s) + c;
                    row[col] = field.add(row[col], na.get(c, j));
                }
                for k in 0..e.dim_at(t) {
                    let col = offsets[t as usize] + k * n.dim_at(t) + j;
                    row[col] = field.sub(row[col], ea.get(i, k));
                }
                rows.push(row);
                rhs.push(Fp::ZERO);
            }
        }
    }
    let iota = &sequence.inclusion;
    for v in 0..nv {
        let iv = iota.map_at(v);
        let dn = n.dim_at(v);
        for i in 0..dn {
            for j in 0..dn {
                let mut row = vec![Fp::ZERO; total];
                for k in 0..e.dim_at(v) {
                    let col = offsets[v as usize] + k * dn + j;
                    row[col] = field.add(row[col], iv.get(i, k));
                }
                rows.push(row);
                rhs.push(if i == j { field.one() } else { field.zero() });
            }
        }
    }
    let a = if rows.is_empty() {
        DenseMat::zero(0, total)
    } else {
        DenseMat::from_rows(&rows)
    };
    (a, rhs)
}

/// The outcome of [`ShortExactSequence::split_status`]; each variant carries
/// its proof.
#[derive(Clone, Debug)]
pub enum SplitStatus {
    Split(SplitWitness),
    NonSplit(NonSplitWitness),
}

/// A retraction and section proving a sequence split.
#[derive(Clone, Debug)]
pub struct SplitWitness {
    retraction: Morphism,
    section: Morphism,
}

impl SplitWitness {
    /// The retraction `r: E -> N` with `iota.then(r) = id`.
    #[inline]
    pub fn retraction(&self) -> &Morphism {
        &self.retraction
    }

    /// The section `s: M -> E` with `s.then(projection) = id`.
    #[inline]
    pub fn section(&self) -> &Morphism {
        &self.section
    }

    /// Rechecks both identities against the sequence: `iota.then(r) = id` on
    /// the sub and `s.then(projection) = id` on the quotient. Both stored
    /// maps are [`Morphism`] values, so A-linearity holds by construction.
    pub fn verify(&self, sequence: &ShortExactSequence) -> bool {
        let Ok(left) = sequence.inclusion.then(&self.retraction) else {
            return false;
        };
        let Ok(right) = self.section.then(&sequence.projection) else {
            return false;
        };
        left == identity(&sequence.sub) && right == identity(&sequence.quotient)
    }
}

/// A dual vector proving the retraction system inconsistent: `y A = 0` and
/// `y b = 1` for the system built in the fixed order.
#[derive(Clone, Debug)]
pub struct NonSplitWitness {
    dual: Vec<Fp>,
}

impl NonSplitWitness {
    /// The dual vector, one entry per equation of the retraction system.
    #[inline]
    pub fn dual(&self) -> &[Fp] {
        &self.dual
    }

    /// Rebuilds the retraction system in the fixed order and checks
    /// `y A = 0` and `y b = 1` by multiplication.
    pub fn verify(&self, sequence: &ShortExactSequence) -> bool {
        let (a, b) = retraction_system(sequence);
        if self.dual.len() != a.rows() {
            return false;
        }
        let field = sequence.middle.field();
        for j in 0..a.cols() {
            let mut acc = Fp::ZERO;
            for (r, &y) in self.dual.iter().enumerate() {
                acc = field.add(acc, field.mul(y, a.get(r, j)));
            }
            if !acc.is_zero() {
                return false;
            }
        }
        let mut acc = Fp::ZERO;
        for (r, &y) in self.dual.iter().enumerate() {
            acc = field.add(acc, field.mul(y, b[r]));
        }
        acc == field.one()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{an_with_relations, linear_an, truncated_poly};
    use crate::field::PrimeField;

    fn f5() -> PrimeField {
        PrimeField::new(5).unwrap()
    }

    fn f2() -> PrimeField {
        PrimeField::new(2).unwrap()
    }

    fn one_class(space: &ExtSpace) -> ExtClass {
        let field = space.source().field();
        let mut coords = vec![field.zero(); space.dim()];
        coords[0] = field.one();
        space.class_from_coordinates(&coords).unwrap()
    }

    #[test]
    fn new_accepts_a_direct_sum_and_split_status_verifies() {
        let algebra = linear_an(3, f5());
        let s = Module::simple(&algebra, 0);
        let p = Module::projective(&algebra, 1);
        let (sum, inclusions, projections) = direct_sum(&[&s, &p]);
        let ses = ShortExactSequence::new(inclusions[0].clone(), projections[1].clone()).unwrap();
        assert!(ses.sub().ptr_eq(&s));
        assert!(ses.middle().ptr_eq(&sum));
        assert!(ses.quotient().ptr_eq(&p));
        match ses.split_status() {
            SplitStatus::Split(witness) => {
                assert!(witness.verify(&ses));
                assert!(witness.retraction().source().ptr_eq(&sum));
                assert!(witness.retraction().target().ptr_eq(&s));
                assert!(witness.section().source().ptr_eq(&p));
                assert!(witness.section().target().ptr_eq(&sum));
            }
            SplitStatus::NonSplit(_) => panic!("a direct sum sequence splits"),
        }
    }

    #[test]
    fn new_rejects_each_defect_with_a_typed_error() {
        let algebra = linear_an(3, f5());
        let s = Module::simple(&algebra, 0);
        let p = Module::projective(&algebra, 1);
        let (sum, inclusions, projections) = direct_sum(&[&s, &p]);
        let (_, _, other_projections) = direct_sum(&[&s, &p]);
        assert_eq!(
            ShortExactSequence::new(inclusions[0].clone(), other_projections[1].clone())
                .unwrap_err(),
            SequenceError::EndpointMismatch
        );
        let zero_inclusion = zero_morphism(&s, &sum).unwrap();
        assert_eq!(
            ShortExactSequence::new(zero_inclusion, projections[1].clone()).unwrap_err(),
            SequenceError::NotMono { vertex: 0 }
        );
        let zero_projection = zero_morphism(&sum, &p).unwrap();
        assert_eq!(
            ShortExactSequence::new(inclusions[0].clone(), zero_projection).unwrap_err(),
            SequenceError::NotEpi { vertex: 1 }
        );
        assert_eq!(
            ShortExactSequence::new(inclusions[0].clone(), projections[0].clone()).unwrap_err(),
            SequenceError::CompositeNonzero { vertex: 0 }
        );
        let (_, triple_inclusions, triple_projections) = direct_sum(&[&s, &p, &s]);
        assert_eq!(
            ShortExactSequence::new(triple_inclusions[0].clone(), triple_projections[1].clone())
                .unwrap_err(),
            SequenceError::DimensionMismatch { vertex: 0 }
        );
    }

    #[test]
    fn from_ext1_of_a_nonzero_class_is_non_split_and_round_trips() {
        for field in [f5(), f2()] {
            let algebra = truncated_poly(3, field).unwrap();
            let s = Module::simple(&algebra, 0);
            let space = ExtSpace::new(&s, &s, 1).unwrap();
            assert_eq!(space.dim(), 1);
            let xi = one_class(&space);
            let ses = ShortExactSequence::from_ext1(&xi).unwrap();
            assert_eq!(ses.sub().dim_vector(), &[1]);
            assert_eq!(ses.middle().dim_vector(), &[2]);
            assert_eq!(ses.quotient().dim_vector(), &[1]);
            let recovered = ses.ext1_class(&space).unwrap();
            assert!(
                recovered.equals(&xi).unwrap(),
                "round trip over F_{}",
                field.modulus()
            );
            match ses.split_status() {
                SplitStatus::NonSplit(witness) => {
                    assert!(witness.verify(&ses));
                    let mut bad = witness.dual().to_vec();
                    bad[0] = field.add(bad[0], field.one());
                    assert!(!NonSplitWitness { dual: bad }.verify(&ses));
                    let zeros = vec![field.zero(); witness.dual().len()];
                    assert!(!NonSplitWitness { dual: zeros }.verify(&ses));
                    assert!(!NonSplitWitness { dual: Vec::new() }.verify(&ses));
                }
                SplitStatus::Split(_) => panic!("a nonzero Ext^1 class gives a non-split sequence"),
            }
        }
    }

    #[test]
    fn from_ext1_of_the_zero_class_splits_with_a_verifying_witness() {
        let algebra = truncated_poly(3, f5()).unwrap();
        let s = Module::simple(&algebra, 0);
        let space = ExtSpace::new(&s, &s, 1).unwrap();
        let ses = ShortExactSequence::from_ext1(&space.zero_class()).unwrap();
        assert_eq!(ses.middle().dim_vector(), &[2]);
        match ses.split_status() {
            SplitStatus::Split(witness) => assert!(witness.verify(&ses)),
            SplitStatus::NonSplit(_) => panic!("the zero class gives a split sequence"),
        }
        let recovered = ses.ext1_class(&space).unwrap();
        assert!(recovered.is_zero());
    }

    #[test]
    fn from_ext1_over_a_projective_quotient_uses_the_empty_presentation() {
        // S_2 is projective over linear A_3, so Ext^1(S_2, S_0) = 0 and the
        // resolution of S_2 has no differential.
        let algebra = linear_an(3, f5());
        let s0 = Module::simple(&algebra, 0);
        let s2 = Module::simple(&algebra, 2);
        let space = ExtSpace::new(&s2, &s0, 1).unwrap();
        assert_eq!(space.dim(), 0);
        let ses = ShortExactSequence::from_ext1(&space.zero_class()).unwrap();
        assert_eq!(ses.sub().dim_vector(), &[1, 0, 0]);
        assert_eq!(ses.quotient().dim_vector(), &[0, 0, 1]);
        match ses.split_status() {
            SplitStatus::Split(witness) => assert!(witness.verify(&ses)),
            SplitStatus::NonSplit(_) => panic!("the zero class gives a split sequence"),
        }
        assert!(ses.ext1_class(&space).unwrap().is_zero());
    }

    // Over kA_3/(ab) the extension of S_0 by S_1 with class the Ext^1
    // generator is P_0 (dimension vector (1, 1, 0)), and the extension of
    // S_1 by S_2 is P_1 (dimension vector (0, 1, 1)); both are non-split.
    // Splicing them realizes the Yoneda product, which is the Ext^2
    // generator detected by the relation: the product of the recovered
    // classes is nonzero in the one-dimensional Ext^2(S_0, S_2).
    #[test]
    fn round_trip_and_splicing_agreement_over_a3_mod_ab() {
        let field = f5();
        let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
        let s0 = Module::simple(&algebra, 0);
        let s1 = Module::simple(&algebra, 1);
        let s2 = Module::simple(&algebra, 2);
        let space_a = ExtSpace::new(&s0, &s1, 1).unwrap();
        let space_b = ExtSpace::new(&s1, &s2, 1).unwrap();
        let alpha = one_class(&space_a);
        let beta = one_class(&space_b);
        let ses_a = ShortExactSequence::from_ext1(&alpha).unwrap();
        let ses_b = ShortExactSequence::from_ext1(&beta).unwrap();
        assert_eq!(ses_a.middle().dim_vector(), &[1, 1, 0]);
        assert_eq!(ses_b.middle().dim_vector(), &[0, 1, 1]);
        let recovered_a = ses_a.ext1_class(&space_a).unwrap();
        let recovered_b = ses_b.ext1_class(&space_b).unwrap();
        assert!(recovered_a.equals(&alpha).unwrap());
        assert!(recovered_b.equals(&beta).unwrap());
        for ses in [&ses_a, &ses_b] {
            match ses.split_status() {
                SplitStatus::NonSplit(witness) => assert!(witness.verify(ses)),
                SplitStatus::Split(_) => panic!("the generator classes are non-split"),
            }
        }
        let spliced = recovered_a.then(&recovered_b).unwrap();
        let direct = alpha.then(&beta).unwrap();
        assert_eq!(spliced.space().dim(), 1);
        assert!(
            !spliced.is_zero(),
            "the spliced 2-extension class is nonzero"
        );
        assert!(spliced.equals(&direct).unwrap());
    }

    #[test]
    fn split_witness_rejects_a_tampered_retraction_or_section() {
        let algebra = linear_an(3, f5());
        let field = f5();
        let s = Module::simple(&algebra, 0);
        let p = Module::projective(&algebra, 1);
        let (_, inclusions, projections) = direct_sum(&[&s, &p]);
        let ses = ShortExactSequence::new(inclusions[0].clone(), projections[1].clone()).unwrap();
        let SplitStatus::Split(witness) = ses.split_status() else {
            panic!("a direct sum sequence splits");
        };
        let scale = |f: &Morphism| {
            let nv = f.source().algebra().quiver().num_vertices();
            let maps = (0..nv)
                .map(|v| {
                    let m = f.map_at(v);
                    let mut out = DenseMat::zero(m.rows(), m.cols());
                    for r in 0..m.rows() {
                        for c in 0..m.cols() {
                            out.set(r, c, field.mul(field.elem(2), m.get(r, c)));
                        }
                    }
                    out
                })
                .collect();
            Morphism::new(f.source(), f.target(), maps).unwrap()
        };
        let bad_retraction = SplitWitness {
            retraction: scale(witness.retraction()),
            section: witness.section().clone(),
        };
        assert!(!bad_retraction.verify(&ses));
        let bad_section = SplitWitness {
            retraction: witness.retraction().clone(),
            section: scale(witness.section()),
        };
        assert!(!bad_section.verify(&ses));
    }

    // Section 15 of the design: a dual vector with y A != 0, and a dual
    // vector with y b = 0. Adding a unit vector at a nonzero row of A
    // moves y A off zero; the zero vector and the doubled vector keep
    // y A = 0 and fail y b = 1.
    #[test]
    fn a_tampered_or_zero_dual_vector_fails_verification() {
        let field = f5();
        let algebra = truncated_poly(3, field).unwrap();
        let s = Module::simple(&algebra, 0);
        let space = ExtSpace::new(&s, &s, 1).unwrap();
        let ses = ShortExactSequence::from_ext1(&one_class(&space)).unwrap();
        let SplitStatus::NonSplit(witness) = ses.split_status() else {
            panic!("the generator class does not split");
        };
        assert!(witness.verify(&ses));
        let (a, _) = retraction_system(&ses);
        let r = (0..a.rows())
            .find(|&r| a.row(r).iter().any(|v| !v.is_zero()))
            .expect("the retraction system has a nonzero row");
        let mut dual = witness.dual().to_vec();
        dual[r] = field.add(dual[r], field.one());
        let off_kernel = NonSplitWitness { dual };
        assert!(!off_kernel.verify(&ses), "y A is nonzero");
        let zero = NonSplitWitness {
            dual: vec![field.zero(); witness.dual().len()],
        };
        assert!(!zero.verify(&ses), "y b is zero");
        let doubled = NonSplitWitness {
            dual: witness
                .dual()
                .iter()
                .map(|&y| field.mul(field.elem(2), y))
                .collect(),
        };
        assert!(!doubled.verify(&ses), "y b is two");
    }

    #[test]
    fn ext1_class_rejects_a_space_with_wrong_degree_or_endpoints() {
        let field = f5();
        let algebra = truncated_poly(3, field).unwrap();
        let s = Module::simple(&algebra, 0);
        let space = ExtSpace::new(&s, &s, 1).unwrap();
        let ses = ShortExactSequence::from_ext1(&one_class(&space)).unwrap();
        let deg2 = ExtSpace::new(&s, &s, 2).unwrap();
        assert_eq!(
            ses.ext1_class(&deg2).unwrap_err(),
            SequenceError::WrongDegree {
                expected: 1,
                got: 2
            }
        );
        let s_copy = Module::simple(&algebra, 0);
        let wrong_source = ExtSpace::new(&s_copy, &s, 1).unwrap();
        assert_eq!(
            ses.ext1_class(&wrong_source).unwrap_err(),
            SequenceError::SpaceSourceMismatch
        );
        let wrong_target = ExtSpace::new(&s, &s_copy, 1).unwrap();
        assert_eq!(
            ses.ext1_class(&wrong_target).unwrap_err(),
            SequenceError::SpaceTargetMismatch
        );
    }

    #[test]
    fn from_ext1_rejects_a_class_of_the_wrong_degree() {
        let field = f5();
        let algebra = truncated_poly(3, field).unwrap();
        let s = Module::simple(&algebra, 0);
        let deg0 = ExtSpace::new(&s, &s, 0).unwrap().identity_class().unwrap();
        assert_eq!(
            ShortExactSequence::from_ext1(&deg0).unwrap_err(),
            SequenceError::WrongDegree {
                expected: 1,
                got: 0
            }
        );
        let deg2 = one_class(&ExtSpace::new(&s, &s, 2).unwrap());
        assert_eq!(
            ShortExactSequence::from_ext1(&deg2).unwrap_err(),
            SequenceError::WrongDegree {
                expected: 1,
                got: 2
            }
        );
    }

    #[test]
    fn a_zero_sub_gives_an_isomorphism_like_split_sequence() {
        let algebra = linear_an(3, f5());
        let p = Module::projective(&algebra, 0);
        let z = Module::zero(&algebra);
        let inclusion = zero_morphism(&z, &p).unwrap();
        let ses = ShortExactSequence::new(inclusion, identity(&p)).unwrap();
        match ses.split_status() {
            SplitStatus::Split(witness) => assert!(witness.verify(&ses)),
            SplitStatus::NonSplit(_) => panic!("a zero-sub sequence splits"),
        }
    }

    #[test]
    fn from_ext1_and_split_status_are_deterministic_across_recomputation() {
        let field = f5();
        let algebra = truncated_poly(3, field).unwrap();
        let s = Module::simple(&algebra, 0);
        let space = ExtSpace::new(&s, &s, 1).unwrap();
        let xi = one_class(&space);
        let first = ShortExactSequence::from_ext1(&xi).unwrap();
        let second = ShortExactSequence::from_ext1(&xi).unwrap();
        for v in 0..algebra.quiver().num_vertices() {
            assert_eq!(
                first.inclusion().map_at(v).entries_u64(),
                second.inclusion().map_at(v).entries_u64()
            );
            assert_eq!(
                first.projection().map_at(v).entries_u64(),
                second.projection().map_at(v).entries_u64()
            );
        }
        let (SplitStatus::NonSplit(a), SplitStatus::NonSplit(b)) =
            (first.split_status(), second.split_status())
        else {
            panic!("the generator class is non-split");
        };
        assert_eq!(
            a.dual().iter().map(|c| c.raw()).collect::<Vec<_>>(),
            b.dual().iter().map(|c| c.raw()).collect::<Vec<_>>()
        );
    }
}

use super::helpers::{factor_through_epi, negate};
use super::{NonSplitWitness, ShortExactSequence, SplitStatus, SplitWitness};
use crate::decompose::add_morphisms;
use crate::field::{Fp, PrimeField};
use crate::hom::{Morphism, identity};
use crate::linalg::DenseMat;
use crate::quiver::ArrowId;

impl ShortExactSequence {
    /// Solves the retraction system in the fixed order stated in the module
    /// docs. Both outcomes carry their proof: a retraction and a section that
    /// recheck by multiplication, or a dual vector proving the system
    /// inconsistent.
    ///
    /// A split sequence costs one reduction of `[A | b]`, a non-split one a
    /// second of `[A | b | I]`. The crate-private `split_status_one_pass`
    /// trades that around for callers that expect the non-split answer.
    pub fn split_status(&self) -> SplitStatus {
        let field = self.middle.field();
        let (a, b) = retraction_system(self);
        match a.solve(&b, &field) {
            Some(x) => SplitStatus::Split(self.split_witness(&x)),
            None => {
                let (reduced, pivots) = augmented_with_dual(&a, &b, &field);
                let cols = a.cols();
                let pivot_row = pivots
                    .iter()
                    .position(|&c| c == cols)
                    .expect("an unsolvable system pivots in the right-side column");
                SplitStatus::NonSplit(non_split_witness(&reduced, pivot_row, cols, a.rows()))
            }
        }
    }

    /// [`ShortExactSequence::split_status`] from one reduction of
    /// `[A | b | I]`, which carries the dual vector along.
    ///
    /// The two routes return the same value. This one saves the second
    /// elimination on a non-split sequence and pays for the identity block on
    /// a split one, so the almost-split construction takes it and the general
    /// entry point does not.
    ///
    /// Same value, because the identity block only adds pivots to the right of
    /// column `cols`, and eliminating those touches rows already zero in the
    /// first `cols + 1` columns. Pivots, entries, and the
    /// free-variables-zeroed solution in those columns are therefore the ones
    /// [`DenseMat::solve`] reads off `[A | b]`.
    pub(crate) fn split_status_one_pass(&self) -> SplitStatus {
        let field = self.middle.field();
        let (a, b) = retraction_system(self);
        let (rows, cols) = (a.rows(), a.cols());
        let (reduced, pivots) = augmented_with_dual(&a, &b, &field);
        if let Some(pivot_row) = pivots.iter().position(|&c| c == cols) {
            return SplitStatus::NonSplit(non_split_witness(&reduced, pivot_row, cols, rows));
        }
        let mut x = vec![Fp::ZERO; cols];
        for (i, &pc) in pivots.iter().enumerate().filter(|&(_, &c)| c < cols) {
            x[pc] = reduced.get(i, cols);
        }
        SplitStatus::Split(self.split_witness(&x))
    }

    /// The retraction of a solution vector and the section it induces.
    fn split_witness(&self, x: &[Fp]) -> SplitWitness {
        let retraction = self.retraction_from_solution(x);
        let e_idem = retraction
            .then(&self.inclusion)
            .expect("the retraction ends at the sub");
        // For p = id - r.then(iota) the composite iota.then(p) is zero, so p
        // kills ker pi and factors through pi. The factor s obeys
        // pi.then(s.then(pi)) = p.then(pi) = pi, and pi is epi, so s.then(pi)
        // is the identity: s is a section.
        let p = add_morphisms(&identity(&self.middle), &negate(&e_idem));
        SplitWitness {
            section: factor_through_epi(&self.projection, &p),
            retraction,
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
            let block = DenseMat::from_flat(de, dn, &x[offset..offset + de * dn]);
            offset += de * dn;
            maps.push(block);
        }
        Morphism::new(&self.middle, &self.sub, maps)
            .expect("the solved system contains every commuting square")
    }
}

fn non_split_witness(
    reduced: &DenseMat,
    pivot_row: usize,
    cols: usize,
    rows: usize,
) -> NonSplitWitness {
    NonSplitWitness {
        dual: (0..rows)
            .map(|r| reduced.get(pivot_row, cols + 1 + r))
            .collect(),
    }
}

/// The reduced row echelon form of `[A | b | I]` and its pivot columns. A
/// pivot in column `A.cols()` proves the system inconsistent, and that row's
/// identity tail is the dual vector `y` with `y A = 0` and `y b = 1`.
fn augmented_with_dual(a: &DenseMat, b: &[Fp], field: &PrimeField) -> (DenseMat, Vec<usize>) {
    let (rows, cols) = (a.rows(), a.cols());
    let mut aug = DenseMat::zero(rows, cols + 1 + rows);
    for (r, &rhs) in b.iter().enumerate() {
        for c in 0..cols {
            aug.set(r, c, a.get(r, c));
        }
        aug.set(r, cols, rhs);
        aug.set(r, cols + 1 + r, field.one());
    }
    aug.into_rref(field)
}

fn arrow_retraction_rows(
    e: &crate::module::Module,
    n: &crate::module::Module,
    offsets: &[usize],
    total: usize,
    field: &PrimeField,
    arrow: ArrowId,
) -> (Vec<Vec<Fp>>, Vec<Fp>) {
    let quiver = e.algebra().quiver();
    let (s, t) = (quiver.source(arrow), quiver.target(arrow));
    let ea = e.map(arrow);
    let na = n.map(arrow);
    let mut rows = Vec::new();
    let mut rhs = Vec::new();
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
    (rows, rhs)
}

fn inclusion_retraction_rows(
    sequence: &ShortExactSequence,
    offsets: &[usize],
    total: usize,
    field: &PrimeField,
) -> (Vec<Vec<Fp>>, Vec<Fp>) {
    let e = &sequence.middle;
    let n = &sequence.sub;
    let nv = e.algebra().quiver().num_vertices();
    let iota = &sequence.inclusion;
    let mut rows = Vec::new();
    let mut rhs = Vec::new();
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
                rhs.push(field.elem((i == j) as i64));
            }
        }
    }
    (rows, rhs)
}

/// The retraction system for `r: E -> N` in the fixed crate order: unknowns
/// vertex-major then row-major; equations are the commuting squares in
/// (arrow, row, column) lexicographic order, then `iota.then(r) = id`
/// vertex-major then row-major.
pub(super) fn retraction_system(sequence: &ShortExactSequence) -> (DenseMat, Vec<Fp>) {
    let e = &sequence.middle;
    let n = &sequence.sub;
    let field: PrimeField = e.field();
    let quiver = e.algebra().quiver();
    let nv = quiver.num_vertices();
    let mut offsets = vec![0usize; nv as usize];
    let mut total = 0usize;
    for vertex in 0..nv {
        offsets[vertex as usize] = total;
        total += e.dim_at(vertex) * n.dim_at(vertex);
    }
    let mut rows: Vec<Vec<Fp>> = Vec::new();
    let mut rhs: Vec<Fp> = Vec::new();
    for idx in 0..quiver.num_arrows() {
        let (arrow_rows, arrow_rhs) =
            arrow_retraction_rows(e, n, &offsets, total, &field, ArrowId(idx as u32));
        rows.extend(arrow_rows);
        rhs.extend(arrow_rhs);
    }
    let (inclusion_rows, inclusion_rhs) =
        inclusion_retraction_rows(sequence, &offsets, total, &field);
    rows.extend(inclusion_rows);
    rhs.extend(inclusion_rhs);
    let a = DenseMat::from_rows_with_cols(&rows, total);
    (a, rhs)
}

impl SplitWitness {
    /// Rechecks both identities against the sequence: `iota.then(r) = id` on
    /// the sub and `s.then(projection) = id` on the quotient.
    pub fn verify(&self, sequence: &ShortExactSequence) -> bool {
        let_or_false!(Ok(left) = sequence.inclusion.then(&self.retraction));
        let_or_false!(Ok(right) = self.section.then(&sequence.projection));
        left == identity(&sequence.sub) && right == identity(&sequence.quotient)
    }
}

impl NonSplitWitness {
    /// Rebuilds the retraction system in the fixed order and checks
    /// `y A = 0` and `y b = 1` by multiplication.
    pub fn verify(&self, sequence: &ShortExactSequence) -> bool {
        let (a, b) = retraction_system(sequence);
        verify_guard!(self.dual.len() == a.rows());
        let field = sequence.middle.field();
        let y = DenseMat::from_flat(1, self.dual.len(), &self.dual);
        let left = y.mul(&a, &field);
        let right = y
            .mul(&DenseMat::from_flat(b.len(), 1, &b), &field)
            .get(0, 0);
        left.row(0).iter().all(|value| value.is_zero()) && right == field.one()
    }
}

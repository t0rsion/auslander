use crate::field::Fp;
use crate::linalg::merge_scaled_terms;
use crate::order::word_cmp;
use crate::profile::{Site, hit};
use crate::quiver::{ArrowId, PathWord, QuiverError};
use crate::relation::Relation;

use super::types::{Algebra, BasisIdx};

impl Algebra {
    accessor_methods! {
        /// The verified certificate this algebra was built from.
        ///
        /// Serialize it with [`crate::certificate::Certificate::to_canonical_json`]
        /// for dumping.
        pub certificate() -> &crate::certificate::Certificate = |this| &this.certificate;
        /// The effective completion limits of this algebra.
        ///
        /// Derived completions, [`crate::opposite::opposite`] included, run
        /// with them.
        pub completion_limits() -> &crate::completion::CompletionLimits = |this| &this.limits;
        /// `dim_k A` = number of normal words.
        pub dim() -> usize = |this| this.basis.len();
        pub quiver() -> &crate::quiver::Quiver = |this| &this.quiver;
        pub field() -> crate::field::PrimeField = |this| this.field;
        /// The normal-word basis, in the order documented on the type.
        pub basis() -> &[PathWord] = |this| &this.basis;
        /// The reduced Groebner basis of the ideal, each element a monic
        /// [`crate::relation::Relation`] with terms in descending order.
        pub relations() -> &[Relation] = |this| &this.relations;
    }

    /// Basis index of `path`.
    ///
    /// `Ok(Some(i))` when the path is a normal word. `Ok(None)` when it is a
    /// valid path of the quiver but not a normal word. `Err` when it is not a
    /// path of this algebra's quiver (see [`PathWord::validate_in`]).
    ///
    /// A non-normal path is not zero in general: it equals its normal form,
    /// a combination of normal words that [`Algebra::nf_word`] computes. For
    /// a monomial ideal the two notions coincide and `Ok(None)` means zero.
    pub fn path_index(&self, path: &PathWord) -> Result<Option<BasisIdx>, QuiverError> {
        path.validate_in(&self.quiver)?;
        Ok(if path.is_trivial() {
            Some(path.source() as usize)
        } else {
            self.index_of.get(path.arrows()).copied()
        })
    }

    accessor_methods! {
        /// Basis index of `e_v`; equals `v`. Panics if `v >= num_vertices`.
        pub vertex_idempotent(v: u32) -> BasisIdx = |this| {
            assert!(v < this.quiver.num_vertices());
            v as usize
        };
        /// Basis indices of normal words with source `v`, the basis of
        /// `e_v A = P_v`. Panics if `v >= num_vertices`.
        pub paths_from(v: u32) -> &[BasisIdx] = |this| &this.from[v as usize];
        /// Basis indices of normal words with target `v`, the basis of `A e_v`.
        /// Panics if `v >= num_vertices`.
        pub paths_to(v: u32) -> &[BasisIdx] = |this| &this.to[v as usize];
        /// Basis indices of normal words from `u` to `v`, the basis of
        /// `e_u A e_v`. Panics if either vertex is out of range.
        pub paths_between(u: u32, v: u32) -> &[BasisIdx] = |this| &this.between[u as usize][v as usize];
    }

    /// Cartan matrix: `c[i][j] = dim e_i A e_j`, the number of normal words
    /// from `i` to `j`; row `i` is the dimension vector of the projective
    /// `P_i = e_i A`.
    pub fn cartan_matrix(&self) -> Vec<Vec<usize>> {
        self.between
            .iter()
            .map(|row| row.iter().map(Vec::len).collect())
            .collect()
    }

    accessor_methods! {
        /// `basis[i] · a` as a sparse coefficient row over the basis, sorted
        /// by basis index. The row is empty when the product is zero, and has
        /// at most one entry over a monomial ideal. Panics on out-of-range `i`
        /// or `a`.
        pub right_mul(i: BasisIdx, a: ArrowId) -> &[(BasisIdx, Fp)] = |this| &this.right_mul[i][a.index()];
        /// `a · basis[i]`, as [`Self::right_mul`].
        pub left_mul(a: ArrowId, i: BasisIdx) -> &[(BasisIdx, Fp)] = |this| &this.left_mul[a.index()][i];
    }

    /// The normal form of `word` as a sparse coefficient row over the basis,
    /// sorted by basis index. Errors when `word` is not a path of this
    /// algebra's quiver.
    pub fn nf_word(&self, word: &PathWord) -> Result<Vec<(BasisIdx, Fp)>, QuiverError> {
        hit(Site::NfWord);
        word.validate_in(&self.quiver)?;
        if word.is_trivial() {
            return Ok(vec![(word.source() as usize, self.field.one())]);
        }
        Ok(self.nf_arrow_word(word.arrows().to_vec()))
    }

    /// `basis[p] · basis[q]` as a sparse coefficient row over the basis,
    /// sorted by basis index. The row is empty when the endpoints do not
    /// compose or the product reduces to zero. Panics on out-of-range
    /// indices.
    pub fn mul_basis(&self, p: BasisIdx, q: BasisIdx) -> Vec<(BasisIdx, Fp)> {
        hit(Site::MulBasis);
        let (left, right) = (&self.basis[p], &self.basis[q]);
        if left.target() != right.source() {
            return Vec::new();
        }
        if left.is_trivial() {
            return vec![(q, self.field.one())];
        }
        if right.is_trivial() {
            return vec![(p, self.field.one())];
        }
        let mut word = left.arrows().to_vec();
        word.extend_from_slice(right.arrows());
        self.nf_arrow_word(word)
    }

    /// Divides `word` against the reduced Groebner basis. Requires `word`
    /// nonempty and composable in the quiver.
    ///
    /// The verified diamond property makes every reduction order give the
    /// same normal form. Reducing the first matching basis element at its
    /// leftmost factor is as good as any other choice.
    pub(super) fn nf_arrow_word(&self, word: Vec<ArrowId>) -> Vec<(BasisIdx, Fp)> {
        let mut poly: Vec<(Fp, Vec<ArrowId>)> = vec![(self.field.one(), word)];
        let mut out: Vec<(BasisIdx, Fp)> = Vec::new();
        while let Some((coeff, word)) = poly.first().cloned() {
            match self.leftmost_reduction(&word) {
                None => {
                    let index = *self
                        .index_of
                        .get(&word)
                        .expect("the verifier enumerated every normal word");
                    out.push((index, coeff));
                    poly.remove(0);
                }
                Some((relation, position)) => {
                    let lead_len = relation.leading().1.len();
                    let left = &word[..position];
                    let right = &word[position + lead_len..];
                    let scale = self.field.neg(coeff);
                    poly = add_scaled(self.field, &poly, scale, left, relation.terms(), right);
                }
            }
        }
        out.sort_unstable_by_key(|&(index, _)| index);
        out
    }

    /// The first Groebner element whose leading word is a factor of `word`,
    /// with the leftmost factor position.
    fn leftmost_reduction(&self, word: &[ArrowId]) -> Option<(&Relation, usize)> {
        self.relations.iter().find_map(|relation| {
            let lead = relation.leading().1.arrows();
            word.windows(lead.len())
                .position(|factor| factor == lead)
                .map(|at| (relation, at))
        })
    }
}

/// `poly + scale · left · terms · right`, merged into strictly descending
/// order. `terms` is descending, and concatenation with a fixed context
/// preserves the order.
fn add_scaled(
    field: crate::field::PrimeField,
    poly: &[(Fp, Vec<ArrowId>)],
    scale: Fp,
    left: &[ArrowId],
    terms: &[(Fp, PathWord)],
    right: &[ArrowId],
) -> Vec<(Fp, Vec<ArrowId>)> {
    let addend: Vec<(Fp, Vec<ArrowId>)> = terms
        .iter()
        .map(|(c, w)| (*c, [left, w.arrows(), right].concat()))
        .collect();
    let mut merged = Vec::new();
    merge_scaled_terms(
        poly,
        &addend,
        (scale, &field),
        |a, b| word_cmp(&b.1, &a.1),
        |term| term.0,
        |term, value| (value, term.1.clone()),
        &mut merged,
    );
    merged
}

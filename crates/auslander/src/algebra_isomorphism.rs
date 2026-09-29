//! Checked algebra isomorphisms given on generators, and matching of an
//! algebra against a finite family.
//!
//! [`AlgebraIsomorphism`] stores a map `φ: A → B` by the images of the vertex
//! idempotents and the arrows of `A`. [`AlgebraIsomorphism::verify`] decides
//! from that data alone that `φ` is an isomorphism.
//! [`FamilyIndex::match_member`] finds a family member isomorphic to a given
//! algebra through [`GentleKey`] or an equal certificate.

use std::sync::Arc;

use rustc_hash::FxHashMap;

use crate::algebra::{Algebra, BasisIdx};
use crate::certificate::Certificate;
use crate::field::{Fp, PrimeField, unit_vector};
use crate::gentle::{GentleError, GentleKey, GentleLabeling, GentlePresentation};
use crate::linalg::DenseMat;
use crate::quiver::{ArrowId, PathWord};
use crate::relation::Relation;

/// An algebra map `φ: A → B` given by `φ(e_v) = e_{π(v)}` for a vertex map
/// `π` and one normal-word coordinate vector `φ(a)` per arrow `a` of `A`.
///
/// Paths compose left to right, so `φ(a_1·…·a_k) = φ(a_1)·…·φ(a_k)`.
/// [`AlgebraIsomorphism::verify`] checks five facts:
///
/// 1. `π` is a bijection of vertex sets.
/// 2. For `a: s → t`, `φ(a)` lies in `e_{π(s)} J_B e_{π(t)}`, where `J_B` is
///    the arrow ideal of `B`.
/// 3. `φ` maps every reduced relation of `A` to zero.
/// 4. The arrow images span `J_B / J_B^2`.
/// 5. `dim A = dim B`.
///
/// These imply that `φ` is an isomorphism. The path algebra `kQ_A` is free on
/// its quiver, and the `e_{π(v)}` are orthogonal idempotents with sum `1`, so
/// checks 1 and 2 extend `φ` to an algebra map `kQ_A → B`. The reduced
/// relations generate the ideal of `A`, so check 3 factors that map through
/// `A`. The image contains every `e_w` and a subspace `V` with
/// `V + J_B^2 = J_B`. Then `J_B ⊆ im φ + J_B^k` for every `k` by induction,
/// and `J_B` is nilpotent, so `J_B ⊆ im φ`. With `B = ⊕ k e_w ⊕ J_B` the map
/// is onto, and check 5 makes it bijective.
#[derive(Clone, Debug)]
pub struct AlgebraIsomorphism {
    pub(crate) source: Arc<Algebra>,
    pub(crate) target: Arc<Algebra>,
    pub(crate) vertex_map: Vec<u32>,
    pub(crate) arrow_images: Vec<Vec<Fp>>,
}

/// Why [`AlgebraIsomorphism::from_gentle`] found no isomorphism.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GentleMatchError {
    /// The algebras live over different prime fields.
    FieldMismatch { source: u64, target: u64 },
    /// Recognition rejected the source presentation.
    SourceNotGentle(GentleError),
    /// Recognition rejected the target presentation.
    TargetNotGentle(GentleError),
    /// Both presentations are gentle with different canonical keys.
    DifferentKeys,
}

display_error! { error GentleMatchError {
    Self::FieldMismatch { source, target } => "the algebras live over GF({source}) and GF({target})";
    Self::SourceNotGentle(error) => "the source presentation is not gentle: {error}";
    Self::TargetNotGentle(error) => "the target presentation is not gentle: {error}";
    Self::DifferentKeys => "the gentle presentations have different canonical keys";
} }

impl AlgebraIsomorphism {
    /// The isomorphism of bound quivers between two gentle presentations with
    /// equal [`GentleKey`], composed through their canonical labelings.
    ///
    /// Each arrow maps to one arrow of `target`, so every image is a single
    /// normal word.
    pub fn from_gentle(
        source: &Arc<Algebra>,
        target: &Arc<Algebra>,
    ) -> Result<AlgebraIsomorphism, GentleMatchError> {
        let (left, right) = (source.field(), target.field());
        if left != right {
            return Err(GentleMatchError::FieldMismatch {
                source: left.modulus(),
                target: right.modulus(),
            });
        }
        let labeling = |algebra, error: fn(GentleError) -> GentleMatchError| {
            GentlePresentation::new(algebra)
                .map(|presentation| presentation.canonical_labeling())
                .map_err(error)
        };
        let source_labels = labeling(source, GentleMatchError::SourceNotGentle)?;
        let target_labels = labeling(target, GentleMatchError::TargetNotGentle)?;
        if source_labels.key() != target_labels.key() {
            return Err(GentleMatchError::DifferentKeys);
        }
        Ok(through_labelings(
            source,
            &source_labels,
            target,
            &target_labels,
        ))
    }

    /// The identity map between two algebras with equal certificates.
    pub(crate) fn between_equal(source: &Arc<Algebra>, target: &Arc<Algebra>) -> Self {
        let vertices = (0..source.quiver().num_vertices()).collect();
        let arrows: Vec<_> = (0..source.quiver().num_arrows() as u32)
            .map(ArrowId)
            .collect();
        on_arrows(source, target, vertices, &arrows)
    }

    accessor_methods! {
        /// The algebra `A`.
        pub source() -> &Arc<Algebra> = |this| &this.source;
        /// The algebra `B`.
        pub target() -> &Arc<Algebra> = |this| &this.target;
        /// The vertex map `π`: vertex `v` of `A` goes to `vertex_map()[v]`.
        pub vertex_map() -> &[u32] = |this| &this.vertex_map;
        /// The image of each arrow of `A` over the normal-word basis of `B`.
        pub arrow_images() -> &[Vec<Fp>] = |this| &this.arrow_images;
    }

    /// Checks the five facts listed on the type, which make `φ` an
    /// isomorphism.
    pub fn verify(&self) -> bool {
        let (source, target) = (&self.source, &self.target);
        source.field() == target.field()
            && source.dim() == target.dim()
            && self.vertices_biject()
            && self.arrow_images.len() == source.quiver().num_arrows()
            && (0..self.arrow_images.len()).all(|arrow| self.image_in_corner(arrow))
            && source
                .relations()
                .iter()
                .all(|relation| self.kills(relation))
            && self.spans_arrow_space()
    }

    fn vertices_biject(&self) -> bool {
        let count = self.target.quiver().num_vertices();
        let mut seen = vec![false; count as usize];
        self.vertex_map.len() == self.source.quiver().num_vertices() as usize
            && self.vertex_map.len() == count as usize
            && self.vertex_map.iter().all(|&vertex| {
                vertex < count && !std::mem::replace(&mut seen[vertex as usize], true)
            })
    }

    /// The target corner `(π(s), π(t))` of arrow `arrow: s → t`.
    fn corner(&self, arrow: usize) -> (u32, u32) {
        let (source, target) = self.source.quiver().arrows()[arrow];
        (
            self.vertex_map[source as usize],
            self.vertex_map[target as usize],
        )
    }

    /// Whether the image of `arrow` lies in `e_{π(s)} J_B e_{π(t)}`. Every
    /// nontrivial normal word lies in `J_B`, and no trivial one does.
    fn image_in_corner(&self, arrow: usize) -> bool {
        let (from, to) = self.corner(arrow);
        let (image, basis) = (&self.arrow_images[arrow], self.target.basis());
        image.len() == basis.len()
            && image.iter().zip(basis).all(|(coefficient, word)| {
                coefficient.is_zero()
                    || (!word.is_trivial() && word.source() == from && word.target() == to)
            })
    }

    /// Whether `φ` maps `relation` to zero in `B`.
    fn kills(&self, relation: &Relation) -> bool {
        let field = self.target.field();
        let mut sum = vec![field.zero(); self.target.dim()];
        for (coefficient, word) in relation.terms() {
            for (entry, value) in sum.iter_mut().zip(self.image_of(word)) {
                *entry = field.add(*entry, field.mul(*coefficient, value));
            }
        }
        sum.iter().all(|entry| entry.is_zero())
    }

    fn image_of(&self, word: &PathWord) -> Vec<Fp> {
        let start = unit_vector(
            self.target.dim(),
            self.vertex_map[word.source() as usize] as usize,
        );
        word.arrows().iter().fold(start, |product, arrow| {
            multiply(&self.target, &product, &self.arrow_images[arrow.index()])
        })
    }

    /// Whether the arrow images span `J_B / J_B^2`, one corner at a time.
    ///
    /// Check 2 has placed every image in `J_B`, so the rank of `J_B^2` plus
    /// the images equals `dim J_B` exactly when they span.
    fn spans_arrow_space(&self) -> bool {
        let (target, field) = (&self.target, self.target.field());
        let positions = target.component_positions();
        let count = target.quiver().num_vertices();
        let corner = |from: u32, to: u32| from as usize * count as usize + to as usize;
        let mut corners = vec![Vec::new(); corner(count, 0)];
        for (arrow, image) in self.arrow_images.iter().enumerate() {
            let (from, to) = self.corner(arrow);
            let mut row = vec![field.zero(); target.paths_between(from, to).len()];
            for (index, &value) in image.iter().enumerate().filter(|(_, v)| !v.is_zero()) {
                row[positions[index]] = value;
            }
            corners[corner(from, to)].push(row);
        }
        (0..count).all(|from| {
            (0..count).all(|to| {
                let square = target.radical_power_matrix(from, to, 2);
                let mut rows: Vec<Vec<Fp>> =
                    (0..square.rows()).map(|r| square.row(r).to_vec()).collect();
                rows.append(&mut corners[corner(from, to)]);
                let columns = target.paths_between(from, to).len();
                DenseMat::from_rows_with_cols(&rows, columns).rank(&field)
                    == target.radical_power_matrix(from, to, 1).rows()
            })
        })
    }
}

/// The product `left · right` of two coordinate vectors of `algebra`.
fn multiply(algebra: &Algebra, left: &[Fp], right: &[Fp]) -> Vec<Fp> {
    let field = algebra.field();
    let support = |vector: &[Fp]| -> Vec<(BasisIdx, Fp)> {
        let nonzero = vector.iter().enumerate().filter(|(_, v)| !v.is_zero());
        nonzero.map(|(index, &value)| (index, value)).collect()
    };
    let mut product = vec![field.zero(); algebra.dim()];
    for (p, x) in support(left) {
        for (q, y) in support(right) {
            for (r, z) in algebra.mul_basis(p, q) {
                product[r] = field.add(product[r], field.mul(field.mul(x, y), z));
            }
        }
    }
    product
}

/// The map that sends vertex `v` to `vertices[v]` and arrow `a` to the
/// normal word of arrow `arrows[a]` of `target`.
fn on_arrows(
    source: &Arc<Algebra>,
    target: &Arc<Algebra>,
    vertices: Vec<u32>,
    arrows: &[ArrowId],
) -> AlgebraIsomorphism {
    let arrow_images = arrows
        .iter()
        .map(|&arrow| {
            let word = PathWord::from_arrows(target.quiver(), &[arrow])
                .expect("an arrow id of the quiver is a path");
            let index = target
                .path_index(&word)
                .expect("the word is a path of the target quiver")
                .expect("an admissible ideal has no arrow as a leading word");
            unit_vector(target.dim(), index)
        })
        .collect();
    AlgebraIsomorphism {
        source: source.clone(),
        target: target.clone(),
        vertex_map: vertices,
        arrow_images,
    }
}

/// The relabeling `target_labels⁻¹ ∘ source_labels` for equal keys.
fn through_labelings(
    source: &Arc<Algebra>,
    source_labels: &GentleLabeling,
    target: &Arc<Algebra>,
    target_labels: &GentleLabeling,
) -> AlgebraIsomorphism {
    let mut vertex_from_label = vec![0; target_labels.vertex_map().len()];
    for (vertex, &label) in target_labels.vertex_map().iter().enumerate() {
        vertex_from_label[label as usize] = vertex as u32;
    }
    let mut arrow_from_label = vec![ArrowId(0); target_labels.arrow_map().len()];
    for (arrow, label) in target_labels.arrow_map().iter().enumerate() {
        arrow_from_label[label.index()] = ArrowId(arrow as u32);
    }
    let vertices = source_labels
        .vertex_map()
        .iter()
        .map(|&label| vertex_from_label[label as usize])
        .collect();
    let arrows: Vec<_> = source_labels
        .arrow_map()
        .iter()
        .map(|label| arrow_from_label[label.index()])
        .collect();
    on_arrows(source, target, vertices, &arrows)
}

/// How one family member is found again: by its gentle key, or by its
/// certificate when its presentation is not gentle.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum MemberKey {
    Gentle(GentleKey),
    Exact(String),
}

/// A family member over a different field than member `0`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FamilyFieldError {
    /// The first member over another field.
    pub member: usize,
    /// The modulus of member `0`.
    pub expected: u64,
    /// The modulus of `member`.
    pub found: u64,
}

display_error! { error FamilyFieldError {
    Self { member, expected, found } => "member {member} lives over GF({found}), member 0 over GF({expected})";
} }

/// A family of algebras over one field, indexed once for
/// [`FamilyIndex::match_member`].
///
/// A gentle member is indexed by its [`GentleKey`], any other member by its
/// canonical certificate. Members with equal index keys are duplicates, and
/// each key resolves to the first of them.
#[derive(Clone, Debug)]
pub struct FamilyIndex {
    field: Option<PrimeField>,
    family: Vec<Arc<Algebra>>,
    labelings: Vec<Option<GentleLabeling>>,
    first: FxHashMap<MemberKey, usize>,
    duplicate_of: Vec<Option<usize>>,
}

impl FamilyIndex {
    /// Indexes `family`. Errors when two members live over different fields.
    pub fn new(family: &[Arc<Algebra>]) -> Result<FamilyIndex, FamilyFieldError> {
        let field = family.first().map(|member| member.field());
        let mismatch = family
            .iter()
            .position(|member| Some(member.field()) != field);
        if let (Some(member), Some(expected)) = (mismatch, field) {
            return Err(FamilyFieldError {
                member,
                expected: expected.modulus(),
                found: family[member].field().modulus(),
            });
        }
        let labelings: Vec<_> = family.iter().map(gentle_labeling).collect();
        let mut first = FxHashMap::default();
        let duplicate_of = family
            .iter()
            .zip(&labelings)
            .enumerate()
            .map(|(position, (member, labeling))| {
                let key = member_key(member.certificate(), labeling.as_ref());
                let earliest = *first.entry(key).or_insert(position);
                (earliest != position).then_some(earliest)
            })
            .collect();
        Ok(FamilyIndex {
            field,
            family: family.to_vec(),
            labelings,
            first,
            duplicate_of,
        })
    }

    accessor_methods! {
        /// The common field of the family, `None` when it is empty.
        pub field() -> Option<PrimeField> = |this| this.field;
        /// The indexed members, in input order.
        pub family() -> &[Arc<Algebra>] = |this| &this.family;
        /// The first earlier member with the same index key, if any.
        pub duplicate_of(member: usize) -> Option<usize> = |this| this.duplicate_of[member];
    }

    /// The isomorphism from `family[member]` to its duplicate `family[other]`.
    pub(crate) fn duplicate_isomorphism(&self, member: usize, other: usize) -> AlgebraIsomorphism {
        let labels = self.labelings[member].as_ref();
        self.isomorphism_to(&self.family[member], labels, other)
    }

    /// The relabeling from `source` to `family[member]` when both are
    /// gentle, otherwise the identity between equal certificates.
    fn isomorphism_to(
        &self,
        source: &Arc<Algebra>,
        labels: Option<&GentleLabeling>,
        member: usize,
    ) -> AlgebraIsomorphism {
        let target = &self.family[member];
        match (labels, &self.labelings[member]) {
            (Some(left), Some(right)) => through_labelings(source, left, target, right),
            _ => AlgebraIsomorphism::between_equal(source, target),
        }
    }

    /// The first member isomorphic to `target` through a gentle key or an
    /// equal certificate, with the isomorphism from `target` to it.
    ///
    /// `None` means only that neither key matched. It proves nothing about
    /// isomorphism: two presentations of one algebra can differ.
    pub fn match_member(&self, target: &Arc<Algebra>) -> Option<(usize, AlgebraIsomorphism)> {
        if Some(target.field()) != self.field {
            return None;
        }
        let labeling = gentle_labeling(target);
        let key = member_key(target.certificate(), labeling.as_ref());
        let member = *self.first.get(&key)?;
        let isomorphism = self.isomorphism_to(target, labeling.as_ref(), member);
        Some((member, isomorphism))
    }
}

fn gentle_labeling(algebra: &Arc<Algebra>) -> Option<GentleLabeling> {
    Some(GentlePresentation::new(algebra).ok()?.canonical_labeling())
}

fn member_key(certificate: &Certificate, labeling: Option<&GentleLabeling>) -> MemberKey {
    match labeling {
        Some(labeling) => MemberKey::Gentle(labeling.key().clone()),
        None => MemberKey::Exact(certificate.to_canonical_json()),
    }
}

#[cfg(test)]
mod tests;

use std::fmt::Write as _;

use auslander::approx::MinimalLeftApproximation;
use auslander::basic::{AddClosureWitness, BasicDecomposition, SupportPairObstruction};
use auslander::endo::EndoAlgebra;
use auslander::field::Fp;
use auslander::hom::Morphism;
use auslander::homspace::HomSpace;
use auslander::indec::IndecomposableModule;
use auslander::linalg::DenseMat;
use auslander::module::Module;
use auslander::mutation::{FacWitness, Mutation};
use auslander::quiver::ArrowId;
use auslander::supporttau::{AlmostCompletePair, SupportTauTiltingPair};
use auslander::taurigid::TauRigidModule;

use super::common;

/// A tagged, length-prefixed text buffer, hashed into one digest.
///
/// Every value enters under a domain tag and with the byte length of its body,
/// so bytes hashed as a forward isomorphism cannot collide with the same bytes
/// hashed as a backward one, and a concatenation admits one partition only.
/// Field elements enter as decimal text through `DenseMat::entries_u64`, so no
/// byte order enters.
pub(crate) struct Payload(String);

impl Payload {
    pub(crate) fn new() -> Payload {
        Payload(String::new())
    }

    /// Appends `tag`, the byte length of `body`, and `body`.
    pub(crate) fn field(&mut self, tag: &str, body: &str) {
        write!(self.0, "{tag}({}){body}", body.len()).unwrap();
    }

    /// Appends a payload built by `fill` under `tag`.
    pub(crate) fn group(&mut self, tag: &str, fill: impl FnOnce(&mut Payload)) {
        let mut inner = Payload::new();
        fill(&mut inner);
        self.field(tag, &inner.0);
    }

    pub(crate) fn number(&mut self, tag: &str, value: u64) {
        self.field(tag, &value.to_string());
    }

    pub(crate) fn flag(&mut self, tag: &str, value: bool) {
        self.field(tag, if value { "1" } else { "0" });
    }

    /// Appends the element count and then each value as decimal text.
    pub(crate) fn numbers(&mut self, tag: &str, values: impl IntoIterator<Item = u64>) {
        let mut body = String::new();
        let mut count = 0u64;
        for value in values {
            write!(body, "{value},").unwrap();
            count += 1;
        }
        self.field(tag, &format!("{count}:{body}"));
    }

    pub(crate) fn sizes(&mut self, tag: &str, values: impl IntoIterator<Item = usize>) {
        self.numbers(tag, values.into_iter().map(|v| v as u64));
    }

    pub(crate) fn vertices(&mut self, tag: &str, values: &[u32]) {
        self.numbers(tag, values.iter().copied().map(u64::from));
    }

    /// Appends the shape and then the entries, row by row.
    ///
    /// The shape goes in first, so a zero row and a missing row differ.
    pub(crate) fn matrix(&mut self, tag: &str, m: &DenseMat) {
        self.group(tag, |p| {
            p.number("rows", m.rows() as u64);
            p.number("cols", m.cols() as u64);
            for row in m.entries_u64() {
                p.numbers("row", row);
            }
        });
    }

    /// Appends a coordinate vector, routed through a one-row `DenseMat` for
    /// the same decimal text every matrix gets.
    pub(crate) fn coords(&mut self, tag: &str, values: &[Fp]) {
        let decimals = if values.is_empty() {
            Vec::new()
        } else {
            DenseMat::from_rows(&[values.to_vec()])
                .entries_u64()
                .remove(0)
        };
        self.numbers(tag, decimals);
    }

    /// Appends a module: its dimension vector and its action on every arrow.
    pub(crate) fn module(&mut self, tag: &str, m: &Module) {
        self.group(tag, |p| {
            p.sizes("dim", m.dim_vector().iter().copied());
            for a in 0..m.algebra().quiver().num_arrows() {
                p.matrix("arrow", m.map(ArrowId(a as u32)));
            }
        });
    }

    pub(crate) fn modules<'a>(&mut self, tag: &str, ms: impl IntoIterator<Item = &'a Module>) {
        self.group(tag, |p| {
            let mut count = 0u64;
            for m in ms {
                p.module("m", m);
                count += 1;
            }
            p.number("count", count);
        });
    }

    /// Appends a morphism: both endpoint modules and its matrix at every
    /// vertex.
    ///
    /// The endpoints go in whole rather than as dimension vectors, so a
    /// morphism pins the modules it runs between even where nothing else in
    /// the payload names them. The approximation's `B` and the cokernel `Y`
    /// reach the rendering only this way.
    pub(crate) fn morphism(&mut self, tag: &str, f: &Morphism) {
        self.group(tag, |p| {
            p.module("source", f.source());
            p.module("target", f.target());
            for v in 0..f.source().algebra().quiver().num_vertices() {
                p.matrix("at", f.map_at(v));
            }
        });
    }

    pub(crate) fn morphisms<'a>(&mut self, tag: &str, fs: impl IntoIterator<Item = &'a Morphism>) {
        self.group(tag, |p| {
            let mut count = 0u64;
            for f in fs {
                p.morphism("f", f);
                count += 1;
            }
            p.number("count", count);
        });
    }

    /// Appends an endomorphism algebra: the dimensions it reports, the
    /// identity coordinates, the radical basis, and the algebra basis.
    pub(crate) fn endo(&mut self, tag: &str, e: &EndoAlgebra) {
        self.group(tag, |p| {
            p.number("dim", e.dim() as u64);
            p.number("radical_dim", e.radical_dim() as u64);
            p.number("quotient_dim", e.quotient_dim() as u64);
            p.number("factors", e.semisimple_factor_count() as u64);
            p.flag("local", e.is_local());
            p.flag("quotient_commutative", e.quotient_is_commutative());
            p.coords("one", e.one());
            p.matrix("radical", e.radical_basis());
            p.morphisms("basis", e.basis());
        });
    }

    pub(crate) fn indecomposable(&mut self, tag: &str, x: &IndecomposableModule) {
        self.group(tag, |p| {
            p.module("module", x.module());
            p.endo("endo", x.endo());
        });
    }

    pub(crate) fn decomposition(&mut self, tag: &str, d: &BasicDecomposition) {
        self.group(tag, |p| {
            p.module("module", d.module());
            p.number("count", d.summands().len() as u64);
            for x in d.summands() {
                p.indecomposable("summand", x);
            }
        });
    }

    /// Appends the tau-rigid data: the caller's summand labels, the summands,
    /// and the certified AR translates.
    pub(crate) fn rigid(&mut self, tag: &str, r: &TauRigidModule) {
        self.group(tag, |p| {
            p.number("count", r.summands().len() as u64);
            for (label, m) in r.summands() {
                p.number("label", *label as u64);
                p.module("summand", m);
            }
            p.modules("translates", r.translates());
        });
    }

    pub(crate) fn pair(&mut self, tag: &str, pair: &SupportTauTiltingPair) {
        self.group(tag, |p| {
            p.decomposition("module", pair.module());
            p.vertices("projective", pair.projective().vertices());
            p.rigid("rigid", pair.rigid());
        });
    }

    pub(crate) fn almost_complete(&mut self, tag: &str, pair: &AlmostCompletePair) {
        self.group(tag, |p| {
            p.decomposition("module", pair.module());
            p.vertices("projective", pair.projective().vertices());
            match pair.omitted_vertex() {
                Some(v) => p.number("omitted", u64::from(v)),
                None => p.field("omitted", "-"),
            }
            p.rigid("rigid", pair.rigid());
        });
    }

    /// Appends an `add` closure witness: both sides with their summands, and
    /// every match with its index and its two maps.
    pub(crate) fn add_closure(&mut self, tag: &str, w: &AddClosureWitness) {
        self.group(tag, |p| {
            p.module("module", w.module());
            p.modules("summands", w.summands());
            p.module("target", w.target());
            p.modules("target_summands", w.target_summands());
            p.number("matches", w.matches().len() as u64);
            for entry in w.matches() {
                p.number("target_index", entry.target_index() as u64);
                p.morphism("forward", entry.forward());
                p.morphism("backward", entry.backward());
            }
        });
    }

    pub(crate) fn obstruction(&mut self, tag: &str, o: &SupportPairObstruction) {
        self.group(tag, |p| match o {
            SupportPairObstruction::ProjectiveSupport { first, second } => {
                p.field("kind", "projective-support");
                p.vertices("first", first);
                p.vertices("second", second);
            }
            SupportPairObstruction::SummandCount { first, second } => {
                p.field("kind", "summand-count");
                p.number("first", *first as u64);
                p.number("second", *second as u64);
            }
            SupportPairObstruction::UnmatchedSummand { index, dim_vector } => {
                p.field("kind", "unmatched-summand");
                p.number("index", *index as u64);
                p.sizes("dim", dim_vector.iter().copied());
            }
        });
    }

    /// Appends the approximation past its map.
    ///
    /// The factorization coordinates are stored per add-generator and per
    /// basis map of `Hom(X, N_i)`, and the count of the second index has no
    /// accessor, so this rebuilds that Hom space to walk it. That is the only
    /// Hom system the rendering builds.
    pub(crate) fn approximation(&mut self, tag: &str, a: &MinimalLeftApproximation) {
        self.group(tag, |p| {
            p.number("summands", a.summands().len() as u64);
            for n in a.summands() {
                p.indecomposable("summand", n);
            }
            p.sizes("slots", a.slots().iter().copied());
            p.morphisms("inclusions", a.inclusions());
            p.morphisms("projections", a.projections());
            for (i, n) in a.summands().iter().enumerate() {
                let space = HomSpace::new(a.map().source(), n.module())
                    .expect("the approximation and its add-generator share one algebra");
                p.number("factorizations", space.dim() as u64);
                for j in 0..space.dim() {
                    p.coords("factorization", a.factorization(i, j));
                }
            }
            p.matrix("kernel", a.kernel_basis());
            p.number("radical_rows", a.kernel_basis().rows() as u64);
            for row in 0..a.kernel_basis().rows() {
                p.coords("radical", a.radical_coordinates(row));
            }
        });
    }

    pub(crate) fn fac(&mut self, tag: &str, w: &FacWitness) {
        self.group(tag, |p| {
            p.module("module", w.module());
            p.modules("summands", w.summands());
            p.module("slot_summand", w.summand());
            p.morphisms("maps", w.maps());
        });
    }

    /// Appends a pair isomorphism: the bijection, then the forward maps and
    /// the backward maps under separate tags.
    pub(crate) fn pair_iso(
        &mut self,
        tag: &str,
        bijection: &[usize],
        forward: &[Morphism],
        backward: &[Morphism],
    ) {
        self.group(tag, |p| {
            p.sizes("bijection", bijection.iter().copied());
            p.morphisms("forward", forward);
            p.morphisms("backward", backward);
        });
    }
}

/// FNV-1a over the payload `fill` builds, as 16 lowercase hex digits.
pub(crate) fn digest(fill: impl FnOnce(&mut Payload)) -> String {
    let mut payload = Payload::new();
    fill(&mut payload);
    format!("{:016x}", common::fnv1a(payload.0.as_bytes()))
}

/// The `iso` field of an edge, over the three stores of the endpoint witness.
///
/// Taking the three slices rather than the witness lets
/// `scaling_an_endpoint_isomorphism_over_f5_changes_the_rendering` feed
/// perturbed maps through the same code the rendering uses.
pub(crate) fn endpoint_digest(
    bijection: &[usize],
    forward: &[Morphism],
    backward: &[Morphism],
) -> String {
    digest(|p| p.pair_iso("endpoint", bijection, forward, backward))
}

/// The `mut` field: the mutation's own target pair and the modules the witness
/// stores around it.
pub(crate) fn mutation_digest(mutation: &Mutation) -> String {
    let witness = mutation.witness();
    digest(|p| {
        p.number("slot", mutation.slot() as u64);
        p.pair("target_pair", mutation.target());
        p.number("witness_slot", witness.slot() as u64);
        p.module("exchanged", witness.exchanged());
        p.module("source_module", witness.source_module());
        p.vertices("source_projective", witness.source_projective());
        p.module("target_module", witness.target_module());
        p.vertices("target_projective", witness.target_projective());
        match witness.replacement() {
            Some(m) => p.module("replacement", m),
            None => p.field("replacement", "-"),
        }
        p.obstruction("distinct", witness.distinct());
    })
}

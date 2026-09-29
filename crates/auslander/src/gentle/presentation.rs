use std::sync::Arc;

use rustc_hash::FxHashSet;

use crate::algebra::Algebra;
use crate::quiver::ArrowId;

use super::aag::AagFunction;
use super::canonical::{GentleKey, GentleLabeling};
use super::errors::GentleError;
use super::invariant::GentleDerivedInvariant;
use super::shape::{Shape, Sign};
use super::surface::RibbonGraph;
use super::threads::{GentleThread, Threads};
use super::validate::{check_gentle_quiver, reduced_quadratic_relations};

/// A connected algebra whose stored presentation is gentle, with its signs,
/// threads, and Avella-Alaminos-Geiss function.
///
/// Recognition reads the reduced relations of [`Algebra`]. It accepts
/// cycles, loops, parallel arrows, and oriented cycles whose consecutive
/// pairs are all relations. Finite dimension holds by construction of
/// [`Algebra`]. A presentation that fails recognition proves nothing about
/// the algebra: another presentation of the same algebra can be gentle.
///
/// Paths compose left to right, so the relation `a·b` means first `a`, then
/// `b`. Avella-Alaminos and Geiss write paths right to left: their relation
/// `γβ` is `β·γ` here, and their `σ(α_1)` for `H = α_n ⋯ α_1` is `σ` of the
/// first arrow of `H`.
#[derive(Clone, Debug)]
pub struct GentlePresentation {
    algebra: Arc<Algebra>,
    relations: Vec<(ArrowId, ArrowId)>,
    shape: Shape,
    threads: Threads,
}

impl GentlePresentation {
    /// Recognizes the reduced presentation of `algebra` as gentle.
    ///
    /// The checks run in a fixed order, and the error names the first failed
    /// one. Every reduced relation is a quadratic monomial
    /// ([`GentleError::NonMonomial`], [`GentleError::NonQuadratic`]). The
    /// quiver is nonempty and connected. Each vertex has at most two incoming
    /// and two outgoing arrows. Each arrow has at most one permitted and at
    /// most one forbidden successor, and likewise for predecessors.
    pub fn new(algebra: &Arc<Algebra>) -> Result<GentlePresentation, GentleError> {
        let forbidden = reduced_quadratic_relations(algebra)?;
        GentlePresentation::from_relations(algebra, &forbidden)
    }

    /// Recognition after the relation check, shared with the gentle-tree route.
    pub(crate) fn from_relations(
        algebra: &Arc<Algebra>,
        forbidden: &FxHashSet<(ArrowId, ArrowId)>,
    ) -> Result<GentlePresentation, GentleError> {
        check_gentle_quiver(algebra.quiver(), forbidden)?;
        let shape = Shape::solve(algebra.quiver(), forbidden);
        let relations = shape.relations();
        assert!(
            relations.len() == forbidden.len()
                && relations.iter().all(|pair| forbidden.contains(pair)),
            "the signs do not reproduce the relations; library bug"
        );
        let threads = Threads::new(&shape);
        Ok(GentlePresentation {
            algebra: algebra.clone(),
            relations,
            shape,
            threads,
        })
    }

    accessor_methods! {
        /// The recognized algebra.
        pub algebra() -> &Arc<Algebra> = |this| &this.algebra;
        /// Every relation `a·b` as the pair `(a, b)`, sorted.
        pub relations() -> &[(ArrowId, ArrowId)] = |this| &this.relations;
        /// The value `σ(arrow)`. Panics if `arrow` is not an arrow of the quiver.
        pub sigma(arrow: ArrowId) -> Sign = |this| this.shape.sigma(arrow);
        /// The value `ε(arrow)`. Panics if `arrow` is not an arrow of the quiver.
        pub epsilon(arrow: ArrowId) -> Sign = |this| this.shape.epsilon(arrow);
        /// The permitted threads, trivial ones included.
        pub permitted_threads() -> &[GentleThread] = |this| &this.threads.permitted;
        /// The forbidden threads, trivial ones included. An arrow on a full
        /// relation cycle lies on no forbidden thread.
        pub forbidden_threads() -> &[GentleThread] = |this| &this.threads.forbidden;
        /// The oriented cycles whose consecutive pairs, the closing pair
        /// included, are all relations. Each starts at its least arrow.
        pub full_relation_cycles() -> &[Vec<ArrowId>] = |this| &this.threads.cycles;
    }

    /// The Avella-Alaminos-Geiss function of this presentation.
    pub fn aag_function(&self) -> AagFunction {
        AagFunction::new(&self.threads, self.shape.vertices())
    }

    /// The genus `g = (n - M - b + 2) / 2` of the surface model.
    ///
    /// Here `n` is the vertex count, `M` the number of permitted threads, and
    /// `b` the number of pairs of [`Self::aag_function`]. The surface of
    /// Opper, Plamondon, and Schroll (arXiv:1801.09659v7, Remark 1.13 and
    /// Theorem 6.1) has `M` marked points, `n` arcs, and one boundary
    /// component per pair. Panics if the value is negative or not an
    /// integer, which is a library bug.
    pub fn genus(&self) -> usize {
        let doubled = self.shape.vertices() as i64 + 2
            - self.threads.permitted.len() as i64
            - self.aag_function().len() as i64;
        assert!(
            doubled >= 0 && doubled % 2 == 0,
            "the doubled genus {doubled} is negative or odd; library bug"
        );
        (doubled / 2) as usize
    }

    /// The complete derived invariant of this presentation.
    ///
    /// Equal values mean derived equivalent algebras, and different values
    /// mean derived inequivalent ones. See [`GentleDerivedInvariant`]. The
    /// cost is polynomial in the vertex count.
    pub fn complete_invariant(&self) -> GentleDerivedInvariant {
        GentleDerivedInvariant::new(self.aag_function(), self.genus(), &self.ribbon_graph())
    }

    /// The ribbon graph of the surface model.
    pub(super) fn ribbon_graph(&self) -> RibbonGraph {
        RibbonGraph::new(&self.shape, &self.threads.permitted)
    }

    /// The canonical labeling of this presentation.
    pub fn canonical_labeling(&self) -> GentleLabeling {
        GentleLabeling::new(&self.shape)
    }

    /// The canonical key of this presentation up to isomorphism.
    pub fn key(&self) -> GentleKey {
        self.canonical_labeling().into_key()
    }
}

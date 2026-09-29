//! Checked derived invariants of one algebra, and witnesses that two algebras
//! are not derived equivalent.
//!
//! [`DerivedInvariants`] computes every [`DerivedInvariantKind`] of one
//! algebra. An invariant that does not finish ends in a typed
//! [`InvariantStop`]: an `i128` overflow, a bar limit, or cancellation. An
//! invariant whose hypothesis fails reads [`InvariantReading::NotApplicable`].
//! [`first_difference`] names the first kind whose values
//! both finished and differ, and [`DerivedInequivalenceWitness`] stores that
//! difference for recomputation.
//!
//! Every invariant here is a necessary condition. For two connected gentle
//! algebras, Amiot, Plamondon, and Schroll prove that the AAG function and
//! the winding class together are also sufficient. Equal values never merge
//! two algebras.
//!
//! # Cartan invariants
//!
//! Let `C` be [`Algebra::cartan_matrix`] of an algebra `A` with `n` vertices.
//! A derived equivalence `D(A) → D(B)` restricts to perfect complexes, which
//! are the compact objects of `D(A)`. It induces an isometry of `K_0(per A)`
//! and `K_0(per B)` for the Euler form `⟨X, Y⟩ = Σ (-1)^i dim Hom(X, Y[i])`.
//! On the basis of indecomposable projectives `P_i = e_i A`, the Gram matrix
//! has entries `dim Hom(P_i, P_j) = dim e_j A e_i`, so it is `C^T`. Hence
//! `C_B = X C_A X^T` for some `X` in `GL_n(Z)`. Happel (1988) gives this
//! argument for algebras of finite global dimension.
//!
//! Integral congruence keeps `n` and `det C`, because `det(X)^2 = 1`. It maps
//! `C ± C^T` to `X (C ± C^T) X^T`, so the invariant factors of `C`,
//! `C + C^T`, and `C - C^T` agree. It multiplies `det(xC + C^T)` by
//! `det(X)^2 = 1`. None of this needs finite global dimension. When `det C`
//! is nonzero, the pencil divided by `det C` is the Coxeter polynomial.
//!
//! Every Cartan invariant is the same for `C` and `C^T`, so the Gram
//! convention does not matter: transposition keeps determinants and invariant
//! factors, negates `C - C^T`, and fixes the pencil, since
//! `det(xC^T + C) = det((xC + C^T)^T)`.
//!
//! The arithmetic is exact over `i128` and checked. An intermediate value
//! outside `i128` gives [`InvariantStop::Overflow`], never a wrong value.
//!
//! # Hochschild invariants
//!
//! Rickard (1991) proves that derived equivalent algebras over a field `k`
//! have isomorphic Hochschild cohomology. So `dim HH^i` agrees for every `i`,
//! and `dim HH^0`, the dimension of the center, agrees too. These dimensions
//! depend on the field. [`DerivedInequivalenceWitness`] requires both
//! algebras over the same `GF(p)`.
//!
//! [`crate::hochschild::bar_hochschild`] computes `HH^0` through `HH^d` under
//! [`InvariantLimits::bar`]. A bar cut keeps the finished degrees and records
//! the cut in [`HochschildDimensions::end`]. The center dimension reads
//! `HH^0` from the same computation.
//!
//! # Avella-Alaminos-Geiss function
//!
//! Avella-Alaminos and Geiss (2008, Theorem A) prove that derived equivalent
//! gentle algebras have equal functions. The reading is
//! [`crate::gentle::GentlePresentation::aag_function`] when
//! [`crate::gentle::GentlePresentation::new`] accepts the stored
//! presentation. Otherwise it is [`InvariantReading::NotApplicable`] with the
//! recognition error. A rejected presentation proves nothing about the
//! algebra, so that reading never separates. The kind sits after the Cartan
//! kinds and before the Hochschild kinds: recognition and the thread walk
//! cost time linear in the arrow count, far below the bar computation.
//!
//! # Winding class
//!
//! For a gentle presentation of genus at least 1, equal AAG functions do not
//! imply derived equivalence. [`crate::gentle::WindingClass`] adds the
//! winding-number data of Lekili and Polishchuk (2020, Theorem 1.2.4) and
//! Amiot, Plamondon, and Schroll (2023, Theorem 5.4): a gcd in genus 1, and
//! the parity or Arf invariant in higher genus. In genus 0 it is `Planar`.
//! A presentation that fails recognition reads
//! [`InvariantReading::NotApplicable`], as for the AAG function.
//! Derived equivalence over `GF(p)` extends to its algebraic closure, so a
//! difference over the closure also separates over `GF(p)`. The repository
//! document `docs/gentle-derived-invariant.md` records the construction.
//!
//! # References
//!
//! - D. Avella-Alaminos and C. Geiss, "Combinatorial derived invariants for
//!   gentle algebras", J. Pure Appl. Algebra 212 (2008), 228-243.
//! - C. Amiot, P.-G. Plamondon, and S. Schroll, "A complete derived invariant
//!   for gentle algebras via winding numbers and Arf invariants", Selecta
//!   Math. (N.S.) 29 (2023), no. 2, paper 30.
//! - D. Happel, "Triangulated categories in the representation theory of
//!   finite dimensional algebras", London Math. Soc. Lecture Note Ser. 119,
//!   Cambridge University Press, 1988.
//! - Y. Lekili and A. Polishchuk, "Derived equivalences of gentle algebras via
//!   Fukaya categories", Math. Ann. 376 (2020), 187-225.
//! - J. Rickard, "Derived equivalences as derived functors", J. London Math.
//!   Soc. (2) 43 (1991), 37-48.

mod integer;
mod witness;

pub use witness::{DerivedInequivalenceWitness, WitnessError};

use std::sync::Arc;

use crate::algebra::Algebra;
use crate::control::ComputationControl;
use crate::gentle::{AagFunction, GentleError, GentlePresentation, WindingClass};
use crate::hochschild::{
    BarBudgetDiagnostics, BarLimits, HochschildDegree, HochschildError, HochschildOutcome,
    bar_hochschild,
};

use integer::{Checked, Overflow};

/// One derived invariant, in the table order of the classification contract.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum DerivedInvariantKind {
    /// The number of vertices, the rank of `K_0`.
    VertexCount,
    /// `det C` in `Z`.
    CartanDeterminant,
    /// The invariant factors of `C`.
    CartanFactors,
    /// The invariant factors of `C + C^T`.
    SymmetricFactors,
    /// The invariant factors of `C - C^T`.
    SkewFactors,
    /// `det(xC + C^T)` in `Z[x]`.
    CartanPencil,
    /// The Avella-Alaminos-Geiss function of a gentle presentation.
    AagFunction,
    /// The [`WindingClass`] of a gentle presentation.
    WindingClass,
    /// `dim HH^i` for each finished degree `i <= d`.
    HochschildDimensions,
    /// `dim HH^0`, the dimension of the center.
    CenterDimension,
}

impl DerivedInvariantKind {
    /// Every kind in table order. [`first_difference`] walks this list.
    pub const ALL: [DerivedInvariantKind; 10] = [
        DerivedInvariantKind::VertexCount,
        DerivedInvariantKind::CartanDeterminant,
        DerivedInvariantKind::CartanFactors,
        DerivedInvariantKind::SymmetricFactors,
        DerivedInvariantKind::SkewFactors,
        DerivedInvariantKind::CartanPencil,
        DerivedInvariantKind::AagFunction,
        DerivedInvariantKind::WindingClass,
        DerivedInvariantKind::HochschildDimensions,
        DerivedInvariantKind::CenterDimension,
    ];
}

/// The finished value of one derived invariant.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum InvariantValue {
    /// The vertex count or the center dimension.
    Count(usize),
    /// The Cartan determinant.
    Integer(i128),
    /// Invariant factors `d_1 | ... | d_n`: nonnegative, zeros last.
    Factors(Vec<i128>),
    /// Coefficients in `Z[x]`, constant term first, with no trailing zero.
    Polynomial(Vec<i128>),
    /// The Avella-Alaminos-Geiss function.
    AagFunction(AagFunction),
    /// The winding class.
    WindingClass(WindingClass),
    /// `dim HH^0, ..., dim HH^k` for the finished degrees `0..=k`. The list
    /// is shorter than `d + 1` exactly when a bar cut stopped the computation
    /// after `HH^k`; [`HochschildDimensions::end`] records that cut.
    Dimensions(Vec<usize>),
}

impl InvariantValue {
    /// Whether the two values of one kind prove a difference.
    ///
    /// Two `Dimensions` prefixes differ only at a degree present in both. A
    /// longer prefix alone proves nothing.
    pub fn differs_from(&self, other: &InvariantValue) -> bool {
        match (self, other) {
            (InvariantValue::Dimensions(left), InvariantValue::Dimensions(right)) => {
                left.iter().zip(right).any(|(left, right)| left != right)
            }
            _ => self != other,
        }
    }
}

/// Why one derived invariant did not finish.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum InvariantStop {
    /// An intermediate integer left the `i128` range.
    Overflow,
    /// The bar computation hit a limit before the value finished.
    BarCut(Box<BarBudgetDiagnostics>),
    /// Cancellation was requested before the bar computation started.
    Cancelled,
}

/// The outcome of one derived invariant: a finished value, a typed stop, or
/// a failed hypothesis.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InvariantReading {
    /// The exact value.
    Finished(InvariantValue),
    /// The computation stopped without a value.
    Stopped(InvariantStop),
    /// The invariant is not defined for this presentation. Only
    /// [`DerivedInvariantKind::AagFunction`] and
    /// [`DerivedInvariantKind::WindingClass`] read this, with the gentle
    /// recognition error. It is not a stop: more resources give the same
    /// reading.
    NotApplicable(GentleError),
}

impl InvariantReading {
    /// Whether both readings finished and their values differ.
    pub fn separates(&self, other: &InvariantReading) -> bool {
        matches!(
            (self, other),
            (InvariantReading::Finished(left), InvariantReading::Finished(right))
                if left.differs_from(right)
        )
    }
}

/// Resource ceilings for one invariant computation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InvariantLimits {
    /// The last Hochschild degree `d`.
    pub hochschild_degree: usize,
    /// The ceilings of the bar computation.
    pub bar: BarLimits,
}

/// How the Hochschild computation ended.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HochschildEnd {
    /// Every degree through `d` finished.
    Complete,
    /// A bar cut or cancellation stopped the computation after the finished
    /// prefix.
    Stopped(InvariantStop),
}

/// `dim HH^i` for the finished degrees, with the typed end of the computation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HochschildDimensions {
    requested_degree: usize,
    dimensions: Vec<usize>,
    end: HochschildEnd,
}

impl HochschildDimensions {
    accessor_methods! {
        /// The requested last degree `d`.
        pub requested_degree() -> usize = |this| this.requested_degree;
        /// `dim HH^i` for the finished degrees `i`, starting at `0`.
        pub dimensions() -> &[usize] = |this| &this.dimensions;
        /// How the computation ended.
        pub end() -> &HochschildEnd = |this| &this.end;
    }

    fn compute(
        algebra: &Arc<Algebra>,
        limits: InvariantLimits,
        control: &ComputationControl,
    ) -> Result<HochschildDimensions, HochschildError> {
        let requested_degree = limits.hochschild_degree;
        let dimensions = |degrees: &[HochschildDegree]| degrees.iter().map(|d| d.dim()).collect();
        let (dimensions, end) = if control.is_cancelled() {
            (Vec::new(), HochschildEnd::Stopped(InvariantStop::Cancelled))
        } else {
            match bar_hochschild(algebra, requested_degree, limits.bar)? {
                HochschildOutcome::Complete(value) => {
                    (dimensions(value.degrees()), HochschildEnd::Complete)
                }
                HochschildOutcome::Cut(cut) => (
                    dimensions(cut.completed_degrees()),
                    HochschildEnd::Stopped(InvariantStop::BarCut(Box::new(
                        cut.diagnostics().clone(),
                    ))),
                ),
            }
        };
        Ok(HochschildDimensions {
            requested_degree,
            dimensions,
            end,
        })
    }

    fn dimensions_reading(&self) -> InvariantReading {
        let finished = !self.dimensions.is_empty();
        self.reading(finished.then(|| InvariantValue::Dimensions(self.dimensions.clone())))
    }

    fn center_reading(&self) -> InvariantReading {
        self.reading(self.dimensions.first().copied().map(InvariantValue::Count))
    }

    /// Reads a value from the finished prefix, or the stop when it has none.
    fn reading(&self, value: Option<InvariantValue>) -> InvariantReading {
        match (value, &self.end) {
            (Some(value), _) => InvariantReading::Finished(value),
            (None, HochschildEnd::Stopped(stop)) => InvariantReading::Stopped(stop.clone()),
            (None, HochschildEnd::Complete) => unreachable!("a complete bar result has HH^0"),
        }
    }
}

/// Every derived invariant of one algebra under one set of limits.
#[derive(Clone, Debug)]
pub struct DerivedInvariants {
    algebra: Arc<Algebra>,
    limits: InvariantLimits,
    readings: Vec<InvariantReading>,
    hochschild: HochschildDimensions,
}

impl DerivedInvariants {
    /// Computes every invariant of `algebra` in table order.
    ///
    /// Cancellation is checked once, before the bar computation starts. The
    /// Cartan invariants always run. Errors only on an internal bar defect.
    pub fn compute(
        algebra: &Arc<Algebra>,
        limits: InvariantLimits,
        control: &ComputationControl,
    ) -> Result<DerivedInvariants, HochschildError> {
        let mut evaluator = Evaluator::new(algebra, limits, control);
        let readings = DerivedInvariantKind::ALL
            .iter()
            .map(|&kind| evaluator.reading(kind))
            .collect::<Result<Vec<_>, _>>()?;
        let hochschild = evaluator.hochschild()?.clone();
        Ok(DerivedInvariants {
            algebra: algebra.clone(),
            limits,
            readings,
            hochschild,
        })
    }

    accessor_methods! {
        /// The algebra these invariants describe.
        pub algebra() -> &Arc<Algebra> = |this| &this.algebra;
        /// The limits of the computation.
        pub limits() -> InvariantLimits = |this| this.limits;
        /// The Hochschild dimensions and how their computation ended.
        pub hochschild() -> &HochschildDimensions = |this| &this.hochschild;
        /// The reading of one invariant.
        pub reading(kind: DerivedInvariantKind) -> &InvariantReading = |this| &this.readings[kind as usize];
    }
}

/// Computes one derived invariant of `algebra` from scratch.
///
/// The bar computation runs only for [`DerivedInvariantKind::HochschildDimensions`]
/// and [`DerivedInvariantKind::CenterDimension`], with the same limits as
/// [`DerivedInvariants::compute`].
pub fn derived_invariant(
    algebra: &Arc<Algebra>,
    kind: DerivedInvariantKind,
    limits: InvariantLimits,
    control: &ComputationControl,
) -> Result<InvariantReading, HochschildError> {
    Evaluator::new(algebra, limits, control).reading(kind)
}

/// The first kind in table order whose readings both finished and differ.
///
/// `None` means that every pair of finished readings agrees. A reading that
/// stopped or is not applicable never separates. The comparison does not check the two fields;
/// [`DerivedInequivalenceWitness::new`] does.
pub fn first_difference(
    left: &DerivedInvariants,
    right: &DerivedInvariants,
) -> Option<DerivedInvariantKind> {
    DerivedInvariantKind::ALL
        .into_iter()
        .find(|&kind| left.reading(kind).separates(right.reading(kind)))
}

/// Computes readings on demand and runs the bar computation at most once.
struct Evaluator<'a> {
    algebra: &'a Arc<Algebra>,
    limits: InvariantLimits,
    control: &'a ComputationControl,
    cartan: Checked<Vec<Vec<i128>>>,
    hochschild: Option<HochschildDimensions>,
}

impl<'a> Evaluator<'a> {
    fn new(
        algebra: &'a Arc<Algebra>,
        limits: InvariantLimits,
        control: &'a ComputationControl,
    ) -> Evaluator<'a> {
        let cartan = algebra
            .cartan_matrix()
            .into_iter()
            .map(|row| {
                row.into_iter()
                    .map(|e| i128::try_from(e).map_err(|_| Overflow))
                    .collect()
            })
            .collect();
        Evaluator {
            algebra,
            limits,
            control,
            cartan,
            hochschild: None,
        }
    }

    fn hochschild(&mut self) -> Result<&HochschildDimensions, HochschildError> {
        let value = match self.hochschild.take() {
            Some(value) => value,
            None => HochschildDimensions::compute(self.algebra, self.limits, self.control)?,
        };
        Ok(self.hochschild.insert(value))
    }

    fn integer(
        &self,
        value: impl FnOnce(&[Vec<i128>]) -> Checked<InvariantValue>,
    ) -> InvariantReading {
        match self
            .cartan
            .as_deref()
            .map_err(|&error| error)
            .and_then(value)
        {
            Ok(value) => InvariantReading::Finished(value),
            Err(Overflow) => InvariantReading::Stopped(InvariantStop::Overflow),
        }
    }

    fn reading(&mut self, kind: DerivedInvariantKind) -> Result<InvariantReading, HochschildError> {
        use DerivedInvariantKind as Kind;
        Ok(match kind {
            Kind::VertexCount => InvariantReading::Finished(InvariantValue::Count(
                self.algebra.quiver().num_vertices() as usize,
            )),
            Kind::CartanDeterminant
            | Kind::CartanFactors
            | Kind::SymmetricFactors
            | Kind::SkewFactors
            | Kind::CartanPencil => self.integer(|cartan| cartan_value(kind, cartan)),
            Kind::AagFunction => gentle_reading(self.algebra, |gentle| {
                InvariantValue::AagFunction(gentle.aag_function())
            }),
            Kind::WindingClass => gentle_reading(self.algebra, |gentle| {
                InvariantValue::WindingClass(gentle.complete_invariant().winding_class())
            }),
            Kind::HochschildDimensions => self.hochschild()?.dimensions_reading(),
            Kind::CenterDimension => self.hochschild()?.center_reading(),
        })
    }
}

/// The value of one Cartan kind, computed from `C`.
fn cartan_value(kind: DerivedInvariantKind, cartan: &[Vec<i128>]) -> Checked<InvariantValue> {
    use DerivedInvariantKind as Kind;
    match kind {
        Kind::CartanDeterminant => integer::determinant(cartan).map(InvariantValue::Integer),
        Kind::CartanFactors => integer::invariant_factors(cartan).map(InvariantValue::Factors),
        Kind::SymmetricFactors => transpose_factors(cartan, 1),
        Kind::SkewFactors => transpose_factors(cartan, -1),
        Kind::CartanPencil => integer::pencil(cartan).map(InvariantValue::Polynomial),
        Kind::VertexCount
        | Kind::AagFunction
        | Kind::WindingClass
        | Kind::HochschildDimensions
        | Kind::CenterDimension => {
            unreachable!("{kind:?} is not read from the Cartan matrix")
        }
    }
}

/// One value of the stored presentation when it is gentle.
fn gentle_reading(
    algebra: &Arc<Algebra>,
    value: impl FnOnce(&GentlePresentation) -> InvariantValue,
) -> InvariantReading {
    match GentlePresentation::new(algebra) {
        Ok(presentation) => InvariantReading::Finished(value(&presentation)),
        Err(error) => InvariantReading::NotApplicable(error),
    }
}

/// The invariant factors of `C + sign · C^T`.
fn transpose_factors(matrix: &[Vec<i128>], sign: i128) -> Checked<InvariantValue> {
    integer::invariant_factors(&integer::with_transpose(matrix, 1, sign)?)
        .map(InvariantValue::Factors)
}

#[cfg(test)]
mod tests;

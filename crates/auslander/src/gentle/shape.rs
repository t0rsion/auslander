use rustc_hash::FxHashSet;

use crate::monomial::MonomialIdeal;
use crate::quiver::{ArrowId, Quiver};

/// One value of the sign functions `σ` and `ε` of Butler and Ringel.
///
/// See M. C. R. Butler and C. M. Ringel, *Comm. Algebra* 15 (1987), section 3.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Sign {
    /// The value `+1`.
    Plus,
    /// The value `-1`.
    Minus,
}

impl Sign {
    const BOTH: [Sign; 2] = [Sign::Plus, Sign::Minus];

    /// The opposite sign.
    pub fn negated(self) -> Sign {
        match self {
            Sign::Plus => Sign::Minus,
            Sign::Minus => Sign::Plus,
        }
    }

    fn index(self) -> usize {
        self as usize
    }
}

/// Which consecutive arrow pairs a thread follows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    Permitted,
    Forbidden,
}

impl Kind {
    /// The `ε` value of an arrow into a vertex whose continuation of this kind
    /// leaves by the outgoing arrow with `σ` value `sign`. The map is an
    /// involution, so it also sends `ε` to `σ`.
    pub(crate) fn partner(self, sign: Sign) -> Sign {
        match self {
            Kind::Permitted => sign.negated(),
            Kind::Forbidden => sign,
        }
    }
}

/// A gentle bound quiver stored as signed slots.
///
/// Every vertex has two outgoing slots, one per `σ` value, and two incoming
/// slots, one per `ε` value. An arrow fills one outgoing slot at its source
/// and one incoming slot at its target. The consecutive pair `b·c` is a
/// relation exactly when `σ(c) = ε(b)`.
///
/// Rule (3) of Butler and Ringel only forces `σ(c) = -ε(b)` for a permitted
/// pair. For a relation `b·c` at a vertex with one incoming and one outgoing
/// arrow it leaves `σ(c)` free. Step 1(b) of the Avella-Alaminos and Geiss
/// algorithm then needs `σ(c) = ε(b)`, which rules (1) and (2) force at every
/// other vertex. This type imposes it at every relation.
#[derive(Clone, Debug)]
pub(crate) struct Shape {
    arrows: Vec<(u32, u32)>,
    sigma: Vec<Sign>,
    epsilon: Vec<Sign>,
    outgoing: Vec<[Option<ArrowId>; 2]>,
    incoming: Vec<[Option<ArrowId>; 2]>,
}

impl Shape {
    /// The shape with vertices `0..vertices` and no arrows.
    pub(crate) fn empty(vertices: u32) -> Shape {
        Shape {
            arrows: Vec::new(),
            sigma: Vec::new(),
            epsilon: Vec::new(),
            outgoing: vec![[None; 2]; vertices as usize],
            incoming: vec![[None; 2]; vertices as usize],
        }
    }

    /// Solves the sign functions of a checked gentle quiver.
    ///
    /// The caller has checked the degree and continuation conditions. Under
    /// them each vertex has one solution up to a common flip of its signs.
    pub(crate) fn solve(quiver: &Quiver, forbidden: &FxHashSet<(ArrowId, ArrowId)>) -> Shape {
        let arrows = quiver.num_arrows();
        let mut sigma = vec![Sign::Plus; arrows];
        let mut epsilon = vec![Sign::Plus; arrows];
        for vertex in 0..quiver.num_vertices() {
            let outgoing = quiver.arrows_from(vertex);
            for (&arrow, sign) in outgoing.iter().zip(Sign::BOTH) {
                sigma[arrow.index()] = sign;
            }
            let incoming = quiver.arrows_to(vertex);
            for (position, &arrow) in incoming.iter().enumerate() {
                epsilon[arrow.index()] = match outgoing.first() {
                    Some(&next) if forbidden.contains(&(arrow, next)) => sigma[next.index()],
                    Some(&next) => sigma[next.index()].negated(),
                    None => Sign::BOTH[position],
                };
            }
        }
        let mut shape = Shape::empty(quiver.num_vertices());
        for (index, &(source, target)) in quiver.arrows().iter().enumerate() {
            shape.push(source, sigma[index], target, epsilon[index]);
        }
        shape
    }

    /// Appends an arrow into two empty slots.
    ///
    /// Panics when a slot is already filled, which is a library bug.
    pub(crate) fn push(&mut self, source: u32, sigma: Sign, target: u32, epsilon: Sign) {
        let arrow = ArrowId(self.arrows.len() as u32);
        let out = &mut self.outgoing[source as usize][sigma.index()];
        assert!(
            out.is_none(),
            "two arrows share an outgoing slot; library bug"
        );
        *out = Some(arrow);
        let into = &mut self.incoming[target as usize][epsilon.index()];
        assert!(
            into.is_none(),
            "two arrows share an incoming slot; library bug"
        );
        *into = Some(arrow);
        self.arrows.push((source, target));
        self.sigma.push(sigma);
        self.epsilon.push(epsilon);
    }

    /// Adds an isolated vertex and returns it.
    pub(crate) fn push_vertex(&mut self) -> u32 {
        self.outgoing.push([None; 2]);
        self.incoming.push([None; 2]);
        self.outgoing.len() as u32 - 1
    }

    accessor_methods! {
        pub(crate) vertices() -> u32 = |this| this.outgoing.len() as u32;
        pub(crate) arrows() -> &[(u32, u32)] = |this| &this.arrows;
        pub(crate) sigma(arrow: ArrowId) -> Sign = |this| this.sigma[arrow.index()];
        pub(crate) epsilon(arrow: ArrowId) -> Sign = |this| this.epsilon[arrow.index()];
        pub(crate) outgoing(vertex: u32, sign: Sign) -> Option<ArrowId> = |this| this.outgoing[vertex as usize][sign.index()];
        pub(crate) incoming(vertex: u32, sign: Sign) -> Option<ArrowId> = |this| this.incoming[vertex as usize][sign.index()];
        pub(crate) source(arrow: ArrowId) -> u32 = |this| this.arrows[arrow.index()].0;
        pub(crate) target(arrow: ArrowId) -> u32 = |this| this.arrows[arrow.index()].1;
    }

    /// The arrow `c` with `arrow·c` a continuation of kind `kind`.
    pub(crate) fn successor(&self, kind: Kind, arrow: ArrowId) -> Option<ArrowId> {
        self.outgoing(self.target(arrow), kind.partner(self.epsilon(arrow)))
    }

    /// The arrow `b` with `b·arrow` a continuation of kind `kind`.
    pub(crate) fn predecessor(&self, kind: Kind, arrow: ArrowId) -> Option<ArrowId> {
        self.incoming(self.source(arrow), kind.partner(self.sigma(arrow)))
    }

    /// The other arrow with the same source.
    pub(crate) fn outgoing_sibling(&self, arrow: ArrowId) -> Option<ArrowId> {
        self.outgoing(self.source(arrow), self.sigma(arrow).negated())
    }

    /// The other arrow with the same target.
    pub(crate) fn incoming_sibling(&self, arrow: ArrowId) -> Option<ArrowId> {
        self.incoming(self.target(arrow), self.epsilon(arrow).negated())
    }

    /// Every relation `b·c` as the pair `(b, c)`, sorted.
    pub(crate) fn relations(&self) -> Vec<(ArrowId, ArrowId)> {
        (0..self.arrows.len() as u32)
            .map(ArrowId)
            .filter_map(|arrow| {
                self.successor(Kind::Forbidden, arrow)
                    .map(|next| (arrow, next))
            })
            .collect()
    }

    /// The monomial ideal with this quiver and these relations.
    pub(crate) fn monomial_ideal(&self) -> MonomialIdeal {
        monomial_ideal(self.vertices(), &self.arrows, &self.relations())
    }
}

/// The monomial ideal with one quadratic forbidden word per relation.
pub(crate) fn monomial_ideal(
    vertices: u32,
    arrows: &[(u32, u32)],
    relations: &[(ArrowId, ArrowId)],
) -> MonomialIdeal {
    let quiver = Quiver::new(vertices, arrows).expect("slot endpoints are vertices");
    let words = relations.iter().map(|&(b, c)| vec![b, c]).collect();
    MonomialIdeal::new(quiver, words).expect("a relation joins an arrow to one at its target")
}

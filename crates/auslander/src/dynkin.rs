//! Dynkin and Euclidean diagrams of a quiver's underlying graph, their root
//! systems, and the indecomposables of a hereditary path algebra of Dynkin
//! type.
//!
//! Recognition matches the underlying graph against the shape of each diagram
//! (Bourbaki, *Groupes et algèbres de Lie*, planches I-IX, and the affine
//! tables of Kac, *Infinite dimensional Lie algebras*, ch. 4). Every decision
//! and every root is an integer computation.
//!
//! Only simply laced diagrams occur: the underlying graph of a quiver has
//! unoriented edges of one length, and a multiple edge is recorded as a
//! multiplicity in the generalized Cartan matrix.

use std::collections::VecDeque;
use std::fmt;
use std::sync::Arc;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::algebra::Algebra;
use crate::decompose::{Certificate, decompose};
use crate::field::{Fp, PrimeField};
use crate::linalg::DenseMat;
use crate::module::Module;
use crate::quiver::Quiver;

/// A simply laced Dynkin diagram.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DynkinType {
    /// The path on `n` vertices, `n ≥ 1`.
    A(usize),
    /// The tree with one vertex of degree three whose three arms have lengths
    /// `1`, `1` and `n - 3`, so `n` vertices in all, `n ≥ 4`.
    D(usize),
    /// The tree with one vertex of degree three whose arms have lengths
    /// `1, 2, 2`.
    E6,
    /// The tree with one vertex of degree three whose arms have lengths
    /// `1, 2, 3`.
    E7,
    /// The tree with one vertex of degree three whose arms have lengths
    /// `1, 2, 4`.
    E8,
}

impl DynkinType {
    /// The number of vertices of the diagram, or `None` when the parameter
    /// names no Dynkin diagram (`A(n)` needs `n ≥ 1`, `D(n)` needs `n ≥ 4`).
    pub fn num_vertices(self) -> Option<usize> {
        match self {
            Self::A(n) => (n >= 1).then_some(n),
            Self::D(n) => (n >= 4).then_some(n),
            Self::E6 => Some(6),
            Self::E7 => Some(7),
            Self::E8 => Some(8),
        }
    }

    /// The number of positive roots, equal by Gabriel's theorem to the number
    /// of isomorphism classes of indecomposable representations of any quiver
    /// with this underlying graph, or `None` when the parameter names no
    /// Dynkin diagram or the count does not fit in a `usize`.
    pub fn indecomposable_count(self) -> Option<usize> {
        match self {
            // Halve the even factor before multiplying: n(n+1)/2 is often
            // representable when n(n+1) is not.
            Self::A(n) => (n >= 1)
                .then(|| {
                    if n % 2 == 0 {
                        (n / 2).checked_mul(n.checked_add(1)?)
                    } else {
                        n.checked_mul(n / 2 + 1)
                    }
                })
                .flatten(),
            Self::D(n) => (n >= 4).then(|| n.checked_mul(n - 1)).flatten(),
            Self::E6 => Some(36),
            Self::E7 => Some(63),
            Self::E8 => Some(120),
        }
    }
}

impl fmt::Display for DynkinType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::A(n) => write!(f, "A_{n}"),
            Self::D(n) => write!(f, "D_{n}"),
            Self::E6 => f.write_str("E_6"),
            Self::E7 => f.write_str("E_7"),
            Self::E8 => f.write_str("E_8"),
        }
    }
}

/// A simply laced Euclidean (affine) diagram. The subscript is the rank of the
/// finite diagram it extends, so the diagram itself has one more vertex.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum EuclideanType {
    /// Two vertices joined by a double edge when `n = 1`, the cycle on
    /// `n + 1` vertices when `n ≥ 2`.
    A(usize),
    /// The tree on `n + 1` vertices with two leaves at each end of a path of
    /// `n - 3` vertices, `n ≥ 4`; for `n = 4` the path is a single vertex of
    /// degree four.
    D(usize),
    /// The tree with one vertex of degree three whose arms have lengths
    /// `2, 2, 2`.
    E6,
    /// The tree with one vertex of degree three whose arms have lengths
    /// `1, 3, 3`.
    E7,
    /// The tree with one vertex of degree three whose arms have lengths
    /// `1, 2, 5`.
    E8,
}

impl EuclideanType {
    /// The number of vertices of the diagram, or `None` when the parameter
    /// names no Euclidean diagram (`A(n)` needs `n ≥ 1`, `D(n)` needs
    /// `n ≥ 4`) or the count does not fit in a `usize`.
    pub fn num_vertices(self) -> Option<usize> {
        match self {
            Self::A(n) => (n >= 1).then(|| n.checked_add(1)).flatten(),
            Self::D(n) => (n >= 4).then(|| n.checked_add(1)).flatten(),
            Self::E6 => Some(7),
            Self::E7 => Some(8),
            Self::E8 => Some(9),
        }
    }
}

impl fmt::Display for EuclideanType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::A(n) => write!(f, "affine A_{n}"),
            Self::D(n) => write!(f, "affine D_{n}"),
            Self::E6 => f.write_str("affine E_6"),
            Self::E7 => f.write_str("affine E_7"),
            Self::E8 => f.write_str("affine E_8"),
        }
    }
}

/// The Dynkin type of the quiver's underlying graph, or `None` when that graph
/// is not a Dynkin diagram.
///
/// The type depends only on the underlying graph, never on the orientation,
/// and never on an ideal of relations, so this takes a [`Quiver`]. Pass
/// `algebra.quiver()` to classify an algebra's quiver.
///
/// ```
/// use auslander::dynkin::{DynkinType, dynkin_type};
/// use auslander::quiver::Quiver;
/// let q = Quiver::new(4, &[(0, 2), (1, 2), (3, 2)]).unwrap();
/// assert_eq!(dynkin_type(&q), Some(DynkinType::D(4)));
/// ```
pub fn dynkin_type(quiver: &Quiver) -> Option<DynkinType> {
    let graph = tree(quiver)?;
    match graph.shape()? {
        Shape::Path(n) => Some(DynkinType::A(n)),
        Shape::Star(arms) => match arms[..] {
            [1, 1, r] => Some(DynkinType::D(r + 3)),
            [1, 2, 2] => Some(DynkinType::E6),
            [1, 2, 3] => Some(DynkinType::E7),
            [1, 2, 4] => Some(DynkinType::E8),
            _ => None,
        },
        Shape::DoubleFork { .. } => None,
    }
}

/// The Euclidean type of the quiver's underlying graph, or `None` when that
/// graph is not a Euclidean diagram.
///
/// ```
/// use auslander::dynkin::{EuclideanType, euclidean_type};
/// use auslander::quiver::Quiver;
/// let kronecker = Quiver::new(2, &[(0, 1), (0, 1)]).unwrap();
/// assert_eq!(euclidean_type(&kronecker), Some(EuclideanType::A(1)));
/// ```
pub fn euclidean_type(quiver: &Quiver) -> Option<EuclideanType> {
    let graph = Underlying::of(quiver);
    if graph.loops > 0 || graph.num_vertices == 0 || !graph.is_connected() {
        return None;
    }
    // The only Euclidean diagram with a multiple edge is affine A_1.
    if graph.max_multiplicity() > 1 {
        return (graph.num_vertices == 2
            && graph.multiplicity.len() == 1
            && graph.num_edges() == 2)
            .then_some(EuclideanType::A(1));
    }
    let n = graph.num_vertices;
    if graph.num_edges() == n {
        let simple = graph.simple();
        return (n >= 3 && (0..n).all(|v| simple.degree(v) == 2))
            .then_some(EuclideanType::A(n - 1));
    }
    let graph = tree(quiver)?;
    match graph.shape()? {
        Shape::Path(_) => None,
        Shape::Star(arms) => match arms[..] {
            [1, 1, 1, 1] => Some(EuclideanType::D(4)),
            [2, 2, 2] => Some(EuclideanType::E6),
            [1, 3, 3] => Some(EuclideanType::E7),
            [1, 2, 5] => Some(EuclideanType::E8),
            _ => None,
        },
        Shape::DoubleFork { separation } => Some(EuclideanType::D(separation + 4)),
    }
}

/// The generalized Cartan matrix of the quiver's underlying graph: `2` on the
/// diagonal and minus the number of edges joining `i` and `j` off it.
///
/// `None` exactly when the quiver has a loop, since a vertex carrying a loop
/// contributes no row with diagonal entry `2` (Kac, *Infinite dimensional Lie
/// algebras*, §1.1).
pub fn generalized_cartan_matrix(quiver: &Quiver) -> Option<Vec<Vec<i64>>> {
    let graph = Underlying::of(quiver);
    if graph.loops > 0 {
        return None;
    }
    let n = graph.num_vertices;
    let mut cartan = vec![vec![0i64; n]; n];
    for (i, row) in cartan.iter_mut().enumerate() {
        row[i] = 2;
    }
    for (&(u, v), &m) in &graph.multiplicity {
        cartan[u][v] = -(m as i64);
        cartan[v][u] = -(m as i64);
    }
    Some(cartan)
}

/// The positive roots of the quiver's underlying graph, in the quiver's own
/// vertex indexing, ordered by height and then lexicographically; `None` when
/// the graph is not a Dynkin diagram.
///
/// The roots are the closure of the simple roots under the simple reflections
/// `s_i(x) = x - (C x)_i e_i`, keeping only vectors with nonnegative entries.
/// Every positive root that is not simple admits a reflection lowering its
/// height while staying positive, so the closure reaches all of them, and it
/// is finite exactly because the diagram is Dynkin.
pub fn positive_roots(quiver: &Quiver) -> Option<Vec<Vec<usize>>> {
    dynkin_type(quiver)?;
    let cartan = generalized_cartan_matrix(quiver)?;
    let n = cartan.len();
    let mut seen: FxHashSet<Vec<i64>> = FxHashSet::default();
    let mut queue: VecDeque<Vec<i64>> = VecDeque::new();
    for i in 0..n {
        let mut simple = vec![0i64; n];
        simple[i] = 1;
        seen.insert(simple.clone());
        queue.push_back(simple);
    }
    let mut roots: Vec<Vec<i64>> = Vec::new();
    while let Some(root) = queue.pop_front() {
        for (i, row) in cartan.iter().enumerate() {
            let pairing: i64 = row.iter().zip(&root).map(|(a, x)| a * x).sum();
            if pairing == 0 {
                continue;
            }
            let mut next = root.clone();
            next[i] -= pairing;
            if next.iter().all(|&x| x >= 0) && seen.insert(next.clone()) {
                queue.push_back(next);
            }
        }
        roots.push(root);
    }
    roots.sort_by(|a, b| {
        let height = |r: &Vec<i64>| r.iter().sum::<i64>();
        height(a).cmp(&height(b)).then_with(|| a.cmp(b))
    });
    Some(
        roots
            .into_iter()
            .map(|r| r.into_iter().map(|x| x as usize).collect())
            .collect(),
    )
}

/// A quiver whose underlying graph is the named Dynkin diagram, oriented away
/// from the branch vertex; `None` when the parameter names no diagram or the
/// vertex count does not fit the `u32` vertex indexing of [`Quiver`].
pub fn dynkin_quiver(dynkin: DynkinType) -> Option<Quiver> {
    u32::try_from(dynkin.num_vertices()?).ok()?;
    Some(match dynkin {
        DynkinType::A(n) => star(&[n - 1]),
        DynkinType::D(n) => star(&[1, 1, n - 3]),
        DynkinType::E6 => star(&[1, 2, 2]),
        DynkinType::E7 => star(&[1, 2, 3]),
        DynkinType::E8 => star(&[1, 2, 4]),
    })
}

/// A quiver whose underlying graph is the named Euclidean diagram; `None` when
/// the parameter names no diagram or the vertex count does not fit the `u32`
/// vertex indexing of [`Quiver`]. The cyclic cases are oriented acyclically,
/// so their path algebras are finite dimensional.
pub fn euclidean_quiver(euclidean: EuclideanType) -> Option<Quiver> {
    let vertices = u32::try_from(euclidean.num_vertices()?).ok()?;
    Some(match euclidean {
        EuclideanType::A(1) => Quiver::new(2, &[(0, 1), (0, 1)]).expect("endpoints in range"),
        EuclideanType::A(_) => {
            let n = vertices - 1;
            let mut arrows: Vec<(u32, u32)> = (0..n).map(|i| (i, i + 1)).collect();
            arrows.push((0, n));
            Quiver::new(vertices, &arrows).expect("endpoints in range")
        }
        EuclideanType::D(n) => double_fork(n - 4),
        EuclideanType::E6 => star(&[2, 2, 2]),
        EuclideanType::E7 => star(&[1, 3, 3]),
        EuclideanType::E8 => star(&[1, 2, 5]),
    })
}

/// Rejected input for [`dynkin_indecomposables`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DynkinError {
    /// The algebra has relations, so it is a proper quotient of `kQ`.
    /// Gabriel's theorem lists the indecomposables of `kQ` itself.
    NonzeroIdeal {
        /// Number of Groebner relations the algebra carries.
        relations: usize,
    },
    /// The underlying graph of the quiver is no Dynkin diagram, so `kQ` is not
    /// representation finite by Gabriel's theorem. `euclidean` reports the
    /// Euclidean type when the graph has one.
    NotDynkin {
        /// The Euclidean type of the underlying graph, when it has one.
        euclidean: Option<EuclideanType>,
    },
}

impl fmt::Display for DynkinError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NonzeroIdeal { relations } => write!(
                f,
                "the algebra has {relations} relations; \
                 Gabriel's theorem needs the full path algebra"
            ),
            Self::NotDynkin { euclidean: None } => {
                f.write_str("the underlying graph is not a Dynkin diagram")
            }
            Self::NotDynkin { euclidean: Some(t) } => {
                write!(f, "the underlying graph is {t}, not a Dynkin diagram")
            }
        }
    }
}

impl std::error::Error for DynkinError {}

/// Every indecomposable right module of a hereditary path algebra `kQ` with
/// `Q` of Dynkin type, one per positive root of the underlying graph
/// (Gabriel), ordered as [`positive_roots`] orders the roots.
///
/// Each module is built from a simple module by a chain of Bernstein-Gelfand-
/// Ponomarev reflection functors: an admissible sequence of sinks is applied to
/// the root until it becomes simple, and the corresponding functors `S_i^-` are
/// applied back. Nothing is enumerated over the field.
///
/// Every module comes with the certificate [`decompose`] produced for it. The
/// construction proves indecomposability, so the certificate is an independent
/// check rather than the source of the claim.
///
/// # Errors
/// [`DynkinError::NonzeroIdeal`] when the algebra is a proper quotient of
/// `kQ`, [`DynkinError::NotDynkin`] when the underlying graph is no Dynkin
/// diagram.
pub fn dynkin_indecomposables(
    algebra: &Arc<Algebra>,
) -> Result<Vec<(Module, Certificate)>, DynkinError> {
    let relations = algebra.relations().len();
    if relations > 0 {
        return Err(DynkinError::NonzeroIdeal { relations });
    }
    let field = algebra.field();
    let quiver = algebra.quiver();
    if dynkin_type(quiver).is_none() {
        return Err(DynkinError::NotDynkin {
            euclidean: euclidean_type(quiver),
        });
    }
    let roots = positive_roots(quiver).expect("a Dynkin graph has a finite root system");
    let sinks = admissible_sink_sequence(quiver).expect("a Dynkin quiver is acyclic");
    let adjacency = tree(quiver).expect("a Dynkin graph is a tree").neighbours;
    let mut out = Vec::with_capacity(roots.len());
    for root in &roots {
        let rep = reflect_up_from_simple(quiver, &sinks, &adjacency, root, roots.len(), field);
        assert_eq!(
            &rep.dims, root,
            "reflection chain landed on the wrong dimension vector; library bug"
        );
        let m = Module::new(algebra.clone(), rep.dims, rep.maps)
            .expect("a representation of kQ with no relations is a module");
        let d = decompose(&m);
        assert_eq!(
            d.summands().len(),
            1,
            "a module built from a positive root split into {} summands; library bug",
            d.summands().len()
        );
        out.push((m, d.certificates()[0]));
    }
    Ok(out)
}

/// A representation of a quiver with the arrow indexing of some orientation:
/// `maps[a]` has shape `dims[source(a)] × dims[target(a)]` and acts on row
/// vectors.
struct Rep {
    dims: Vec<usize>,
    maps: Vec<DenseMat>,
}

/// The indecomposable representation of `quiver` with dimension vector `root`.
///
/// `sinks` is an admissible sequence of sinks and `roots` the number of
/// positive roots, both supplied by the caller. The state of the reflection
/// chain is the pair (position in `sinks`, current root), so after
/// `sinks.len() * roots` steps without reaching a simple root the chain would
/// have repeated a state and could never reach one. The Bernstein-Gelfand-
/// Ponomarev theorem says the chain does reach one, so exceeding that count is
/// a library bug.
fn reflect_up_from_simple(
    quiver: &Quiver,
    sinks: &[u32],
    adjacency: &[Vec<usize>],
    root: &[usize],
    roots: usize,
    field: PrimeField,
) -> Rep {
    let mut endpoints: Vec<(u32, u32)> = quiver.arrows().to_vec();
    let mut dim: Vec<i64> = root.iter().map(|&d| d as i64).collect();
    let mut chain: Vec<(u32, Vec<(u32, u32)>)> = Vec::new();
    let mut simple_at = None;
    for step in 0..=sinks.len() * roots {
        let i = sinks[step % sinks.len()];
        if is_simple_root(&dim, i) {
            simple_at = Some(i);
            break;
        }
        reflect_dim(&mut dim, adjacency, i);
        assert!(
            dim.iter().all(|&d| d >= 0),
            "a reflection left the positive cone; library bug"
        );
        reflect_endpoints(&mut endpoints, i);
        chain.push((i, endpoints.clone()));
    }
    let vertex =
        simple_at.expect("reflections of a positive root reach a simple root within the bound");
    let mut rep = simple_rep(&endpoints, &dim, vertex);
    while let Some((i, source_endpoints)) = chain.pop() {
        rep = reflect_minus(&source_endpoints, i, &rep, field);
    }
    rep
}

fn is_simple_root(dim: &[i64], i: u32) -> bool {
    dim[i as usize] == 1
        && dim
            .iter()
            .enumerate()
            .all(|(v, &d)| v == i as usize || d == 0)
}

/// `s_i` on a dimension vector: `d_i ↦ -d_i + Σ_{j ~ i} d_j`, the reflection in
/// the simple root `e_i` for a simply laced diagram.
fn reflect_dim(dim: &mut [i64], adjacency: &[Vec<usize>], i: u32) {
    let neighbours: i64 = adjacency[i as usize].iter().map(|&j| dim[j]).sum();
    dim[i as usize] = neighbours - dim[i as usize];
}

/// Reverses every arrow incident to `i`; arrow ids are unchanged.
fn reflect_endpoints(endpoints: &mut [(u32, u32)], i: u32) {
    for e in endpoints.iter_mut() {
        if e.0 == i || e.1 == i {
            *e = (e.1, e.0);
        }
    }
}

fn simple_rep(endpoints: &[(u32, u32)], dim: &[i64], vertex: u32) -> Rep {
    let dims: Vec<usize> = (0..dim.len())
        .map(|v| usize::from(v == vertex as usize))
        .collect();
    let maps = endpoints
        .iter()
        .map(|&(s, t)| DenseMat::zero(dims[s as usize], dims[t as usize]))
        .collect();
    Rep { dims, maps }
}

/// The reflection functor `S_i^-` applied to `rep`, a representation of
/// `source_endpoints` in which `i` is a source; the result is a representation
/// of the quiver obtained by reversing every arrow at `i`, in which `i` is a
/// sink.
///
/// With `φ: N_i → ⊕_{a: i→u} N_u` the map assembled from the outgoing arrows,
/// the new space at `i` is `coker φ` and the new map along `a: u → i` is the
/// inclusion of the `a`-block followed by the quotient projection
/// (Bernstein-Gelfand-Ponomarev, *Coxeter functors and Gabriel's theorem*).
///
/// `φ` must be injective, which holds for an indecomposable `rep` not
/// isomorphic to the simple module at `i`.
fn reflect_minus(source_endpoints: &[(u32, u32)], i: u32, rep: &Rep, field: PrimeField) -> Rep {
    let outgoing: Vec<usize> = (0..source_endpoints.len())
        .filter(|&a| source_endpoints[a].0 == i)
        .collect();
    let mut offsets = Vec::with_capacity(outgoing.len());
    let mut width = 0usize;
    for &a in &outgoing {
        offsets.push(width);
        width += rep.dims[source_endpoints[a].1 as usize];
    }
    let mut phi = DenseMat::zero(rep.dims[i as usize], width);
    for (k, &a) in outgoing.iter().enumerate() {
        let block = &rep.maps[a];
        for r in 0..block.rows() {
            for c in 0..block.cols() {
                phi.set(r, offsets[k] + c, block.get(r, c));
            }
        }
    }
    let (reduced, pivots) = phi.rref(&field);
    assert_eq!(
        pivots.len(),
        rep.dims[i as usize],
        "the reflection functor met a non-injective structure map; library bug"
    );
    let mut is_pivot = vec![false; width];
    for &c in &pivots {
        is_pivot[c] = true;
    }
    let free: Vec<usize> = (0..width).filter(|&c| !is_pivot[c]).collect();
    // The rows of `reduced` are in reduced echelon form, so the free
    // coordinates split off a complement of the image and `projection` sends a
    // vector to its coordinates there.
    let mut projection = DenseMat::zero(width, free.len());
    for (k, &f) in free.iter().enumerate() {
        projection.set(f, k, Fp::ONE);
        for (j, &p) in pivots.iter().enumerate() {
            projection.set(p, k, field.neg(reduced.get(j, f)));
        }
    }
    let mut dims = rep.dims.clone();
    dims[i as usize] = free.len();
    let mut maps = rep.maps.clone();
    for (k, &a) in outgoing.iter().enumerate() {
        let rows = rep.dims[source_endpoints[a].1 as usize];
        let mut block = DenseMat::zero(rows, free.len());
        for r in 0..rows {
            for (c, entry) in (0..free.len()).map(|c| (c, projection.get(offsets[k] + r, c))) {
                block.set(r, c, entry);
            }
        }
        maps[a] = block;
    }
    Rep { dims, maps }
}

/// A sequence `i_1, …, i_n` listing every vertex once, with `i_1` a sink of
/// `quiver` and `i_k` a sink after reversing at `i_1, …, i_{k-1}`; `None` when
/// the quiver has an oriented cycle. Reversing at all of them in order returns
/// the original orientation.
fn admissible_sink_sequence(quiver: &Quiver) -> Option<Vec<u32>> {
    let n = quiver.num_vertices();
    let mut endpoints: Vec<(u32, u32)> = quiver.arrows().to_vec();
    let mut used = vec![false; n as usize];
    let mut sequence = Vec::with_capacity(n as usize);
    for _ in 0..n {
        let sink = (0..n).find(|&v| !used[v as usize] && endpoints.iter().all(|&(s, _)| s != v))?;
        used[sink as usize] = true;
        sequence.push(sink);
        reflect_endpoints(&mut endpoints, sink);
    }
    Some(sequence)
}

/// The underlying undirected multigraph of a quiver.
struct Underlying {
    num_vertices: usize,
    loops: usize,
    /// Edge multiplicities keyed by `(min, max)`; loops are excluded.
    multiplicity: FxHashMap<(usize, usize), usize>,
}

/// A connected loopless simple graph, with sorted adjacency lists.
struct Simple {
    neighbours: Vec<Vec<usize>>,
}

/// The shape of a tree, as far as the Dynkin and Euclidean classifications
/// distinguish shapes.
enum Shape {
    /// A path on this many vertices.
    Path(usize),
    /// One branch vertex with arms of these lengths, sorted ascending.
    Star(Vec<usize>),
    /// Two branch vertices of degree three, each carrying two leaves, joined by
    /// a path with this many edges.
    DoubleFork { separation: usize },
}

impl Underlying {
    fn of(quiver: &Quiver) -> Underlying {
        let mut loops = 0usize;
        let mut multiplicity: FxHashMap<(usize, usize), usize> = FxHashMap::default();
        for &(s, t) in quiver.arrows() {
            let (u, v) = (s as usize, t as usize);
            if u == v {
                loops += 1;
            } else {
                *multiplicity.entry((u.min(v), u.max(v))).or_insert(0) += 1;
            }
        }
        Underlying {
            num_vertices: quiver.num_vertices() as usize,
            loops,
            multiplicity,
        }
    }

    fn num_edges(&self) -> usize {
        self.loops + self.multiplicity.values().sum::<usize>()
    }

    fn max_multiplicity(&self) -> usize {
        self.multiplicity.values().copied().max().unwrap_or(0)
    }

    fn simple(&self) -> Simple {
        let mut neighbours = vec![Vec::new(); self.num_vertices];
        for &(u, v) in self.multiplicity.keys() {
            neighbours[u].push(v);
            neighbours[v].push(u);
        }
        for list in &mut neighbours {
            list.sort_unstable();
        }
        Simple { neighbours }
    }

    fn is_connected(&self) -> bool {
        if self.num_vertices == 0 {
            return false;
        }
        let simple = self.simple();
        let mut seen = vec![false; self.num_vertices];
        let mut stack = vec![0usize];
        seen[0] = true;
        let mut count = 1usize;
        while let Some(v) = stack.pop() {
            for &w in &simple.neighbours[v] {
                if !seen[w] {
                    seen[w] = true;
                    count += 1;
                    stack.push(w);
                }
            }
        }
        count == self.num_vertices
    }
}

/// The underlying graph of `quiver` when it is a connected loopless simple
/// tree, which every Dynkin diagram is.
fn tree(quiver: &Quiver) -> Option<Simple> {
    let graph = Underlying::of(quiver);
    if graph.loops > 0 || graph.max_multiplicity() > 1 || graph.num_vertices == 0 {
        return None;
    }
    if graph.num_edges() != graph.num_vertices - 1 || !graph.is_connected() {
        return None;
    }
    Some(graph.simple())
}

impl Simple {
    fn degree(&self, v: usize) -> usize {
        self.neighbours[v].len()
    }

    /// Walks from `center` into `first` while degrees stay `2`. Returns the
    /// number of edges walked and the vertex where the walk stopped.
    fn arm(&self, center: usize, first: usize) -> (usize, usize) {
        let mut previous = center;
        let mut current = first;
        let mut length = 1usize;
        while self.degree(current) == 2 {
            let next = if self.neighbours[current][0] == previous {
                self.neighbours[current][1]
            } else {
                self.neighbours[current][0]
            };
            previous = current;
            current = next;
            length += 1;
        }
        (length, current)
    }

    /// The tree's shape, or `None` when it has a vertex of degree at least
    /// five, three or more branch vertices, or two branch vertices in any
    /// arrangement other than a double fork.
    fn shape(&self) -> Option<Shape> {
        let n = self.neighbours.len();
        let branch: Vec<usize> = (0..n).filter(|&v| self.degree(v) >= 3).collect();
        match branch[..] {
            [] => Some(Shape::Path(n)),
            [center] => {
                if self.degree(center) > 4 {
                    return None;
                }
                let mut arms: Vec<usize> = self.neighbours[center]
                    .iter()
                    .map(|&w| self.arm(center, w).0)
                    .collect();
                arms.sort_unstable();
                Some(Shape::Star(arms))
            }
            [first, second] => {
                if self.degree(first) != 3 || self.degree(second) != 3 {
                    return None;
                }
                let mut separation = None;
                for &center in &[first, second] {
                    let mut leaves = 0usize;
                    for &w in &self.neighbours[center] {
                        let (length, end) = self.arm(center, w);
                        if end == first || end == second {
                            separation = Some(length);
                        } else if length == 1 {
                            leaves += 1;
                        }
                    }
                    if leaves != 2 {
                        return None;
                    }
                }
                separation.map(|separation| Shape::DoubleFork { separation })
            }
            _ => None,
        }
    }
}

/// A star quiver: a center with arms of the given lengths, every arrow
/// pointing away from the center. The caller must ensure the total vertex
/// count fits in `u32`; the internal counter does not check.
fn star(arms: &[usize]) -> Quiver {
    let mut arrows: Vec<(u32, u32)> = Vec::new();
    let mut next = 1u32;
    for &length in arms {
        let mut previous = 0u32;
        for _ in 0..length {
            arrows.push((previous, next));
            previous = next;
            next += 1;
        }
    }
    Quiver::new(next, &arrows).expect("star endpoints are in range")
}

/// Two leaves at each end of a path with `separation` edges; `separation = 0`
/// collapses the two ends into one vertex of degree four. The caller must
/// ensure the total vertex count `separation + 5` fits in `u32`; the internal
/// cast does not check.
fn double_fork(separation: usize) -> Quiver {
    let spine: Vec<u32> = (2..=2 + separation as u32).collect();
    let last = *spine.last().expect("the spine has at least one vertex");
    let mut arrows = vec![(0u32, 2u32), (1u32, 2u32)];
    for pair in spine.windows(2) {
        arrows.push((pair[0], pair[1]));
    }
    arrows.push((last, last + 1));
    arrows.push((last, last + 2));
    Quiver::new(last + 3, &arrows).expect("double fork endpoints are in range")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{an_with_relations, kronecker, linear_an};
    use crate::iso::{IsoOutcome, is_isomorphic};

    fn path_algebra(quiver: Quiver, field: PrimeField) -> Arc<Algebra> {
        let presentation = crate::algebra::MonomialPresentation::new(quiver, Vec::new())
            .expect("an acyclic quiver has a finite kQ");
        Algebra::from_monomial(
            field,
            &presentation,
            &crate::completion::CompletionLimits::default(),
        )
        .expect("the zero ideal completes")
    }

    fn dynkin_types() -> Vec<DynkinType> {
        let mut types: Vec<DynkinType> = (1..=8).map(DynkinType::A).collect();
        types.extend((4..=8).map(DynkinType::D));
        types.extend([DynkinType::E6, DynkinType::E7, DynkinType::E8]);
        types
    }

    fn euclidean_types() -> Vec<EuclideanType> {
        let mut types: Vec<EuclideanType> = (1..=8).map(EuclideanType::A).collect();
        types.extend((4..=8).map(EuclideanType::D));
        types.extend([EuclideanType::E6, EuclideanType::E7, EuclideanType::E8]);
        types
    }

    #[test]
    fn each_dynkin_diagram_is_recognised_as_its_own_type() {
        for t in dynkin_types() {
            let q = dynkin_quiver(t).unwrap();
            assert_eq!(q.num_vertices() as usize, t.num_vertices().unwrap());
            assert_eq!(dynkin_type(&q), Some(t), "{t}");
            assert_eq!(euclidean_type(&q), None, "{t}");
        }
    }

    #[test]
    fn each_euclidean_diagram_is_recognised_as_its_own_type() {
        for t in euclidean_types() {
            let q = euclidean_quiver(t).unwrap();
            assert_eq!(q.num_vertices() as usize, t.num_vertices().unwrap());
            assert_eq!(euclidean_type(&q), Some(t), "{t}");
            assert_eq!(dynkin_type(&q), None, "{t}");
        }
    }

    #[test]
    fn a_double_edge_is_affine_a_1() {
        let kronecker_quiver = Quiver::new(2, &[(0, 1), (0, 1)]).unwrap();
        assert_eq!(euclidean_type(&kronecker_quiver), Some(EuclideanType::A(1)));
        let two_cycle = Quiver::new(2, &[(0, 1), (1, 0)]).unwrap();
        assert_eq!(euclidean_type(&two_cycle), Some(EuclideanType::A(1)));
    }

    #[test]
    fn a_triple_edge_is_neither_dynkin_nor_euclidean() {
        let q = Quiver::new(2, &[(0, 1), (0, 1), (0, 1)]).unwrap();
        assert_eq!(dynkin_type(&q), None);
        assert_eq!(euclidean_type(&q), None);
    }

    #[test]
    fn orientation_does_not_change_the_recognised_type() {
        let forward = Quiver::new(4, &[(0, 1), (1, 2), (2, 3)]).unwrap();
        let alternating = Quiver::new(4, &[(0, 1), (2, 1), (2, 3)]).unwrap();
        assert_eq!(dynkin_type(&forward), Some(DynkinType::A(4)));
        assert_eq!(dynkin_type(&alternating), Some(DynkinType::A(4)));
    }

    #[test]
    fn a_disconnected_graph_has_no_type() {
        let q = Quiver::new(4, &[(0, 1), (2, 3)]).unwrap();
        assert_eq!(dynkin_type(&q), None);
        assert_eq!(euclidean_type(&q), None);
    }

    #[test]
    fn a_loop_has_no_type_and_no_generalized_cartan_matrix() {
        let q = Quiver::new(1, &[(0, 0)]).unwrap();
        assert_eq!(dynkin_type(&q), None);
        assert_eq!(euclidean_type(&q), None);
        assert_eq!(generalized_cartan_matrix(&q), None);
    }

    #[test]
    fn the_star_with_arms_2_2_3_is_neither_dynkin_nor_euclidean() {
        let q = star(&[2, 2, 3]);
        assert_eq!(dynkin_type(&q), None);
        assert_eq!(euclidean_type(&q), None);
    }

    #[test]
    fn the_star_with_five_arms_is_neither_dynkin_nor_euclidean() {
        let q = star(&[1, 1, 1, 1, 1]);
        assert_eq!(dynkin_type(&q), None);
        assert_eq!(euclidean_type(&q), None);
    }

    #[test]
    fn generalized_cartan_matrix_has_minus_the_edge_multiplicity_off_diagonal() {
        let q = Quiver::new(2, &[(0, 1), (0, 1)]).unwrap();
        assert_eq!(
            generalized_cartan_matrix(&q),
            Some(vec![vec![2, -2], vec![-2, 2]])
        );
        let a3 = Quiver::new(3, &[(0, 1), (2, 1)]).unwrap();
        assert_eq!(
            generalized_cartan_matrix(&a3),
            Some(vec![vec![2, -1, 0], vec![-1, 2, -1], vec![0, -1, 2]])
        );
    }

    #[test]
    fn positive_root_count_matches_the_dynkin_type() {
        for t in dynkin_types() {
            let q = dynkin_quiver(t).unwrap();
            let roots = positive_roots(&q).unwrap();
            assert_eq!(roots.len(), t.indecomposable_count().unwrap(), "{t}");
        }
    }

    #[test]
    fn the_highest_root_has_the_tabulated_height() {
        for (t, height) in [
            (DynkinType::A(5), 5),
            (DynkinType::D(4), 5),
            (DynkinType::D(7), 11),
            (DynkinType::E6, 11),
            (DynkinType::E7, 17),
            (DynkinType::E8, 29),
        ] {
            let roots = positive_roots(&dynkin_quiver(t).unwrap()).unwrap();
            let highest = roots.iter().map(|r| r.iter().sum::<usize>()).max().unwrap();
            assert_eq!(highest, height, "{t}");
        }
    }

    #[test]
    fn the_positive_roots_of_a3_are_the_six_intervals() {
        let roots = positive_roots(linear_an(3, PrimeField::new(5).unwrap()).quiver()).unwrap();
        assert_eq!(
            roots,
            vec![
                vec![0, 0, 1],
                vec![0, 1, 0],
                vec![1, 0, 0],
                vec![0, 1, 1],
                vec![1, 1, 0],
                vec![1, 1, 1],
            ]
        );
    }

    #[test]
    fn a_euclidean_graph_has_no_positive_root_list() {
        assert_eq!(
            positive_roots(kronecker(2, PrimeField::new(5).unwrap()).quiver()),
            None
        );
    }

    #[test]
    fn the_admissible_sequence_lists_every_vertex_and_restores_the_orientation() {
        for t in dynkin_types() {
            let q = dynkin_quiver(t).unwrap();
            let sequence = admissible_sink_sequence(&q).unwrap();
            let mut sorted = sequence.clone();
            sorted.sort_unstable();
            assert_eq!(sorted, (0..q.num_vertices()).collect::<Vec<_>>(), "{t}");
            let mut endpoints: Vec<(u32, u32)> = q.arrows().to_vec();
            for &i in &sequence {
                reflect_endpoints(&mut endpoints, i);
            }
            assert_eq!(endpoints, q.arrows(), "{t}");
        }
    }

    #[test]
    fn a_cyclic_quiver_has_no_admissible_sink_sequence() {
        let q = Quiver::new(3, &[(0, 1), (1, 2), (2, 0)]).unwrap();
        assert_eq!(admissible_sink_sequence(&q), None);
    }

    #[test]
    fn a_bound_algebra_is_rejected_as_a_nonzero_ideal() {
        let algebra = an_with_relations(3, &[(0, 2)], PrimeField::new(5).unwrap()).unwrap();
        assert_eq!(
            dynkin_indecomposables(&algebra).unwrap_err(),
            DynkinError::NonzeroIdeal { relations: 1 }
        );
    }

    #[test]
    fn the_kronecker_algebra_is_rejected_as_affine_a_1() {
        assert_eq!(
            dynkin_indecomposables(&kronecker(2, PrimeField::new(5).unwrap())).unwrap_err(),
            DynkinError::NotDynkin {
                euclidean: Some(EuclideanType::A(1)),
            }
        );
    }

    #[test]
    fn constructed_dimension_vectors_are_exactly_the_positive_roots() {
        let field = PrimeField::new(32003).unwrap();
        for t in [
            DynkinType::A(1),
            DynkinType::A(4),
            DynkinType::D(4),
            DynkinType::D(5),
        ] {
            let quiver = dynkin_quiver(t).unwrap();
            let roots = positive_roots(&quiver).unwrap();
            let algebra = path_algebra(quiver, field);
            let built: Vec<Vec<usize>> = dynkin_indecomposables(&algebra)
                .unwrap()
                .iter()
                .map(|(m, _)| m.dim_vector().to_vec())
                .collect();
            assert_eq!(built, roots, "{t}");
        }
    }

    #[test]
    fn every_constructed_module_is_certified_indecomposable() {
        let field = PrimeField::new(2).unwrap();
        for t in [DynkinType::A(5), DynkinType::D(4)] {
            let algebra = path_algebra(dynkin_quiver(t).unwrap(), field);
            for (_, certificate) in dynkin_indecomposables(&algebra).unwrap() {
                assert_eq!(certificate, Certificate::Indecomposable, "{t}");
            }
        }
    }

    #[test]
    fn the_exceptional_types_have_36_63_and_120_indecomposables() {
        let field = PrimeField::new(32003).unwrap();
        for (t, count) in [
            (DynkinType::E6, 36),
            (DynkinType::E7, 63),
            (DynkinType::E8, 120),
        ] {
            let algebra = path_algebra(dynkin_quiver(t).unwrap(), field);
            let modules = dynkin_indecomposables(&algebra).unwrap();
            assert_eq!(modules.len(), count, "{t}");
            assert_eq!(t.indecomposable_count(), Some(count));
        }
    }

    /// `n(n+1)/2` must be reported whenever it is representable, even when the
    /// intermediate product `n(n+1)` is not, and `None` only when the count
    /// itself does not fit.
    #[test]
    fn root_counts_survive_an_unrepresentable_intermediate_product() {
        // Both widths need an n whose raw product overflows while its
        // triangular number still fits; the literal is cast rather than
        // written as a usize so it also compiles at 32 bits.
        let n: usize = if usize::BITS >= 64 {
            5_000_000_000u64 as usize
        } else {
            80_000
        };
        let expected = u128::from(n as u64) * (u128::from(n as u64) + 1) / 2;
        assert_eq!(n.checked_mul(n + 1), None, "the product must overflow");
        assert_eq!(
            DynkinType::A(n).indecomposable_count().map(u128::try_from),
            Some(Ok(expected))
        );
        assert_eq!(DynkinType::A(usize::MAX).indecomposable_count(), None);
        assert_eq!(DynkinType::A(usize::MAX).num_vertices(), Some(usize::MAX));
        assert_eq!(DynkinType::D(usize::MAX).indecomposable_count(), None);
        assert_eq!(EuclideanType::A(usize::MAX).num_vertices(), None);
        assert_eq!(EuclideanType::D(usize::MAX).num_vertices(), None);
        // Odd and even n take different branches of the halving.
        assert_eq!(DynkinType::A(7).indecomposable_count(), Some(28));
        assert_eq!(DynkinType::A(8).indecomposable_count(), Some(36));
    }

    /// A diagram whose vertex count exceeds the `u32` indexing of `Quiver`
    /// must be refused, never truncated into a small wrong quiver. The
    /// abstract counts stay available: `num_vertices` answers over `usize`.
    #[test]
    fn diagram_quivers_reject_vertex_counts_beyond_u32() {
        // The rejected parameters exist only at 64 bits; at 32 bits usize
        // itself enforces the bound.
        if usize::BITS < 64 {
            return;
        }
        let beyond = u32::MAX as u64 as usize + 1;
        assert!(dynkin_quiver(DynkinType::A(beyond)).is_none());
        assert!(dynkin_quiver(DynkinType::D(beyond)).is_none());
        assert_eq!(DynkinType::A(beyond).num_vertices(), Some(beyond));
        // Affine A and D have one vertex more than their subscript, so the
        // boundary parameter is already unrepresentable.
        assert!(euclidean_quiver(EuclideanType::A(beyond - 1)).is_none());
        assert!(euclidean_quiver(EuclideanType::D(beyond - 1)).is_none());
        assert!(euclidean_quiver(EuclideanType::A(beyond)).is_none());
        assert_eq!(EuclideanType::A(beyond).num_vertices(), Some(beyond + 1));
    }

    #[test]
    fn constructed_modules_are_pairwise_non_isomorphic() {
        let field = PrimeField::new(5).unwrap();
        let algebra = path_algebra(dynkin_quiver(DynkinType::D(4)).unwrap(), field);
        let modules = dynkin_indecomposables(&algebra).unwrap();
        assert_eq!(modules.len(), 12);
        for (i, (m, _)) in modules.iter().enumerate() {
            for (n, _) in modules.iter().skip(i + 1) {
                assert!(matches!(
                    is_isomorphic(m, n).unwrap(),
                    IsoOutcome::NotIsomorphic(_)
                ));
            }
        }
    }
}

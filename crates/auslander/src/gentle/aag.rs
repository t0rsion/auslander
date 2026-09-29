use super::shape::Sign;
use super::threads::{GentleThread, Threads};

/// The Avella-Alaminos-Geiss function `φ_A` of a gentle presentation, as a
/// sorted multiset of pairs `(n, m)`.
///
/// Each pair with `n > 0` is one orbit of the algorithm in section 3 of
/// D. Avella-Alaminos and C. Geiss, *Combinatorial derived invariants for
/// gentle algebras*, J. Pure Appl. Algebra 212 (2008), 228-243. The orbit
/// visits `n` permitted threads and `m` arrows of forbidden threads. Each
/// oriented cycle of length `m` whose consecutive pairs are all relations
/// adds the pair `(0, m)`. Derived equivalent gentle algebras have equal
/// functions (their Theorem A).
///
/// The pairs are sorted in increasing lexicographic order, so two functions
/// are equal exactly when their pair lists are equal. `Display` prints the
/// list as `[(0, 1), (1, 0)]`.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct AagFunction {
    pairs: Vec<(usize, usize)>,
}

impl AagFunction {
    pub(crate) fn new(threads: &Threads, vertices: u32) -> AagFunction {
        let permitted = SlotIndex::new(vertices, &threads.permitted, |h| (h.start(), h.sigma()));
        let forbidden = SlotIndex::new(vertices, &threads.forbidden, |p| (p.end(), p.epsilon()));
        let mut visited = vec![false; threads.permitted.len()];
        let mut pairs = Vec::new();
        for first in 0..threads.permitted.len() {
            let mut current = first;
            let (mut n, mut m) = (0, 0);
            while !visited[current] {
                visited[current] = true;
                let thread = &threads.permitted[current];
                let closing = &threads.forbidden[forbidden.at(thread.end(), thread.epsilon())];
                current = permitted.at(closing.start(), closing.sigma());
                n += 1;
                m += closing.length();
            }
            assert_eq!(
                current, first,
                "the thread map is not a bijection; library bug"
            );
            if n > 0 {
                pairs.push((n, m));
            }
        }
        pairs.extend(threads.cycles.iter().map(|cycle| (0, cycle.len())));
        pairs.sort_unstable();
        AagFunction { pairs }
    }

    accessor_methods! {
        /// The pairs `(n, m)`, sorted, with multiplicity.
        pub pairs() -> &[(usize, usize)] = |this| &this.pairs;
        /// The number of pairs, counted with multiplicity.
        pub len() -> usize = |this| this.pairs.len();
        /// Whether the function has no pairs. No gentle presentation has one.
        pub is_empty() -> bool = |this| this.pairs.is_empty();
    }
}

impl std::fmt::Display for AagFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("[")?;
        for (position, (n, m)) in self.pairs.iter().enumerate() {
            let separator = if position == 0 { "" } else { ", " };
            write!(f, "{separator}({n}, {m})")?;
        }
        f.write_str("]")
    }
}

/// Thread positions keyed by one vertex and one sign.
struct SlotIndex(Vec<Option<usize>>);

impl SlotIndex {
    fn new(
        vertices: u32,
        threads: &[GentleThread],
        key: impl Fn(&GentleThread) -> (u32, Sign),
    ) -> SlotIndex {
        let mut slots = vec![None; 2 * vertices as usize];
        for (position, thread) in threads.iter().enumerate() {
            let (vertex, sign) = key(thread);
            let slot = &mut slots[slot(vertex, sign)];
            assert!(slot.is_none(), "two threads share a slot; library bug");
            *slot = Some(position);
        }
        SlotIndex(slots)
    }

    /// The thread in the slot of `vertex` whose sign is opposite to `sign`.
    ///
    /// Step 1(b) of the algorithm pairs `H` with `Π` where `ε(Π) = -ε(H)`, and
    /// step 1(c) pairs `Π` with the next `H` where `σ(H) = -σ(Π)`.
    fn at(&self, vertex: u32, sign: Sign) -> usize {
        self.0[slot(vertex, sign.negated())].expect("every thread end meets a thread; library bug")
    }
}

fn slot(vertex: u32, sign: Sign) -> usize {
    2 * vertex as usize + usize::from(sign == Sign::Minus)
}

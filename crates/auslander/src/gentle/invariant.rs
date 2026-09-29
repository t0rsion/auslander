use super::aag::AagFunction;
use super::surface::RibbonGraph;

/// A complete derived invariant of a gentle presentation: the
/// Avella-Alaminos-Geiss function, the genus, and the [`WindingClass`].
///
/// Two finite-dimensional connected gentle algebras over one field are
/// derived equivalent exactly when their values are equal. This is Theorem
/// 5.4 of C. Amiot, P.-G. Plamondon, and S. Schroll, arXiv:1904.02555, with
/// the orbit classification of Y. Lekili and A. Polishchuk, arXiv:1801.06370,
/// Theorem 1.2.4. `docs/gentle-derived-invariant.md` gives the construction
/// and the citation of every formula.
///
/// The AAG function fixes the genus. In genus 0 the class is
/// [`WindingClass::Planar`] and the AAG function alone is complete.
///
/// `Display` prints `[(2, 4)], genus 1, gcd 2`.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct GentleDerivedInvariant {
    aag: AagFunction,
    genus: usize,
    class: WindingClass,
}

/// The winding class of a gentle presentation: the winding data of its line
/// field beyond the boundary winding numbers.
///
/// Winding numbers are those of the line field of Amiot, Plamondon, and
/// Schroll on the surface model. `Display` prints the lowercase name and the
/// value, as `planar`, `gcd 2`, `odd`, `even`, or `arf 1`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum WindingClass {
    /// Genus 0.
    Planar,
    /// Genus 1: the invariant `Ã` of Lekili and Polishchuk, the gcd of the
    /// winding numbers of nonseparating curves and of `w + 2` over the
    /// boundary winding numbers `w`.
    Gcd(u64),
    /// Genus at least 2, and some closed curve has an odd winding number.
    Odd,
    /// Genus at least 2, every winding number even, and some boundary winding
    /// number divisible by 4.
    Even,
    /// Genus at least 2, every winding number even, and every boundary
    /// winding number `2 mod 4`: the Arf invariant, 0 or 1.
    Arf(u8),
}

impl GentleDerivedInvariant {
    /// Computes the invariant from the ribbon graph of the presentation.
    ///
    /// Panics when a consistency check fails, which is a library bug: the
    /// rank of the intersection pairing mod 2 is `2 * genus`, a separating
    /// curve in genus 1 has winding number `±2` modulo the boundary gcd, even
    /// interior winding numbers force even boundary ones, and the Arf form
    /// vanishes on the radical.
    pub(super) fn new(
        aag: AagFunction,
        genus: usize,
        graph: &RibbonGraph,
    ) -> GentleDerivedInvariant {
        let cycles = graph.fundamental_cycles();
        let windings: Vec<i64> = cycles.iter().map(|cycle| graph.winding(cycle)).collect();
        let pairing = graph.pairing(&cycles);
        let boundary: Vec<i64> = aag
            .pairs()
            .iter()
            .map(|&(n, m)| n as i64 - m as i64)
            .collect();
        let reduction = Reduction::new(&pairing, &windings);
        assert_eq!(
            reduction.pairs,
            genus,
            "the intersection pairing has rank {} mod 2, not twice the genus {genus}; library bug",
            2 * reduction.pairs
        );
        let class = match genus {
            0 => WindingClass::Planar,
            1 => WindingClass::Gcd(torus_gcd(&boundary, &windings, &pairing)),
            _ => higher_class(&boundary, &windings, &reduction),
        };
        GentleDerivedInvariant { aag, genus, class }
    }

    accessor_methods! {
        /// The Avella-Alaminos-Geiss function.
        pub aag_function() -> &AagFunction = |this| &this.aag;
        /// The genus of the surface model.
        pub genus() -> usize = |this| this.genus;
        /// The winding class.
        pub winding_class() -> WindingClass = |this| this.class;
    }
}

impl std::fmt::Display for GentleDerivedInvariant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}, genus {}, {}", self.aag, self.genus, self.class)
    }
}

impl std::fmt::Display for WindingClass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WindingClass::Planar => f.write_str("planar"),
            WindingClass::Gcd(value) => write!(f, "gcd {value}"),
            WindingClass::Odd => f.write_str("odd"),
            WindingClass::Even => f.write_str("even"),
            WindingClass::Arf(value) => write!(f, "arf {value}"),
        }
    }
}

/// `Ã` from a homology basis of simple closed curves.
///
/// A basis curve is separating exactly when its row of `pairing` is zero.
/// On a separating curve the winding number is `2` or `-2` modulo the gcd
/// `d` of `w + 2` over the boundary; the note derives this from a flat line
/// field on the torus.
fn torus_gcd(boundary: &[i64], windings: &[i64], pairing: &[Vec<i64>]) -> u64 {
    let shifted = boundary.iter().fold(0, |acc, &w| gcd(acc, w + 2));
    let mut total = shifted;
    for (winding, row) in windings.iter().zip(pairing) {
        if row.iter().any(|&entry| entry != 0) {
            total = gcd(total, *winding);
        } else {
            assert!(
                divides(shifted, winding - 2) || divides(shifted, winding + 2),
                "a separating curve has winding number {winding} modulo {shifted}; library bug"
            );
        }
    }
    total
}

fn higher_class(boundary: &[i64], windings: &[i64], reduction: &Reduction) -> WindingClass {
    if windings.iter().any(|w| w % 2 != 0) {
        return WindingClass::Odd;
    }
    assert!(
        boundary.iter().all(|w| w % 2 == 0),
        "even interior winding numbers with an odd boundary one; library bug"
    );
    if boundary.iter().any(|w| w % 4 == 0) {
        return WindingClass::Even;
    }
    assert!(
        reduction.radical_is_isotropic,
        "the Arf form does not vanish on the radical; library bug"
    );
    WindingClass::Arf(u8::from(reduction.arf))
}

/// Symplectic reduction over `F_2` of the intersection pairing, with the
/// quadratic form `q(z) = w(z) / 2 + 1` on the basis.
///
/// `q` extends by `q(x + y) = q(x) + q(y) + x · y`. The values are meaningful
/// only when every winding number is even.
struct Reduction {
    /// The number of hyperbolic pairs, half the rank mod 2.
    pairs: usize,
    /// `Σ q(a_i) q(b_i)` over the pairs.
    arf: bool,
    /// Whether `q` vanishes on a basis of the radical.
    radical_is_isotropic: bool,
}

/// A vector over `F_2` in the basis of fundamental cycles, with its image
/// `x^T G` under the Gram matrix `G`.
#[derive(Clone)]
struct Vector {
    coords: Vec<bool>,
    image: Vec<bool>,
}

impl Vector {
    fn add(&mut self, other: &Vector) {
        xor_into(&mut self.coords, &other.coords);
        xor_into(&mut self.image, &other.image);
    }

    fn pair(&self, other: &Vector) -> bool {
        dot(&self.image, &other.coords)
    }
}

impl Reduction {
    fn new(pairing: &[Vec<i64>], windings: &[i64]) -> Reduction {
        let gram: Vec<Vec<bool>> = pairing
            .iter()
            .map(|row| row.iter().map(|&entry| entry % 2 != 0).collect())
            .collect();
        let values: Vec<bool> = windings
            .iter()
            .map(|w| (w.div_euclid(2) + 1) % 2 != 0)
            .collect();
        let quadratic = |x: &Vector| quadratic(&gram, &values, &x.coords);
        let mut pool: Vec<Vector> = (0..gram.len())
            .map(|index| Vector {
                coords: (0..gram.len()).map(|j| j == index).collect(),
                image: gram[index].clone(),
            })
            .collect();
        let (mut pairs, mut arf, mut radical_is_isotropic) = (0, false, true);
        while let Some(first) = pool.pop() {
            let Some(index) = pool.iter().position(|other| first.pair(other)) else {
                radical_is_isotropic &= !quadratic(&first);
                continue;
            };
            let second = pool.swap_remove(index);
            arf ^= quadratic(&first) && quadratic(&second);
            project(&mut pool, &first, &second);
            pairs += 1;
        }
        Reduction {
            pairs,
            arf,
            radical_is_isotropic,
        }
    }
}

/// Makes every vector of `pool` orthogonal to the hyperbolic pair.
fn project(pool: &mut [Vector], first: &Vector, second: &Vector) {
    for vector in pool {
        let (with_first, with_second) = (vector.pair(first), vector.pair(second));
        if with_second {
            vector.add(first);
        }
        if with_first {
            vector.add(second);
        }
    }
}

/// `Σ x_i q_i + Σ_{i < j} x_i x_j G_ij` mod 2.
fn quadratic(gram: &[Vec<bool>], values: &[bool], coords: &[bool]) -> bool {
    let mut total = false;
    for (i, _) in coords.iter().enumerate().filter(|(_, x)| **x) {
        total ^= values[i];
        for j in (i + 1..coords.len()).filter(|&j| coords[j]) {
            total ^= gram[i][j];
        }
    }
    total
}

fn dot(left: &[bool], right: &[bool]) -> bool {
    left.iter().zip(right).filter(|(a, b)| **a && **b).count() % 2 == 1
}

fn xor_into(target: &mut [bool], other: &[bool]) {
    for (bit, &flip) in target.iter_mut().zip(other) {
        *bit ^= flip;
    }
}

fn gcd(a: u64, b: i64) -> u64 {
    let (mut a, mut b) = (a, b.unsigned_abs());
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

fn divides(divisor: u64, value: i64) -> bool {
    match divisor {
        0 => value == 0,
        _ => value.unsigned_abs().is_multiple_of(divisor),
    }
}

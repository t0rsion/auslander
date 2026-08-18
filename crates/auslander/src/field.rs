//! Prime fields F_p with construction-time primality checking.

use crate::profile::{Site, hit};

/// Rejection reason from [`PrimeField::new`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FieldError {
    /// The modulus is 0, 1, or composite.
    NotPrime(u64),
    /// The modulus is >= 2^31; see [`PrimeField::new`] for the bound.
    ModulusTooLarge(u64),
}

impl std::fmt::Display for FieldError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FieldError::NotPrime(n) => write!(f, "modulus {n} is not prime"),
            FieldError::ModulusTooLarge(n) => write!(f, "modulus {n} is not below 2^31"),
        }
    }
}

impl std::error::Error for FieldError {}

/// An element of a prime field, stored as its canonical representative in `0..p`.
///
/// Elements are opaque and always reduced. Create them with
/// [`PrimeField::elem`], [`PrimeField::zero`], or [`PrimeField::one`], and
/// combine them with the arithmetic methods on [`PrimeField`]. An `Fp` carries
/// no reference to its field. Mixing elements of different fields is a logic
/// error the types do not catch.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Fp(u64);

impl Fp {
    pub(crate) const ZERO: Fp = Fp(0);
    pub(crate) const ONE: Fp = Fp(1);

    /// Whether this is the additive identity (the same element in every field).
    #[inline]
    pub const fn is_zero(self) -> bool {
        self.0 == 0
    }

    /// The canonical representative in `0..p`.
    #[inline]
    pub(crate) const fn raw(self) -> u64 {
        self.0
    }
}

/// The field F_p = Z/pZ for a prime p < 2^31.
///
/// The bound keeps sums below 2^32 and products below 2^62, so all arithmetic
/// on reduced representatives stays within `u64`.
///
/// Every arithmetic method takes elements already reduced modulo `p`. Debug
/// builds assert that. Release builds do not check it, and an unreduced
/// input then gives a wrong result.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PrimeField {
    p: u64,
}

/// Exclusive upper bound on moduli.
const MODULUS_BOUND: u64 = 1 << 31;

/// Trial division by 2, 3, and 6k±1. Exact for every `n` below 2^62; a
/// larger `n` can overflow `k * k`.
fn is_prime(n: u64) -> bool {
    if n < 2 {
        return false;
    }
    if n < 4 {
        return true;
    }
    if n.is_multiple_of(2) || n.is_multiple_of(3) {
        return false;
    }
    let mut k = 5;
    while k * k <= n {
        if n.is_multiple_of(k) || n.is_multiple_of(k + 2) {
            return false;
        }
        k += 6;
    }
    true
}

impl PrimeField {
    /// Constructs F_p after verifying that `p` is prime and below 2^31.
    ///
    /// The bound is checked first: `p >= 2^31` gives
    /// [`FieldError::ModulusTooLarge`], a smaller non-prime `p` gives
    /// [`FieldError::NotPrime`].
    pub fn new(p: u64) -> Result<PrimeField, FieldError> {
        if p >= MODULUS_BOUND {
            return Err(FieldError::ModulusTooLarge(p));
        }
        if !is_prime(p) {
            return Err(FieldError::NotPrime(p));
        }
        Ok(PrimeField { p })
    }

    /// The characteristic `p`.
    #[inline]
    pub const fn modulus(self) -> u64 {
        self.p
    }

    /// The residue class of `v`, reduced into `0..p`.
    #[inline]
    pub fn elem(self, v: i64) -> Fp {
        Fp(v.rem_euclid(self.p as i64) as u64)
    }

    /// The residue class of a `u128`, reduced into `0..p`.
    ///
    /// A dot product of reduced entries fits in `u128` for any length the
    /// machine can hold, so a caller accumulates the whole product and reduces
    /// once here instead of once per term. See [`crate::linalg::DenseMat::mul`].
    ///
    /// An accumulator below `2^64` takes the narrow route, one hardware
    /// divide. The wide route is a call into the compiler runtime
    /// (`__umodti3` on x86-64). Each product of reduced entries is below
    /// `2^62`, so a dot product needs more than four terms before it can
    /// leave 64 bits, and only entries near the modulus bound take it there.
    /// Over F_5 a dot product of 78 terms reaches 1248, far below `2^64`.
    #[inline]
    pub(crate) fn reduce_wide(self, x: u128) -> Fp {
        hit(Site::FieldReduceWide);
        match u64::try_from(x) {
            Ok(narrow) => Fp(narrow % self.p),
            Err(_) => Fp((x % self.p as u128) as u64),
        }
    }

    /// The additive identity.
    #[inline]
    pub const fn zero(self) -> Fp {
        Fp::ZERO
    }

    /// The multiplicative identity.
    #[inline]
    pub const fn one(self) -> Fp {
        Fp::ONE
    }

    /// The sum `a + b`.
    #[inline]
    pub fn add(self, a: Fp, b: Fp) -> Fp {
        hit(Site::FieldAdd);
        debug_assert!(
            a.0 < self.p && b.0 < self.p,
            "unreduced input in F_{}",
            self.p
        );
        let s = a.0 + b.0;
        Fp(if s >= self.p { s - self.p } else { s })
    }

    /// The difference `a - b`.
    #[inline]
    pub fn sub(self, a: Fp, b: Fp) -> Fp {
        hit(Site::FieldSub);
        debug_assert!(
            a.0 < self.p && b.0 < self.p,
            "unreduced input in F_{}",
            self.p
        );
        Fp(if a.0 >= b.0 {
            a.0 - b.0
        } else {
            a.0 + self.p - b.0
        })
    }

    /// The negative `-a`.
    #[inline]
    pub fn neg(self, a: Fp) -> Fp {
        debug_assert!(a.0 < self.p, "unreduced input in F_{}", self.p);
        if a.0 == 0 { a } else { Fp(self.p - a.0) }
    }

    /// The product `a * b`.
    #[inline]
    pub fn mul(self, a: Fp, b: Fp) -> Fp {
        hit(Site::FieldMul);
        debug_assert!(
            a.0 < self.p && b.0 < self.p,
            "unreduced input in F_{}",
            self.p
        );
        Fp(a.0 * b.0 % self.p)
    }

    /// The inverse `a^-1`, by the extended Euclidean algorithm.
    ///
    /// # Panics
    /// Panics if `a` is zero.
    pub fn inv(self, a: Fp) -> Fp {
        hit(Site::FieldInv);
        debug_assert!(a.0 < self.p, "unreduced input in F_{}", self.p);
        assert!(!a.is_zero(), "inverse of zero in F_{}", self.p);
        // Bezout coefficients stay within +-p, so i64 suffices for p < 2^31.
        let (mut r0, mut r1) = (a.0 as i64, self.p as i64);
        let (mut s0, mut s1) = (1i64, 0i64);
        while r1 != 0 {
            let q = r0 / r1;
            (r0, r1) = (r1, r0 - q * r1);
            (s0, s1) = (s1, s0 - q * s1);
        }
        Fp(s0.rem_euclid(self.p as i64) as u64)
    }

    /// `a` to the power `exp`, by binary exponentiation. `pow(a, 0)` is 1
    /// for every `a`, zero included.
    pub fn pow(self, a: Fp, mut exp: u64) -> Fp {
        debug_assert!(a.0 < self.p, "unreduced input in F_{}", self.p);
        let mut base = a;
        let mut acc = Fp::ONE;
        while exp > 0 {
            if exp & 1 == 1 {
                acc = self.mul(acc, base);
            }
            base = self.mul(base, base);
            exp >>= 1;
        }
        acc
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(p: u64) -> PrimeField {
        PrimeField::new(p).unwrap()
    }

    #[test]
    fn small_primes_are_accepted() {
        for p in [2, 3, 5, 7, 101, 32003, (1 << 31) - 1] {
            assert!(PrimeField::new(p).is_ok(), "p = {p}");
        }
    }

    #[test]
    fn composites_and_units_are_rejected() {
        for n in [0, 1, 4, 9, 10, 15, 49, 1_000_000] {
            assert_eq!(PrimeField::new(n), Err(FieldError::NotPrime(n)));
        }
    }

    #[test]
    fn moduli_at_or_above_the_bound_are_rejected() {
        for n in [1u64 << 31, (1 << 31) + 11, u64::MAX] {
            assert_eq!(PrimeField::new(n), Err(FieldError::ModulusTooLarge(n)));
        }
    }

    #[test]
    fn elem_reduces_to_the_canonical_representative() {
        let f7 = f(7);
        assert_eq!(f7.elem(0), f7.zero());
        assert_eq!(f7.elem(7), f7.zero());
        assert_eq!(f7.elem(-1), f7.elem(6));
        assert_eq!(f7.elem(-13), f7.elem(1));
        assert_eq!(f7.elem(i64::MIN), f7.elem(6));
    }

    #[test]
    fn f7_satisfies_ring_identities() {
        let f7 = f(7);
        let elems: Vec<Fp> = (0..7).map(|i| f7.elem(i)).collect();
        for &a in &elems {
            assert_eq!(f7.add(a, f7.zero()), a);
            assert_eq!(f7.mul(a, f7.one()), a);
            assert_eq!(f7.add(a, f7.neg(a)), f7.zero());
            for &b in &elems {
                assert_eq!(f7.add(a, b), f7.add(b, a));
                assert_eq!(f7.mul(a, b), f7.mul(b, a));
                assert_eq!(f7.sub(f7.add(a, b), b), a);
                for &c in &elems {
                    assert_eq!(f7.mul(a, f7.add(b, c)), f7.add(f7.mul(a, b), f7.mul(a, c)));
                }
            }
        }
    }

    #[test]
    fn f2_arithmetic_is_boolean() {
        let f2 = f(2);
        let one = f2.one();
        assert_eq!(f2.add(one, one), f2.zero());
        assert_eq!(f2.neg(one), one);
        assert_eq!(f2.mul(one, one), one);
        assert_eq!(f2.inv(one), one);
    }

    #[test]
    fn inv_round_trips_for_all_nonzero_elements() {
        for p in [2, 7, 101] {
            let fp = f(p);
            for i in 1..p as i64 {
                let a = fp.elem(i);
                assert_eq!(fp.mul(a, fp.inv(a)), fp.one(), "a = {i} in F_{p}");
            }
        }
        let big = f((1 << 31) - 1);
        for i in [1, 2, 12345, (1 << 31) - 2] {
            let a = big.elem(i);
            assert_eq!(big.mul(a, big.inv(a)), big.one());
        }
    }

    #[test]
    #[should_panic(expected = "inverse of zero")]
    fn inv_of_zero_panics() {
        let f7 = f(7);
        let _ = f7.inv(f7.zero());
    }

    #[test]
    fn pow_matches_repeated_multiplication() {
        let fp = f(101);
        let a = fp.elem(7);
        let mut acc = fp.one();
        for e in 0..20 {
            assert_eq!(fp.pow(a, e), acc);
            acc = fp.mul(acc, a);
        }
        assert_eq!(fp.pow(fp.zero(), 0), fp.one());
        assert_eq!(fp.pow(fp.zero(), 5), fp.zero());
    }

    #[test]
    fn pow_satisfies_fermats_little_theorem() {
        let fp = f(101);
        for i in 1..101 {
            assert_eq!(fp.pow(fp.elem(i), 100), fp.one());
        }
    }

    /// `x` modulo `p`, by doubling over the bits of `x`. Uses addition alone,
    /// so it is independent of the reduction under test.
    fn by_doubling(fp: PrimeField, x: u128) -> Fp {
        let mut r = fp.zero();
        for i in (0..128).rev() {
            r = fp.add(r, r);
            if (x >> i) & 1 == 1 {
                r = fp.add(r, fp.one());
            }
        }
        r
    }

    #[test]
    fn mul_stays_exact_at_the_modulus_bound() {
        let mut x = 0x243f_6a88_85a3_08d3u64;
        for p in [2, 101, 2_147_483_629, (1 << 31) - 1] {
            let fp = f(p);
            let top = fp.elem((p - 1) as i64);
            let square = (p - 1) as u128 * (p - 1) as u128;
            assert_eq!(fp.mul(top, top), by_doubling(fp, square), "in F_{p}");
            assert_eq!(fp.mul(top, fp.one()), top);
            assert_eq!(fp.mul(top, fp.zero()), fp.zero());
            for _ in 0..2_000 {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                let a = fp.elem((x % p) as i64);
                let b = fp.elem((x.rotate_left(32) % p) as i64);
                let product = a.raw() as u128 * b.raw() as u128;
                assert_eq!(fp.mul(a, b), by_doubling(fp, product), "in F_{p}");
            }
        }
    }

    #[test]
    fn reduce_wide_matches_bitwise_reduction() {
        let mut x = 0x9e37_79b9_7f4a_7c15u64;
        for p in [2, 7, 101, (1 << 31) - 1] {
            let fp = f(p);
            for e in [0u32, 1, 31, 63, 64, 65, 96, 127] {
                let v = (1u128 << e) - 1;
                assert_eq!(fp.reduce_wide(v), by_doubling(fp, v), "2^{e} - 1 in F_{p}");
            }
            assert_eq!(fp.reduce_wide(u128::MAX), by_doubling(fp, u128::MAX));
            for _ in 0..2_000 {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                let v = (x as u128) << 64 | x.rotate_left(29) as u128;
                assert_eq!(fp.reduce_wide(v), by_doubling(fp, v), "in F_{p}");
            }
        }
    }
}

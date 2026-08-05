//! Prime fields F_p with construction-time primality checking.

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
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PrimeField {
    p: u64,
}

/// Exclusive upper bound on moduli.
const MODULUS_BOUND: u64 = 1 << 31;

/// Trial division over 2, 3, and 6k±1; exact for every `n` below 2^62.
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
    pub fn new(p: u64) -> Result<PrimeField, FieldError> {
        if p >= MODULUS_BOUND {
            return Err(FieldError::ModulusTooLarge(p));
        }
        if !is_prime(p) {
            return Err(FieldError::NotPrime(p));
        }
        Ok(PrimeField { p })
    }

    /// The characteristic p.
    #[inline]
    pub const fn modulus(self) -> u64 {
        self.p
    }

    /// The residue class of `v`, reduced into `0..p`.
    #[inline]
    pub fn elem(self, v: i64) -> Fp {
        Fp(v.rem_euclid(self.p as i64) as u64)
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

    /// a + b.
    #[inline]
    pub fn add(self, a: Fp, b: Fp) -> Fp {
        debug_assert!(
            a.0 < self.p && b.0 < self.p,
            "unreduced input in F_{}",
            self.p
        );
        let s = a.0 + b.0;
        Fp(if s >= self.p { s - self.p } else { s })
    }

    /// a - b.
    #[inline]
    pub fn sub(self, a: Fp, b: Fp) -> Fp {
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

    /// -a.
    #[inline]
    pub fn neg(self, a: Fp) -> Fp {
        debug_assert!(a.0 < self.p, "unreduced input in F_{}", self.p);
        if a.0 == 0 { a } else { Fp(self.p - a.0) }
    }

    /// a * b.
    #[inline]
    pub fn mul(self, a: Fp, b: Fp) -> Fp {
        debug_assert!(
            a.0 < self.p && b.0 < self.p,
            "unreduced input in F_{}",
            self.p
        );
        Fp(a.0 * b.0 % self.p)
    }

    /// a^-1, by the extended Euclidean algorithm.
    ///
    /// # Panics
    /// Panics if `a` is zero.
    pub fn inv(self, a: Fp) -> Fp {
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

    /// a^exp by binary exponentiation; `pow(a, 0)` is 1 for every `a`.
    pub fn pow(self, a: Fp, mut exp: u64) -> Fp {
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

    /// The entrywise inverse, with zero entries mapped to zero.
    ///
    /// Montgomery's trick: one field inversion plus three multiplications per
    /// nonzero entry.
    pub fn batch_inv(self, values: &[Fp]) -> Vec<Fp> {
        let mut prefix = Vec::with_capacity(values.len());
        let mut acc = Fp::ONE;
        for &v in values {
            if !v.is_zero() {
                acc = self.mul(acc, v);
            }
            prefix.push(acc);
        }
        let mut result = vec![Fp::ZERO; values.len()];
        let mut inv_acc = self.inv(acc);
        for i in (0..values.len()).rev() {
            if values[i].is_zero() {
                continue;
            }
            let before = if i == 0 { Fp::ONE } else { prefix[i - 1] };
            result[i] = self.mul(inv_acc, before);
            inv_acc = self.mul(inv_acc, values[i]);
        }
        result
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

    #[test]
    fn batch_inv_matches_inv_and_maps_zeros_to_zero() {
        let fp = f(101);
        let values: Vec<Fp> = [3, 0, 5, 100, 0, 0, 1, 42]
            .into_iter()
            .map(|i| fp.elem(i))
            .collect();
        let invs = fp.batch_inv(&values);
        assert_eq!(invs.len(), values.len());
        for (&v, &w) in values.iter().zip(&invs) {
            if v.is_zero() {
                assert!(w.is_zero());
            } else {
                assert_eq!(w, fp.inv(v));
            }
        }
        assert!(fp.batch_inv(&[]).is_empty());
        let zeros = vec![fp.zero(); 4];
        assert!(fp.batch_inv(&zeros).iter().all(|w| w.is_zero()));
    }
}

//! Ext groups over minimal resolutions: dimensions, global dimension,
//! [`ExtSpace`] and [`ExtClass`] as explicit vector space data, and Yoneda
//! products with their chain-lift witnesses.
//!
//! `Ext^k(M, N)` is the cohomology of `Hom_A(P_*, N)` for a projective
//! resolution `P_* -> M`. Every term built by
//! [`projective_cover`](crate::resolution::projective_cover) is a sum
//! `(+)_v P_v^{t_v}` in a canonical layout, and Yoneda identifies
//! `Hom_A(e_v A, N)` with `N_v`. So `Hom_A(P, N)` has an explicit basis indexed
//! by (generator, basis vector of `N` at the generator's vertex). The element
//! for generator `g` at `v` and index `j` sends the summand basis path
//! `p: v -> w` to row `j` of `N(p)`. Coordinates of a morphism in this basis are
//! its generator rows, read off directly. No linear system is solved.
//!
//! Sign convention: the induced cochain map is `delta^k(f) = d_{k+1}.then(f)`,
//! with no signs. Alternating signs exist to force `delta^2 = 0` under other
//! conventions for the differential; here it follows from `d^2 = 0`. A sign
//! choice rescales basis vectors and leaves every rank alone, so no dimension
//! depends on it.
//!
//! Exactness: [`ext_dim`]`(m, n, k)` resolves `m` for `k + 1` steps. The result
//! is either a complete finite resolution or a prefix with differentials
//! `d_1, ..., d_{k+1}`. Cohomology at position `k` needs only `d_k` and
//! `d_{k+1}`, so the answer is exact for every `k`, even when the projective
//! dimension is unknown.

mod foundation;
mod product;
mod space;

pub use foundation::{ExtError, ext_dim, ext_table, global_dimension};
pub use product::{ExtClass, ProductWitness};
pub use space::{ExtClassError, ExtSpace};

pub(crate) use foundation::{ext_table_from_resolution, lift_through};

#[cfg(test)]
mod tests;

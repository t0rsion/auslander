//! Minimal left `add(N)`-approximations, with factorization data and a
//! radical-containment minimality witness.
//!
//! Give `N` by its indecomposable summands `N_1, ..., N_k`, one module per
//! isomorphism class. A map `f: X -> B` with `B` in `add(N)` is a left
//! `add(N)`-approximation when every map `X -> N'` with `N'` in `add(N)`
//! factors through `f`. Testing the `N_i` is enough, since a map into a sum is
//! its components, and testing an `F_p` basis of each `Hom(X, N_i)` is enough,
//! since factorization through `f` is linear in the target map. The witness
//! stores the factorization coordinates of every basis map.
//!
//! `f` is left minimal exactly when `K_f = ker(End(B) -> Hom(X, B))` under
//! `h |-> f.then(h)` lies inside `rad End(B)`. `K_f` is a right ideal, so
//! `K_f` inside the radical says every `1 - u` with `u` in `K_f` is invertible,
//! which is the usual statement: `f.then(h) = f` forces `h` invertible. The
//! witness stores the RREF basis of `K_f` in `End(B)` coordinates together with
//! the coordinates that place each basis row inside `rad End(B)`.
//!
//! [`crate::arquiver::category_radical`] does not settle minimality when `B` is
//! decomposable. It is defined between two certified indecomposables, and the
//! criterion needs `rad End(B)` for the whole middle term. [`crate::endo::EndoAlgebra`]
//! supplies that radical exactly, over any prime field.
//!
//! # Multiplicities are dimensions over a division ring
//!
//! The number of copies of `N_i` in `B` is not `dim_{F_p} Hom(X, N_i)`. Write
//! `L = End(N)` and read `Hom(X, N)` as a right `L`-module. A map `f: X -> B`
//! with `B` in `add(N)` is a left approximation exactly when
//! `Hom(B, N) -> Hom(X, N)`, `h |-> f.then(h)`, is onto, and `f` is minimal
//! exactly when that map is a projective cover, because `Hom(-, N)` is a
//! duality from `add(N)` onto the projective right `L`-modules. So the
//! multiplicity of `N_i` is the multiplicity of the `i`-th simple in the top
//! `Hom(X, N) / Hom(X, N) rad L`, counted over the residue division ring
//! `D_i = End(N_i) / rad End(N_i)`. With `d_i = dim_{F_p} D_i` the residue
//! degree of `N_i`, an `F_p` basis of `Hom(X, N_i)` gives `d_i` times too many
//! copies. Over an algebraically closed field every `d_i` is 1 and the two
//! counts agree. That is the only place the algebraically closed hypothesis
//! enters this construction. The prime fields here have `d_i > 1`: the
//! Kronecker module `(I_3, C)` over `F_2` for `C` the companion matrix of
//! `x^3 + x + 1` has `End = F_8` and `d = 3`.
//!
//! [`left_approximation`] therefore picks generators over `D_i`, not over
//! `F_p`. See its docstring for the loop.

mod certify;
mod construct;
mod error;
mod linear;
mod witness;

pub use construct::left_approximation;
pub use error::{ApproxDefect, ApproxError};
pub use witness::MinimalLeftApproximation;

#[cfg(test)]
mod tests;

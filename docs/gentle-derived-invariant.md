# A complete derived invariant for gentle algebras

This note fixes the construction behind
`GentlePresentation::complete_invariant`. It extends the
Avella-Alaminos-Geiss (AAG) function by the line-field data that the AAG
function misses when the surface model has genus at least 1.

Statement numbers refer to these arXiv versions:

- [APS] C. Amiot, P.-G. Plamondon, S. Schroll, *A complete derived invariant
  for gentle algebras via winding numbers and Arf invariants*,
  arXiv:1904.02555v3; Selecta Math. (N.S.) 29 (2023), no. 2, paper 30.
- [LP] Y. Lekili, A. Polishchuk, *Derived equivalences of gentle algebras
  via Fukaya categories*, arXiv:1801.06370v5; Math. Ann. 376 (2020),
  187-225.
- [OPS] S. Opper, P.-G. Plamondon, S. Schroll, *A geometric model for the
  derived category of gentle algebras*, arXiv:1801.09659v7.

The printed versions may number statements differently. That numbering
was not checked.

## 1. Theorem

Let `k` be a field and `A`, `A'` finite-dimensional connected gentle
algebras over `k`. APS work over an arbitrary base field (section
"Conventions") and state no condition on the characteristic.

[APS, Theorem 4.1] `A` and `A'` are derived equivalent exactly when an
orientation-preserving homeomorphism of their marked surfaces preserves the
winding number of every simple closed curve. [APS, Theorem 5.4] turns this
into numbers. `A` and `A'` are derived equivalent exactly when:

1. the genus `g`, the number of boundary components, the number of marked
   points, and the number of punctures agree;
2. after a permutation, the pairs (marked points, winding number) of the
   boundary components and punctures agree;
3. when `g = 1`, the number `Ã` below agrees;
4. when `g >= 2`, one of three cases holds for both algebras: some winding
   number is odd; all winding numbers are even and some boundary winding
   number is divisible by 4; or all winding numbers are even, every
   boundary winding number is `2 mod 4`, and the Arf invariants agree.

The orbit classification behind items 3 and 4 is [LP, Theorem 1.2.4]. LP
alone give only the direction "equal invariants imply derived equivalent"
[LP, Corollary 3.2.4, with the Koszul duality of section 3.3]. APS prove
both directions. The library uses the invariant to separate algebras, which
needs the direction "derived equivalent implies equal invariants" from APS.

## 2. The surface of a gentle presentation

Write `n` for the vertex count and `M` for the number of permitted threads,
trivial ones included.

- Each permitted thread is one marked point on the boundary, and each
  vertex of `Q` is one arc of the dissection [APS, Definition 2.1 and
  Theorem 2.3; OPS]. The arcs at one marked point, in counterclockwise
  order, are the vertices of its permitted thread in path order.
- Every vertex lies on exactly two thread positions [LP, Remark 3.1.6]. In
  `Shape` terms, the pair (vertex `v`, sign `s`) is one position of one
  permitted thread: the position that leaves `v` through the outgoing slot
  `s`, filled or not. The arc `v` joins its two positions.
- The graph `Γ` with one node per permitted thread and one edge per vertex
  is a deformation retract of the surface minus its punctures [LP, section
  3.2, the ribbon graph `R_A` of the Koszul dual; APS, Proposition 1.12].
  So `H_1` of the surface is the cycle space of `Γ`, of rank `n - M + 1`.
- The boundary components and punctures are the pairs of the AAG function.
  A pair `(n_j, m_j)` has `n_j` marked points and boundary winding number
  `w(c_j) = n_j - m_j` [APS, Remark 4.2; LP, Theorem 3.2.2].

## 3. Winding numbers of closed walks

A closed walk in `Γ` traverses arcs. Between two arcs it turns at one
marked point, from position `p` to position `q != p` of that thread.

[APS, Proposition 1.20 (3) and (4)] Concatenating arcs at a marked point
adds `+1` when the point lies to the left of the curve and `-1` otherwise.
Arcs of the dissection have winding number 0 (proof of [APS, Theorem 4.1]),
so a closed walk has `w = ℓ - r`. Near a boundary point the arcs leave in
counterclockwise order, and the curve passes the point on the interior
side. The point lies to the left exactly when `q > p`. Hence

```
w(walk) = #{turns with q > p} - #{turns with q < p}.
```

[LP, Remark 3.2.6] gives the same count. For the Koszul dual with every
arrow in degree 1 [LP, section 3.3], a step forward along a thread adds
`1 - m + m = 1` and a step backward adds `-1`.

A cycle of `Γ` that visits each node once is a simple closed curve. The
fundamental cycles of a spanning tree are such cycles and form a basis
`z_1, ..., z_r` of `H_1(Σ; Z)`, where `Σ` is the surface minus its punctures.

Every invariant below is unchanged when all interior winding numbers change
sign together, or when the surface orientation is reversed. So the
orientation conventions of APS and LP cannot change a result.

## 4. The intersection pairing

The papers give no algorithm for a symplectic basis. [APS, Remark 5.6]
says that finding one "may be much more complicated in high genus". This is
the one step not taken from a numbered statement.

The pairing `J_kl = z_k · z_l` is computed in the thickening of `Γ`. Draw
`z_k` on the center line of each strip. Draw `z_l` on a parallel copy, to
the left of each arc oriented from its `+` position to its `-` position.
Near a marked point the copy sits at position `p + 1/2` at a `+` end and
`p - 1/2` at a `-` end. The two curves cross only near marked points, once
for each pair of turns whose position pairs interleave. A turn of `z_k`
from `a` to `b` crossing a turn of `z_l` from `a'` to `b'` counts
`sign(b - a)` when `a'` lies between `a` and `b`, and `-sign(b - a)` when
`b'` does.

Three checks pin this formula. `J` is antisymmetric, and the two entries
come from different drawings. The rank of `J` over `Q` and over `F_2` is
`2g`, with `g` from the AAG function [LP, equation (1.8)]. The radical of
`J` is the span of the boundary classes [LP, section 1.2].

A fundamental cycle is separating exactly when its row of `J` is zero.

## 5. The extra invariants

Let `W = {w(z_k)}` and `B = {n_j - m_j}` over the AAG pairs.

### Genus 0

Nothing more. The boundary winding numbers determine the line
field up to homotopy [LP, Theorem 1.2.4 (i)].

### Genus 1

[LP, equation (1.6)] defines

```
Ã = gcd(w(α), w(β), w(∂_1) + 2, ..., w(∂_d) + 2)
```

for nonseparating `α`, `β` that project to a basis of `H_1` of the closed
surface. The library computes

```
Ã = gcd({w(z_k) : z_k nonseparating} ∪ {b + 2 : b in B}).
```

The two agree by the following argument, built from [LP, section 1.1].
Let `η_0` be a translation-invariant line field on the torus, restricted to
`Σ`. A nonseparating simple closed curve of `Σ` is isotopic in the torus to
a geodesic, so `w_{η_0} = 0` on it. Each boundary curve bounds a disc in the
torus, so `w_{η_0}(∂_i) = -2` [LP, equation (1.3)]. Write `η = η_0 + c` with
`c` in `H^1(Σ; Z)`; then `w_η(γ) = w_{η_0}(γ) + <c, γ>`. So
`w_η = <c, ->` on nonseparating simple curves and `w_η(∂_i) + 2 = <c, ∂_i>`.
Both gcds equal the gcd of `c` over `H_1(Σ; Z)`. A separating `z_k` lies in
the span of the boundary classes, so it adds nothing.

### Genus at least 2

The value `σ` is 0 when every `w(z_k)` is even
[LP, Definition 1.2.1; APS, Proposition 1.4 (4)]. When `σ = 0` and every
`b` in `B` is `2 mod 4`, the Arf invariant is defined. Set

```
q(z_k) = w(z_k) / 2 + 1  (mod 2)
q(x + y) = q(x) + q(y) + x · y  (mod 2)
```

[APS, Lemma 5.5; LP, Proposition 1.2.2 and equation (1.5)]. The form `q`
vanishes on the radical of `J` and descends to `H_1` of the closed surface.
Its Arf invariant is `sum q(a_i) q(b_i)` over a symplectic basis. The
library finds that basis by symplectic reduction of `J mod 2`.

## 6. The value

`GentleDerivedInvariant` stores the AAG function, the genus, and one
`WindingClass`:

| Genus | Condition | Class | Display |
| --- | --- | --- | --- |
| 0 | none | `Planar` | `planar` |
| 1 | none | `Gcd(Ã)` | `gcd 2` |
| `>= 2` | some `w` odd | `Odd` | `odd` |
| `>= 2` | all even, some `b = 0 mod 4` | `Even` | `even` |
| `>= 2` | all even, every `b = 2 mod 4` | `Arf(0 or 1)` | `arf 1` |

`Display` prints `[(2, 4)], genus 1, gcd 2`. Two values are equal exactly
when [APS, Theorem 5.4] calls the algebras derived equivalent: the AAG
function carries items 1 and 2, and the class carries items 3 and 4.

## 7. Relation to the AAG function

The AAG function is the multiset of pairs `(n_j, n_j - w(c_j))` over the
boundary components and punctures [APS, Remark 4.2]. It fixes the marked
points on each component, the boundary winding numbers, the number of
punctures (pairs with `n_j = 0`), and the genus by
`sum (n_j - m_j + 2) = 4 - 4g` [LP, Corollary 3.2.3]. It also fixes `n`,
because a dissection has `M + P + b + 2g - 2` arcs [APS, Proposition 1.11].

So in genus 0 the complete invariant carries exactly the AAG function. The
extra data are needed exactly when `g >= 1`: `Ã` in genus 1, and `σ` with
the Arf invariant in genus at least 2. These depend on winding numbers of
curves that go around handles, which no boundary curve sees.

## 8. Validation

Paper examples, over `F_2` and `F_3`:

- [APS, section 7], first pair. `Λ_1` is `1 ⇉ 2 ⇉ 3` with relations
  `a_1·b_1` and `a_2·b_2`. `Λ_2` has arrows `a: 1 → 2`, `b: 2 → 3`, and
  `c, c': 3 → 1`, with relations `c·a`, `a·b`, `b·c'`. Both have AAG function
  `[(2, 4)]`. APS compute `Ã = 0` and `Ã = 2`, so they are not derived
  equivalent.
- [APS, section 7], second pair: six vertices, genus 1, boundary winding
  numbers `-3, 0, -3`. Both have `Ã = 1` and are derived equivalent.
- [LP, Example 3.3.3]: the Koszul dual of the six-vertex algebra there has
  AAG function `[(2, 4), (2, 4)]`, genus 1, and `w(α) = w(β) = 0`, so
  `Ã = 0`.

Consistency with existing tests:

- Genus 0: the class is `Planar` for every enumerated presentation of
  genus 0, and equal AAG functions give equal invariants.
- Relabeling: random relabelings from `classes_tests.rs` keep the value.
  A relabeling changes the spanning tree, so this checks basis independence.
- The Arf invariant from symplectic reduction equals the majority value of
  `q` over all of `H_1(Σ; F_2)` [LP, section 1.2].

The strongest check is the certified discovery corpus. Every target that
`discover_equivalences` recovers and recognition accepts must have the same
complete invariant as its source. `discovery_tests.rs` extends
`gentle_targets_agree` to compare `complete_invariant`, on the existing
sources, the genus-1 fixture there (two vertices, arrows `0 → 1`, `1 → 0`,
`0 → 1`, relations `a_2·a_1` and `a_1·a_0`), and both algebras of the first
APS pair.

Separation at `n = 4`: group the 894 connected gentle presentations by AAG
function and count the groups that the class splits. The complete invariant
splits no group of genus 0. A split of a group that discovery merged is a
defect.

## 9. Limits

- The intersection pairing of section 4 is derived here, not quoted. The
  rank and antisymmetry checks run on every call and panic as a library bug.
- APS state their results over any field. [Opper, arXiv:1904.04859,
  Theorem B] proves Theorem 4.1 independently over an algebraically closed
  field. No test covers a field other than `F_2` and `F_3`.
- A fundamental cycle has at most `n` turns, so `|w(z_k)| <= n`.

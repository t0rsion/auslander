# Checked computation results

This document states the checked computation results used by the current
release. It does not rename an established representation-theoretic theorem as
a new result.
Each statement names the implementation boundary that depends on it.

## Fixed-pattern relation specialization

Let `A = kQ/I` use the reduced Groebner basis stored by [`Algebra`]. Fix a
dimension vector, an arrow-major coordinate layout, fixed entries, and named
parameter entries. Unnamed entries are zero.

**Proposition 1.** `CompiledModuleFamily::specialize` accepts a parameter
vector exactly when `Module::new` accepts the same arrow matrices.

For each reduced relation, `RelationEvaluationLayout` stores every coefficient
and arrow sequence in its stored order. Specialization starts with the identity
at the relation source. It multiplies the selected arrow matrices from left to
right, scales each path action, and adds the result. These are the operations
in `Module::new`.

`FamilyLayout` fixes the map count and each matrix shape. Fixed and parameter
entry checks prove field canonicity. The compiled zero test therefore
discharges every generic constructor obligation. Debug builds run
`Module::new` on the same data and compare acceptance.

The proposition removes repeated layout construction. It does not remove the
matrix products needed to evaluate a relation at a new fiber.

## Fixed-pattern Hom specialization

Two fibers of one `CompiledModuleFamily` have the same dimension vector. At a
vertex `v`, both source and target Hom matrices are square of size `d_v`.

**Proposition 2.** `CompiledModuleFamily::hom_space` returns the same ordered
flat basis as `HomSpace::new` on the same two fibers.

Both paths order the variable `f_v[r,c]` by vertex, row, and column. For an
arrow `a: u → v`, both add one equation for each pair `(i,j)`:

```text
sum_c f_u[i,c] N(a)[c,j] - sum_r M(a)[i,r] f_v[r,j] = 0.
```

`HomEquationLayout` stores the same variable and coefficient positions.
`SparseRow::from_entries` combines a repeated variable, which covers loops,
and drops a zero coefficient. Both paths drop an all-zero equation. They then
call the same deterministic sparse kernel reduction.

Debug builds compare the exact flat basis with `HomSpace::new`. The result
does not permit reuse of a reduced form across fibers. Such reuse needs proved
rank-stratum conditions.

## Separator Hom equalizer

Let the vertices split into a left interior, an interface, and a right
interior. Assume no arrow joins the two interiors. Assume no reduced relation
uses both interiors.

**Established theorem.** A global module morphism is a pair of piece
morphisms whose vertex maps agree on the interface.

`InterfacePartition::new` checks the two hypotheses. `InterfaceHomPlan`
builds the two piece kernels, restricts both bases to the interface, and takes
their equalizer. It lifts each equalizer row to a global morphism through
`Morphism::new`.

The final equalizer has one column per piece basis element and one row per
interface map coordinate. Once the two piece bases exist, its dimensions do
not depend on the interior variable counts. Piece basis construction still
depends on the piece sizes.

The equalizer theorem is established. The checked bound-quiver hypotheses,
deterministic lift, and exact work record are implementation results.

## Fixed-interior family Hom reduction

Fix one compiled family and one checked interface. Every parameter lies on an
arrow whose endpoints are in the interface. Let `C` be the constant Hom
constraint matrix for all other arrows, and let `K` be its canonical kernel
basis. Let `J` contain the Hom variables used by interface-arrow equations.

For a fiber pair, let `D_J` be the interface constraint matrix restricted to
the columns in `J`. Write `K_J` for the same columns of `K`.

**Proposition 3.** `InterfaceFamilyHomPlan::compute` returns the same ordered
flat basis as `HomSpace::new` on the two specialized fibers.

Every solution of `C x^T = 0` has a unique expression `x = c K`. Its
interface equations are

```text
D_J K_J^T c^T = 0.
```

The compiler therefore returns `H K`, where `H` is the canonical kernel basis
of `D_J K_J^T`. The free coordinates of `K` are an identity matrix. Kernel
elimination on `D_J K_J^T` therefore selects the same remaining free
coordinates, in the same order, as elimination on the full stacked matrix
`[C; D]`.

Compilation builds `C`, `K`, `J`, and `K_J` once. A fiber pair assembles only
`D_J` and eliminates a matrix with `dim ker(C)` columns. The final lift writes
the global basis, so its output cost still depends on the global Hom-variable
count. The result makes no Ext claim and does not bound `dim ker(C)` by the
interface size.

## Hereditary family Ext reduction

Let `A = kQ` be finite-dimensional, so `Q` is acyclic. For right modules
`M` and `N`, the standard projective resolution gives the exact sequence

```text
0 → Hom_A(M,N) → ⊕_v Hom_k(M_v,N_v)
  → ⊕_{a:u→v} Hom_k(M_u,N_v) → Ext^1_A(M,N) → 0.
```

The middle map is the commuting-square matrix used by the Hom calculation.
Let its fixed and interface row blocks be `C` and `D`. Keep the notation `J`
and `K` from Proposition 3.

**Proposition 4.** `InterfaceFamilyHereditaryPlan::compute` returns exact Hom
and Ext dimensions for every fiber pair. It returns zero in every Ext degree
above one.

The standard resolution has length one. Its first cochain map has one row for
each coordinate in `Hom_k(M_u,N_v)` over an arrow `a: u -> v`. Therefore

```text
dim Ext^1_A(M,N) = arrow_cochains - rank [C; D].
```

Every row of `D` uses only columns in `J`. The kernel decomposition from
Proposition 3 gives

```text
rank [C; D] = rank C + rank(D_J K_J^T).
```

The plan stores `rank C` once. Each fiber pair computes the second rank while
it computes Hom. `InterfaceFamilyHereditaryPair::verify` rebuilds the plan and
recomputes `Ext^1` and `Ext^2` through `ExtSpace::new`.

The formula does not apply to a nonzero relation ideal. The compiler rejects
that case before returning a hereditary plan.

The family record compares compiled and generic Hom on identical
fibers. At A16 interface width 2, compiled modules take 49692.3 ns/op and
generic Hom takes 96228.3 ns/op. At width 8, compiled modules take 286284.8
ns/op and generic Hom takes 89865.2 ns/op. Compilation is not a universal
speedup. The raw record and machine limits are in
[`compiled-family-performance.md`](compiled-family-performance.md).

## Locality under one tilting mutation

Let a tilting-complex candidate have `n` ordered summands. Its classification
uses a homotopy quotient for an ordered source, target, and shift degree.

**Proposition 5.** If mutation replaces only summand `r`, every cached block
whose two endpoints differ from `r` remains valid. For each fixed degree,
`(n - 1)^2` ordered blocks can remain, and at most `2n - 1` ordered blocks
touch the changed summand.

A homotopy quotient depends only on its source complex, target complex, and
degree. Mutation leaves every other summand unchanged. `HomotopyBlockCache`
checks structural agreement of both endpoints before reuse. It discards every
block in the changed row or column.

The work record counts built and reused blocks. Classification still checks
every required shift and the generation witness. The proposition does not
claim a local update for the target algebra's two-sided Groebner basis.

## Bounded self-pair retention

`HomologicalSelfPairStream` pulls one source chunk before it builds an ordinary
`HomologicalBatch`.

**Proposition 6.** The stream itself passes at most `max_live_sources` modules
to a live batch and retains no completed chunk.

`chunk_capacity` is the minimum of the live-source, pair, and Ext-cell
capacities. `next_chunk` takes at most that count. It returns the completed
chunk by value and keeps no reference to it.

The caller can retain returned chunks and exceed this process-wide bound.
Dropping each chunk after its rows are written gives the stated retention
bound. `peak_live_sources` records the largest completed chunk.

## Portable prefix replay

The portable computation format stores no nominal module or algebra identity.
It stores a completion certificate, coordinate order, cursor, exact counters,
and retained witnesses.

**Proposition 7.** A live checkpoint becomes resumable only when a
fresh process rebuilds the algebra and reproduces its completed prefix.

`verify_census_portable` applies bounded canonical parsing, verifies the
embedded completion certificate, rebuilds a fresh algebra, reconstructs the
stored modules and witnesses, and replays the exact census outcome. Only the
returned `VerifiedCensus` exposes direct resume. Fresh-process command tests
exercise inspection, verification, canonicalization, and fingerprinting.
The corruption corpus rejects altered domain fields, counters, witnesses, and
fingerprints.

A checksum alone is not the proof. It detects an accidental byte change
before mathematical replay. Replay uses the public census semantics. It is
not a second isomorphism algorithm.

## Certified commutative-square loci

Let `A` be the commutative square over `F_2`, with relation `ab - cd`. Arrow
order is `(a,b,c,d)`.

**Proposition 8.** At dimension vector `[1,1,1,1]`, the raw domain contains 10
isomorphism classes. Exactly the class with coordinates `[1,1,1,1]` has
vanishing self-Ext in every degree from 1 through 3.

The raw domain has 16 tuples. Complete census replay accepts 10 and rejects 6.
It records 45 isomorphism checks and 61 work units. The complete homological
checkpoint computes 10 self-pairs in five chunks with two live sources.

The theorem artifact lists representative index 9. Verification rebuilds the
census, replays every stored row, and recomputes the locus through
`ExtSpace::new`. That constructor is the crate's generic Ext path. The locus
check can stop at the first mismatch.

**Proposition 9.** At dimension vector `[2,1,1,2]`, the raw domain contains 256
tuples and 58 accepted modules. The census retains 12 representatives. Degree 1
vanishes at indices `[5,10,11]`. Degrees 1 through 3 vanish at `[5,10]`.
Representative 11 has Ext dimensions `[5,0,1,0]` and is isomorphic to
`P_0 + S_0 + S_3`. A finite hand count of accepted modules is `58 = 7^2 + 9`.

Complete census replay rejects 198 candidates, records 439 isomorphism checks,
and uses 695 work units. The complete homological checkpoint computes 12
self-pairs in six chunks with two live sources.

Both propositions are checked finite computations. Each covers only its stated
field, dimension vector, and degree interval. Neither classifies the module
category. The committed bytes and reproduction commands are in
[`commutative-square-study.md`](commutative-square-study.md).

## Limits

These results apply over the checked prime fields supported by the crate.
They make no uniform-rank claim across a module family. They do not reduce
truncated Ext over a nonzero relation ideal without extra projectivity or Tor
hypotheses.
They do not turn a finite catalog into a global classification without a
coverage certificate.

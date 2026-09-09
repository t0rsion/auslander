# Checked higher homology

This document fixes the checked higher-homology layer. A deviation needs a
documented reason and a design update in the same change.

The certified algebra layer established checked construction. The witnessed AR
layer put homological answers in checked objects. Support tau-tilting made a
complete enumeration depend on a closure certificate. This layer adds the
checked complex needed for higher homological claims.

A checked module complex decides exactness. The relative normalized bar
complex computes Hochschild cohomology under explicit limits. A checked
exact complex certifies the generation condition for classical tilting
modules of any finite projective dimension reached by the caller's bound.

## 1. Scope

In scope:

- Finite complexes of right modules and checked morphisms.
- Exact homology dimension vectors at every term.
- Exact complexes and a witness at the first nonexact term.
- Relative normalized bar Hochschild cohomology with deterministic bases.
- Limits on tensor tuples, cochain dimensions, matrix entries, and work.
- A typed cut that retains only cohomology degrees completed before the cut.
- Classical tilting modules with projective dimension and generation length
  within caller bounds.
- Automatic construction of the generation complex through minimal left
  `add(T)`-approximations.
- Rust and Python APIs for the full release path.
- Independent checks against a full bar complex, the center, derivations, and
  GAP with QPA where QPA has the required operation.
- Memoized primitive computations within one top-level verification.
- A production code count below the preceding baseline.

Out of scope: cup products, Gerstenhaber brackets, arbitrary coefficient
bimodules, a public enveloping algebra, derived equivalences, tilting
enumeration, infinite complexes, characteristic zero, and wall-clock limits.
The Hochschild layer returns graded vector spaces through the requested
degree. It does not return the Hochschild ring.

## 2. Finite module complexes

`CheckedComplex` stores nonempty `terms` and `maps` in display order:

```text
terms[0] --maps[0]--> terms[1] --maps[1]--> ... --> terms[r]
```

Every term lives over one algebra value. `maps[i]` has the nominal endpoints
`terms[i]` and `terms[i + 1]`. The constructor checks each composite
`maps[i].then(maps[i + 1])` is zero. It rejects a bad endpoint or a nonzero
composite as `ComplexError`. It never repairs or rebinds a map.

The type uses display order instead of homological degree. This makes a short
exact sequence read `N -> E -> M` and a tilting generation complex read
`A -> T^0 -> ... -> T^n`. A projective resolution reverses its stored terms
when it enters this type.

At term `i` and vertex `v`, the homology dimension is

```text
dim terms[i]_v - rank maps[i - 1]_v - rank maps[i]_v,
```

where an absent map has rank zero. The checked zero composite puts the
incoming image in the outgoing kernel, so the difference is nonnegative and
exact. `HomologyDimensions` stores the term index and the full dimension
vector. The name does not claim that the type stores the quotient module.

`CheckedComplex::exactness()` returns one of two values:

- `ExactnessOutcome::Exact(ExactComplex)`, after every homology dimension is
  zero.
- `ExactnessOutcome::NotExact(NonExactWitness)`, with the first term whose
  homology dimension vector is nonzero.

`ExactComplex` has no public unchecked constructor. Its `verify()` repeats the
endpoint, zero-composite, and rank checks. `NonExactWitness::verify()` repeats
the same checks and requires its stored index and dimension vector to be the
first nonzero result. A one-term complex is valid and is exact only when its
term is zero. An empty term list is rejected.

Verification of one stored complex uses nominal endpoints. Verification of a
complex rebuilt by another certificate compares each term entrywise: the
dimension vector and every arrow matrix must agree. It compares each map by
the same endpoint positions and every vertex matrix. Fresh allocation alone
cannot make a recomputed complex fail.

`ProjectiveResolution::checked_complex()` turns stored terms
`P_0, ..., P_l`, maps
`d_1, ..., d_l`, and the augmentation into

```text
P_l -> ... -> P_0 -> M.
```

It reverses the term and differential lists, then appends the augmentation. A
cut resolution returns `ResolutionComplexError::Cut` and makes no exactness
claim. The fields of `ProjectiveResolution` are public, so malformed finite
data returns `Invalid` or `NotExact` rather than panicking.

This layer does not duplicate kernels, images, or quotient construction.
Callers that need those module objects use `hom::{kernel, image, cokernel}`.

## 3. The relative normalized bar complex

Let `S` be the span of the vertex idempotents and `J = rad A`. For a bound
quiver algebra with an admissible ideal,

```text
S = product_v F_p e_v
```

is separable and the nontrivial normal words form a basis of `J`. The
`S`-relative normalized bar resolution therefore computes ordinary
Hochschild cohomology. This construction works for several vertices and does
not assume an augmentation `A -> F_p`.

Admissibility puts every relation in the square of the arrow ideal and a high
enough arrow-ideal power inside the ideal. Thus the vertex idempotents survive
as `S`, every other normal word lies in `J`, and `A = S + J` is a direct sum of
`S`-bimodules. These are required properties of every `Algebra` value, not
assumptions accepted from a caller.

The degree `n` input basis consists of composable `n`-tuples of nontrivial
normal-word indices. For `n = 0`, the input is an empty tuple tagged by one
vertex. A cochain coordinate adds an output normal word in
`e_source A e_target`. Tuples use lexicographic basis-index order. Outputs use
`Algebra::paths_between` order.

Write `C^n` for the resulting coordinate space and `D_n` for the row-action
matrix `C^n -> C^(n + 1)`. For inputs `(a_1, ..., a_(n + 1))`, the differential
is

```text
a_1 f(a_2, ..., a_(n + 1))
+ sum_i (-1)^i f(..., a_i a_(i + 1), ...)
+ (-1)^(n + 1) f(a_1, ..., a_n) a_(n + 1).
```

The middle sum uses `i = 1, ..., n`. Each product expands through
`Algebra::mul_basis`. Signs use `PrimeField::neg`, including in characteristic
two. Products compose left to right, as every other product in the crate.

For `n = 0`, a coordinate belongs to one vertex component and

```text
(D_0 f)(a) = a f(e_target(a)) - f(e_source(a)) a.
```

The implementation checks `D_(n - 1) D_n = 0` before it publishes degree
`n`. A failure is a crate defect, not a cut and not a zero cohomology group.

For degree `n`:

- cocycles are the left kernel of `D_n`;
- coboundaries are the row space of `D_(n - 1)`;
- representatives use the crate-wide deterministic complement rule.

`HochschildDegree` stores its cochain coordinate basis as tuple ranks and
output indices, plus all three RREF bases. It decodes a tuple rank only when
an accessor needs the tuple. `dim()` is the number of complement rows.
`HochschildClass` stores coordinates in that complement and evaluates its
representative on one bar input tuple. Evaluation rejects a tuple of the
wrong degree, a trivial or non-normal input, and noncomposable indices. It
never normalizes bad input. Class coordinates are stable for the same
algebra, field, degree, and sealed normal-word order.

`bar_hochschild(algebra, max_degree, limits)` returns
`HochschildOutcome::Complete` or `HochschildOutcome::Cut`. A complete result
contains exact `H^0` through `H^max_degree`. A cut contains only degrees for
which the outgoing differential, the zero-square check, and the quotient
bases all finished.

Both outcomes store the requested degree and effective limits. `verify()`
recomputes the same prefix. It compares the tuple and coordinate order, every
stored differential, the cocycle and coboundary RREF bases, the complement,
and the diagnostics. Verification of a cut must reach the same first blocked
reservation. It preflights every shape again before allocation.

## 4. Bar limits

`BarLimits` has four independent ceilings:

```text
max_tensor_tuples
max_cochain_dim
max_matrix_entries
max_work_units
```

There is no wall-clock limit. Rust callers pass all four ceilings. Python
callers do the same through one immutable limits value. Tuple and cochain
ceilings apply to each degree. The matrix ceiling covers cumulative stored
entries plus the largest live scratch reservation. Work is cumulative across
the request.

The radical adjacency matrix has entry

```text
R[u, v] = number of nontrivial normal words from u to v.
```

`R^n[u, v]` counts degree `n` input tuples from `u` to `v`, with `R^0` the
identity. `max_tensor_tuples` bounds `sum_(u,v) R^n[u,v]` separately at each
materialized degree. The cochain dimension is

```text
c_n = sum_(u,v) R^n[u, v] dim(e_u A e_v).
```

The preflight computes these counts with checked arithmetic. It checks tensor
tuples before tuple traversal, `c_n` before cochain allocation, and
`c_n c_(n + 1)` before differential allocation. Tuple traversal is streamed.
The implementation never stores all degree `n` tuples. Arithmetic overflow is
`BarCutReason::SizeOverflow`, never a panic or wrapped count. `BarCutReason`
also names each of the four caller ceilings.

One work unit is one deterministic loop-cell visit. It is not one API call and
not elapsed time. For a degree `n` differential, with `t_(n + 1)` input tuples
and `d = dim A`, the reservations are:

```text
degree record: 1
shape recurrence: r^3 + r^2
tuple and coordinate scan: t_(n + 1) (n + 1) + c_n
dense zero-fill: c_n c_(n + 1)
differential terms: c_n t_(n + 1) (n + 2) (d + 1)
square check: c_(n - 1) c_n c_(n + 1)
```

The first reservation happens before any degree result, including a
zero-dimensional one. It prevents an unbounded request over a semisimple
algebra from allocating uncharged empty records. The shape formula covers one
adjacency-power step and its sums. The next formula counts each tuple entry
and source coordinate. The
differential formula reserves one branch visit and at most `d` multiplication
support visits for every formula term. The square check streams each output
entry and allocates no product matrix.

For an `r` by `c` matrix, one transpose reserves `r c` units. One RREF or
row-space elimination reserves

```text
E(r, c) = r c + min(r, c) (1 + 2 c + 2 r (c + 1)).
```

The first term covers pivot searches. Each possible pivot then covers one
inverse, row-swap and normalization visits, and forward and backward factor
and cell visits. A left kernel reserves `r c + E(c, r) + r^2`, including
transpose and its largest possible output. A deterministic complement with
`z` cocycle rows, `b` coboundary rows, and width `c_n` reserves
`E(z + b, c_n)`. All products and sums use checked `u128` arithmetic before
conversion to the public `u64` counter.

The matrix ceiling counts the differentials and RREF bases retained in every
completed degree. Before each operation, it adds a conservative live scratch
reservation: the input clone, transpose where used, elimination buffer, and
largest possible output. It releases scratch after the operation and retains
the actual output entry count. Thus a zero-column differential cannot admit
an unbounded `c_n` by `c_n` left-kernel basis.

For an `r` by `c` differential, the left-kernel scratch reservation is
`2 r c + r^2`. A row-space basis reserves `2 r c`. For `z` cocycle rows, `b`
coboundary rows, and width `w`, the complement reserves
`(min(z + b, w) + 2 z) w`. A new differential first requires
`stored_entries + r c <= max_matrix_entries`. Each later operation requires
`stored_entries + scratch_entries` under the same ceiling. Its actual output
entries join `stored_entries` only after the operation finishes.

`BarBudgetDiagnostics` records the completed degrees, the first uncomputed
differential, the used and proposed counts, the ceiling, and the first
blocking reservation. A cut happens before the rejected allocation or dense
operation. A rerun with that ceiling raised can expose a later limit.

## 5. Classical tilting

A basic module `T` is classical tilting when three conditions hold for some
finite `n`:

1. `pd T <= n`.
2. `Ext^i(T, T) = 0` for every `i > 0`.
3. There is an exact complex
   `0 -> A -> T^0 -> ... -> T^n -> 0` with every `T^i` in `add(T)`.

`classify(t, limits)` first builds a `BasicDecomposition`. `TiltingLimits`
contains `max_projective_dimension` and `max_generation_steps`. The first
bound limits the resolution. A cut records the genuine lower bound. It does not
claim that `T` has infinite projective dimension or that `T` is not tilting
for a larger bound.

When the resolution finishes with projective dimension `p`, only degrees
`1..=p` need an Ext check. Higher Ext groups vanish from the finite
resolution. The first nonzero space returns `NotTilting` with its degree and
positive dimension.

The generation check starts with the regular right module
`A = direct_sum_v P_v`. At stage `i`, it builds the minimal left
`add(T)`-approximation

```text
f_i: K_i -> T^i,
```

with `K_0 = A`. The map must be mono. Its cokernel is `K_(i + 1)`. The next
displayed map is the cokernel projection followed by `f_(i + 1)`. The process
stops when the cokernel is zero. `max_generation_steps` bounds the number of
approximation maps. If `f_m` first has zero cokernel, the stored complex is
`A -> T^0 -> ... -> T^m`; it has no trailing zero terms. A non-monic map or a
nonzero last cokernel blocks this bounded construction.

Successive minimal left approximations are the construction route, not one
arbitrary proposed complex. A failed bounded construction does not prove that
no longer `add(T)`-coresolution exists. It returns `Undetermined` with the
first non-monic stage or the final nonzero cokernel dimension vector. It never
becomes `NotTilting`.

The built sequence enters `CheckedComplex` as

```text
A -> T^0 -> ... -> T^m
```

and must produce `ExactComplex`. Every `T^i` also gets an
`AddClosureWitness` against the stored basic decomposition. The accepted
`ClassicalTiltingModule` stores the complete projective resolution, the zero
Ext spaces, the exact generation complex, and all add-closure witnesses.
`verify()` recomputes every condition from the live module.

The classification has three mathematical outcomes:

- `Tilting`, with `ClassicalTiltingModule`.
- `NotTilting`, only after projective dimension is known finite and a positive
  self-extension is found.
- `Undetermined`, with a projective-dimension lower bound or a blocked bounded
  generation construction. It leaves the global tilting question open.

The non-monic generation blocker stores its kernel dimension vector and the
checked minimal approximation, plus its stage. The step blocker stores the
last nonzero cokernel, its dimension vector, and the maps built before it.
Each blocker has `verify()`, which rebuilds the same minimal approximations
through its recorded stage. Neither is reduced to a message string.

Invalid endpoints, a non-basic input, and a blocked decomposition remain
typed errors. They are not mathematical outcomes.

## 6. Verification context

One top-level verifier creates one private `VerificationContext`. The context
memoizes only certified primitive computations on their exact nominal
operands: opposite algebras, endomorphism algebras, Hom dimensions, tau,
decomposition, and basic-pair isomorphism.

A memo stores successes and exact failures. It never stores a witness verdict.
A hit can replace a repeated computation, but it cannot replace endpoint
binding, comparison with stored data, or `verify()` itself. Keys own their
module and algebra clones, so address reuse cannot identify a later value.

`ClosureWitness::verify` owns the context. Its context-aware routes cover pair
identity, tau-rigidity, approximations, mutations, and their nested basic and
isomorphism checks. No public signature takes a context. Tilting uses the same
primitive helpers where its verification reaches them, but the release claim
does not depend on a tilting benchmark.

The internal entry points use the suffix `_with_context`; the public entry
points create an empty context and call them. `TauCache` remains the
construction cache for one ordered summand list. A context memo never reads or
warms a `TauCache`. There is no general `is_isomorphic` memo: its witnesses
bind fresh endpoints. Only `pair_iso` is memoized, with the full ordered basic
pair in its key.

The release benchmark records call totals, distinct nominal operands, context
hits, and context misses. A complete closure verification must show fewer
primitive computations with the context than without it. Equal wall time is
not evidence either way.

The always-on test `context_reduces_d4_closure_rechecks` builds the closed D4
graph over `F_5`, fingerprints the verified result, and verifies it through
both routes under the `profiling` feature. The fingerprints must match. The
sum of calls at `hom_dim`, `tau`, `EndoAlgebra::new`, `decompose`, and
`pair_iso` must be lower with the context. The test also asserts at least one
hit and one miss, so a disconnected memo cannot pass.

## 7. Python boundary

Python exposes the same distinctions as Rust:

- `CheckedComplex`, `ExactComplex`, `NonExactWitness`, and
  `HomologyDimensions`.
- `BarLimits`, complete and incomplete Hochschild results,
  `HochschildDegree`, and `HochschildClass`.
- `ClassicalTiltingModule` and its three classification outcomes.

`CheckedComplex(terms, maps)` exposes `terms`, `maps`, `verify()`,
`homology_dimensions(index)`, and `exactness()`. Exactness returns an
`ExactComplex` or `NonExactWitness`. The witness exposes `index`,
`dimension_vector`, and `verify()`.

`Algebra.hochschild_cohomology(field, max_degree, limits)` returns
`HochschildCohomology` or `IncompleteHochschildCohomology`. The complete class
has `degree(index)`. The incomplete class has `completed_degrees`, `reason`,
`diagnostics`, and `verify()`, but no accessor that can name an uncomputed
degree.

`ClassicalTiltingModule.classify(module, limits)` returns
`ClassicalTiltingResult`. Exactly one of `tilting`, `rejection`, and `blocker`
is set. Its `is_tilting` is `True`, `False`, or `None` in the same order.

Bad shapes, endpoints, and a nonzero composite in a supplied complex raise
`ValueError`. A bar cut is an incomplete value, not an exception. A nonzero
square in the crate-generated bar differential raises `DefectError`. Long
bar, tilting, and verification calls release the GIL.

`HochschildError::DifferentialSquare` maps to `DefectError`. Limit reasons and
their used, proposed, and ceiling counts are attributes on the incomplete
value, not exception text. `test_higher_homology_long_calls_release_gil` runs a Python
thread counter while bar and tilting calls execute and requires the counter to
advance.

Only a complete Hochschild result has the requested-degree accessor. An
incomplete result exposes its completed prefix, reason, and diagnostics. A
projective-dimension or generation blocker maps the unbounded Python
`is_tilting` property to `None`, never `False`.

## 8. Independent checks

The production Hochschild implementation is the relative normalized bar
route. Tests compare it with three independent routes:

- a full unnormalized bar complex on small algebras;
- `H^0` from a separate center commutator system;
- `H^1` from derivations modulo inner derivations.

Hand-derived fixtures pin these dimensions:

- `F_p^r`: `(r, 0, 0, ...)`;
- connected linearly oriented `A_r`: `(1, 0, 0, ...)`;
- `F_5[x]/(x^2)`: `(2, 1, 1, ...)`;
- `F_2[x]/(x^2)`: `(2, 2, 2, ...)`.

The characteristic-two fixture pins the signs. Nonmonomial and inhomogeneous
fixtures pin reduction through the verified multiplication table. Fresh
processes must reproduce the tuple order, all three RREF bases, dimensions,
and cut diagnostics.

The full bar test has its own tuple enumerator and differential builder. It
shares only the algebra multiplication table and dense linear algebra with
the production route. It is not the relative builder under a normalization
flag.

QPA 1.36 has classical tilting but no Hochschild operation. The QPA oracle
checks the tilting route only. Schema v8 adds designated classical-tilting
candidates. Each record names its construction, the bound, QPA's result,
projective dimension when QPA accepts, and the dimension vectors of every term
in each projective coresolution QPA returns. Candidate identity never comes
from a dimension-vector lookup.

Before QPA's boolean becomes oracle truth, the generator calls
`IsExactSequence` on every returned finite complex. This checks the last term
against QPA's terminal zero differential. The reader requires every
`coresolutions_exact` entry to be true. A false entry rejects the document, so
no part of that QPA boolean becomes oracle truth.

A live GAP and QPA run must produce the committed oracle data. One designated
projective-dimension-one candidate over `F_5` is the control. The
projective-dimension-two records over `F_2` and `F_5` test the generalized
path. The library never generates expected QPA data from its own answers.

## 9. Release gates

The release requires all of these gates:

- Every Rust test passes on the pinned toolchain and MSRV 1.88.
- Clippy passes for all targets with warnings denied.
- Rustfmt and rustdoc pass.
- The Python wheel builds, installs, and passes its full test suite.
- `QPA_ORACLE=1 cargo test -p auslander --test qpa_oracle` passes against the
  installed live GAP and QPA. This is a separate required release command.
- Complex and Hochschild mutation tests reject altered maps, signs, products,
  bases, dimensions, and cut records.
- The production code count is at most 16,113 under
  `tests/production_line_budget.rs`. The constant does not move.
- No production item sits below the first test module to escape that count.
- Both production budget tests lose their `#[ignore]` attributes before the
  release, so ordinary CI enforces them.
- The repository contains the design, changelog, and oracle provenance. The
  crate package contains its declared README and both licenses.
- Every manifest declares the same package version.

The code-count gate is a release condition, not a target. Comments do not
count. Moving code outside the scanned crate does not satisfy the design.

The deletion pass first removes the dead context allowance and collapses its
specialized memo boilerplate. It then extracts the representation and map
comparison repeated by complex, tilting, and existing verifiers. The bar and
tilting layers reuse `DenseMat`, `deterministic_complement`,
`left_approximation`, `AddClosureWitness`, and resolution data. They do not
copy the removed tilting module. Further deletion comes from shared
checked helpers in the largest source files, without sharing the completion
engine with its independent verifier.

## 10. Acceptance examples

One Rust example and one Python test run the full release path over two
fixtures.

For `A = F_p Q/(ab)` with `Q: 0 -> 1 -> 2`, let

```text
T = D(A) = I_0 + I_1 + I_2 = S_0 + P_0 + P_1.
```

The gates run over `F_2` and `F_5`. They require dimension vector `[2, 2, 1]`,
projective dimension two, and the generation term dimension vectors

```text
[1, 2, 2] -> [1, 3, 2] -> [1, 1, 0] -> [1, 0, 0].
```

The second Ext argument is injective, which independently gives
`Ext^i(T,T) = 0` for positive `i`. The checked complex supplies the generation
claim.

For `F_p[x]/(x^3)`, the bar route computes through degree two and a lower work
ceiling cuts before the next nonzero differential. The two fixtures together:

1. Build a nontrivial checked exact complex.
2. Compute `H^0`, `H^1`, and `H^2` through the relative bar route.
3. Force the next bar differential to cut under one stated limit.
4. Certify a classical tilting module of projective dimension two.
5. Recheck the exact generation complex and every stored witness.

The regular module supplies the projective-dimension-zero control. The
linear-A3 candidate `S_0 + P_0 + P_2` is the named
projective-dimension-one oracle control. The generator checks the
projective-dimension-two example over `F_2` and `F_5` against a live GAP and
QPA run.

## 11. Files and metadata

The Rust surface adds `complex.rs`, `hochschild.rs`, and `tilting.rs` and
exports them from `lib.rs`. Python adds wrappers and tests in the existing
binding crate. `README.md`, `crates/auslander-py/README.md`, `ROADMAP.md`, and
`CHANGELOG.md` describe the same public names and limits.

`crates/auslander/Cargo.toml`, `crates/auslander-py/Cargo.toml`,
`crates/auslander-py/pyproject.toml`, and `Cargo.lock` declare the same package
version. The release workflow still derives its version from the tag and must reject any
manifest mismatch.

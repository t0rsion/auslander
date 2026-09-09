# Classical tilting workbench

This document specifies the classical tilting component. The public package also
includes the [derived workbench](derived-equivalence-workbench.md). A deviation
needs a documented reason and a design update in the same change.

The checked higher-homology layer certifies a classical tilting module `T` over
a bound quiver algebra `A`. The workbench recovers a split bound quiver
presentation of its target algebra,
checks the resulting derived-equivalence certificate, and realizes the
equivalence on bounded complexes in the additive closure of `T`.

The workbench also adds bounded graded self-Ext algebras and the homotopy layer
needed to check maps between bounded complexes.

## 1. Scope

In scope:

- A deterministic bound quiver presentation of the split target algebra.
- A separate verifier for the target presentation and its algebra map.
- A typed unsupported result when the target is not split over the prime
  field.
- Limits on radical products, path enumeration, relation terms, and algebra
  completion.
- Bounded graded self-Ext algebras with explicit Yoneda product tensors.
- Degree-indexed bounded complexes, chain maps, homotopies, shifts, direct
  sums, cones, and Hom modulo null-homotopy.
- A certificate that the source and recovered target are derived equivalent.
- Strict transport between bounded `add(T)` complexes and bounded projective
  target complexes.
- Rust and Python APIs for every mathematical outcome and every cut.
- Determinism, mutation, independent verifier, oracle, and performance gates.

Out of scope for this component: non-split species, modulated quivers,
arbitrary tilting complexes, unbounded derived categories, characteristic
zero, minimal `A-infinity` models, Gerstenhaber operations, and automatic
replacement of every bounded complex by an `add(T)` complex. The certificate
proves the full derived equivalence. The transport API realizes the concrete
equivalence where terms already carry the required finite witnesses.

## 2. Ring and side conventions

All source modules are right `A`-modules. The crate endomorphism algebra

```text
E = End_A(T)
```

multiplies `f * g` as `f.then(g)`, which applies `f` first and `g` second.
The target algebra for right modules is

```text
B = E^op.
```

For `h: T -> X` and `f` in `E`, the right `B`-action is precomposition:

```text
h * f = f.then(h).
```

If `f star g = g * f` in `E`, then

```text
(h * f) * g = h * (f star g).
```

No API calls the target `End_A(T)` without stating this opposite. Paths in
`B` still compose left to right.

Let `T_0, ..., T_(r-1)` be the deterministic indecomposable summands of `T`.
The verified split gives idempotents `e_i` in `E`. An arrow `i -> j` of `B`
is represented by a map `T_j -> T_i`, namely an element of

```text
e_j rad(E) e_i / e_j rad(E)^2 e_i.
```

This direction is fixed by the right action above.

## 3. Split target boundary

An ordinary admissible bound quiver algebra over `F_p` is split basic. The
target has that form exactly when every indecomposable summand `T_i` has
residue degree one:

```text
End_A(T_i) / rad End_A(T_i) = F_p.
```

`TargetPresentationOutcome::Unsupported` stores the first summand index and
its exact residue degree when this test fails. It does not return a quiver or
an algebra.

In the current domain, a certified classical tilting module cannot reach that
branch. Every summand is tau-rigid, and
`crates/auslander/tests/residue_degree.rs` proves that a tau-rigid
indecomposable over a supported prime field has residue degree one. The
outcome keeps the representation-class boundary explicit if the base-field
scope widens.

This is a representation-class boundary, not a work limit. Increasing a
budget cannot change it. Species and division-ring vertex labels remain out
of scope.

The successful path retains one verified decomposition of `T`. It does not
run a second decomposition to recover its inclusions and projections.

## 4. Target quiver and relations

Build `E = End_A(T)` once. Let `J = rad(E)`, with its stored RREF basis. Compute
the radical chain by

```text
J^(q + 1) = span { x * y : x in a basis of J^q, y in a basis of J }.
```

Every span is reduced to RREF. The first zero power is `J^lambda`. Exact
nilpotence gives `lambda <= dim J + 1`.

For each ordered pair `(i, j)`, project the rows of `J` and `J^2` into the
corner `e_j E e_i`. Apply the crate-wide deterministic complement rule to
the square inside the radical. One arrow `i -> j` is emitted for each kept
row. Pairs use source-major order. Rows retain complement order.

Evaluate a target path in `E^op`. Its trivial word maps to `e_i`. If its
current image is `x` and the next arrow image is `y`, the next image is

```text
y * x
```

in `E`.

Enumerate all target paths of lengths `2..=lambda`, in length, source, then
lexicographic arrow order. For each endpoint pair, form the matrix whose rows
are their images in `E`. Its left-kernel rows are uniform relations. Zero
coefficients are omitted.

The arrow images generate `J` modulo `J^2`. Nakayama's lemma makes the path
map surjective. Every path of length `lambda` maps to zero. The listed kernels
therefore generate the full kernel of `F_p Q -> E^op`. No relation contains a
word of length zero or one.

The presentation runs through the existing completion engine and verifier.
The target is an ordinary `Algebra` only after that gate passes.

## 5. Target limits and outcomes

`TargetLimits` has five independent parts:

```text
max_endo_dimension
max_radical_products
max_paths
max_relation_terms
completion
```

There is no wall-clock limit. Checked arithmetic rejects size overflow before
allocation.

`max_endo_dimension` is checked before the first multiplication can build the
full structure-constant table. One radical product is one call to that table
while building a radical power or a corner. One path is one enumerated word
of length at least two. One relation term is one nonzero coefficient copied
from a kernel row. `completion` is the existing `CompletionLimits` value
passed to `Algebra::new`.

`TargetPresentationOutcome` has three variants:

- `Presented(VerifiedTargetPresentation)`.
- `Unsupported(NonSplitTarget)`.
- `Cut(TargetPresentationCut)`.

A cut stores the source, both effective limit values, the first rejected
reservation, and its stage. A completion cut retains the existing
`TruncationDiagnostics`. Its `verify()` recomputes the same first cut. No cut
exposes a target algebra or a partial relation list.

A successful target stores the exact counts of endomorphism dimension,
radical products, paths, and relation terms. Performance records copy these
counts. They are not elapsed-time measurements.

Input rejection and a failed internal cross-check are `TargetError`. Neither
is a cut.

## 6. Independent target verifier

The target builder and target verifier share data types and field arithmetic.
They do not share relation-kernel enumeration.

The verifier rebuilds `E` and the deterministic split of `T`. It checks:

1. The stored tilting classification recomputes and verifies.
2. Every summand has residue degree one.
3. The idempotents satisfy `e_i e_j = delta_(i,j) e_i` and sum to one.
4. Every arrow image lies in its claimed corner of `J`.
5. The arrow images form the required complements modulo `J^2`.
6. Every input relation evaluates to zero in `E^op`.
7. The existing completion certificate verifies independently.
8. Every normal-word image recomputes from its path.
9. The normal-word image matrix is square and invertible.
10. Unit and every basis-pair product agree with multiplication in `E^op`.

The last two checks prove that the verified target algebra is isomorphic to
`E^op`. The verifier does not need to trust that the emitted relations span a
kernel.

Private mutation helpers alter one stored idempotent, arrow image, relation,
normal-word image, or multiplication claim. The mutation corpus must reject
each alteration.

## 7. Bounded graded Ext algebras

`ExtAlgebraOutcome::compute(M, max_degree)` computes

```text
Ext^0_A(M, M) + ... + Ext^max_degree_A(M, M)
```

with the deterministic bases of `ExtSpace`. A complete value stores every
degree, every basis class, the degree-zero identity, and one product record
for each ordered basis pair whose total degree is within the bound.

A product record stores its result coordinates and the existing
`ProductWitness`. Product order is degree of the left factor, left basis
index, degree of the right factor, then right basis index.

`verify()` recomputes every space and product witness. It also checks:

- the degree-zero identity is a left and right unit;
- each stored tensor is bilinear;
- every triple within the degree bound is associative;
- product degrees add exactly.

The bound is mathematical, not evidence that higher groups vanish. A result
is `Complete` only when the source resolution proves finite projective
dimension at or below the requested degree. Otherwise it is `Cut` and states
the next uncomputed degree. Both variants keep all exact degrees already
computed. No absent degree means zero.

## 8. Bounded homotopy layer

`BoundedComplex` stores terms by integer homological degree and differentials

```text
d_n: X_n -> X_(n - 1).
```

Zero terms outside the finite support are implicit. Construction rejects an
empty term list, a bad endpoint, or a nonzero consecutive composite. One
explicit zero term represents the zero complex.

`ChainMap` stores

```text
f_n: X_n -> Y_n
```

and checks the chain identity. Maps compose with `then`. A shift satisfies
`(X[s])_n = X_(n-s)` and multiplies the differential by `(-1)^s`. The cone of
`f: X -> Y` has `Cone(f)_n = Y_n + X_(n-1)`. These signs are tested in
characteristics two and five.

`Homotopy` witnesses that two parallel degree-zero chain maps differ by

```text
d_X h + h d_Y.
```

`HomotopyHom` computes degree-`q` chain maps modulo null-homotopic maps. It
stores RREF cycle and boundary bases plus the crate-wide deterministic
complement. It can return representatives and reduce a chain map to class
coordinates.

Direct sums, shifts, and cones return checked complexes. The cone constructor
rechecks its differential square. A malformed sign or block is a construction
error, never a complex value.

Fresh-process tests pin term order, coordinate order, quotient bases, shifts,
and cone renderings.

## 9. Strict transport

The target presentation defines an additive equivalence

```text
Hom_A(T, -): add(T) -> proj(B).
```

For an `add(T)` module `X`, target vertex `i` is `Hom_A(T_i, X)`. An arrow
`i -> j`, represented by `x: T_j -> T_i`, acts by precomposition

```text
f |-> x.then(f).
```

For a morphism `g: X -> Y`, transport acts by postcomposition

```text
f |-> f.then(g).
```

The constructor requires an `AddClosureWitness` for every term. It verifies
the target relations through `Module::new` and every map through
`Morphism::new`.

The inverse additive equivalence sends the target projective `e_i B` to
`T_i`. A projective target term carries a finite decomposition into these
canonical projectives. A target morphism is expressed in the path basis,
mapped through the verified target isomorphism, and applied between the
matching summands of `T`.

Both functors apply degreewise to bounded complexes. They preserve shifts,
direct sums, differentials, chain maps, homotopies, and cones. The transport
certificate stores unit and counit chain isomorphisms. Verification recomputes
both round trips and both inverse identities.

The concrete transport domain is explicit:

- source terms need verified membership in `add(T)`;
- target terms need verified projectivity.

Failure of either condition is a typed rejection that names the first term.
`StrictTransport` attempts no automatic resolution. The separate
`DerivedTransport` layer performs checked replacement before strict transport.

## 10. Derived-equivalence certificate

`DerivedEquivalenceCertificate` stores:

- the verified classical tilting data;
- the verified split target presentation;
- the bounded minimal projective resolution of `T`;
- its graded homotopy endomorphism spaces through the resolution width;
- the exact generation complex and its `add(T)` witnesses;
- the strict `add(T)` and projective transport data.

The verifier checks the three tilting-complex conditions:

1. The resolution of `T` is bounded and projective.
2. Its nonzero-degree self-Hom groups in the homotopy category vanish.
3. The generation complex puts `A` in the thick closure of `T`.

It then checks that the degree-zero endomorphism algebra is the recovered
target, with the opposite fixed in section 2. Rickard's theorem identifies
the perfect categories. For finite-dimensional algebras, this is the derived
equivalence of bounded module categories.

The certificate proves that the full equivalence exists. The strict transport
API covers the displayed `add(T)` and projective models. It does not claim to
construct an `add(T)` model for arbitrary input.

## 11. Cross-checks

For each transported bounded complex `X`, compare the graded homotopy Hom
spaces before and after transport through every degree allowed by the finite
supports. Compare dimensions, basis-map images, products, units, and zero
classes.

For a module `M`, compare `ExtAlgebra` product tensors against direct repeated
calls to `ExtClass::then_with_witness`. The independent route rebuilds every
factor space.

Target recovery has a second arrow check through category radicals inside
`add(T)`. It is an acceptance check, not builder input.

GAP with QPA checks target quivers and relations where QPA exposes a stable
endomorphism-algebra presentation. If QPA cannot provide a canonical relation
basis, the oracle compares algebra dimension, Cartan data, radical layers,
and Ext dimensions instead. The schema records which comparison ran.

## 12. Acceptance fixtures

The release includes both `F_2` and `F_5` for:

- the projective generator, whose target recovers the source up to opposite
  convention;
- a projective-dimension-one tilting module with changed arrow orientation;
- the projective-dimension-two fixture over `A_3/(ab)`;
- a target with at least one nonzero relation;
- the residue-degree obstruction that makes `Unsupported` unreachable for a
  certified tilting module in the current domain;
- one cut at each target limit;
- nonzero and zero Ext products through at least degree four;
- shifts, cones, homotopies, and homotopy quotients;
- both strict transport round trips.

Hand-derived assertions pin vertex counts, arrow counts, relation degrees,
target dimensions, radical-layer dimensions, Cartan matrices, Ext dimensions,
and selected product coordinates. A fixture comment derives every pinned
number.

## 13. Python surface

Python exposes the same three target outcomes, target limits, target
certificate, graded Ext algebra, bounded homotopy values, transport domain
checks, and derived-equivalence certificate.

Long target recovery, Ext-algebra, homotopy-quotient, and verification calls
release the GIL. Rust objects retain their owning algebra and module values,
as the existing bindings do.

One Python example starts with the projective-dimension-two tilting
module, recovers its target, verifies the derived-equivalence certificate,
transports a two-term complex in both directions, and compares its graded
Hom dimensions.

## 14. Determinism and resource gates

Fresh processes must produce identical:

- target quivers and relation lists;
- completion certificate bytes;
- normal-word image matrices;
- Ext bases and product tensors;
- homotopy quotient bases;
- transport matrices and round-trip witnesses;
- cut diagnostics.

The target performance record reports exact profile counters and elapsed
samples separately. CI gates deterministic work counts, not time. The fixed
production case is chosen and recorded before target optimization.
The component record is
[`classical-tilting-performance.md`](classical-tilting-performance.md).

The release gates are:

1. `cargo test` on Rust 1.92.
2. `cargo +1.88 test`.
3. `cargo clippy --all-targets -- -D warnings`.
4. `cargo fmt --all --check`.
5. Python release build and the full Python suite.
6. The live GAP with QPA differential run.
7. The target and derived-certificate mutation corpora.
8. Fresh-process determinism.
9. The recorded target work ceiling.
10. A deletion and duplicate-logic pass.
11. The repository prose gate.

## 15. Implementation order

1. Freeze this design and the target orientation.
2. Recover and independently verify split target presentations.
3. Build bounded graded Ext algebras.
4. Build the bounded homotopy layer.
5. Build strict transport and its round-trip witnesses.
6. Assemble the derived-equivalence certificate.
7. Add Python parity, oracle rows, determinism, mutations, and performance
   evidence.
8. Run every release gate and finish the release notes.

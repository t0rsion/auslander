# auslander

[![CI](https://github.com/t0rsion/auslander/actions/workflows/ci.yml/badge.svg)](https://github.com/t0rsion/auslander/actions/workflows/ci.yml)
[![crates.io](https://img.shields.io/crates/v/auslander.svg)](https://crates.io/crates/auslander)
[![docs.rs](https://img.shields.io/docsrs/auslander)](https://docs.rs/auslander)
[![PyPI](https://img.shields.io/pypi/v/auslander.svg)](https://pypi.org/project/auslander/)

Computational representation theory of finite-dimensional bound quiver algebras.

Scope: finite-dimensional basic algebras kQ/I over a checked prime field, where I
is an admissible *monomial* ideal, and finite-dimensional right modules. Correct
before general.

Every construction is certified up front. `MonomialAlgebra::new` decides
finiteness of the standard-path basis exactly, by cycle detection on the
forbidden-subword automaton, and rejects infinite-dimensional input. Dimension,
Cartan data, and multiplication tables are therefore exact, and nothing in the
crate truncates. `Module::new` verifies that every forbidden word acts as zero.
Partial computations say so in their types: `projective_dimension` returns
`Bounded::Exact(n)` or `Bounded::AtLeast(n)`, a resolution prefix ends with
`ResolutionEnd::Finite` or `ResolutionEnd::Cut { at }`, and no
`None`-means-infinite convention exists anywhere.

Answers that are harder to certify follow the same discipline. Decomposition,
isomorphism, and indecomposability each return a machine-checkable witness or an
explicit statement that no witness was found. None of them returns a bare yes.

## Contents

Algebras and modules:

- Prime fields `F_p` for `p < 2^31`, with primality checked at construction.
  Dense and sparse exact linear algebra over them.
- Quivers, path words, and monomial bound quiver algebras with certified finite
  standard-path bases. Named constructors: `linear_an`, `kronecker`,
  `dual_numbers`, `truncated_poly`, `linear_nakayama` and `cyclic_nakayama`
  (validated Kupisch series), `radical_square_zero_cycle`, `an_with_relations`.
- Validated right modules; simples, indecomposable projectives and injectives;
  direct sums with inclusions and projections.
- Morphisms with checked commuting squares, `hom` bases, kernels, images,
  cokernels; radical, top, socle, and Loewy series.

Homological algebra:

- Minimal projective resolutions via projective covers, projective dimension,
  `ext_dim` and `ext_table` (exact in every degree, even when the projective
  dimension is unknown), and global dimension.
- Minimal injective coresolutions via injective envelopes, and injective
  dimension. These are the k-duals of the projective constructions over `A^op`
  and carry the same typed partiality.

Duality and the Auslander-Reiten translate:

- The opposite algebra, the k-dual `D`, and the Nakayama functor
  `ν = D ∘ Hom(−, A)` applied to presentation maps, with matrices over the
  algebra rather than over the field (`ElementMatrix`). `ν` is exposed on maps
  between projective sums, which is what the translate needs, not as a functor
  on arbitrary modules.
- `tau` computes the translate two ways on every call: the Nakayama kernel
  `ker ν(d₁)` and the transpose-then-dual `D(Tr M)` over `A^op`. The results are
  cross-checked. The two routes share the minimal presentation and the
  element-matrix encoding; their back ends are independent, so agreement checks
  everything downstream of the shared encoding. A certified disagreement and an
  undecided cross-check are distinct typed errors.

Decomposition and isomorphism:

- `EndoAlgebra`: `End(M)` as a structure-constant algebra with an exact Jacobson
  radical over `F_p` in every characteristic. The radical computation uses the
  Friedl-Rónyai chain, which never trusts the trace form in small
  characteristic.
- `decompose` and `krull_schmidt`: verified splittings. Each summand carries a
  `Certificate`: `Indecomposable` means its endomorphism algebra was proved
  local; `Undetermined` means no splitting route succeeded, and the summand may
  or may not be indecomposable.
- `is_isomorphic` returns one of three outcomes: an isomorphism verified by a
  checked two-sided inverse; a proof of non-isomorphism as one of five
  `Obstruction` kinds (differing dimension vectors, differing Loewy series,
  Hom-dimension asymmetry, the radical criterion, or an unmatched Krull-Schmidt
  summand); or `Unknown`, which means undetermined rather than "no".

Classification and enumeration:

- Exact recognition of Dynkin and Euclidean type from the underlying graph, the
  generalized Cartan matrix, and the positive roots. Recognition is
  combinatorial; nothing in the crate decides a type numerically.
- `dynkin_indecomposables`: every indecomposable of a hereditary path algebra of
  Dynkin type, one per positive root, constructed through BGP reflection
  functors (Gabriel's theorem) rather than enumerated and filtered.
  Preconditions are typed errors: a nonzero ideal or a non-Dynkin graph is
  reported as such, and a Euclidean quiver is named as Euclidean rather than
  merely rejected.
- `nakayama_indecomposables`: every indecomposable of a Nakayama algebra, each
  with its certificate.

## Not included

Deferred on purpose:

- Non-monomial relations. These wait for the planned noncommutative Gröbner
  engine (admissible orders, full remainder division, overlap and inclusion
  compositions). The commutative-square algebra is excluded for exactly this
  reason: its relation `ab − cd` is not monomial.
- Almost-split sequences, AR quivers, and bounded AR component exploration. The
  crate provides `tau` itself, not the meshes around it; the meshes will come
  with universal-property verification.
- Derived categories, tilting, and Hochschild cohomology.
- Characteristic 0.

## Conventions

Fixed crate-wide and documented on the types:

- Paths compose left to right: the word `a·b` means "first `a`, then `b`" and
  requires `target(a) == source(b)`.
- Modules are right modules. A module assigns to each vertex `v` the row-vector
  space `k^{dims[v]}`, and to each arrow `a` a
  `dims[source(a)] × dims[target(a)]` matrix. A path acts by the product of its
  arrow matrices in word order, so `M(p·q) = M(p) M(q)`.
- A morphism `f: M → N` stores one `dim M_v × dim N_v` matrix per vertex, acting
  on row vectors (`x ↦ x f_v`). A-linearity is the commuting square
  `f_{s(a)} · N(a) = M(a) · f_{t(a)}` for every arrow `a`.
- Composition is `f.then(g)`, "first `f`, then `g`": at each vertex the matrix
  is `f_v · g_v`.
- Cartan matrix: `c[i][j] = dim e_i A e_j`. Row `i` is the dimension vector of
  the projective `P_i = e_i A`; column `j` is the dimension vector of the
  injective `I_j = D(A e_j)`.
- The opposite algebra reverses path words, so a right A-module dualises to a
  right `A^op`-module. `D` is applied through `OppositeMap`, which carries the
  arrow and word translation in both directions.

## Quick start

The Ext table of the simples of kA_3/(ab), the algebra of the linearly oriented
quiver `0 → 1 → 2` with the composite path set to zero:

```rust
use auslander::algebra::an_with_relations;
use auslander::ext::ext_table;
use auslander::field::PrimeField;
use auslander::module::Module;

let algebra = an_with_relations(3, &[(0, 2)]).unwrap();
let field = PrimeField::new(5).unwrap();
let s0 = Module::simple(&algebra, field, 0);
let s2 = Module::simple(&algebra, field, 2);
// [dim Ext^0, ..., dim Ext^4]: the relation from 0 to 2 sits in Ext^2.
assert_eq!(ext_table(&s0, &s2, 4).unwrap(), vec![0, 0, 1, 0, 0]);
```

Decomposing a module and reading the certificates:

```rust
use auslander::algebra::truncated_poly;
use auslander::decompose::{Certificate, decompose};
use auslander::field::PrimeField;
use auslander::module::{Module, direct_sum};

let algebra = truncated_poly(3).unwrap();
let field = PrimeField::new(32003).unwrap();
let p = Module::projective(&algebra, field, 0);
let s = Module::simple(&algebra, field, 0);
let (m, _, _) = direct_sum(&[&p, &p, &s]);
let d = decompose(&m);
assert_eq!(d.summands().len(), 3);
// Every summand was proved indecomposable, not merely left unsplit.
assert!(d.certificates().iter().all(|c| *c == Certificate::Indecomposable));
```

Both examples run as tests in `crates/auslander/tests/`.

## Python

Python bindings live in `crates/auslander-py`; the PyPI package is `auslander`.
With [maturin](https://www.maturin.rs/) installed:

```sh
cd crates/auslander-py
maturin develop --release   # install into the active virtualenv
maturin build --release     # or build an abi3 wheel for CPython >= 3.10
```

## Building and testing

MSRV 1.88; development is pinned to Rust 1.92 via `rust-toolchain.toml`:

```
cargo test
```

## Correctness protocol

- Unit tests live in every module and are named after the fact they check. They
  include randomized dense-vs-sparse solver agreement and structural properties
  of resolutions: `d² = 0`, exactness of computed prefixes, and minimality.
- `crates/auslander/tests/fixtures.rs` holds twelve textbook fixtures (A_2, A_3,
  D_4, `k[x]/(x²)`, `k[x]/(x³)`, kA_3/(ab), Kronecker-2, a radical-square-zero
  cycle, three Nakayama algebras, a gentle tree algebra) with hand-derived
  dimensions, Cartan matrices, radical series, Ext tables, and projective and
  global dimensions. Each fixture runs over both F_2 and F_5. Two entries are
  regressions from an earlier in-house prototype: hereditary Kronecker has
  global dimension exactly 1 (the prototype's examples database claimed
  infinite), and Kupisch series [2, 2, 1] runs to completion (the prototype hung
  on it).
- Facts that are characteristic-free are checked over a large prime as well as
  over F_2 and F_5. Small fields hide failure modes that depend on how rare
  units are: a decomposition defect survived the suite because every test ran at
  F_2 and F_5, where a random endomorphism of `P ⊕ P` is a non-unit often
  enough to split by luck.
- `crates/auslander/tests/qpa-oracle/` is a differential harness against QPA
  under GAP. The committed `qpa_expected.json` was produced by a real GAP+QPA
  run (provenance in `crates/auslander/tests/qpa-oracle/README.md`), and an
  always-on test compares the library against it. A missing or corrupted file is
  a hard failure, and regression tests pin the corruption checks.
  `native_snapshot.json` is a drift snapshot of the library's own output, not an
  oracle. Setting `QPA_ORACLE=1` invokes GAP itself and fails hard if GAP or QPA
  is unavailable or any value disagrees.

## License

Licensed under either of the MIT license (`LICENSE-MIT`) or the Apache License,
Version 2.0 (`LICENSE-APACHE`), at your option.

# auslander

[![CI](https://github.com/t0rsion/auslander/actions/workflows/ci.yml/badge.svg)](https://github.com/t0rsion/auslander/actions/workflows/ci.yml)
[![crates.io](https://img.shields.io/crates/v/auslander.svg)](https://crates.io/crates/auslander)
[![docs.rs](https://img.shields.io/docsrs/auslander)](https://docs.rs/auslander)
[![PyPI](https://img.shields.io/pypi/v/auslander.svg)](https://pypi.org/project/auslander/)

Computational representation theory of finite-dimensional bound quiver algebras.

Scope of v0.1: finite-dimensional basic algebras kQ/I over a checked prime field,
where I is an admissible *monomial* ideal, and finite-dimensional right modules.
Correct before general.

Every construction is certified up front. `MonomialAlgebra::new` decides finiteness
of the standard-path basis exactly (cycle detection on the forbidden-subword
automaton) and errors on infinite-dimensional input, so dimension, Cartan data, and
multiplication tables are exact and nothing in the crate truncates. `Module::new`
verifies that every forbidden word acts as zero. Partial computations say so in
their types: `projective_dimension` returns `Bounded::Exact(n)` or
`Bounded::AtLeast(n)`, a resolution prefix ends with `ResolutionEnd::Finite` or
`ResolutionEnd::Cut { at }`, and no `None`-means-infinite convention exists
anywhere.

## What v0.1 contains

- Prime fields `F_p` (`p < 2^31`, primality checked at construction) and dense and
  sparse exact linear algebra over them.
- Quivers, path words, and monomial bound quiver algebras with certified finite
  standard-path bases; named constructors: `linear_an`, `kronecker`,
  `dual_numbers`, `truncated_poly`, `linear_nakayama` and `cyclic_nakayama`
  (validated Kupisch series), `radical_square_zero_cycle`, `an_with_relations`.
- Validated right modules; simples, indecomposable projectives and injectives;
  direct sums with inclusions and projections.
- Morphisms with checked commuting squares, `hom` bases, kernels, images,
  cokernels; radical, top, socle, Loewy series.
- Minimal projective resolutions via projective covers, projective dimension,
  `ext_dim`/`ext_table` (exact in every degree, even when the projective dimension
  is unknown), global dimension.

## What v0.1 does not contain

Deliberately deferred, with their planned releases:

- Non-monomial relations: v0.3, after the new noncommutative Gröbner engine
  (admissible orders, full remainder division, overlap and inclusion
  compositions). The commutative-square algebra is excluded from v0.1 for exactly
  this reason: its relation `ab − cd` is not monomial.
- Isomorphism testing and direct-sum decomposition: v0.2, via Fitting's lemma and
  idempotent lifting, with `Unknown` as an honest outcome.
- Auslander–Reiten theory (τ, almost-split sequences, AR quivers): v0.2+.
- Derived categories, tilting, Hochschild cohomology: v0.4+.
- Characteristic 0.

## Conventions

Fixed crate-wide and documented on the types:

- Paths compose left to right: the word `a·b` means "first `a`, then `b`" and
  requires `target(a) == source(b)`.
- Modules are right modules. A module assigns to each vertex `v` the row-vector
  space `k^{dims[v]}` and to each arrow `a` a `dims[source(a)] × dims[target(a)]`
  matrix; a path acts by the product of its arrow matrices in word order, so
  `M(p·q) = M(p) M(q)`.
- A morphism `f: M → N` stores one `dim M_v × dim N_v` matrix per vertex, acting
  on row vectors (`x ↦ x f_v`). A-linearity is the commuting square
  `f_{s(a)} · N(a) = M(a) · f_{t(a)}` for every arrow `a`.
- Composition is `f.then(g)`, "first `f`, then `g`": at each vertex the matrix is
  `f_v · g_v`.
- Cartan matrix: `c[i][j] = dim e_i A e_j`, so row `i` is the dimension vector of
  the projective `P_i = e_i A` and column `j` the dimension vector of the
  injective `I_j = D(A e_j)`.

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

The same code runs as `readme_quick_start_example` in
`crates/auslander/tests/fixtures.rs`.

## Python

Python bindings live in `crates/auslander-py`; the PyPI package will be
`auslander`. With [maturin](https://www.maturin.rs/) installed:

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

- Unit tests in every module, named after the fact they check, including
  randomized dense-vs-sparse solver agreement and structural properties of
  resolutions (`d² = 0`, exactness of computed prefixes, minimality).
- `crates/auslander/tests/fixtures.rs`: twelve textbook fixtures (A_2, A_3, D_4,
  `k[x]/(x²)`, `k[x]/(x³)`, kA_3/(ab), Kronecker-2, a radical-square-zero cycle,
  three Nakayama algebras, a gentle tree algebra) with hand-derived dimensions,
  Cartan matrices, radical series, Ext tables, and projective and global
  dimensions, each run over both F_2 and F_5. Two entries are regressions from
  an earlier in-house prototype: hereditary Kronecker has global dimension
  exactly 1 (the prototype's examples database claimed infinite), and Kupisch
  series [2, 2, 1] runs to completion (the prototype hung on it).
- `crates/auslander/tests/qpa-oracle/`: a differential harness against QPA under
  GAP. The committed `qpa_expected.json` was produced by a real GAP+QPA run
  (provenance in `crates/auslander/tests/qpa-oracle/README.md`) and an always-on
  test compares the library against it; a missing or corrupted file is a hard
  failure, with regression tests pinning the corruption checks.
  `native_snapshot.json` is a drift snapshot
  of the library's own output, not an oracle. Setting `QPA_ORACLE=1` invokes GAP
  itself and fails hard if GAP or QPA is unavailable or any value disagrees.

## License

Licensed under either of the MIT license (`LICENSE-MIT`) or the Apache License,
Version 2.0 (`LICENSE-APACHE`), at your option.

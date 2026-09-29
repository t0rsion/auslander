# auslander

[![CI](https://github.com/t0rsion/auslander/actions/workflows/ci.yml/badge.svg)](https://github.com/t0rsion/auslander/actions/workflows/ci.yml)
[![crates.io](https://img.shields.io/crates/v/auslander.svg)](https://crates.io/crates/auslander)
[![docs.rs](https://img.shields.io/docsrs/auslander)](https://docs.rs/auslander)
[![PyPI](https://img.shields.io/pypi/v/auslander.svg)](https://pypi.org/project/auslander/)

auslander is a Rust library, with Python bindings, for exact computation
with finite-dimensional algebras `kQ/I` over a prime field and their right
modules. The ideal `I` may be any admissible ideal, given by relations such
as `ab - cd`.

Every answer is either exact or says in its type how it is partial. A
projective dimension is `Exact(n)` or `AtLeast(n)`, and a resolution ends
`Finite` or `Cut`. Nothing truncates silently. Most results also carry a
witness that a separate verifier rechecks, so a claim does not depend on
trusting the code that found it.

## What it computes

An algebra is built by Gröbner completion of its relations. The completion
emits a certificate, and an independent verifier checks it before an
`Algebra` value exists. Dimension, the Cartan matrix, and all structure
constants are then exact.

Modules come with the standard homological toolkit: Hom spaces, kernels and
cokernels, minimal projective and injective resolutions, Ext in every
degree, and projective, injective, and global dimension. Hochschild
cohomology is computed from the bar construction under explicit limits.

The Auslander-Reiten layer computes the translate `τ` by two independent
routes, almost split sequences with recheckable witnesses, and AR quivers
for Nakayama, zero-ideal Dynkin, and gentle-tree algebras. Support
τ-tilting pairs are classified and mutated, and a complete mutation graph is
certified by a closure witness.

The derived layer works with bounded complexes of projectives. It certifies
classical tilting modules and tilting complexes, recovers `End(T)^op`, and
finds derived equivalences by tilting mutation. Version 0.10 classifies a
finite family of algebras up to derived equivalence: two members share a
class only through a replayable equivalence, and two classes are separated
only by a recomputed invariant. For the 894 connected gentle algebras with 4
vertices over `F_2` this gives 103 classes with one pair left unresolved.

Results can be saved as portable JSON artifacts. Replay rebuilds every
algebra and rechecks every claim. The same verifier runs in the browser as
WebAssembly.

## Install

```sh
cargo add auslander
python -m pip install auslander
```

The crate needs Rust 1.88 or later. The Python package needs CPython 3.10
or later.

## Example: modules over the commutative square

The algebra `kQ/(ab - cd)` on the square quiver `0 → 1 → 3`, `0 → 2 → 3`:

```rust
use auslander::algebra::commutative_square;
use auslander::ar::tau;
use auslander::ext::ext_table;
use auslander::field::PrimeField;
use auslander::module::Module;
use auslander::resolution::{Bounded, projective_dimension};

let algebra = commutative_square(PrimeField::new(5).unwrap());
assert_eq!(algebra.dim(), 9);

let s0 = Module::simple(&algebra, 0);
let s3 = Module::simple(&algebra, 3);
assert_eq!(projective_dimension(&s0, 5), Bounded::Exact(2));
// dim Ext^k(S_0, S_3) for k = 0..3: the relation ab - cd sits in degree 2.
assert_eq!(ext_table(&s0, &s3, 3).unwrap(), vec![0, 0, 1, 0]);
// The Auslander-Reiten translate, checked by two independent routes.
assert_eq!(tau(&s0).unwrap().dim_vector(), [1, 1, 1, 0]);
```

## Example: derived classification

Rust. The 77 connected gentle algebras with 3 vertices over `F_2` fall into
30 derived equivalence classes, and every pair is decided:

```rust
use auslander::control::ComputationControl;
use auslander::derived_classification::{ClassificationLimits, classify_derived};
use auslander::field::PrimeField;
use auslander::gentle::connected_gentle_algebras;

let family = connected_gentle_algebras(3, PrimeField::new(2).unwrap()).unwrap();
let limits = ClassificationLimits::with_walk_vertices(8);
let result = classify_derived(&family, &limits, &ComputationControl::new()).unwrap();
assert_eq!((family.len(), result.classes().len()), (77, 30));
assert!(result.unresolved().is_empty());
```

Python. Classify all connected gentle algebras with at most 3 vertices,
export the result, and replay the file from scratch:

```python
import auslander as au

F = au.PrimeField(2)
family = [A for n in (1, 2, 3) for A in au.connected_gentle_algebras(n, field=F)]
result = au.classify_derived(family)
print(result.status, len(family), len(result.classes), len(result.unresolved))
replayed = au.verify_derived_atlas(result.export("atlas.json"))
print(replayed.verification, replayed.fingerprint)
```

```text
complete 88 40 0
replayed 2e101da54286279b
```

`result.explain()` states for each pair why it is merged, separated, or
unresolved, and `au.to_latex(result)` writes the class table.

The command line runs the same classification and verifies any artifact:

```sh
auslander classify gentle --vertices 3 --field 2 --output atlas.json
auslander verify atlas.json
```

## Conventions

Modules are right modules, and paths compose left to right: `a·b` means
first `a`, then `b`, and `M(a·b) = M(a) M(b)`. Row `i` of the Cartan matrix
is the dimension vector of the projective `P_i`. The
[guide](docs/guide.md#conventions) states every convention in full.

## Scope

Fields are prime fields `F_p` with `p < 2^31`. Characteristic zero and
extension fields are not supported. Algebras and modules are finite
dimensional; an infinite-dimensional quotient is rejected with a word
witness. Complete lists of indecomposable modules exist only for Nakayama,
zero-ideal Dynkin, and gentle-tree algebras. The
[guide](docs/guide.md#not-included) lists the remaining limits.

Correctness is checked against exact fixtures, deterministic artifact bytes,
and a differential run against GAP with QPA. See the
[correctness protocol](docs/correctness-protocol.md).

## Documentation

- [Library guide](docs/guide.md): the certified pipeline, capabilities,
  return types, and longer examples.
- [API reference](https://docs.rs/auslander) on docs.rs.
- [Python package](crates/auslander-py/README.md) and its guides.
- [Derived classification contract](docs/derived-classification.md) and the
  [complete gentle invariant](docs/gentle-derived-invariant.md).
- [Browser verifier](docs/browser-verifier.md).
- [Catalog artifacts](docs/catalog-artifacts.md) and
  [theorem artifacts](docs/theorem-artifacts.md).
- [Changelog](CHANGELOG.md) and [roadmap](ROADMAP.md).

To cite the library, use [`CITATION.cff`](CITATION.cff).

## License

Licensed under either of the MIT license ([`LICENSE-MIT`](LICENSE-MIT)) or
the Apache License, Version 2.0 ([`LICENSE-APACHE`](LICENSE-APACHE)), at
your option.

# Migrating to 0.3

Every breaking change, ordered by how often you will hit it. The `after`
snippets compile against the current crate.

The one structural change behind all of them: `MonomialAlgebra` is gone.
`Algebra` is now the only runtime algebra type, it owns its prime field, and it
exists only after the completion certificate has been verified. Wherever a field
travelled beside an algebra, it now comes from the algebra.

## 1. Named constructors take a field

Each constructor now builds a runtime algebra, so it needs the field.
`linear_an`, `kronecker`, `dual_numbers`, and `radical_square_zero_cycle`
return `Arc<Algebra>`. `truncated_poly`, `linear_nakayama`, `cyclic_nakayama`,
and `an_with_relations` return `Result<Arc<Algebra>, AlgebraBuildError>`.

Before:

```rust
let algebra = truncated_poly(3).unwrap();
let field = PrimeField::new(5).unwrap();
```

After:

```rust
use auslander::algebra::{linear_an, truncated_poly};
use auslander::field::PrimeField;

let field = PrimeField::new(5).unwrap();
let a3 = linear_an(3, field);
let x3 = truncated_poly(3, field).unwrap();
assert_eq!(a3.field(), field);
```

Each of these except `dual_numbers` also has a `_presentation` form
(`truncated_poly_presentation`, `linear_an_presentation`, and so on) that stops
at the field-free `MonomialPresentation`.

## 2. Modules no longer take a field

`Module::new`, `Module::simple`, `Module::projective`, and `Module::injective`
drop the field argument. `Module::new` still validates the module; it now checks
that every element of the reduced Groebner basis acts as zero.

Before:

```rust
let m = Module::new(algebra.clone(), field, dims, maps).unwrap();
let s = Module::simple(&algebra, field, 0);
```

After:

```rust
use auslander::algebra::dual_numbers;
use auslander::field::PrimeField;
use auslander::linalg::DenseMat;
use auslander::module::Module;

let field = PrimeField::new(5).unwrap();
let algebra = dual_numbers(field);
let maps = vec![DenseMat::zero(1, 1)];
let m = Module::new(algebra.clone(), vec![1], maps).unwrap();
let s = Module::simple(&algebra, 0);
let p = Module::projective(&algebra, 0);
let i = Module::injective(&algebra, 0);
```

## 3. Building a monomial algebra

`MonomialAlgebra::new(quiver, forbidden)` becomes
`MonomialPresentation::new(quiver, forbidden)` plus
`Algebra::from_monomial(field, &presentation, &limits)`. The presentation keeps the
field-free combinatorics: dimension, Cartan data, the standard-path basis, and
the finiteness decision. `from_monomial` routes the same forbidden words through
the completion pipeline, and the resulting basis equals the standard-path basis
word for word.

Before:

```rust
let algebra = MonomialAlgebra::new(quiver, forbidden).unwrap();
```

After:

```rust
use auslander::algebra::{Algebra, MonomialPresentation, monomial_completion_limits};
use auslander::field::PrimeField;
use auslander::quiver::{ArrowId, Quiver};

let field = PrimeField::new(5).unwrap();
let quiver = Quiver::new(1, &[(0, 0)]).unwrap();
let forbidden = vec![vec![ArrowId(0), ArrowId(0), ArrowId(0)]];
let presentation = MonomialPresentation::new(quiver, forbidden).unwrap();
let limits = monomial_completion_limits(&presentation);
let algebra = Algebra::from_monomial(field, &presentation, &limits).unwrap();
assert_eq!(algebra.dim(), 3);
```

`monomial_completion_limits` derives limits that are always adequate for the
presentation; the named monomial constructors use it internally.

## 4. Building a general algebra

New capability, no `before`. A `Relation` is a k-combination of paths of length
at least 2 that share one source and one target. `Presentation` bundles the
quiver, the field, and the relations. `Algebra::new` completes, emits the
certificate, verifies the bytes, and builds the tables from the verified data.

```rust
use auslander::algebra::Algebra;
use auslander::completion::CompletionLimits;
use auslander::field::PrimeField;
use auslander::quiver::{ArrowId, Quiver};
use auslander::relation::{Presentation, Relation};

let field = PrimeField::new(5).unwrap();
let quiver = Quiver::new(4, &[(0, 1), (1, 3), (0, 2), (2, 3)]).unwrap();
let relation = Relation::new(
    &quiver,
    field,
    vec![
        (field.one(), vec![ArrowId(0), ArrowId(1)]),
        (field.elem(-1), vec![ArrowId(2), ArrowId(3)]),
    ],
)
.unwrap();
let presentation = Presentation::new(quiver, field, vec![relation]).unwrap();
let algebra = Algebra::new(presentation, &CompletionLimits::default()).unwrap();
assert_eq!(algebra.dim(), 9);
```

`Relation::new` rejects bad input by term index: an empty relation, a zero or
non-canonical coefficient, a duplicate word, a word that is not a path, a word
of length below 2, and mixed sources or targets. `Algebra::new` adds
`AlgebraBuildError::Truncated` when a completion budget runs out and
`AlgebraBuildError::InfiniteDimensional`, which carries the certificate and a
cyclic word witness.

## 5. `right_mul` and `left_mul` return a sparse row

A product of a basis element and an arrow is a combination of normal words in
general, so both return `&[(BasisIdx, Fp)]` instead of `Option<BasisIdx>`. Over
a monomial ideal the row has at most one entry.

Before:

```rust
if let Some(j) = algebra.right_mul(i, a) {
    row[j] = field.add(row[j], c);
}
```

After:

```rust
use auslander::algebra::{BasisIdx, linear_an};
use auslander::field::PrimeField;
use auslander::quiver::ArrowId;

let field = PrimeField::new(5).unwrap();
let algebra = linear_an(3, field);
let i: BasisIdx = 0;
let a = ArrowId(0);
let c = field.one();
let mut row = vec![field.zero(); algebra.dim()];
for &(j, coeff) in algebra.right_mul(i, a) {
    row[j] = field.add(row[j], field.mul(c, coeff));
}
assert_eq!(row[3], field.one());
```

`left_mul(a, i)` changes the same way. `mul_basis(p, q)` returns an owned row of
the same shape, and `nf_word(&word)` returns one inside a `Result`.

## 6. `forbidden()` becomes `relations()`

`Algebra::relations` returns the reduced Groebner basis of the ideal, each
element a monic `Relation` with terms in strictly descending order. Use
`leading()` for the leading term.

Before:

```rust
let words: &[Vec<ArrowId>] = algebra.forbidden();
```

After:

```rust
use auslander::algebra::truncated_poly;
use auslander::field::PrimeField;
use auslander::quiver::ArrowId;

let field = PrimeField::new(5).unwrap();
let algebra = truncated_poly(3, field).unwrap();
assert_eq!(algebra.relations().len(), 1);
let (_coefficient, word) = algebra.relations()[0].leading();
assert_eq!(word.arrows(), &[ArrowId(0), ArrowId(0), ArrowId(0)]);
```

`MonomialPresentation::forbidden` still exists and still returns words. It is
the presentation, not the runtime algebra.

## 7. `path_index(...) == Ok(None)` no longer means zero

`Ok(None)` means "this path is not a normal word". Over a general ideal such a
path need not be zero: it equals its normal form, a combination of normal words.
Use `nf_word` to get that form. Over a monomial ideal the two notions still
agree, so old monomial code keeps its meaning.

```rust
use auslander::algebra::Algebra;
use auslander::completion::CompletionLimits;
use auslander::field::PrimeField;
use auslander::quiver::{ArrowId, PathWord, Quiver};
use auslander::relation::{Presentation, Relation};

let field = PrimeField::new(5).unwrap();
let quiver = Quiver::new(4, &[(0, 1), (1, 3), (0, 2), (2, 3)]).unwrap();
let relation = Relation::new(
    &quiver,
    field,
    vec![
        (field.one(), vec![ArrowId(0), ArrowId(1)]),
        (field.elem(-1), vec![ArrowId(2), ArrowId(3)]),
    ],
)
.unwrap();
let presentation = Presentation::new(quiver, field, vec![relation]).unwrap();
let algebra = Algebra::new(presentation, &CompletionLimits::default()).unwrap();
let cd = PathWord::from_arrows(algebra.quiver(), &[ArrowId(2), ArrowId(3)]).unwrap();
// cd is not a normal word, and it is not zero either.
assert_eq!(algebra.path_index(&cd), Ok(None));
let normal = algebra.nf_word(&cd).unwrap();
assert_eq!(normal.len(), 1);
```

Radical powers follow the same rule. `radical_power_component` iterates row
spaces; word length decides nothing, because an inhomogeneous relation can put a
short normal word into a deep radical power.

## 8. `opposite` returns a `Result`

The opposite algebra reverses the quiver and every relation word, then runs
completion and verification again. That build can fail, so `opposite` returns
`Result<OppositeMap, AlgebraBuildError>`. It never fails with
`InfiniteDimensional`: reversal bijects paths, so the opposite has the same
dimension.

Before:

```rust
let op = opposite(&algebra);
```

After:

```rust
use auslander::algebra::{AlgebraBuildError, an_with_relations};
use auslander::field::PrimeField;
use auslander::opposite::opposite;

fn example() -> Result<(), AlgebraBuildError> {
    let field = PrimeField::new(5).unwrap();
    let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
    let op = opposite(&algebra)?;
    assert_eq!(op.opposite().dim(), algebra.dim());
    Ok(())
}
```

## 9. The injective constructions return a `Result`

`injective_envelope`, `coresolve`, and `injective_dimension` build the opposite
algebra, so each propagates `AlgebraBuildError`. Nothing else about them
changes.

Before:

```rust
let (envelope, into) = injective_envelope(&s0);
let coresolution = coresolve(&s0, 5);
let id = injective_dimension(&s0, 5);
```

After:

```rust
use auslander::algebra::{AlgebraBuildError, an_with_relations};
use auslander::field::PrimeField;
use auslander::injective::{coresolve, injective_dimension, injective_envelope};
use auslander::module::Module;
use auslander::resolution::Bounded;

fn example() -> Result<(), AlgebraBuildError> {
    let field = PrimeField::new(5).unwrap();
    let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
    let s0 = Module::simple(&algebra, 0);
    let (envelope, into) = injective_envelope(&s0)?;
    let coresolution = coresolve(&s0, 5)?;
    let id: Bounded<usize> = injective_dimension(&s0, 5)?;
    Ok(())
}
```

`tau` reports the same failure as `TauError::Opposite(AlgebraBuildError)`.

## 10. `ElementMatrix::new` drops the field

The field comes from the algebra. Coefficient vectors are unchanged: entry
`(k, l)` lists the coefficients over `paths_between(targets[l], sources[k])`.

Before:

```rust
let em = ElementMatrix::new(algebra, field, sources, targets, entries).unwrap();
```

After:

```rust
use auslander::algebra::linear_an;
use auslander::field::PrimeField;
use auslander::opposite::ElementMatrix;

let field = PrimeField::new(5).unwrap();
let algebra = linear_an(2, field);
let entries = vec![vec![vec![field.one()]]];
let em = ElementMatrix::new(algebra, vec![0], vec![0], entries).unwrap();
```

## 11. `global_dimension` and `dynkin_indecomposables` drop the field

Before:

```rust
let g = global_dimension(&algebra, field, 5);
let modules = dynkin_indecomposables(&algebra, field).unwrap();
```

After:

```rust
use auslander::algebra::linear_an;
use auslander::dynkin::dynkin_indecomposables;
use auslander::ext::global_dimension;
use auslander::field::PrimeField;
use auslander::resolution::Bounded;

let field = PrimeField::new(5).unwrap();
let algebra = linear_an(3, field);
assert_eq!(global_dimension(&algebra, 5), Bounded::Exact(1));
assert_eq!(dynkin_indecomposables(&algebra).unwrap().len(), 6);
```

`dynkin_indecomposables` still requires the zero ideal; it now counts
`algebra.relations()` and reports `DynkinError::NonzeroIdeal { relations }`.
`nakayama_indecomposables` keeps its preconditions.

## 12. `DifferentFields` is gone

`HomError::DifferentFields` and `ExtError::DifferentFields` are removed. The
field comes from the algebra, so two modules over one algebra share a field, and
`DifferentAlgebras` is the only mismatch left.

Before:

```rust
assert_eq!(hom(&m, &n).unwrap_err(), HomError::DifferentFields);
```

After:

```rust
use auslander::algebra::linear_an;
use auslander::ext::{ExtError, ext_dim};
use auslander::field::PrimeField;
use auslander::hom::{HomError, hom};
use auslander::module::Module;

let field = PrimeField::new(5).unwrap();
let a = linear_an(2, field);
let b = linear_an(2, field);
let m = Module::simple(&a, 0);
let n = Module::simple(&b, 0);
assert_eq!(hom(&m, &n).unwrap_err(), HomError::DifferentAlgebras);
assert_eq!(ext_dim(&m, &n, 1).unwrap_err(), ExtError::DifferentAlgebras);
```

Two algebras built from the same input are still different algebras: the check
is `Arc::ptr_eq`, so share one `Arc<Algebra>` between modules that must
interact.

## 13. New: certificates and budgets

Nothing to migrate, but two entry points are worth knowing.

Dump, reload, verify, rebuild:

```rust
use auslander::algebra::{Algebra, truncated_poly};
use auslander::field::PrimeField;
use auslander::verify::verify;

let field = PrimeField::new(5).unwrap();
let algebra = truncated_poly(3, field).unwrap();
let bytes = algebra.certificate().to_canonical_json();
let verified = verify(&bytes).unwrap();
let rebuilt = Algebra::from_verified(verified);
assert_eq!(rebuilt.dim(), algebra.dim());
```

`from_verified` keeps the default completion limits: certificate bytes never
carry or select downstream budgets. `Algebra::from_verified_with_limits`
preserves raised budgets across a reload.

Budgets. `CompletionLimits::default()` allows 4096 basis elements, words of at
most 64 arrows, and 1,000,000 work units (each reduction step and each emitted
normal word costs one). Tighten them when you want a run to stop early; an
exhausted budget gives
`AlgebraBuildError::Truncated(TruncationDiagnostics)` with the basis size, the
pending ambiguity count, the steps used, and which budget ran out.

```rust
use auslander::completion::CompletionLimits;

let limits = CompletionLimits {
    max_basis: 4,
    max_word_len: 8,
    max_steps: 100,
};
```

## 14. Python

- `MonomialAlgebra` is an alias of `Algebra`. Existing monomial code keeps
  working: `Algebra(quiver, forbidden)` and the named constructors still build a
  field-free monomial presentation, and a field still enters at
  `algebra.module(field, ...)`, `algebra.simple(field, v)` and the like.
- `Algebra.from_relations(quiver, relations, field)` builds a general-relation
  algebra. Each relation is a list of `(coefficient, path)` terms, a path is a
  list of arrow ids, and coefficients are integers reduced mod p.
- A general-relation algebra is bound to the one field it was verified over.
  `algebra.field` names that field, and is `None` for a monomial algebra. Any
  other field raises `ValueError`.
- `algebra.certificate_json()` returns the canonical certificate bytes, and
  `Algebra.from_certificate(json)` verifies untrusted bytes and rebuilds. A
  monomial algebra is field-free and a certificate is not, so there
  `certificate_json(field)` requires the field, and the reloaded algebra is
  always field-bound.
- An exhausted completion budget raises `TruncationError`, a `RuntimeError` with
  `basis_len`, `pending_ambiguities`, `steps_used`, and `reason` attributes. The
  `max_basis`, `max_word_len`, and `max_steps` keywords of `from_relations` set
  the budgets.

```python
import auslander

F = auslander.PrimeField(5)
# a: 0 -> 1, b: 1 -> 3, c: 0 -> 2, d: 2 -> 3
Q = auslander.Quiver(4, [(0, 1), (1, 3), (0, 2), (2, 3)])
A = auslander.Algebra.from_relations(Q, [[(1, [0, 1]), (-1, [2, 3])]], F)
assert A.dim == 9
assert A.field.p == 5
```

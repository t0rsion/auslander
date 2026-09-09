# Certified self-Ext loci on the commutative square

This study runs the full certified path on a nonmonomial algebra. Each result is a
checked finite computation. It is not a new theorem or classification.

## Starter domain

Let `A` be the commutative square over `F_2`:

```text
0 -a-> 1 -b-> 3
 \-c-> 2 -d-/
```

The relation is `ab - cd`. The starter census fixes dimension vector
`[1,1,1,1]`. Each arrow matrix has one entry, so the raw domain contains 16
tuples.

The relation accepts 10 tuples and rejects 6. Over `F_2`, each one-dimensional
vertex space has only the identity change of basis. The 10 accepted tuples are
therefore 10 distinct isomorphism classes. The census still checks all 45
pairwise class comparisons through the generic isomorphism path.

## Starter self-Ext table

The stream computes each self-pair through degree 3. Coordinates use arrow
order `(a,b,c,d)`.

| Representative indices | Coordinates | `dim Ext^0..3(M,M)` |
| --- | --- | --- |
| 0 | `[0,0,0,0]` | `[4,4,1,0]` |
| 1, 2, 3, 6 | one nonzero arrow | `[3,2,0,0]` |
| 4, 5, 7, 8 | two nonzero arrows satisfying the relation | `[2,1,0,0]` |
| 9 | `[1,1,1,1]` | `[1,0,0,0]` |

Exactly representative 9 has vanishing self-Ext in degrees 1 through 3. It is
the representation with every arrow equal to the identity scalar.
It is `P_0`, also `I_3`, so this vanishing is a projective check.

The stream uses five chunks and retains at most two live sources. Its record
contains 10 resolutions, 10 Hom spaces, 10 projective-factor spaces, and 10
Ext tables. These are exact work counts from the committed checkpoint.

## Flagship domain

The flagship census uses the same algebra at dimension vector `[2,1,1,2]`.
The eight arrow-matrix coordinates give raw domain size `2^8 = 256`. Complete
census replay accepts 58 modules and rejects 198. It retains 12
representatives. A finite hand count of the accepted modules is
`58 = 7^2 + 9`.

Each path acts by a column times a row over `F_2`. Seven pairs give the zero
matrix: four with zero column and three with nonzero column and zero row.
Each of the nine nonzero rank-one matrices has one factorization. Requiring
the two path actions to agree therefore gives `7^2 + 9` assignments.

## Flagship self-Ext table

The stream computes each self-pair through degree 3. Coordinates stay in
arrow-major order `(a,b,c,d)`.

| Representative index | Coordinates | `dim Ext^0..3(M,M)` |
| --- | --- | --- |
| 0 | `[0,0,0,0,0,0,0,0]` | `[10,8,4,0]` |
| 1 | `[0,0,0,0,0,0,0,1]` | `[8,4,2,0]` |
| 2 | `[0,0,0,0,0,1,0,0]` | `[8,4,2,0]` |
| 3 | `[0,0,0,1,0,0,0,0]` | `[8,4,2,0]` |
| 4 | `[0,0,0,1,0,0,0,1]` | `[7,3,2,0]` |
| 5 | `[0,0,0,1,0,0,1,0]` | `[6,0,0,0]` |
| 6 | `[0,0,0,1,0,1,0,0]` | `[6,1,1,0]` |
| 7 | `[0,1,0,0,0,0,0,0]` | `[8,4,2,0]` |
| 8 | `[0,1,0,0,0,0,0,1]` | `[6,1,1,0]` |
| 9 | `[0,1,0,0,0,1,0,0]` | `[7,3,2,0]` |
| 10 | `[0,1,0,0,1,0,0,0]` | `[6,0,0,0]` |
| 11 | `[0,1,0,1,0,1,0,1]` | `[5,0,1,0]` |

Degree 1 vanishes at indices `[5,10,11]`. Degrees 1 through 3 vanish at
`[5,10]`. Representative 11 has Ext dimensions `[5,0,1,0]` and is isomorphic
to `P_0 + S_0 + S_3`.

The stream uses six chunks and retains at most two live sources. Its record
contains 12 resolutions, 12 Hom spaces, 12 projective-factor spaces, and 12
Ext tables.

## Verification

The starter artifact is
[`commutative-square-f2-d1111-self-ext-1-3.json`](../crates/auslander/artifacts/research/commutative-square-f2-d1111-self-ext-1-3.json).
Its fingerprint is `c89b7f314194f289`.

The flagship artifact is
[`commutative-square-f2-d2112-self-ext-1-3.json`](../crates/auslander/artifacts/research/commutative-square-f2-d2112-self-ext-1-3.json).
Its fingerprint is `748d068629a7d970`.

Verification rebuilds the algebra and census, then replays every stored
homological row. It then recomputes the locus through `ExtSpace::new`. That
constructor is the crate's generic Ext path, not a second Ext implementation.
The locus check can stop at the first mismatch.

Run the construction and the committed-artifact test:

```sh
cargo run -p auslander --example self_ext_workflow
cargo test -p auslander --test self_ext_artifact
```

The Python CLI checks each artifact in a fresh process:

```sh
auslander theorem verify \
  crates/auslander/artifacts/research/commutative-square-f2-d1111-self-ext-1-3.json
auslander theorem verify \
  crates/auslander/artifacts/research/commutative-square-f2-d2112-self-ext-1-3.json
```

## Limit

The starter covers `F_2`, dimension vector `[1,1,1,1]`, and degrees 1 through
3. The flagship covers `F_2`, dimension vector `[2,1,1,2]`, and the same
degrees. Neither claim extends to another field, dimension vector, or degree.
Each finite census proves coverage of its stated raw matrix domain only.

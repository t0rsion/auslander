//! Acceptance tests over nonmonomial quotients.
//!
//! Fixtures:
//!
//! - A: the commutative square `kQ/(ab - cd)` over F_5, arrows `a: 0 → 1`
//!   (id 0), `b: 1 → 3` (1), `c: 0 → 2` (2), `d: 2 → 3` (3). Under
//!   `deglex-arrowid-v1` the leading word of `ab - cd` is `cd`, so the
//!   reduced Groebner basis is `{cd - ab}` and the normal words are
//!   `{e_0..e_3, a, c, b, d, ab}`: dim 9.
//! - B: the preprojective algebra of A_3 over F_2, the double quiver
//!   `a: 0 → 1` (0), `b: 1 → 2` (1), `abar: 1 → 0` (2), `bbar: 2 → 1` (3)
//!   with relations `a·abar`, `abar·a - b·bbar`, `bbar·b`: dim 10,
//!   self-injective. Its presentation and all pinned values come from
//!   `tests/qpa-oracle/README.md` and the committed `qpa_expected.json`.
//! - C: the inhomogeneous algebra `kQ/(ab - cde)` over F_5, arrows
//!   `a: 0 → 1` (0), `b: 1 → 4` (1), `c: 0 → 2` (2), `d: 2 → 3` (3),
//!   `e: 3 → 4` (4): dim 13. The relation mixes path lengths, so a short
//!   normal word sits inside a deep radical power.
//!
//! Every pinned value for A is hand-derived on the test that uses it. The
//! same values appear in the committed QPA oracle for the
//! `commutative-square` `f5` fixture.

mod common;
#[path = "acceptance_nonmonomial/decomposition.rs"]
mod decomposition;
#[path = "acceptance_nonmonomial/duality.rs"]
mod duality;
#[path = "acceptance_nonmonomial/fixtures.rs"]
mod fixtures;
#[path = "acceptance_nonmonomial/resolutions.rs"]
mod resolutions;
#[path = "acceptance_nonmonomial/structure.rs"]
mod structure;
#[path = "acceptance_nonmonomial/tau.rs"]
mod tau;
#[path = "acceptance_nonmonomial/validation.rs"]
mod validation;

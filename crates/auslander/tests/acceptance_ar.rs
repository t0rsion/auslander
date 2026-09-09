//! Acceptance tests for AR translations, sequences, and quivers.
//!
//! Tier 1 covers Ext dimensions, Yoneda products, extensions from degree-1
//! classes, AR-duality almost-split sequences, and stable Hom, on the
//! non-monomial matrix plus k[x]/(x^3) and linear A_3. Tier 2 covers the AR
//! quiver, the middle-term cross-check, the catalog witness route, and arrow
//! valuations, and runs only where an exhaustive catalog exists. The
//! preprojective algebra of A_3 is representation finite but has no certified
//! catalog here, so it runs tier 1 only and the AR quiver dispatch rejects it
//! with both carried reasons.

mod common;

#[path = "acceptance_ar/almost_split.rs"]
mod almost_split;
#[path = "acceptance_ar/ar_quiver.rs"]
mod ar_quiver;
#[path = "acceptance_ar/support.rs"]
mod support;
#[path = "acceptance_ar/yoneda.rs"]
mod yoneda;

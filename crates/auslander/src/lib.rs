//! Finite-dimensional basic algebras `kQ/I` over a checked prime field, and
//! their finite-dimensional right modules.
//!
//! `I` is an admissible ideal presented by uniform relations. Each relation is
//! a k-linear combination of parallel paths. Every algebra comes from one
//! pipeline: completion rewrites the relations into a reduced Groebner basis
//! and emits a certificate. An independent verifier checks that certificate
//! before the algebra is built.
//!
//! Two conventions are fixed crate-wide. Modules are right modules, written
//! with row vectors. Paths compose left to right: `a·b` means first `a`, then
//! `b`, and `M(a·b) = M(a) M(b)`.
//!
//! Partiality is typed. A dimension known only from below is
//! `Bounded::AtLeast`. A resolution prefix that runs out of budget ends in
//! `ResolutionEnd::Cut` with the next syzygy known to be nonzero. Nothing
//! truncates silently.

macro_rules! accessor_methods {
    ($($(#[$attr:meta])* $vis:vis $name:ident($($argument:ident: $argument_type:ty),*) -> $output:ty = |$receiver:ident| $value:expr;)+) => {$(
        $(#[$attr])*
        #[inline]
        $vis fn $name(&self, $($argument: $argument_type),*) -> $output { let $receiver = self; $value }
    )+};
}

macro_rules! display_error {
    (error $type:ty { $($body:tt)* }) => {
        display_error!($type { $($body)* });
        impl std::error::Error for $type {}
    };
    ($type:ty { $($pattern:pat => $format:literal $(, $argument:expr)*;)+ }) => {
        impl std::fmt::Display for $type {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self { $($pattern => write!(f, $format $(, $argument)*),)+ }
            }
        }
    };
}

macro_rules! from_variants {
    ($target:ty { $($source:ty => $variant:ident),+ $(,)? }) => {$ (
        impl From<$source> for $target {
            fn from(error: $source) -> Self { Self::$variant(error) }
        }
    )+};
}

macro_rules! error_source {
    ($error:ty { $($pattern:pat => $source:expr),+ $(,)? }) => {
        impl std::error::Error for $error {
            fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
                match self { $($pattern => $source,)+ }
            }
        }
    };
}

macro_rules! debug_fields {
    ($(#[$attr:meta])* $type:ty |$this:ident| { $($field:literal => $value:expr;)+ }) => {
        $(#[$attr])*
        impl std::fmt::Debug for $type {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let $this = self;
                f.debug_struct(stringify!($type))$(.field($field, &$value))+.finish()
            }
        }
    };
}

macro_rules! verify_methods {
    ($visibility:vis, $prologue:block, $(#[$attr:meta])* |$this:ident, $context:ident| $body:block) => {
        $(#[$attr])*
        pub fn verify(&$this) -> bool {
            $this.verify_with_context(&VerificationContext::new())
        }
        $visibility fn verify_with_context(&$this, $context: &VerificationContext) -> bool {
            $prologue
            $body
        }
    };
}

macro_rules! binary_outcome_accessors {
    (
        $positive:ident, $negative:ident,
        $positive_method:ident -> $positive_ty:ty = |$positive_binding:ident| $positive_ref:expr,
        $negative_method:ident -> $negative_ty:ty = |$negative_binding:ident| $negative_ref:expr,
        $flag:ident,
        $into:ident -> $into_ty:ty = |$into_binding:ident| $into_value:expr;
        flag = $flag_doc:literal;
        positive = $positive_doc:literal;
        negative = $negative_doc:literal;
        into = $into_doc:literal;
    ) => {
        #[doc = $flag_doc]
        #[inline]
        pub fn $flag(&self) -> bool {
            matches!(self, Self::$positive(_))
        }
        optional_accessors! {
            #[doc = $positive_doc]
            pub $positive_method() -> &$positive_ty = Self::$positive($positive_binding) => $positive_ref;
            #[doc = $negative_doc]
            pub $negative_method() -> &$negative_ty = Self::$negative($negative_binding) => $negative_ref;
        }
        #[doc = $into_doc]
        #[inline]
        pub fn $into(self) -> Option<$into_ty> {
            match self {
                Self::$positive($into_binding) => Some($into_value),
                _ => None,
            }
        }
    };
}

macro_rules! binary_power {
    ($base:expr, $one:expr, $exponent:expr, |$left:ident, $right:ident| $product:expr) => {{
        let mut base = $base;
        let mut accumulator = $one;
        let mut exponent = $exponent;
        while exponent > 0 {
            if exponent & 1 == 1 {
                let ($left, $right) = (&accumulator, &base);
                accumulator = $product;
            }
            let ($left, $right) = (&base, &base);
            base = $product;
            exponent >>= 1;
        }
        accumulator
    }};
}

macro_rules! nominal_key {
    ($type:ty, |$left:ident, $right:ident| $equal:expr, |$this:ident| $address:expr) => {
        impl PartialEq for $type {
            fn eq(&self, other: &$type) -> bool {
                let ($left, $right) = (self, other);
                $equal
            }
        }
        impl Eq for $type {}
        impl std::hash::Hash for $type {
            fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
                let $this = self;
                std::hash::Hash::hash(&$address, state);
            }
        }
    };
}

macro_rules! optional_accessors {
    ($($(#[$attr:meta])* $vis:vis $name:ident() -> $output:ty = $pattern:pat => $value:expr;)+) => {$(
        $(#[$attr])*
        #[inline]
        $vis fn $name(&self) -> Option<$output> {
            match self { $pattern => Some($value), _ => None }
        }
    )+};
}

macro_rules! let_or_false {
    ($pattern:pat = $value:expr) => {
        let $pattern = $value else { return false };
    };
}

macro_rules! verify_guard {
    ($condition:expr) => {
        if !$condition {
            return false;
        }
    };
}

pub mod algebra;
pub mod almost_split;
pub mod approx;
pub mod ar;
pub mod arquiver;
pub mod atlas;
pub mod atlas_artifact;
pub mod basic;
pub mod batch;
pub mod batch_stream;
pub mod catalog_coordinates;
pub mod census;
pub mod certificate;
pub mod completion;
pub mod complex;
pub mod complex_target;
pub(crate) mod context;
pub mod control;
pub mod decompose;
pub mod derived;
pub mod derived_artifact;
pub mod derived_hom;
pub mod derived_transport;
pub mod dynkin;
pub mod endo;
pub mod enumerate;
pub mod equivalence_discovery;
pub mod equivalence_edge;
pub mod ext;
pub mod extalgebra;
pub mod family;
pub mod field;
pub mod gentle;
pub mod higher;
pub mod hochschild;
pub mod hom;
pub mod homotopy;
pub mod homspace;
pub mod indec;
pub mod injective;
pub mod interface;
pub mod iso;
pub mod linalg;
pub mod module;
pub mod monomial;
pub mod mutation;
pub mod opposite;
pub mod order;
pub mod perfect;
pub mod profile;
pub mod quiver;
pub mod radical;
pub mod relation;
pub mod resolution;
pub mod sequence;
pub mod supporttau;
pub mod target;
pub mod taugraph;
pub mod taurigid;
pub mod theorem_artifact;
pub mod tilting;
pub mod tilting_complex;
pub mod verify;

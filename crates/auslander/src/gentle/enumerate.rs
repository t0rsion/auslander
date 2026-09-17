use std::collections::BTreeSet;
use std::sync::Arc;

use crate::algebra::Algebra;
use crate::decompose::{Certificate, decompose};
use crate::linalg::DenseMat;
use crate::module::Module;
use crate::quiver::{ArrowId, Quiver};

use super::errors::GentleError;
use super::validate::{ValidatedGentle, validate};

/// One arrow letter in a string, with `inverse` recording its orientation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct GentleLetter {
    arrow: ArrowId,
    inverse: bool,
}

impl GentleLetter {
    /// The direct letter `a` for arrow `a`.
    pub fn direct(arrow: ArrowId) -> GentleLetter {
        GentleLetter {
            arrow,
            inverse: false,
        }
    }

    /// The inverse letter `a⁻¹` for arrow `a`.
    pub fn inverse(arrow: ArrowId) -> GentleLetter {
        GentleLetter {
            arrow,
            inverse: true,
        }
    }

    accessor_methods! {
        /// The underlying quiver arrow.
        pub arrow() -> ArrowId = |this| this.arrow;
        /// Whether the letter traverses its arrow backwards.
        pub is_inverse() -> bool = |this| this.inverse;
    }
}

/// A canonical reduced string, with one chosen orientation from its endpoint
/// pair. Its inverse is represented by the same endpoint pair in reverse order.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct GentleString {
    start: u32,
    vertices: Vec<u32>,
    letters: Vec<GentleLetter>,
}

impl GentleString {
    fn new(start: u32, vertices: Vec<u32>, letters: Vec<GentleLetter>) -> GentleString {
        GentleString {
            start,
            vertices,
            letters,
        }
    }

    accessor_methods! {
        /// The first vertex of the chosen orientation.
        pub start() -> u32 = |this| this.start;
        /// The last vertex of the chosen orientation.
        pub end() -> u32 = |this| *this.vertices.last().expect("a string has one vertex");
        /// Vertices visited by the string, including both endpoints.
        pub vertices() -> &[u32] = |this| &this.vertices;
        /// Letters in left-to-right string order.
        pub letters() -> &[GentleLetter] = |this| &this.letters;
        /// Number of letters.
        pub len() -> usize = |this| this.letters.len();
        /// Whether the string has no letters.
        pub is_empty() -> bool = |this| this.letters.is_empty();
    }
}

/// Every reduced string of a gentle tree algebra, modulo inverse, in endpoint
/// order. The classification theorem makes this list complete and finite.
pub fn gentle_tree_strings(algebra: &Arc<Algebra>) -> Result<Vec<GentleString>, GentleError> {
    let checked = validate(algebra)?;
    let vertices = algebra.quiver().num_vertices() as usize;
    let mut strings = Vec::new();
    let mut keys = BTreeSet::new();
    for start in 0..vertices as u32 {
        let mut collector = Collector {
            quiver: algebra.quiver(),
            checked: &checked,
            start,
            letters: Vec::new(),
            vertices: vec![start],
            keys: &mut keys,
            output: &mut strings,
        };
        collector.visit(start, None);
    }
    strings.sort_by_key(|string| (string.start, string.end()));
    Ok(strings)
}

/// Every indecomposable right module of a gentle algebra on a tree.
///
/// Butler and Ringel classify indecomposables of a string algebra as string or
/// band modules. See M. C. R. Butler and C. M. Ringel, *Auslander-Reiten
/// sequences with few middle terms and applications to string algebras*,
/// *Comm. Algebra* 15 (1987), 145-179. A reduced string is a walk in the
/// underlying graph. A tree has no nontrivial closed reduced walk, so it has no
/// bands. Every remaining string is a simple undirected path, and its inverse
/// gives the same module. The path between two endpoints is unique, so the
/// endpoint key `(start, end)` selects one representative of each class.
pub fn gentle_tree_indecomposables(
    algebra: &Arc<Algebra>,
) -> Result<Vec<(Module, Certificate)>, GentleError> {
    gentle_tree_strings(algebra).map(|strings| {
        strings
            .into_iter()
            .map(|string| certified_module(algebra, &string))
            .collect()
    })
}

struct Collector<'a> {
    quiver: &'a Quiver,
    checked: &'a ValidatedGentle,
    start: u32,
    letters: Vec<GentleLetter>,
    vertices: Vec<u32>,
    keys: &'a mut BTreeSet<(u32, u32)>,
    output: &'a mut Vec<GentleString>,
}

impl Collector<'_> {
    fn visit(&mut self, current: u32, previous: Option<u32>) {
        self.emit(current);
        let neighbours = self.checked.neighbours[current as usize].clone();
        for (next, arrow) in neighbours {
            if Some(next) == previous {
                continue;
            }
            let letter = letter_for_step(self.quiver, current, arrow);
            if !allows(
                self.letters.last().copied(),
                letter,
                &self.checked.forbidden,
            ) {
                continue;
            }
            self.letters.push(letter);
            self.vertices.push(next);
            self.visit(next, Some(current));
            self.vertices.pop();
            self.letters.pop();
        }
    }

    fn emit(&mut self, current: u32) {
        if self.start <= current {
            let key = (self.start, current);
            assert!(
                self.keys.insert(key),
                "two tree paths share a string endpoint key"
            );
            self.output.push(GentleString::new(
                self.start,
                self.vertices.clone(),
                self.letters.clone(),
            ));
        }
    }
}

fn letter_for_step(quiver: &Quiver, current: u32, arrow: ArrowId) -> GentleLetter {
    if current != quiver.source(arrow) {
        GentleLetter::inverse(arrow)
    } else {
        GentleLetter::direct(arrow)
    }
}

fn allows(
    previous: Option<GentleLetter>,
    next: GentleLetter,
    forbidden: &rustc_hash::FxHashSet<(ArrowId, ArrowId)>,
) -> bool {
    let Some(previous) = previous else {
        return true;
    };
    if previous.arrow == next.arrow && previous.inverse != next.inverse {
        return false;
    }
    if previous.inverse == next.inverse {
        let pair = if previous.inverse {
            (next.arrow, previous.arrow)
        } else {
            (previous.arrow, next.arrow)
        };
        return !forbidden.contains(&pair);
    }
    true
}

fn certified_module(algebra: &Arc<Algebra>, string: &GentleString) -> (Module, Certificate) {
    let module = module_from_string(algebra, string);
    let decomposition = decompose(&module);
    assert_eq!(
        decomposition.summands().len(),
        1,
        "a tree string split into {} summands; library bug",
        decomposition.summands().len()
    );
    assert_eq!(
        decomposition.certificates(),
        [Certificate::Indecomposable],
        "a tree string was not certified indecomposable; library bug"
    );
    (module, Certificate::Indecomposable)
}

fn module_from_string(algebra: &Arc<Algebra>, string: &GentleString) -> Module {
    let quiver = algebra.quiver();
    let mut dims = vec![0usize; quiver.num_vertices() as usize];
    for &vertex in &string.vertices {
        dims[vertex as usize] = 1;
    }
    let mut maps = zero_maps(algebra, &dims);
    for letter in &string.letters {
        maps[letter.arrow.index()].set(0, 0, algebra.field().one());
    }
    Module::new(algebra.clone(), dims, maps)
        .expect("a reduced gentle string satisfies every checked relation")
}

fn zero_maps(algebra: &Algebra, dims: &[usize]) -> Vec<DenseMat> {
    algebra
        .quiver()
        .arrows()
        .iter()
        .map(|&(source, target)| DenseMat::zero(dims[source as usize], dims[target as usize]))
        .collect()
}

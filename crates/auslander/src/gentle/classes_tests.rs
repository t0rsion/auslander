use std::collections::BTreeSet;
use std::sync::Arc;

use super::presentation_tests::bound;
use super::*;
use crate::algebra::Algebra;
use crate::field::PrimeField;
use crate::monomial::{MonomialError, MonomialIdeal, MonomialPresentation};
use crate::quiver::{ArrowId, Quiver};

fn f2() -> PrimeField {
    PrimeField::new(2).unwrap()
}

#[test]
fn one_and_two_vertices_match_the_hand_count() {
    // n = 1: k and k[x]/(x²). A loop x with x² ∉ I, or two loops, has a
    // permitted cycle.
    let one = connected_gentle_keys(1);
    assert_eq!(one.len(), 2);
    assert_eq!(one[0].arrows(), []);
    assert_eq!(one[1].arrows(), [(0, 0)]);
    assert_eq!(one[1].relations(), [(ArrowId(0), ArrowId(0))]);
    // n = 2, one arrow: A_2. Two arrows: the Kronecker quiver, the 2-cycle
    // with one or two relations, and a loop x with x² = 0 at either end of an
    // arrow. Three arrows: two parallel arrows and one back with relations
    // b·c and c·a, the 2-cycle with one loop, and an arrow with a loop at
    // each end. That is 1 + 5 + 3 = 9.
    let two = connected_gentle_keys(2);
    let by_arrows: Vec<usize> = (1..=3)
        .map(|count| two.iter().filter(|key| key.arrows().len() == count).count())
        .collect();
    assert_eq!(by_arrows, [1, 5, 3]);
    assert_eq!(connected_gentle_keys(0), []);
}

#[test]
fn enumeration_matches_brute_force_up_to_three_vertices() {
    for vertices in 1..=3 {
        let keys = connected_gentle_keys(vertices);
        assert_eq!(
            keys.len(),
            brute_force_classes(vertices).len(),
            "n = {vertices}"
        );
        let sorted = keys.windows(2).all(|pair| pair[0] < pair[1]);
        assert!(sorted, "keys are sorted and distinct");
    }
}

#[test]
fn every_enumerated_presentation_up_to_five_vertices_is_consistent() {
    for vertices in 1..=5 {
        let keys = connected_gentle_keys(vertices);
        let algebras = connected_gentle_algebras(vertices, f2()).unwrap();
        assert_eq!(algebras.len(), keys.len());
        for (key, algebra) in keys.iter().zip(&algebras) {
            let presentation = GentlePresentation::new(algebra).unwrap();
            assert_eq!(&presentation.key(), key);
            check_counts(&presentation);
            check_paper_signs(&presentation);
        }
    }
}

#[test]
fn aag_function_and_key_survive_random_relabeling() {
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    for key in connected_gentle_keys(4).iter().step_by(5) {
        let algebra = key.algebra(f2()).unwrap();
        let presentation = GentlePresentation::new(&algebra).unwrap();
        for _ in 0..3 {
            let relabeled = GentlePresentation::new(&relabel(key, &mut state)).unwrap();
            assert_eq!(relabeled.aag_function(), presentation.aag_function());
            assert_eq!(&relabeled.key(), key);
            assert_eq!(relabeled.genus(), presentation.genus());
        }
    }
}

#[test]
fn a_labeling_maps_the_presentation_onto_its_key() {
    let algebra = bound(
        3,
        &[(1, 2), (2, 0), (0, 1), (0, 0)],
        &[(0, 1), (1, 2), (3, 3)],
    );
    let labeling = GentlePresentation::new(&algebra)
        .unwrap()
        .canonical_labeling();
    let key = labeling.key();
    for (index, &(source, target)) in algebra.quiver().arrows().iter().enumerate() {
        let image = labeling.arrow_map()[index];
        let endpoints = (
            labeling.vertex_map()[source as usize],
            labeling.vertex_map()[target as usize],
        );
        assert_eq!(key.arrows()[image.index()], endpoints);
    }
}

fn check_counts(presentation: &GentlePresentation) {
    let quiver = presentation.algebra().quiver();
    let (vertices, arrows) = (quiver.num_vertices() as usize, quiver.num_arrows());
    let permitted = presentation.permitted_threads().len();
    let aag = presentation.aag_function();
    // Avella-Alaminos and Geiss, Remark 8: the first entries sum to the number
    // of permitted threads and the second entries to the number of arrows.
    assert_eq!(
        aag.pairs().iter().map(|pair| pair.0).sum::<usize>(),
        permitted
    );
    assert_eq!(aag.pairs().iter().map(|pair| pair.1).sum::<usize>(), arrows);
    assert_eq!(permitted, 2 * vertices - arrows);
    let doubled = (vertices + 2) as i64 - permitted as i64 - aag.len() as i64;
    assert!(doubled >= 0 && doubled % 2 == 0, "doubled genus {doubled}");
    assert_eq!(presentation.genus() as i64, doubled / 2);
}

/// Checks rules (1)-(3) of section 2.2 of Avella-Alaminos and Geiss, the
/// imposed rule for relations, and the trivial threads of the same section.
fn check_paper_signs(presentation: &GentlePresentation) {
    let quiver = presentation.algebra().quiver();
    let relations: BTreeSet<_> = presentation.relations().iter().copied().collect();
    for vertex in 0..quiver.num_vertices() {
        let (outgoing, incoming) = (quiver.arrows_from(vertex), quiver.arrows_to(vertex));
        if let [first, second] = outgoing {
            assert_ne!(presentation.sigma(*first), presentation.sigma(*second));
        }
        if let [first, second] = incoming {
            assert_ne!(presentation.epsilon(*first), presentation.epsilon(*second));
        }
        for (&b, &c) in incoming
            .iter()
            .flat_map(|b| outgoing.iter().map(move |c| (b, c)))
        {
            let same = presentation.sigma(c) == presentation.epsilon(b);
            assert_eq!(same, relations.contains(&(b, c)));
        }
        check_trivial_threads(presentation, vertex, &relations);
    }
}

fn check_trivial_threads(
    presentation: &GentlePresentation,
    vertex: u32,
    relations: &BTreeSet<(ArrowId, ArrowId)>,
) {
    let quiver = presentation.algebra().quiver();
    let (outgoing, incoming) = (quiver.arrows_from(vertex), quiver.arrows_to(vertex));
    let small = outgoing.len() <= 1 && incoming.len() <= 1;
    let through = incoming
        .first()
        .zip(outgoing.first())
        .map(|(&b, &c)| relations.contains(&(b, c)));
    // The paper defines one trivial thread per qualifying vertex and assumes
    // an arrow exists. The quiver of k has none and gets two of each kind.
    let copies = if quiver.num_arrows() == 0 { 2 } else { 1 };
    let count = |qualifies: bool| if small && qualifies { copies } else { 0 };
    let from_out = outgoing.first().map(|&c| presentation.sigma(c).negated());
    let from_in = incoming.first().map(|&b| presentation.epsilon(b));
    let permitted = from_out.or(from_in);
    let forbidden = from_out.or(from_in.map(Sign::negated));
    let at = |threads: &[GentleThread]| -> Vec<GentleThread> {
        threads
            .iter()
            .filter(|thread| thread.is_trivial() && thread.start() == vertex)
            .cloned()
            .collect()
    };
    check_trivial_kind(
        &at(presentation.permitted_threads()),
        count(through != Some(true)),
        permitted,
        Sign::negated,
    );
    check_trivial_kind(
        &at(presentation.forbidden_threads()),
        count(through != Some(false)),
        forbidden,
        |sign| sign,
    );
}

/// Checks the count of trivial threads at one vertex, `σ` against the
/// paper's reference value, and `ε` as a function of `σ`.
fn check_trivial_kind(
    trivial: &[GentleThread],
    count: usize,
    reference: Option<Sign>,
    epsilon_of: fn(Sign) -> Sign,
) {
    assert_eq!(trivial.len(), count);
    for thread in trivial {
        assert_eq!(thread.epsilon(), epsilon_of(thread.sigma()));
        assert!(reference.is_none_or(|sign| sign == thread.sigma()));
    }
}

fn next_random(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

fn shuffled(len: usize, state: &mut u64) -> Vec<usize> {
    let mut order: Vec<usize> = (0..len).collect();
    for position in (1..len).rev() {
        order.swap(position, next_random(state) as usize % (position + 1));
    }
    order
}

/// The key's presentation under a random vertex and arrow relabeling.
pub(super) fn relabel(key: &GentleKey, state: &mut u64) -> Arc<Algebra> {
    let vertices = shuffled(key.vertices() as usize, state);
    let arrows = shuffled(key.arrows().len(), state);
    let mut new_arrows = vec![(0, 0); arrows.len()];
    for (old, &new) in arrows.iter().enumerate() {
        let (source, target) = key.arrows()[old];
        new_arrows[new] = (
            vertices[source as usize] as u32,
            vertices[target as usize] as u32,
        );
    }
    let relations: Vec<(u32, u32)> = key
        .relations()
        .iter()
        .map(|&(b, c)| (arrows[b.index()] as u32, arrows[c.index()] as u32))
        .collect();
    bound(key.vertices(), &new_arrows, &relations)
}

type BruteKey = (Vec<(u32, u32)>, Vec<(usize, usize)>);

/// Classes by exhaustive search, independent of slots and of the key walk.
fn brute_force_classes(vertices: u32) -> BTreeSet<BruteKey> {
    let pairs: Vec<(u32, u32)> = (0..vertices)
        .flat_map(|source| (0..vertices).map(move |target| (source, target)))
        .collect();
    let mut classes = BTreeSet::new();
    let mut counts = vec![0usize; pairs.len()];
    loop {
        let arrows: Vec<(u32, u32)> = pairs
            .iter()
            .zip(&counts)
            .flat_map(|(&pair, &count)| std::iter::repeat_n(pair, count))
            .collect();
        if degrees_fit(vertices, &arrows) && connected(vertices, &arrows) {
            add_relation_choices(vertices, &arrows, &mut classes);
        }
        if !advance(&mut counts) {
            return classes;
        }
    }
}

fn advance(counts: &mut [usize]) -> bool {
    for count in counts.iter_mut() {
        if *count < 2 {
            *count += 1;
            return true;
        }
        *count = 0;
    }
    false
}

fn degrees_fit(vertices: u32, arrows: &[(u32, u32)]) -> bool {
    (0..vertices).all(|vertex| {
        arrows.iter().filter(|arrow| arrow.0 == vertex).count() <= 2
            && arrows.iter().filter(|arrow| arrow.1 == vertex).count() <= 2
    })
}

fn connected(vertices: u32, arrows: &[(u32, u32)]) -> bool {
    let mut reached = vec![false; vertices as usize];
    reached[0] = true;
    for _ in 0..vertices {
        for &(source, target) in arrows {
            let either = reached[source as usize] || reached[target as usize];
            reached[source as usize] |= either;
            reached[target as usize] |= either;
        }
    }
    reached.iter().all(|&value| value)
}

fn add_relation_choices(vertices: u32, arrows: &[(u32, u32)], classes: &mut BTreeSet<BruteKey>) {
    let composable: Vec<(usize, usize)> = (0..arrows.len())
        .flat_map(|b| (0..arrows.len()).map(move |c| (b, c)))
        .filter(|&(b, c)| arrows[b].1 == arrows[c].0)
        .collect();
    for mask in 0..1u32 << composable.len() {
        let relations: Vec<(usize, usize)> = (0..composable.len())
            .filter(|bit| mask >> bit & 1 == 1)
            .map(|bit| composable[bit])
            .collect();
        if continuations_fit(arrows, &composable, &relations)
            && finite(vertices, arrows, &relations)
        {
            classes.insert(brute_key(vertices, arrows, &relations));
        }
    }
}

fn continuations_fit(
    arrows: &[(u32, u32)],
    composable: &[(usize, usize)],
    relations: &[(usize, usize)],
) -> bool {
    (0..arrows.len()).all(|arrow| {
        let count = |pick: &dyn Fn(&(usize, usize)) -> bool, related: bool| {
            composable
                .iter()
                .filter(|pair| pick(pair) && relations.contains(pair) == related)
                .count()
                <= 1
        };
        let after = |pair: &(usize, usize)| pair.0 == arrow;
        let before = |pair: &(usize, usize)| pair.1 == arrow;
        count(&after, true) && count(&after, false) && count(&before, true) && count(&before, false)
    })
}

fn finite(vertices: u32, arrows: &[(u32, u32)], relations: &[(usize, usize)]) -> bool {
    let quiver = Quiver::new(vertices, arrows).unwrap();
    let words = relations
        .iter()
        .map(|&(b, c)| vec![ArrowId(b as u32), ArrowId(c as u32)])
        .collect();
    match MonomialPresentation::new(MonomialIdeal::new(quiver, words).unwrap()) {
        Ok(_) => true,
        Err(MonomialError::InfiniteDimensional) => false,
        Err(error) => panic!("unexpected monomial error {error}"),
    }
}

/// The least relabeled form over every vertex permutation and every order of
/// parallel arrows.
fn brute_key(vertices: u32, arrows: &[(u32, u32)], relations: &[(usize, usize)]) -> BruteKey {
    permutations(vertices as usize)
        .into_iter()
        .flat_map(|permutation| {
            let mapped: Vec<(u32, u32)> = arrows
                .iter()
                .map(|&(s, t)| {
                    (
                        permutation[s as usize] as u32,
                        permutation[t as usize] as u32,
                    )
                })
                .collect();
            arrow_orders(&mapped)
                .into_iter()
                .map(move |order| encode(&mapped, &order, relations))
                .collect::<Vec<_>>()
        })
        .min()
        .unwrap()
}

fn encode(mapped: &[(u32, u32)], order: &[usize], relations: &[(usize, usize)]) -> BruteKey {
    let mut label = vec![0; order.len()];
    for (position, &arrow) in order.iter().enumerate() {
        label[arrow] = position;
    }
    let arrows = order.iter().map(|&arrow| mapped[arrow]).collect();
    let mut related: Vec<(usize, usize)> = relations
        .iter()
        .map(|&(b, c)| (label[b], label[c]))
        .collect();
    related.sort_unstable();
    (arrows, related)
}

/// Every order of the arrows sorted by endpoints, with parallel arrows in
/// either order.
fn arrow_orders(mapped: &[(u32, u32)]) -> Vec<Vec<usize>> {
    let mut base: Vec<usize> = (0..mapped.len()).collect();
    base.sort_by_key(|&arrow| mapped[arrow]);
    let pairs: Vec<usize> = (1..base.len())
        .filter(|&position| mapped[base[position]] == mapped[base[position - 1]])
        .collect();
    (0..1usize << pairs.len())
        .map(|mask| {
            let mut order = base.clone();
            for (bit, &position) in pairs.iter().enumerate() {
                if mask >> bit & 1 == 1 {
                    order.swap(position - 1, position);
                }
            }
            order
        })
        .collect()
}

fn permutations(len: usize) -> Vec<Vec<usize>> {
    if len == 0 {
        return vec![Vec::new()];
    }
    permutations(len - 1)
        .into_iter()
        .flat_map(|shorter| {
            (0..len).map(move |position| {
                let mut longer = shorter.clone();
                longer.insert(position, len - 1);
                longer
            })
        })
        .collect()
}

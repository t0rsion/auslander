use super::polynomial::raw_word;
use super::types::Word;
use crate::certificate::AutomatonData;
use crate::quiver::{ArrowId, Quiver};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
/// Builds the shared normal-word automaton states and transitions.
///
/// `forbidden` must be factor-minimal. Then a prefix match cannot hide a
/// shorter forbidden suffix.
pub(super) fn normal_word_transitions<W: AsRef<[ArrowId]>>(
    quiver: &Quiver,
    forbidden: &[W],
) -> (Vec<Word>, Vec<Vec<Option<usize>>>) {
    let n = quiver.num_vertices() as usize;
    let mut prefix_set = BTreeSet::new();
    for word in forbidden {
        let word = word.as_ref();
        for len in 1..word.len() {
            prefix_set.insert(word[..len].to_vec());
        }
    }
    let mut words = vec![Word::new(); n];
    let mut prefix_index = BTreeMap::new();
    for prefix in prefix_set {
        prefix_index.insert(prefix.clone(), words.len());
        words.push(prefix);
    }
    let forbidden_set: BTreeSet<&[ArrowId]> = forbidden.iter().map(|word| word.as_ref()).collect();
    let mut trans = vec![vec![None; quiver.num_arrows()]; words.len()];
    for (state, row) in trans.iter_mut().enumerate() {
        let (word, vertex) = if state < n {
            (&[][..], state as u32)
        } else {
            let word = words[state].as_slice();
            (word, quiver.target(word[word.len() - 1]))
        };
        for &arrow in quiver.arrows_from(vertex) {
            let mut extended = word.to_vec();
            extended.push(arrow);
            let mut next = Some(quiver.target(arrow) as usize);
            for start in 0..extended.len() {
                let suffix = &extended[start..];
                if forbidden_set.contains(suffix) {
                    next = None;
                    break;
                }
                if let Some(&index) = prefix_index.get(suffix) {
                    next = Some(index);
                    break;
                }
            }
            row[arrow.index()] = next;
        }
    }
    (words, trans)
}

/// The normal-word automaton over the final leading words. States `0..n`
/// are the vertices. The rest are the proper nonempty prefixes of leading
/// words, sorted lexicographically. Reading a normal word from its
/// source-vertex state ends in the state of that word's longest tracked
/// suffix. An arrow that completes a leading word has no transition.
pub(super) struct PrefixAutomaton {
    /// The word of each state; empty for the start states.
    words: Vec<Word>,
    trans: Vec<Vec<Option<usize>>>,
    starts: usize,
}

impl PrefixAutomaton {
    pub(super) fn build(quiver: &Quiver, forbidden: &[&Word]) -> PrefixAutomaton {
        let (words, trans) = normal_word_transitions(quiver, forbidden);
        PrefixAutomaton {
            words,
            trans,
            starts: quiver.num_vertices() as usize,
        }
    }

    /// The automaton as certificate data: state words in state order,
    /// sparse transition triples sorted by state then arrow.
    pub(super) fn data(&self) -> AutomatonData {
        let states = self.words.iter().map(|w| raw_word(w)).collect();
        let mut transitions = Vec::new();
        for (state, row) in self.trans.iter().enumerate() {
            for (arrow, next) in row.iter().enumerate() {
                if let Some(next) = next {
                    transitions.push((state, arrow as u32, *next));
                }
            }
        }
        AutomatonData {
            states,
            transitions,
        }
    }

    fn reachable_states(&self) -> (Vec<bool>, Vec<Option<(usize, u32)>>) {
        let m = self.trans.len();
        let mut reachable = vec![false; m];
        let mut parent: Vec<Option<(usize, u32)>> = vec![None; m];
        let mut queue: VecDeque<usize> = (0..self.starts).collect();
        reachable[..self.starts].fill(true);
        while let Some(state) = queue.pop_front() {
            for (arrow, next) in self.trans[state].iter().enumerate() {
                let Some(next) = *next else { continue };
                if !reachable[next] {
                    reachable[next] = true;
                    parent[next] = Some((state, arrow as u32));
                    queue.push_back(next);
                }
            }
        }
        (reachable, parent)
    }

    fn outgoing_graph(&self, reachable: &[bool]) -> (Vec<usize>, Vec<Vec<usize>>) {
        let mut out_degree = vec![0usize; self.trans.len()];
        let mut predecessors: Vec<Vec<usize>> = vec![Vec::new(); self.trans.len()];
        for state in 0..self.trans.len() {
            if !reachable[state] {
                continue;
            }
            for &next in self.trans[state].iter().flatten() {
                out_degree[state] += 1;
                predecessors[next].push(state);
            }
        }
        (out_degree, predecessors)
    }

    fn live_states(
        &self,
        reachable: &[bool],
        mut out_degree: Vec<usize>,
        predecessors: Vec<Vec<usize>>,
    ) -> Vec<bool> {
        let mut removed = vec![false; self.trans.len()];
        let mut ready: VecDeque<usize> = (0..self.trans.len())
            .filter(|&state| reachable[state] && out_degree[state] == 0)
            .collect();
        while let Some(state) = ready.pop_front() {
            removed[state] = true;
            for &before in &predecessors[state] {
                out_degree[before] -= 1;
                if out_degree[before] == 0 {
                    ready.push_back(before);
                }
            }
        }
        reachable
            .iter()
            .zip(removed)
            .map(|(&reachable, removed)| reachable && !removed)
            .collect()
    }

    fn cycle_path(&self, live: &[bool]) -> Option<(usize, usize, Vec<u32>)> {
        let start = (0..self.trans.len()).find(|&state| live[state])?;
        let mut position = BTreeMap::new();
        let mut walk: Vec<u32> = Vec::new();
        let mut current = start;
        let (entry, cycle_state) = loop {
            if let Some(&at) = position.get(&current) {
                break (at, current);
            }
            position.insert(current, walk.len());
            let (arrow, next) = self.trans[current]
                .iter()
                .enumerate()
                .find_map(|(arrow, next)| next.filter(|&t| live[t]).map(|t| (arrow as u32, t)))
                .expect("a state that survives pruning keeps a surviving successor");
            walk.push(arrow);
            current = next;
        };
        Some((entry, cycle_state, walk))
    }

    /// A `(prefix, cycle)` word witness when the reachable part of the
    /// automaton has a cycle; `None` when it is acyclic, so the language
    /// is finite. The prefix reads from the start state of its source
    /// vertex to a state on the cycle, and the cycle returns to exactly
    /// that state, so every step follows an automaton edge and the whole
    /// walk spells a normal word.
    pub(super) fn cycle_witness(&self) -> Option<(Vec<u32>, Vec<u32>)> {
        let (reachable, parent) = self.reachable_states();
        let (out_degree, predecessors) = self.outgoing_graph(&reachable);
        let live = self.live_states(&reachable, out_degree, predecessors);
        let (entry, cycle_state, walk) = self.cycle_path(&live)?;
        let cycle = walk[entry..].to_vec();
        let mut prefix = Vec::new();
        let mut state = cycle_state;
        while let Some((before, arrow)) = parent[state] {
            prefix.push(arrow);
            state = before;
        }
        prefix.reverse();
        Some((prefix, cycle))
    }

    #[inline]
    pub(super) fn step(&self, state: usize, arrow: ArrowId) -> Option<usize> {
        self.trans[state][arrow.index()]
    }
}

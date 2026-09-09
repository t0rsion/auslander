use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::certificate::{Certificate, FinitenessData};
use crate::quiver::{ArrowId, PathWord, Quiver};

use super::common::{find_factor, first_mismatch, ids, is_suffix};
use super::types::{CycleWitness, VerifyError, WitnessDefect};

/// The normal-word automaton. State `v < starts` is the start state at
/// vertex `v`. Every other state is a proper nonempty prefix of a basis
/// leading word, and those states are sorted lexicographically. After
/// reading a word the automaton sits in the state of that word's longest
/// suffix that is still a proper prefix of a leading word.
struct Automaton {
    /// The word of each state; empty for the start states.
    words: Vec<Vec<u32>>,
    /// Outgoing edges `(arrow, target state)` in arrow order.
    edges: Vec<Vec<(u32, usize)>>,
    starts: usize,
}

fn build_automaton(quiver: &Quiver, leads: &[Vec<u32>]) -> Automaton {
    let starts = quiver.num_vertices() as usize;
    let mut prefixes = BTreeSet::new();
    for lead in leads {
        for len in 1..lead.len() {
            prefixes.insert(lead[..len].to_vec());
        }
    }
    let mut words: Vec<Vec<u32>> = vec![Vec::new(); starts];
    let mut vertices: Vec<u32> = (0..quiver.num_vertices()).collect();
    let mut index_of = BTreeMap::new();
    for prefix in &prefixes {
        index_of.insert(prefix.clone(), words.len());
        vertices.push(quiver.target(ArrowId(prefix[prefix.len() - 1])));
        words.push(prefix.clone());
    }
    let mut edges = vec![Vec::new(); words.len()];
    for state in 0..words.len() {
        for &arrow in quiver.arrows_from(vertices[state]) {
            let mut candidate = words[state].clone();
            candidate.push(arrow.0);
            if leads.iter().any(|lead| is_suffix(lead, &candidate)) {
                continue;
            }
            let mut next = quiver.target(arrow) as usize;
            for cut in 0..candidate.len() {
                if let Some(&found) = index_of.get(&candidate[cut..]) {
                    next = found;
                    break;
                }
            }
            edges[state].push((arrow.0, next));
        }
    }
    Automaton {
        words,
        edges,
        starts,
    }
}

/// The certificate's automaton section must equal the verifier's own
/// automaton state for state and transition for transition, in canonical
/// order: states are the vertices then the sorted prefixes; transitions
/// are sorted by state then arrow.
fn check_automaton(own: &Automaton, certificate: &Certificate) -> Result<(), VerifyError> {
    let found_states = &certificate.automaton.states;
    if let Some((position, expected, found)) =
        first_mismatch(own.words.iter().cloned(), found_states)
    {
        return Err(VerifyError::AutomatonStates {
            position,
            expected,
            found,
        });
    }
    let expected = own
        .edges
        .iter()
        .enumerate()
        .flat_map(|(state, row)| row.iter().map(move |&(arrow, next)| (state, arrow, next)));
    if let Some((position, expected, found)) =
        first_mismatch(expected, &certificate.automaton.transitions)
    {
        return Err(VerifyError::AutomatonTransitions {
            position,
            expected,
            found,
        });
    }
    Ok(())
}

/// Whether the reachable part of the automaton has a cycle. Repeatedly
/// removing states with no outgoing edge leaves exactly the states that
/// start an infinite walk, so a survivor means a cycle.
fn automaton_has_cycle(automaton: &Automaton) -> bool {
    let n = automaton.edges.len();
    let mut reachable = vec![false; n];
    let mut queue: VecDeque<usize> = (0..automaton.starts).collect();
    reachable[..automaton.starts].fill(true);
    while let Some(state) = queue.pop_front() {
        for &(_, next) in &automaton.edges[state] {
            if !reachable[next] {
                reachable[next] = true;
                queue.push_back(next);
            }
        }
    }
    let mut out_degree = vec![0usize; n];
    let mut predecessors: Vec<Vec<usize>> = vec![Vec::new(); n];
    for state in 0..n {
        if !reachable[state] {
            continue;
        }
        out_degree[state] = automaton.edges[state].len();
        for &(_, next) in &automaton.edges[state] {
            predecessors[next].push(state);
        }
    }
    let mut removed = 0usize;
    let total = reachable.iter().filter(|&&r| r).count();
    let mut ready: VecDeque<usize> = (0..n)
        .filter(|&state| reachable[state] && out_degree[state] == 0)
        .collect();
    while let Some(state) = ready.pop_front() {
        removed += 1;
        for &before in &predecessors[state] {
            out_degree[before] -= 1;
            if out_degree[before] == 0 {
                ready.push_back(before);
            }
        }
    }
    removed < total
}

/// Reads `word` from `start` along automaton edges. Returns the reached
/// state, or the position of the first arrow without an edge.
fn replay_word(automaton: &Automaton, start: usize, word: &[u32]) -> Result<usize, usize> {
    let mut state = start;
    for (at, &arrow) in word.iter().enumerate() {
        match automaton.edges[state].iter().find(|&&(a, _)| a == arrow) {
            Some(&(_, next)) => state = next,
            None => return Err(at),
        }
    }
    Ok(state)
}

/// Full verification of an infinite-dimension witness: the cycle is
/// nonempty, `prefix·cycle·cycle` is a path free of every leading word,
/// the prefix reads to a state `s`, and one cycle from `s` returns to
/// exactly `s`. State return proves arbitrary repetition, so every
/// `prefix·cycle^k` is a normal word.
fn check_witness(
    quiver: &Quiver,
    automaton: &Automaton,
    leads: &[Vec<u32>],
    prefix: &[u32],
    cycle: &[u32],
) -> Result<CycleWitness, VerifyError> {
    let defect = |defect: WitnessDefect| VerifyError::InfiniteWitness { defect };
    if cycle.is_empty() {
        return Err(defect(WitnessDefect::EmptyCycle));
    }
    let mut word = prefix.to_vec();
    word.extend_from_slice(cycle);
    word.extend_from_slice(cycle);
    let path = PathWord::from_arrows(quiver, &ids(&word))
        .map_err(|error| defect(WitnessDefect::NotAPath(error)))?;
    for (lead, lead_word) in leads.iter().enumerate() {
        if let Some(position) = find_factor(&word, lead_word) {
            return Err(defect(WitnessDefect::ContainsLeadingWord {
                lead,
                position,
            }));
        }
    }
    let start = path.source() as usize;
    let reached = replay_word(automaton, start, prefix)
        .map_err(|at| defect(WitnessDefect::PrefixLeaves { at }))?;
    let back = replay_word(automaton, reached, cycle)
        .map_err(|at| defect(WitnessDefect::CycleLeaves { at }))?;
    if back != reached {
        return Err(defect(WitnessDefect::CycleDoesNotReturn { reached, back }));
    }
    Ok(CycleWitness {
        prefix: prefix.to_vec(),
        cycle: cycle.to_vec(),
    })
}

/// Longest walk length from each state. The caller guarantees the
/// automaton is acyclic. Every walk prefix is a walk, so a walk of length
/// `k` exists from a state exactly when `k <= longest[state]`.
fn longest_walks(automaton: &Automaton) -> Vec<usize> {
    let n = automaton.edges.len();
    let mut indegree = vec![0usize; n];
    for row in &automaton.edges {
        for &(_, next) in row {
            indegree[next] += 1;
        }
    }
    let mut order = Vec::with_capacity(n);
    let mut queue: VecDeque<usize> = (0..n).filter(|&state| indegree[state] == 0).collect();
    while let Some(state) = queue.pop_front() {
        order.push(state);
        for &(_, next) in &automaton.edges[state] {
            indegree[next] -= 1;
            if indegree[next] == 0 {
                queue.push_back(next);
            }
        }
    }
    debug_assert_eq!(order.len(), n, "the caller checked acyclicity");
    let mut longest = vec![0usize; n];
    for &state in order.iter().rev() {
        longest[state] = automaton.edges[state]
            .iter()
            .map(|&(_, next)| longest[next] + 1)
            .max()
            .unwrap_or(0);
    }
    longest
}

/// Yields the normal words in the fixed basis order without materializing
/// the list: trivial words in vertex order, then words by length, then by
/// source vertex, then in lexicographic arrow order. Each length comes
/// from a depth-first walk that `longest` prunes, so memory stays bounded
/// by the automaton size.
struct NormalWordGen<'a> {
    automaton: &'a Automaton,
    longest: Vec<usize>,
    max_length: usize,
    trivial_emitted: usize,
    length: usize,
    source: usize,
    stack: Vec<(usize, usize)>,
    word: Vec<u32>,
    dfs_active: bool,
}

impl<'a> NormalWordGen<'a> {
    fn new(automaton: &'a Automaton) -> NormalWordGen<'a> {
        let longest = longest_walks(automaton);
        let max_length = (0..automaton.starts).map(|s| longest[s]).max().unwrap_or(0);
        NormalWordGen {
            automaton,
            longest,
            max_length,
            trivial_emitted: 0,
            length: 1,
            source: 0,
            stack: Vec::new(),
            word: Vec::new(),
            dfs_active: false,
        }
    }

    fn start_next_walk(&mut self) -> bool {
        loop {
            if self.length > self.max_length {
                return false;
            }
            if self.source >= self.automaton.starts {
                self.source = 0;
                self.length += 1;
                continue;
            }
            let source = self.source;
            self.source += 1;
            if self.longest[source] < self.length {
                continue;
            }
            self.stack.clear();
            self.stack.push((source, 0));
            self.word.clear();
            self.dfs_active = true;
            return true;
        }
    }

    fn next_depth_first(&mut self) -> Option<Vec<u32>> {
        while let Some(&(state, edge_at)) = self.stack.last() {
            if self.word.len() == self.length {
                let emitted = self.word.clone();
                self.stack.pop();
                self.word.pop();
                return Some(emitted);
            }
            let next = self.automaton.edges[state]
                .iter()
                .enumerate()
                .skip(edge_at)
                .find(|&(_, &(_, next))| self.longest[next] + 1 >= self.length - self.word.len())
                .map(|(edge_at, &(arrow, next))| (edge_at + 1, arrow, next));
            if let Some((edge_at, arrow, next)) = next {
                self.stack.last_mut().expect("stack is nonempty").1 = edge_at;
                self.word.push(arrow);
                self.stack.push((next, 0));
            } else {
                self.stack.pop();
                self.word.pop();
            }
        }
        None
    }

    fn ensure_walk(&mut self) -> bool {
        self.dfs_active || self.start_next_walk()
    }
}

impl Iterator for NormalWordGen<'_> {
    type Item = Vec<u32>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.trivial_emitted < self.automaton.starts {
            self.trivial_emitted += 1;
            return Some(Vec::new());
        }
        loop {
            if !self.ensure_walk() {
                return None;
            }
            if let Some(word) = self.next_depth_first() {
                return Some(word);
            }
            self.dfs_active = false;
        }
    }
}

/// Lockstep comparison of the certificate's normal words against the lazy
/// enumeration. After the certificate list is exhausted the generator is
/// asked for at most one more word; its existence is the extra-word error.
fn check_normal_words_lockstep(
    automaton: &Automaton,
    found: &[Vec<u32>],
) -> Result<(), VerifyError> {
    if let Some((position, expected, found)) = first_mismatch(NormalWordGen::new(automaton), found)
    {
        return Err(VerifyError::NormalWords {
            position,
            expected,
            found,
        });
    }
    Ok(())
}

/// Checks the automaton section, the finiteness claim, and the normal
/// words. A verified infinite claim returns
/// [`VerifyError::InfiniteDimensional`] carrying the certificate's own
/// witness.
pub(super) fn check_finiteness_and_normal_words(
    quiver: &Quiver,
    certificate: &Certificate,
) -> Result<(), VerifyError> {
    let leads: Vec<Vec<u32>> = certificate.basis.iter().map(|g| g[0].1.clone()).collect();
    let automaton = build_automaton(quiver, &leads);
    check_automaton(&automaton, certificate)?;
    let cyclic = automaton_has_cycle(&automaton);
    let claimed_finite = matches!(&certificate.finiteness, FinitenessData::Finite);
    if claimed_finite == cyclic {
        return Err(VerifyError::FinitenessClaim { claimed_finite });
    }
    match &certificate.finiteness {
        FinitenessData::Finite => {
            check_normal_words_lockstep(&automaton, &certificate.normal_words)
        }
        FinitenessData::Infinite { prefix, cycle } => {
            let witness = check_witness(quiver, &automaton, &leads, prefix, cycle)?;
            if let Some(first) = certificate.normal_words.first() {
                return Err(VerifyError::NormalWords {
                    position: 0,
                    expected: None,
                    found: Some(first.clone()),
                });
            }
            Err(VerifyError::InfiniteDimensional { witness })
        }
    }
}

use crate::algebra::{Algebra, BasisIdx};

use super::super::limits::{BarInput, HochschildError};

pub(crate) fn tuple_starts(algebra: &Algebra, degree: usize) -> Vec<Vec<usize>> {
    let vertices = algebra.quiver().num_vertices() as usize;
    let mut starts = vec![vec![1; vertices]];
    for _ in 0..degree {
        let previous = starts.last().expect("degree zero starts exist");
        let next = (0..vertices)
            .map(|source| {
                algebra.paths_from(source as u32)[1..]
                    .iter()
                    .try_fold(0usize, |total, &word| {
                        total.checked_add(previous[algebra.basis()[word].target() as usize])
                    })
                    .expect("a completed tuple count fits usize")
            })
            .collect();
        starts.push(next);
    }
    starts
}

fn select_word(
    algebra: &Algebra,
    candidates: impl Iterator<Item = BasisIdx>,
    remaining: &[usize],
    rank: &mut usize,
) -> Option<BasisIdx> {
    for word in candidates {
        let block = remaining[algebra.basis()[word].target() as usize];
        if *rank < block {
            return Some(word);
        }
        *rank -= block;
    }
    None
}

pub(crate) fn decode_tuple(
    algebra: &Algebra,
    degree: usize,
    tuple_rank: usize,
    starts: &[Vec<usize>],
    tuple: &mut Vec<BasisIdx>,
) {
    let first_word = algebra.quiver().num_vertices() as usize;
    tuple.clear();
    let mut suffix_rank = tuple_rank;
    for position in 0..degree {
        let remaining = &starts[degree - position - 1];
        let word = if let Some(&previous) = tuple.last() {
            let source = algebra.basis()[previous].target();
            select_word(
                algebra,
                algebra.paths_from(source)[1..].iter().copied(),
                remaining,
                &mut suffix_rank,
            )
        } else {
            select_word(
                algebra,
                first_word..algebra.dim(),
                remaining,
                &mut suffix_rank,
            )
        };
        tuple.push(word.expect("a measured tuple rank decodes"));
    }
}

pub(crate) fn walk_tuples<E>(
    algebra: &Algebra,
    degree: usize,
    tuples: usize,
    starts: &[Vec<usize>],
    mut callback: impl FnMut(usize, &[BasisIdx], u32, u32) -> Result<(), E>,
) -> Result<(), E> {
    let vertices = algebra.quiver().num_vertices();
    if degree == 0 {
        for vertex in 0..vertices {
            callback(vertex as usize, &[], vertex, vertex)?;
        }
        return Ok(());
    }
    let mut tuple: Vec<BasisIdx> = Vec::with_capacity(degree);
    for tuple_rank in 0..tuples {
        decode_tuple(algebra, degree, tuple_rank, starts, &mut tuple);
        let first = &algebra.basis()[tuple[0]];
        let last = &algebra.basis()[*tuple.last().expect("positive-degree tuple")];
        callback(tuple_rank, &tuple, first.source(), last.target())?;
    }
    Ok(())
}

fn vertex_rank(algebra: &Algebra, vertex: u32) -> Result<usize, HochschildError> {
    if vertex >= algebra.quiver().num_vertices() {
        Err(HochschildError::VertexOutOfRange {
            vertex,
            num_vertices: algebra.quiver().num_vertices(),
        })
    } else {
        Ok(vertex as usize)
    }
}

fn validate_tuple(algebra: &Algebra, words: &[BasisIdx]) -> Result<(), HochschildError> {
    let vertices = algebra.quiver().num_vertices() as usize;
    words.iter().enumerate().try_for_each(|(position, &word)| {
        if word >= algebra.dim() {
            return Err(HochschildError::BasisOutOfRange {
                position,
                index: word,
            });
        }
        if word < vertices {
            return Err(HochschildError::TrivialInput { position });
        }
        if position > 0
            && algebra.basis()[words[position - 1]].target() != algebra.basis()[word].source()
        {
            return Err(HochschildError::NonComposableInput {
                position: position - 1,
            });
        }
        Ok(())
    })
}

fn tuple_rank(
    algebra: &Algebra,
    degree: usize,
    words: &[BasisIdx],
) -> Result<usize, HochschildError> {
    if words.len() != degree {
        return Err(HochschildError::WrongInputDegree {
            expected: degree,
            got: words.len(),
        });
    }
    validate_tuple(algebra, words)?;
    let starts = tuple_starts(algebra, degree);
    let tuples = starts[degree]
        .iter()
        .try_fold(0usize, |total, &count| total.checked_add(count))
        .expect("a completed tuple count fits usize");
    let mut tuple = Vec::with_capacity(degree);
    let rank = (0..tuples)
        .find(|&rank| {
            decode_tuple(algebra, degree, rank, &starts, &mut tuple);
            tuple.as_slice() == words
        })
        .expect("a validated tuple occurs in the streamed basis");
    Ok(rank)
}

pub(crate) fn input_rank(
    algebra: &Algebra,
    degree: usize,
    input: &BarInput,
) -> Result<usize, HochschildError> {
    match (degree, input) {
        (0, BarInput::Vertex(vertex)) => vertex_rank(algebra, *vertex),
        (0, BarInput::Tuple(words)) => Err(HochschildError::WrongInputDegree {
            expected: 0,
            got: words.len(),
        }),
        (_, BarInput::Vertex(_)) => Err(HochschildError::WrongInputDegree {
            expected: degree,
            got: 0,
        }),
        (_, BarInput::Tuple(words)) => tuple_rank(algebra, degree, words),
    }
}

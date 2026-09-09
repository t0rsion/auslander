use super::*;

#[test]
fn origins_expand_to_their_basis_elements() {
    for presentation in all_examples() {
        let c = completed(&presentation);
        let field = PrimeField::new(c.field).unwrap();
        for (j, origin) in c.origin.iter().enumerate() {
            assert_eq!(
                expand_origin(field, &c.input_relations, origin),
                c.basis[j],
                "origin {j}"
            );
        }
    }
}

#[test]
fn all_traces_replay_to_zero() {
    for presentation in all_examples() {
        let c = completed(&presentation);
        let field = PrimeField::new(c.field).unwrap();
        for (i, trace) in c.membership.iter().enumerate() {
            assert_eq!(trace.start, c.input_relations[i]);
            assert_trace_reduces_to_zero(field, &c.basis, trace);
        }
        for entry in &c.ambiguities {
            assert_trace_reduces_to_zero(field, &c.basis, &entry.trace);
        }
    }
}

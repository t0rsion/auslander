"""Presentation text, merge displays, and the LaTeX class table."""

from __future__ import annotations

import re
from pathlib import Path

import pytest

import auslander

F2 = auslander.PrimeField(2)
GUIDE = Path(__file__).parents[1] / "docs" / "derived-classification.md"


@pytest.fixture(scope="module")
def n3():
    return auslander.classify_derived(auslander.connected_gentle_algebras(3, F2))


def _guide_block(after: str) -> list[str]:
    text = GUIDE.read_text().split(after)[1]
    return re.search(r"```text\n(.*?)```", text, re.S).group(1).splitlines()


@pytest.mark.parametrize("vertices", [1, 2, 3])
def test_presentation_text_rebuilds_every_gentle_member(vertices):
    for member in auslander.connected_gentle_algebras(vertices, F2):
        rebuilt = auslander.parse_presentation(auslander.presentation_text(member)).build()
        assert rebuilt.certificate_json() == member.certificate_json()


def test_presentation_text_writes_general_relations_with_residues():
    field = auslander.PrimeField(3)
    quiver = auslander.Quiver(4, [(0, 1), (1, 3), (0, 2), (2, 3)])
    square = auslander.Algebra.from_relations(quiver, [[(1, [0, 1]), (-1, [2, 3])]], field)
    text = auslander.presentation_text(square)

    assert text.splitlines()[-1] == "relations 2*a2*a3 + a0*a1 = 0"
    assert auslander.parse_presentation(text).build().certificate_json() == square.certificate_json()


def test_field_free_algebras_show_their_relations_and_need_a_field_for_text():
    algebra = auslander.Algebra(auslander.Quiver(3, [(0, 1), (1, 2)]), [[0, 1]])

    assert str(auslander.show(algebra)).splitlines()[0] == "Algebra: dim 5, field-free"
    assert "relations a0*a1 = 0" in str(auslander.show(algebra))
    with pytest.raises(ValueError, match="needs a field"):
        auslander.presentation_text(algebra)


def test_guide_member_and_merge_output_is_current(n3):
    family = n3.family
    merge = n3.classes[n3.class_of(44)].merges[0]

    assert _guide_block("## Identify a member") == auslander.presentation_text(family[44]).splitlines()
    assert _guide_block("## Read a merge") == str(auslander.show(merge)).splitlines()
    assert str(auslander.show(merge.isomorphism)).startswith("AlgebraIsomorphism: dim 10, F_2")


def test_latex_table_lists_every_class_member_and_open_pair(n3):
    table = auslander.to_latex(n3)
    rows = [line for line in table.splitlines() if line.endswith(r" \\")]

    assert table.startswith("% DerivedClassification: 77 members, 30 classes")
    assert len(rows) == 1 + len(n3.classes)
    assert rows[1 + n3.class_of(44)].startswith(
        "17 & 44, 45, 46, 47, 48, 50, 51, 62, 69 & 1 & $(2, 4)$ & gcd 1 & 1, 2, 0"
    )
    assert "% unresolved" not in table


def test_one_class_summary_uses_the_singular():
    duplicate = [auslander.Algebra.linear_an(2, F2), auslander.Algebra.linear_an(2, F2)]
    text = repr(auslander.classify_derived(duplicate))

    assert text.startswith("DerivedClassification: 2 members, 1 class, status complete")


def test_a_bar_cut_prefix_is_marked_in_the_invariant_table():
    member = auslander.connected_gentle_algebras(4, F2)[2]
    invariants = member.derived_invariants()
    reading = invariants["hochschild_dimensions"]

    assert (reading.status, reading.value, reading.stop) == ("finished", [1, 7], None)
    assert "[1, 7], bar cut at HH^2" in repr(invariants)

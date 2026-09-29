"""Presentation text of verified algebras, isomorphisms, and merges."""

from __future__ import annotations

import json
from typing import Any

from ._core import PrimeField


def _word(word: list[int], index: int) -> str:
    """Name arrow `i` as `a{i}`. An empty word is the trivial path `e_v`."""
    return "*".join(f"a{arrow}" for arrow in word) if word else f"e{index}"


def _combination(terms: list[tuple[int, str]]) -> str:
    return " + ".join(
        text if coefficient == 1 else f"{coefficient}*{text}" for coefficient, text in terms
    )


def _certificate(algebra: Any, field: PrimeField | None) -> dict[str, Any]:
    return json.loads(algebra.certificate_json(field))


def presentation_text(algebra: Any, field: PrimeField | None = None) -> str:
    """Return the presentation of `algebra` in the `parse_presentation` language.

    Arrow `i` is named `a{i}`, and paths compose left to right. The
    relations are the input relations of the verified completion
    certificate, with coefficients in `0..p`. `parse_presentation(text)`
    rebuilds an algebra with the same certificate, and `Session.algebra`
    stores it by name. Field-free presentations need `field`.
    """
    certificate = _certificate(algebra, field)
    quiver = certificate["quiver"]
    arrows = " ".join(
        f"a{index}: {source} -> {target}"
        for index, (source, target) in enumerate(quiver["arrows"])
    )
    relations = "; ".join(
        _combination([(coefficient, _word(word, 0)) for coefficient, word in relation]) + " = 0"
        for relation in certificate["input_relations"]
    )
    lines = [
        f"field {certificate['field']}",
        "vertices " + " ".join(map(str, range(quiver["vertices"]))),
        f"arrows {arrows}".rstrip(),
    ]
    if relations:
        lines.append(f"relations {relations}")
    return "\n".join(lines) + "\n"


def algebra_lines(algebra: Any) -> list[str]:
    """Return a header and the presentation lines of one algebra.

    A field-free presentation is monomial. Its relations have coefficient 1
    over every field, so any prime reads them.
    """
    bound = algebra.field
    text = presentation_text(algebra, bound or PrimeField(2)).splitlines()
    field = f"F_{bound.p}" if bound is not None else "field-free"
    return [f"Algebra: dim {algebra.dim}, {field}", *(f"  {line}" for line in text[1:])]


def _vector(vector: list[int], words: list[list[int]]) -> str:
    terms = [(value, _word(words[index], index)) for index, value in enumerate(vector) if value]
    return _combination(terms) or "0"


def isomorphism_lines(isomorphism: Any) -> list[str]:
    """Return the vertex map and each arrow image as a path combination.

    Arrow images are written in the arrows `a{i}` of the target.
    """
    words = _certificate(isomorphism.target, None)["normal_words"]
    vertex_map = ", ".join(
        f"{vertex} -> {image}" for vertex, image in enumerate(isomorphism.vertex_map)
    )
    return [
        f"  vertex map: {vertex_map}",
        *(
            f"  arrow {arrow} -> {_vector(image, words)}"
            for arrow, image in enumerate(isomorphism.arrow_images)
        ),
    ]


def render_isomorphism(value: Any, _: int) -> tuple[list[str], str | None]:
    """Render an algebra isomorphism through its vertex map and arrow images."""
    header = f"AlgebraIsomorphism: dim {value.source.dim}, F_{value.source.field.p}"
    return [header, *isomorphism_lines(value)], None


def _recipe_text(recipe: list[tuple[str, int]]) -> str:
    return ", then ".join(
        f"{direction} mutation at summand {summand}" for direction, summand in recipe
    )


def render_merge(value: Any, _: int) -> tuple[list[str], str | None]:
    """Render one merge: the recipe, the recovered target, and the isomorphism."""
    header = f"DerivedMerge: member {value.source} to member {value.member}"
    if value.is_duplicate:
        return [header, "  duplicate presentation: empty recipe, identity path"], None
    target = value.recovered_target
    return [
        header,
        f"  recipe from the regular complex of member {value.source}: {_recipe_text(value.recipe)}",
        f"  recovered target End(T)^op: dim {target.dim}, isomorphic to member {value.member}",
        *isomorphism_lines(value.isomorphism),
    ], None

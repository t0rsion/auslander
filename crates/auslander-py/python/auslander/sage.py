"""Optional copying adapters for Sage matrices."""

from __future__ import annotations

from typing import Any


def matrix_from_sage(value: Any) -> list[list[int]]:
    """Copy a Sage matrix into canonical Python integers."""
    return [[int(value[row, column]) for column in range(value.ncols())] for row in range(value.nrows())]


def matrix_to_sage(value: list[list[int]], field: Any) -> Any:
    """Copy an integer matrix into a caller-supplied Sage field."""
    try:
        from sage.all import matrix
    except ImportError as error:
        raise ImportError("Sage is required for matrix_to_sage") from error
    return matrix(field, value)

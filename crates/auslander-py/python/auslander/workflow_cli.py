"""Implement the workflow command-line handlers."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from ._core import CensusLimits, HomologicalStreamBudget, HomologicalStreamConfig
from .workflow import (
    checkpoint as workflow_checkpoint,
    compute as workflow_compute,
    define as workflow_define,
    export as workflow_export,
    inspect as workflow_inspect,
    resume as workflow_resume,
    verify as workflow_verify,
    write_definition,
)


def _workflow_text(path: str) -> str:
    if path == "-":
        return sys.stdin.read()
    return Path(path).read_text(encoding="utf-8")


def _decode_dimensions(text: str) -> object:
    try:
        value = json.loads(text)
    except json.JSONDecodeError:
        parts = text.split(",")
        value = [part.strip() for part in parts if part.strip()]
    return value


def _dimension(item: object, index: int) -> int:
    if isinstance(item, bool):
        raise ValueError(f"dimensions[{index}] must be a nonnegative integer")
    try:
        dimension = int(item)
    except (TypeError, ValueError):
        raise ValueError(f"dimensions[{index}] must be a nonnegative integer") from None
    if dimension < 0 or str(item).strip() != str(dimension):
        raise ValueError(f"dimensions[{index}] must be a nonnegative integer")
    return dimension


def _dimensions(text: str) -> list[int]:
    """Parse a dimension vector written as JSON or comma-separated integers."""
    value = _decode_dimensions(text)
    if not isinstance(value, list) or not value:
        raise ValueError("dimensions must be a nonempty array")
    return [_dimension(item, index) for index, item in enumerate(value)]


def _workflow_census_limits(args: argparse.Namespace) -> CensusLimits | None:
    names = (
        "max_candidates",
        "max_representatives",
        "max_assignments",
        "max_isomorphism_checks",
        "census_max_work_units",
    )
    values = {name: getattr(args, name) for name in names}
    retention = args.retention
    for name, value in values.items():
        if value is not None and value < 0:
            option = name.replace("_", "-")
            raise ValueError(f"--{option} must be nonnegative")
    if retention is None and all(value is None for value in values.values()):
        return None
    return CensusLimits(
        retention=retention,
        max_candidates=values["max_candidates"],
        max_representatives=values["max_representatives"],
        max_assignments=values["max_assignments"],
        max_isomorphism_checks=values["max_isomorphism_checks"],
        max_work_units=values["census_max_work_units"],
    )


def _workflow_stream_config(args: argparse.Namespace) -> HomologicalStreamConfig | None:
    names = (
        "max_live_sources",
        "max_pairs",
        "max_ext_cells",
        "max_sources",
        "max_work_units",
    )
    values = {name: getattr(args, name) for name in names}
    for name, value in values.items():
        if value is not None and value < 0:
            raise ValueError(f"--{name.replace('_', '-')} must be nonnegative")
    if all(value is None for value in values.values()):
        return None
    return HomologicalStreamConfig(**values)


def _workflow_budget(args: argparse.Namespace) -> HomologicalStreamBudget | None:
    values = {
        name: getattr(args, name)
        for name in ("max_sources", "max_work_units")
    }
    for name, value in values.items():
        if value is not None and value < 0:
            raise ValueError(f"--{name.replace('_', '-')} must be nonnegative")
    if all(value is None for value in values.values()):
        return None
    return HomologicalStreamBudget(**values)


def _add_workflow_census_options(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--retention",
        choices=("all_assignments", "representatives_only"),
        help="duplicate records to retain in a census checkpoint",
    )
    for name in (
        "max_candidates",
        "max_representatives",
        "max_assignments",
        "max_isomorphism_checks",
    ):
        parser.add_argument(
            f"--{name.replace('_', '-')}",
            type=int,
            default=None,
            help=f"maximum census {name.replace('_', ' ')}",
        )
    parser.add_argument(
        "--census-max-work-units",
        type=int,
        default=None,
        help="maximum census work units",
    )


def _add_workflow_stream_options(parser: argparse.ArgumentParser) -> None:
    for name in (
        "max_live_sources",
        "max_pairs",
        "max_ext_cells",
        "max_sources",
        "max_work_units",
    ):
        parser.add_argument(
            f"--{name.replace('_', '-')}",
            type=int,
            default=None,
            help=f"maximum stream {name.replace('_', ' ')}",
        )


def _add_workflow_budget_options(parser: argparse.ArgumentParser) -> None:
    for name in ("max_sources", "max_work_units"):
        parser.add_argument(
            f"--{name.replace('_', '-')}",
            type=int,
            default=None,
            help=f"new absolute stream {name.replace('_', ' ')} ceiling",
        )


def _workflow_define(args: argparse.Namespace) -> int:
    definition = workflow_define(
        _workflow_text(args.presentation),
        _dimensions(args.dimensions),
        field=args.field,
        first_degree=args.first_degree,
        last_degree=args.last_degree,
    )
    write_definition(args.output, definition)
    print(f"written {args.output}")
    print(definition)
    return 0


def _workflow_compute(args: argparse.Namespace) -> int:
    from .workflow import load_definition

    definition = load_definition(args.definition)
    result = workflow_compute(
        definition,
        census_limits=_workflow_census_limits(args),
        stream_config=_workflow_stream_config(args),
        output=args.output,
    )
    written = workflow_inspect(args.output)
    print(f"written {args.output}")
    print(f"status {result.status}")
    print(f"fingerprint {written.fingerprint}")
    return 0


def _workflow_inspect(args: argparse.Namespace) -> int:
    print(workflow_inspect(args.source))
    return 0


def _workflow_checkpoint(args: argparse.Namespace) -> int:
    inspection = workflow_inspect(args.source)
    workflow_checkpoint(inspection.value, args.output)
    print(f"written {args.output}")
    return 0


def _workflow_resume(args: argparse.Namespace) -> int:
    result = workflow_resume(
        args.source,
        args.output,
        census_limits=_workflow_census_limits(args),
        budget=_workflow_budget(args),
    )
    written = workflow_inspect(args.output)
    print(f"written {args.output}")
    print(f"status {result.status}")
    print(f"fingerprint {written.fingerprint}")
    return 0


def _workflow_verify(args: argparse.Namespace) -> int:
    result = workflow_verify(args.source)
    print(f"verified {getattr(result, 'fingerprint', 'definition')}")
    if hasattr(result, "status"):
        print(f"status {result.status}")
    return 0


def _workflow_export(args: argparse.Namespace) -> int:
    text = workflow_export(
        args.source,
        args.output,
        format=args.format,
        verify_value=args.verify,
    )
    if args.output is None:
        sys.stdout.write(text)
    else:
        print(f"written {args.output}")
    return 0

"""Start the Auslander workbench shell."""

from __future__ import annotations

import argparse
import code
import sys
from collections.abc import Sequence
from pathlib import Path

from . import (
    Algebra,
    CensusCheckpoint,
    CensusLimits,
    CensusVerifyLimits,
    HomologicalCheckpoint,
    HomologicalStreamBudget,
    HomologicalStreamConfig,
    HomologicalStreamVerifyLimits,
    PrimeField,
    SelfExtLocusArtifact,
    SelfExtLocusVerifyLimits,
    Session,
    __version__,
    build_self_ext_locus_artifact_file,
    explain,
    load_checkpoint,
    load_homological_checkpoint,
    load_self_ext_locus_artifact,
    run_census,
    run_homological_stream,
    show,
    start_homological_stream,
    verify_checkpoint,
    verify_file,
    verify_homological_checkpoint_file,
    verify_self_ext_locus_artifact_file,
    write_checkpoint,
)
from .checkpoint import _read_utf8_bounded
from .compute import compute_json
from .workflow_cli import (
    _add_workflow_budget_options,
    _add_workflow_census_options,
    _add_workflow_stream_options,
    _dimensions,
    _workflow_checkpoint,
    _workflow_compute,
    _workflow_define,
    _workflow_export,
    _workflow_inspect,
    _workflow_resume,
    _workflow_verify,
)


def _namespace() -> dict[str, object]:
    session = Session()

    return {
        "session": session,
        "F": session.field,
        "PrimeField": PrimeField,
        "Algebra": Algebra,
        "CensusCheckpoint": CensusCheckpoint,
        "CensusLimits": CensusLimits,
        "CensusVerifyLimits": CensusVerifyLimits,
        "HomologicalCheckpoint": HomologicalCheckpoint,
        "HomologicalStreamBudget": HomologicalStreamBudget,
        "HomologicalStreamConfig": HomologicalStreamConfig,
        "HomologicalStreamVerifyLimits": HomologicalStreamVerifyLimits,
        "algebra": session.algebra,
        "module": session.module,
        "run_census": run_census,
        "start_homological_stream": start_homological_stream,
        "run_homological_stream": run_homological_stream,
        "show": show,
        "write_checkpoint": write_checkpoint,
        "load_checkpoint": load_checkpoint,
        "verify_checkpoint": verify_checkpoint,
        "explain": explain,
        "verify_file": verify_file,
    }


def repl() -> None:
    """Start IPython when installed, else Python's standard console."""
    namespace = _namespace()
    try:
        from IPython import start_ipython
    except ImportError:
        code.interact(
            banner="Auslander workbench. Names: session, F, algebra, module, run_census, CensusVerifyLimits, show, explain, verify_file.",
            local=namespace,
        )
    else:
        start_ipython(argv=[], user_ns=namespace)


def _compute(path: str | None) -> int:
    try:
        text = (
            sys.stdin.read()
            if path is None or path == "-"
            else Path(path).read_text(encoding="utf-8")
        )
        result = compute_json(text)
    except (OSError, OverflowError, RuntimeError, TypeError, ValueError) as error:
        print(f"auslander: error: {error}", file=sys.stderr)
        return 2
    sys.stdout.write(result + "\n")
    return 0


def _census_limits(
    args: argparse.Namespace, default_retention: str | None = None
) -> CensusLimits:
    values = {
        name: getattr(args, name)
        for name in (
            "retention",
            "max_candidates",
            "max_representatives",
            "max_assignments",
            "max_isomorphism_checks",
            "max_work_units",
        )
    }
    if values["retention"] is None:
        values["retention"] = default_retention
    for name, value in values.items():
        if name != "retention" and value is not None and value < 0:
            raise ValueError(f"--{name.replace('_', '-')} must be nonnegative")
    return CensusLimits(**values)


def _add_census_limits(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--retention",
        choices=("all_assignments", "representatives_only"),
        help="duplicate records to retain in the checkpoint",
    )
    for name in (
        "max_candidates",
        "max_representatives",
        "max_assignments",
        "max_isomorphism_checks",
        "max_work_units",
    ):
        parser.add_argument(
            f"--{name.replace('_', '-')}",
            type=int,
            help=f"maximum {name.replace('_', ' ')} for this run",
        )


_VERIFY_LIMIT_NAMES = (
    "max_input_bytes",
    "max_certificate_bytes",
    "max_dimensions",
    "max_dimension",
    "max_representatives",
    "max_assignments",
    "max_coordinate_values",
    "max_witness_matrices",
    "max_witness_rows",
    "max_witness_columns",
    "max_witness_entries",
    "max_numeric_values",
    "max_array_elements",
    "max_integer_digits",
    "max_string_bytes",
    "max_vertices",
    "max_coordinates",
    "max_candidates",
    "max_isomorphism_checks",
    "max_work_units",
)


def _census_verify_limits(
    args: argparse.Namespace, prefix: str = "verify"
) -> CensusVerifyLimits:
    values = {
        name: getattr(args, f"{prefix}_{name}")
        for name in _VERIFY_LIMIT_NAMES
    }
    for name, value in values.items():
        if value is not None and value < 0:
            option = f"--{prefix.replace('_', '-')}-{name.replace('_', '-')}"
            raise ValueError(f"{option} must be nonnegative")
    return CensusVerifyLimits(**values)


def _add_census_verify_limits(
    parser: argparse.ArgumentParser, prefix: str = "verify"
) -> None:
    for name in _VERIFY_LIMIT_NAMES:
        parser.add_argument(
            f"--{prefix.replace('_', '-')}-{name.replace('_', '-')}",
            dest=f"{prefix}_{name}",
            type=int,
            help=f"maximum {name.replace('_', ' ')} while parsing or verifying",
        )


def _census_summary(checkpoint: CensusCheckpoint) -> None:
    print(f"status {checkpoint.status}")
    print(f"retention {checkpoint.limits.retention}")
    print(f"cursor {checkpoint.cursor}")
    print(f"raw_space_size {checkpoint.raw_space_size}")
    print(f"candidates {checkpoint.candidates}")
    print(f"accepted_modules {checkpoint.accepted_modules}")
    print(f"rejected_candidates {checkpoint.rejected_candidates}")
    print(f"isomorphism_checks {checkpoint.isomorphism_checks}")
    print(f"work_units {checkpoint.work_units}")
    print(f"representatives {checkpoint.representative_count}")
    print(f"assignments {checkpoint.assignment_count}")
    reason = checkpoint.cut_reason
    print(f"cut_reason {reason.kind if reason is not None else 'none'}")
    print(f"fingerprint {checkpoint.fingerprint}")


def _census_start(args: argparse.Namespace) -> int:
    certificate = _read_utf8_bounded(
        args.certificate,
        _certificate_limit(args),
        "certificate",
        "max_certificate_bytes",
    )
    algebra = Algebra.from_certificate(certificate)
    checkpoint = run_census(
        algebra,
        _dimensions(args.dimensions),
        limits=_census_limits(args),
    )
    write_checkpoint(args.output, checkpoint)
    print(f"written {args.output}")
    _census_summary(checkpoint)
    return 0


def _certificate_limit(args: argparse.Namespace) -> int:
    value = args.max_certificate_bytes
    if value is None:
        return CensusVerifyLimits().max_certificate_bytes
    if value < 0:
        raise ValueError("--max-certificate-bytes must be nonnegative")
    return value


def _census_inspect(args: argparse.Namespace) -> int:
    checkpoint = load_checkpoint(args.checkpoint, _census_verify_limits(args))
    print("schema auslander-computation-v1")
    print("kind census-v1")
    print(f"field {checkpoint.field}")
    print(f"dimensions {','.join(map(str, checkpoint.dimensions))}")
    _census_summary(checkpoint)
    return 0


def _census_verify(args: argparse.Namespace) -> int:
    checkpoint = verify_checkpoint(args.checkpoint, _census_verify_limits(args))
    print(f"verified {checkpoint.fingerprint}")
    return 0


def _census_resume(args: argparse.Namespace) -> int:
    verified = verify_checkpoint(args.checkpoint, _census_verify_limits(args))
    checkpoint = verified.resume(
        limits=_census_limits(args, verified.limits.retention)
    )
    write_checkpoint(args.output, checkpoint)
    print(f"written {args.output}")
    _census_summary(checkpoint)
    return 0


def _nonnegative_options(args: argparse.Namespace, names: tuple[str, ...]) -> dict[str, int | None]:
    values = {name: getattr(args, name) for name in names}
    for name, value in values.items():
        if value is not None and value < 0:
            raise ValueError(f"--{name.replace('_', '-')} must be nonnegative")
    return values


_HOMOLOGICAL_CONFIG_NAMES = (
    "max_live_sources",
    "max_pairs",
    "max_ext_cells",
    "max_sources",
    "max_work_units",
)


def _homological_config(args: argparse.Namespace) -> HomologicalStreamConfig:
    return HomologicalStreamConfig(**_nonnegative_options(args, _HOMOLOGICAL_CONFIG_NAMES))


def _add_homological_config(parser: argparse.ArgumentParser) -> None:
    for name in _HOMOLOGICAL_CONFIG_NAMES:
        parser.add_argument(
            f"--{name.replace('_', '-')}",
            type=int,
            help=f"maximum {name.replace('_', ' ')}",
        )


def _homological_budget(args: argparse.Namespace) -> HomologicalStreamBudget:
    names = ("max_sources", "max_work_units")
    return HomologicalStreamBudget(**_nonnegative_options(args, names))


def _add_homological_budget(parser: argparse.ArgumentParser) -> None:
    for name in ("max_sources", "max_work_units"):
        parser.add_argument(
            f"--{name.replace('_', '-')}",
            type=int,
            help=f"new absolute {name.replace('_', ' ')} ceiling",
        )


_HOMOLOGICAL_VERIFY_NAMES = (
    "max_input_bytes",
    "max_census_bytes",
    "max_rows",
    "max_ext_dimensions",
    "max_numeric_values",
    "max_array_elements",
    "max_integer_digits",
    "max_string_bytes",
    "max_representatives",
    "max_degree",
    "max_work_units",
)


def _homological_verify_limits(args: argparse.Namespace) -> HomologicalStreamVerifyLimits:
    values = {
        name: getattr(args, f"homological_verify_{name}")
        for name in _HOMOLOGICAL_VERIFY_NAMES
    }
    for name, value in values.items():
        if value is not None and value < 0:
            raise ValueError(f"--verify-{name.replace('_', '-')} must be nonnegative")
    if hasattr(args, "verify_census_max_input_bytes"):
        values["census"] = _census_verify_limits(args, "verify_census")
    return HomologicalStreamVerifyLimits(**values)


def _add_homological_verify_limits(parser: argparse.ArgumentParser) -> None:
    for name in _HOMOLOGICAL_VERIFY_NAMES:
        parser.add_argument(
            f"--verify-{name.replace('_', '-')}",
            dest=f"homological_verify_{name}",
            type=int,
            help=f"maximum {name.replace('_', ' ')} while parsing or verifying",
        )


def _homological_summary(checkpoint: HomologicalCheckpoint) -> None:
    print(f"status {checkpoint.status}")
    print(f"census_fingerprint {checkpoint.census_fingerprint}")
    print(f"max_degree {checkpoint.max_degree}")
    print(f"next_source {checkpoint.next_source}")
    print(f"rows {checkpoint.row_count}")
    print(f"chunks {checkpoint.work.chunks}")
    print(f"peak_live_sources {checkpoint.work.peak_live_sources}")
    reason = checkpoint.cut_reason
    print(f"cut_reason {reason.kind if reason is not None else 'none'}")
    print(f"fingerprint {checkpoint.fingerprint}")


def _homological_start(args: argparse.Namespace) -> int:
    census = verify_checkpoint(
        args.census,
        _census_verify_limits(args, "census_verify"),
    )
    stream = start_homological_stream(
        census,
        args.max_degree,
        _homological_config(args),
    )
    checkpoint = run_homological_stream(args.output, stream)
    print(f"written {args.output}")
    _homological_summary(checkpoint)
    return 0


def _homological_inspect(args: argparse.Namespace) -> int:
    checkpoint = load_homological_checkpoint(
        args.checkpoint,
        _homological_verify_limits(args),
    )
    print("schema auslander-computation-v1")
    print("kind homological-self-pair-stream-v2")
    _homological_summary(checkpoint)
    return 0


def _homological_verify(args: argparse.Namespace) -> int:
    checkpoint = verify_homological_checkpoint_file(
        args.checkpoint,
        _homological_verify_limits(args),
    )
    print(f"verified {checkpoint.fingerprint}")
    return 0


def _homological_resume(args: argparse.Namespace) -> int:
    verified = verify_homological_checkpoint_file(
        args.checkpoint,
        _homological_verify_limits(args),
    )
    stream = verified.resume(_homological_budget(args))
    checkpoint = run_homological_stream(args.output, stream)
    print(f"written {args.output}")
    _homological_summary(checkpoint)
    return 0


_THEOREM_VERIFY_NAMES = (
    "max_input_bytes",
    "max_vanishing_indices",
    "max_integer_digits",
    "max_string_bytes",
    "max_representatives",
    "max_degree_span",
    "max_ext_spaces",
)


def _theorem_limits(args: argparse.Namespace) -> SelfExtLocusVerifyLimits:
    values = _nonnegative_options(args, _THEOREM_VERIFY_NAMES)
    return SelfExtLocusVerifyLimits(**values)


def _add_theorem_limits(parser: argparse.ArgumentParser) -> None:
    for name in _THEOREM_VERIFY_NAMES:
        parser.add_argument(
            f"--{name.replace('_', '-')}",
            type=int,
            help=f"maximum {name.replace('_', ' ')} while parsing or verifying",
        )


def _theorem_summary(artifact: SelfExtLocusArtifact) -> None:
    print(f"schema {artifact.schema}")
    print(f"kind {artifact.kind}")
    print(f"checkpoint_fingerprint {artifact.checkpoint.fingerprint}")
    print(f"first_degree {artifact.first_degree}")
    print(f"last_degree {artifact.last_degree}")
    print(f"vanishing_count {artifact.vanishing_count}")
    print(f"fingerprint {artifact.fingerprint}")


def _theorem_self_ext_locus(args: argparse.Namespace) -> int:
    artifact = build_self_ext_locus_artifact_file(
        args.checkpoint,
        args.output,
        args.first_degree,
        args.last_degree,
        _theorem_limits(args),
    )
    print(f"written {args.output}")
    _theorem_summary(artifact)
    return 0


def _theorem_inspect(args: argparse.Namespace) -> int:
    artifact = load_self_ext_locus_artifact(args.artifact, _theorem_limits(args))
    _theorem_summary(artifact)
    return 0


def _theorem_verify(args: argparse.Namespace) -> int:
    artifact = verify_self_ext_locus_artifact_file(
        args.artifact,
        _theorem_limits(args),
    )
    print(f"verified {artifact.fingerprint}")
    print(f"vanishing_count {artifact.vanishing_count}")
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="auslander",
        description="Compute checked invariants of bound quiver algebras.",
    )
    parser.add_argument("--version", action="version", version=f"%(prog)s {__version__}")
    commands = parser.add_subparsers(dest="command")
    commands.add_parser("repl", help="start the interactive workbench")
    compute = commands.add_parser("compute", help="run a canonical JSON request")
    compute.add_argument(
        "request",
        nargs="?",
        metavar="REQUEST.json",
        help="request file, or standard input when omitted or '-'",
    )
    census = commands.add_parser("census", help="run and verify durable module censuses")
    census_commands = census.add_subparsers(dest="census_command", required=True)
    start = census_commands.add_parser(
        "start", help="run a census from a completion certificate"
    )
    start.add_argument("certificate", metavar="CERTIFICATE.json")
    start.add_argument("dimensions", metavar="DIMENSIONS", help="JSON array, such as [1,1]")
    start.add_argument("output", metavar="CHECKPOINT.json")
    start.add_argument(
        "--max-certificate-bytes",
        type=int,
        help="maximum completion-certificate bytes to read",
    )
    _add_census_limits(start)
    inspect = census_commands.add_parser("inspect", help="inspect a checkpoint without replay")
    inspect.add_argument("checkpoint", metavar="CHECKPOINT.json")
    _add_census_verify_limits(inspect)
    verify = census_commands.add_parser("verify", help="replay-verify a checkpoint")
    verify.add_argument("checkpoint", metavar="CHECKPOINT.json")
    _add_census_verify_limits(verify)
    resume = census_commands.add_parser("resume", help="resume a verified cut checkpoint")
    resume.add_argument("checkpoint", metavar="CHECKPOINT.json")
    resume.add_argument("output", metavar="CHECKPOINT.json")
    _add_census_limits(resume)
    _add_census_verify_limits(resume)
    homological = commands.add_parser(
        "homological", help="run and verify durable homological self-pair streams"
    )
    homological_commands = homological.add_subparsers(
        dest="homological_command", required=True
    )
    homological_start = homological_commands.add_parser(
        "start", help="start from a verified complete census"
    )
    homological_start.add_argument("census", metavar="CENSUS.json")
    homological_start.add_argument("max_degree", metavar="MAX_DEGREE", type=int)
    homological_start.add_argument("output", metavar="CHECKPOINT.json")
    _add_homological_config(homological_start)
    _add_census_verify_limits(homological_start, "census_verify")
    homological_inspect = homological_commands.add_parser(
        "inspect", help="inspect a checkpoint without replay"
    )
    homological_inspect.add_argument("checkpoint", metavar="CHECKPOINT.json")
    _add_homological_verify_limits(homological_inspect)
    homological_verify = homological_commands.add_parser(
        "verify", help="replay-verify a checkpoint"
    )
    homological_verify.add_argument("checkpoint", metavar="CHECKPOINT.json")
    _add_homological_verify_limits(homological_verify)
    _add_census_verify_limits(homological_verify, "verify_census")
    homological_resume = homological_commands.add_parser(
        "resume", help="resume after the last verified source row"
    )
    homological_resume.add_argument("checkpoint", metavar="CHECKPOINT.json")
    homological_resume.add_argument("output", metavar="CHECKPOINT.json")
    _add_homological_budget(homological_resume)
    _add_homological_verify_limits(homological_resume)
    _add_census_verify_limits(homological_resume, "verify_census")
    theorem = commands.add_parser(
        "theorem", help="build and independently verify finite theorem artifacts"
    )
    theorem_commands = theorem.add_subparsers(dest="theorem_command", required=True)
    theorem_self_ext = theorem_commands.add_parser(
        "self-ext-locus", help="build a positive self-Ext vanishing locus"
    )
    theorem_self_ext.add_argument("checkpoint", metavar="CHECKPOINT.json")
    theorem_self_ext.add_argument("first_degree", metavar="FIRST_DEGREE", type=int)
    theorem_self_ext.add_argument("last_degree", metavar="LAST_DEGREE", type=int)
    theorem_self_ext.add_argument("output", metavar="ARTIFACT.json")
    _add_theorem_limits(theorem_self_ext)
    theorem_inspect = theorem_commands.add_parser(
        "inspect", help="inspect a theorem artifact without independent verification"
    )
    theorem_inspect.add_argument("artifact", metavar="ARTIFACT.json")
    _add_theorem_limits(theorem_inspect)
    theorem_verify = theorem_commands.add_parser(
        "verify", help="replay and independently verify a theorem artifact"
    )
    theorem_verify.add_argument("artifact", metavar="ARTIFACT.json")
    _add_theorem_limits(theorem_verify)
    workflow = commands.add_parser(
        "workflow", help="run the finite definition and self-Ext workflow"
    )
    workflow_commands = workflow.add_subparsers(
        dest="workflow_command", required=True
    )
    workflow_define = workflow_commands.add_parser(
        "define", help="write a workflow definition"
    )
    workflow_define.add_argument("presentation", metavar="PRESENTATION.txt")
    workflow_define.add_argument("dimensions", metavar="DIMENSIONS")
    workflow_define.add_argument("output", metavar="DEFINITION.json")
    workflow_define.add_argument("--field", type=int)
    workflow_define.add_argument("--first-degree", type=int, default=1)
    workflow_define.add_argument("--last-degree", type=int, default=3)
    workflow_compute = workflow_commands.add_parser(
        "compute", help="compute a workflow definition"
    )
    workflow_compute.add_argument("definition", metavar="DEFINITION.json")
    workflow_compute.add_argument("output", metavar="CHECKPOINT.json")
    _add_workflow_census_options(workflow_compute)
    _add_workflow_stream_options(workflow_compute)
    workflow_inspect = workflow_commands.add_parser(
        "inspect", help="inspect a workflow value without replay"
    )
    workflow_inspect.add_argument("source", metavar="VALUE.json")
    workflow_checkpoint = workflow_commands.add_parser(
        "checkpoint", help="copy a canonical workflow value"
    )
    workflow_checkpoint.add_argument("source", metavar="VALUE.json")
    workflow_checkpoint.add_argument("output", metavar="VALUE.json")
    workflow_resume = workflow_commands.add_parser(
        "resume", help="resume a cut workflow checkpoint"
    )
    workflow_resume.add_argument("source", metavar="CHECKPOINT.json")
    workflow_resume.add_argument("output", metavar="CHECKPOINT.json")
    _add_workflow_census_options(workflow_resume)
    _add_workflow_budget_options(workflow_resume)
    workflow_verify = workflow_commands.add_parser(
        "verify", help="replay-verify a workflow value"
    )
    workflow_verify.add_argument("source", metavar="VALUE.json")
    workflow_export = workflow_commands.add_parser(
        "export", help="write a workflow report"
    )
    workflow_export.add_argument("source", metavar="VALUE.json")
    workflow_export.add_argument("output", nargs="?", metavar="REPORT")
    workflow_export.add_argument(
        "--format", choices=("markdown", "csv"), default="markdown"
    )
    workflow_export.add_argument(
        "--verify", action="store_true", help="replay before writing the report"
    )
    args = parser.parse_args(argv)
    if args.command == "compute":
        return _compute(args.request)
    if args.command == "census":
        try:
            return {
                "start": _census_start,
                "inspect": _census_inspect,
                "verify": _census_verify,
                "resume": _census_resume,
            }[args.census_command](args)
        except (OSError, OverflowError, RuntimeError, TypeError, ValueError) as error:
            print(f"auslander: error: {error}", file=sys.stderr)
            return 2
    if args.command == "homological":
        try:
            return {
                "start": _homological_start,
                "inspect": _homological_inspect,
                "verify": _homological_verify,
                "resume": _homological_resume,
            }[args.homological_command](args)
        except (OSError, OverflowError, RuntimeError, TypeError, ValueError) as error:
            print(f"auslander: error: {error}", file=sys.stderr)
            return 2
    if args.command == "theorem":
        try:
            return {
                "self-ext-locus": _theorem_self_ext_locus,
                "inspect": _theorem_inspect,
                "verify": _theorem_verify,
            }[args.theorem_command](args)
        except (OSError, OverflowError, RuntimeError, TypeError, ValueError) as error:
            print(f"auslander: error: {error}", file=sys.stderr)
            return 2
    if args.command == "workflow":
        try:
            return {
                "define": _workflow_define,
                "compute": _workflow_compute,
                "inspect": _workflow_inspect,
                "checkpoint": _workflow_checkpoint,
                "resume": _workflow_resume,
                "verify": _workflow_verify,
                "export": _workflow_export,
            }[args.workflow_command](args)
        except (OSError, OverflowError, RuntimeError, TypeError, ValueError) as error:
            print(f"auslander: error: {error}", file=sys.stderr)
            return 2
    repl()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

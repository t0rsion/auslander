"""Run a small finite workflow with a cut, replay, and report."""

from __future__ import annotations

import argparse
from pathlib import Path

import auslander


PRESENTATION = """
field 2
vertices 0 1
arrows a:0->1
"""


def run(directory: Path) -> auslander.VerifiedWorkflowResult:
    """Write the workflow files and return the replay-verified result."""
    directory.mkdir(parents=True, exist_ok=True)
    definition = auslander.define(PRESENTATION, [1, 1], last_degree=2)
    definition_path = directory / "definition.json"
    auslander.write_definition(definition_path, definition)

    config = auslander.HomologicalStreamConfig(max_live_sources=1)
    cut = auslander.compute(
        definition,
        census_limits=auslander.CensusLimits(
            max_candidates=1,
            retention="representatives_only",
        ),
        stream_config=config,
    )
    auslander.checkpoint(cut, directory / "census-cut.json")
    complete = auslander.resume(
        cut,
        output=directory / "homological.json",
        census_limits=auslander.CensusLimits(
            max_candidates=2,
            retention="representatives_only",
        ),
    )
    verified = auslander.verify(complete)
    auslander.checkpoint(verified, directory / "artifact.json", stage="artifact")
    auslander.export(verified, directory / "report.md", format="markdown")
    return verified


def main() -> None:
    """Run the example and print its verified scope."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "directory", nargs="?", type=Path, default=Path("self-ext-workflow")
    )
    args = parser.parse_args()
    result = run(args.directory)
    print(f"status {result.status}")
    print(f"representatives {result.scope['representatives']}")
    print(f"fingerprint {result.fingerprint}")


if __name__ == "__main__":
    main()

"""CLI commands for generating SSZ conformance test fixtures and exporting them."""

import shutil
import subprocess
import sys
from collections.abc import Sequence
from pathlib import Path

import click

from ssz_testing.ssz_generic import export


def find_workspace_root() -> Path:
    """Walk up from the current directory to the one whose pyproject declares the uv workspace."""
    candidate = Path.cwd()
    while candidate != candidate.parent:
        pyproject = candidate / "pyproject.toml"
        if pyproject.exists() and "[tool.uv.workspace]" in pyproject.read_text():
            return candidate
        candidate = candidate.parent
    return Path.cwd()


@click.command(
    context_settings={
        "ignore_unknown_options": True,
        "allow_extra_args": True,
    },
    epilog="""\
\b
Examples:
    # Generate all SSZ fixtures
    fill --clean
\b
    # Generate a single filler file, verbose
    fill tests/fillers/ssz/test_basic_types.py --clean -v
""",
)
@click.argument("pytest_args", nargs=-1, type=click.UNPROCESSED)
@click.option(
    "--output",
    "-o",
    default="fixtures",
    help="Output directory for generated fixtures",
)
@click.option(
    "--clean",
    is_flag=True,
    help="Clean output directory before generating",
)
@click.pass_context
def fill(
    ctx: click.Context,
    pytest_args: Sequence[str],
    output: str,
    clean: bool,
) -> None:
    """Generate SSZ conformance test fixtures from test specifications."""
    config_path = Path(__file__).parent / "pytest_ini_files" / "pytest-fill.ini"
    # The project root is the workspace pyproject.toml.
    project_root = find_workspace_root()

    args = [
        "-c",
        str(config_path),
        f"--rootdir={project_root}",
        f"--output={output}",
    ]

    if clean:
        args.append("--clean")

    args.extend(pytest_args)
    args.extend(ctx.args)

    exit_code = subprocess.run([sys.executable, "-m", "pytest", *args]).returncode
    sys.exit(exit_code)


@click.command()
@click.option(
    "--source",
    "-s",
    default="fixtures",
    help="Directory holding the filled JSON vectors",
)
@click.option(
    "--output",
    "-o",
    default="fixtures-ssz-generic",
    help="Output directory for the exported tree",
)
@click.option(
    "--clean",
    is_flag=True,
    help="Clean output directory before exporting",
)
def export_ssz_generic(source: str, output: str, clean: bool) -> None:
    """
    Export the filled vectors as the ssz_generic tree consensus-specs used to publish.

    Raises:
        UsageError: When the output directory is not one inside the workspace.
        UsageError: When the output directory exists and cleaning was not asked for.
    """
    workspace_root = find_workspace_root().resolve()
    destination = (workspace_root / output).resolve()

    # --clean removes the whole tree, so a path the workspace does not contain is refused.
    if not destination.is_relative_to(workspace_root) or destination == workspace_root:
        raise click.UsageError(
            f"Output directory '{destination}' must be a directory under '{workspace_root}'."
        )
    if destination.exists():
        if not clean:
            raise click.UsageError(
                f"Output directory '{destination}' is not empty. Use --clean to remove it "
                "or specify a different output directory."
            )
        shutil.rmtree(destination)

    manifest = export((workspace_root / source).resolve(), destination)
    click.echo(
        f"{len(manifest['exported'])} cases exported to {destination}, "
        f"{len(manifest['skipped'])} read by no ssz_generic handler"
    )

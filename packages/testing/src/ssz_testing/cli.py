"""CLI command for generating SSZ conformance test fixtures."""

import subprocess
import sys
from collections.abc import Sequence
from pathlib import Path

import click


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

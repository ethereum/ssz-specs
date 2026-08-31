"""What the fill command finds, and what it hands the pytest it starts."""

import subprocess
import sys
from pathlib import Path

import pytest
from click.testing import CliRunner

from ssz_testing import cli

FILL_INI = Path(cli.__file__).parent / "pytest_ini_files" / "pytest-fill.ini"


@pytest.fixture
def workspace(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    """A workspace root holding one member, with the command run from inside the member."""
    (tmp_path / "pyproject.toml").write_text(
        "[tool.uv.workspace]\nmembers = ['packages/*']\n", encoding="utf-8"
    )
    member = tmp_path / "packages" / "testing"
    member.mkdir(parents=True)
    (member / "pyproject.toml").write_text("[project]\nname = 'ssz-testing'\n", encoding="utf-8")
    monkeypatch.chdir(member)
    return tmp_path


@pytest.fixture
def recorded_argv(monkeypatch: pytest.MonkeyPatch) -> list[list[str]]:
    """Capture the argv the command would start pytest with, without starting it."""
    recorded: list[list[str]] = []

    def record(argv: list[str]) -> subprocess.CompletedProcess[bytes]:
        recorded.append(argv)
        return subprocess.CompletedProcess(argv, 0)

    monkeypatch.setattr(cli.subprocess, "run", record)
    return recorded


def test_the_workspace_root_is_the_pyproject_that_declares_it(workspace: Path) -> None:
    """The root is the nearest ancestor whose pyproject declares the uv workspace."""
    assert cli.find_workspace_root() == workspace


def test_without_a_workspace_the_root_is_where_the_command_was_run(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Walking to the filesystem root without finding one falls back to where the walk began."""
    monkeypatch.chdir(tmp_path)

    assert cli.find_workspace_root() == tmp_path


def test_pytest_is_pointed_at_the_workspace_root(
    workspace: Path, recorded_argv: list[list[str]]
) -> None:
    """Every fill names its config, its root and its output, so it means the same anywhere."""
    result = CliRunner().invoke(cli.fill, ["--clean", "-o", "vectors", "tests/fillers", "-x"])

    assert result.exit_code == 0
    assert recorded_argv == [
        [
            sys.executable,
            "-m",
            "pytest",
            "-c",
            str(FILL_INI),
            f"--rootdir={workspace}",
            "--output=vectors",
            "--clean",
            "tests/fillers",
            "-x",
        ]
    ]


def test_cleaning_is_asked_for_only_when_it_was_asked_for(
    workspace: Path, recorded_argv: list[list[str]]
) -> None:
    """Without --clean the flag is absent, and pytest refuses a non-empty output directory."""
    assert CliRunner().invoke(cli.fill, []).exit_code == 0

    assert "--clean" not in recorded_argv[0]


def test_the_command_exits_with_the_code_pytest_returned(
    workspace: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A failed fill has to fail the shell that asked for it."""
    monkeypatch.setattr(
        cli.subprocess,
        "run",
        lambda argv: subprocess.CompletedProcess(argv, 1),
    )

    assert CliRunner().invoke(cli.fill, []).exit_code == 1

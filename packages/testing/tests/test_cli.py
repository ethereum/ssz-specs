"""What the fill command finds, what it hands the pytest it starts, and where the export lands."""

import json
import subprocess
import sys
from pathlib import Path

import pytest
from click.testing import CliRunner

from ssz_testing import cli
from ssz_testing.plugin import FIXTURE_FORMAT_VERSION
from ssz_testing.ssz_generic import SUITE_ROOT

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


def write_filled_tree(root: Path) -> Path:
    """A filled tree of one case, in the shape the export command reads."""
    source = root / "fixtures"
    case = source / "ssz" / "uint8" / "valid" / "uint8-max.json"
    case.parent.mkdir(parents=True)
    case.write_text(
        json.dumps(
            {
                "typeName": "Uint8",
                "serialized": "0xff",
                "value": "255",
                "root": "0xff" + "00" * 31,
                "valid": True,
                "typeDescriptor": {"kind": "Uint8", "bits": 8},
            }
        ),
        encoding="utf-8",
    )
    (source / "index.json").write_text(
        json.dumps({"cases": [{"id": "uint8/max", "path": "ssz/uint8/valid/uint8-max.json"}]}),
        encoding="utf-8",
    )
    (source / "manifest.json").write_text(
        json.dumps({"formatVersion": FIXTURE_FORMAT_VERSION, "specVersion": "0.0.0"}),
        encoding="utf-8",
    )
    return source


def test_the_export_lands_beside_the_vectors_it_was_read_from(workspace: Path) -> None:
    """Both paths resolve against the workspace root, so the command means the same anywhere."""
    write_filled_tree(workspace)

    result = CliRunner().invoke(cli.export_ssz_generic, [])

    assert result.exit_code == 0
    assert "1 cases exported" in result.output
    exported = workspace / "fixtures-ssz-generic" / SUITE_ROOT / "uints" / "valid"
    assert (exported / "uint_8_uint8_max" / "value.yaml").read_text(encoding="utf-8") == "255\n"


def test_an_output_directory_the_workspace_does_not_contain_is_refused(workspace: Path) -> None:
    """--clean removes the whole tree, so a path reaching outside the root is refused."""
    write_filled_tree(workspace)
    elsewhere = workspace.parent / "not-the-workspace"
    elsewhere.mkdir()
    (elsewhere / "irreplaceable.txt").write_text("keep me", encoding="utf-8")

    refused = CliRunner().invoke(cli.export_ssz_generic, ["--clean", "-o", str(elsewhere)])

    assert refused.exit_code == 2
    assert (elsewhere / "irreplaceable.txt").exists()

    # The root itself holds the workspace, so it is refused for the same reason.
    assert CliRunner().invoke(cli.export_ssz_generic, ["--clean", "-o", "."]).exit_code == 2


def test_an_existing_export_is_never_written_over(workspace: Path) -> None:
    """An export is replaced only when --clean asks for it, and then nothing of it survives."""
    write_filled_tree(workspace)
    leftover = workspace / "fixtures-ssz-generic" / "leftover.txt"
    leftover.parent.mkdir()
    leftover.write_text("from an older export", encoding="utf-8")

    refused = CliRunner().invoke(cli.export_ssz_generic, [])
    assert refused.exit_code == 2
    assert leftover.exists()

    assert CliRunner().invoke(cli.export_ssz_generic, ["--clean"]).exit_code == 0
    assert not leftover.exists()

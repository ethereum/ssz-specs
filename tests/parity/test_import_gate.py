"""The audited source graph must come from real Lean import headers."""

import subprocess
import sys
from pathlib import Path

import pytest

CHECKER = Path(__file__).resolve().parents[2] / "lean/scripts/check-imports.py"
# Python-only CI does not install Lean; the Lean parity job builds this binary first.
pytestmark = pytest.mark.skipif(
    not (CHECKER.parents[1] / ".lake/build/bin/conformance").exists(),
    reason="Lean checker is not built",
)


def check(root: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(CHECKER), str(root)], capture_output=True, text=True, timeout=30
    )


def tree(root: Path, implementation: str, proofs: str = "import Ssz\n") -> None:
    (root / "Ssz").mkdir()
    (root / "Ssz.lean").write_text(implementation)
    (root / "Ssz/Proofs.lean").write_text(proofs)
    (root / "Ssz/Orphan.lean").write_text("def orphan := 1\n")


@pytest.mark.parametrize(
    "phantom",
    [
        "/-\nimport Ssz.Orphan\n-/\n",
        "/- outer /- nested -/\nimport Ssz.Orphan\n-/\n",
        '-- import Ssz.Orphan\ndef text := "import Ssz.Orphan"\n',
        'def text := "\\"\nimport Ssz.Orphan\n"\n',
    ],
)
def test_phantom_import_does_not_cover_source(tmp_path: Path, phantom: str) -> None:
    tree(tmp_path, phantom)
    result = check(tmp_path)
    assert result.returncode != 0
    assert "missing from the audited import closure:\nSsz.Orphan" in result.stderr


@pytest.mark.parametrize(
    "header",
    [
        "import /- between tokens /- nested -/ -/ Ssz.Orphan\n",
        "module\npublic import Ssz.Orphan\n",
        "module\nmeta import all Ssz.Orphan\n",
    ],
)
def test_real_import_covers_source(tmp_path: Path, header: str) -> None:
    tree(tmp_path, header)
    result = check(tmp_path)
    assert result.returncode == 0, result.stderr


def test_escaped_module_components(tmp_path: Path) -> None:
    tree(tmp_path, "import Ssz.«Odd.name»\nimport Ssz.Orphan\n")
    (tmp_path / "Ssz/Odd.name.lean").write_text("def odd := 1\n")
    result = check(tmp_path)
    assert result.returncode == 0, result.stderr


def test_indirect_proof_import_is_rejected(tmp_path: Path) -> None:
    tree(tmp_path, "import Ssz.Orphan\n")
    (tmp_path / "Ssz/Orphan.lean").write_text("import Ssz.Proofs\n")
    result = check(tmp_path)
    assert result.returncode != 0
    assert "proof modules imported by the implementation:\nSsz.Proofs" in result.stderr


def test_shared_module_cannot_hide_acyclic_proof_dependency(tmp_path: Path) -> None:
    tree(
        tmp_path,
        "import Shared\n",
        "import Ssz\nimport Ssz.Orphan\nimport Ssz.Proofs.Helper\n",
    )
    (tmp_path / "Ssz/Proofs").mkdir()
    (tmp_path / "Ssz/Proofs/Helper.lean").write_text("def helper := 1\n")
    (tmp_path / "Shared.lean").write_text("import Ssz.Proofs.Helper\n")
    result = check(tmp_path)
    assert result.returncode != 0
    assert "proof modules imported by the implementation:\nSsz.Proofs.Helper" in result.stderr
    assert "missing from the audited import closure" not in result.stderr


def test_shared_module_can_cover_owned_implementation(tmp_path: Path) -> None:
    tree(tmp_path, "import Shared\n")
    (tmp_path / "Shared.lean").write_text("import Ssz.Orphan\n")
    (tmp_path / "Unused.lean").write_text("def unused := 1\n")
    result = check(tmp_path)
    assert result.returncode == 0, result.stderr


def test_directory_alias_cannot_hide_acyclic_proof_dependency(tmp_path: Path) -> None:
    tree(
        tmp_path,
        "import Alias.Helper\nimport Ssz.Orphan\n",
        "import Ssz\nimport Ssz.Proofs.Helper\n",
    )
    (tmp_path / "Ssz/Proofs").mkdir()
    (tmp_path / "Ssz/Proofs/Helper.lean").write_text("def helper := 1\n")
    alias = tmp_path / "Alias"
    try:
        alias.symlink_to(tmp_path / "Ssz/Proofs", target_is_directory=True)
    except (OSError, NotImplementedError) as error:
        pytest.skip(f"directory symlinks unavailable: {error}")
    result = check(tmp_path)
    assert result.returncode != 0
    assert "source-directory symlinks are unsupported" in result.stderr
    assert str(alias) in result.stderr


@pytest.mark.parametrize("excluded", [".lake", ".git", ".venv"])
def test_dependency_and_build_directories_are_not_parsed(tmp_path: Path, excluded: str) -> None:
    tree(tmp_path, "import Ssz.Orphan\n")
    ignored = tmp_path / excluded / "nested"
    ignored.mkdir(parents=True)
    (ignored / "Ignored.lean").write_text("/- unterminated")
    result = check(tmp_path)
    assert result.returncode == 0, result.stderr


@pytest.mark.parametrize("name", [".lake", ".git", ".venv"])
def test_nested_names_remain_owned_source(tmp_path: Path, name: str) -> None:
    tree(tmp_path, "import Ssz.Orphan\n")
    nested = tmp_path / "Ssz" / name
    nested.mkdir()
    (nested / "Hidden.lean").write_text("def hidden := 1\n")
    result = check(tmp_path)
    assert result.returncode != 0
    assert "missing from the audited import closure" in result.stderr
    assert "Hidden" in result.stderr


@pytest.mark.parametrize("name", [".lake", ".git", ".venv"])
def test_import_from_excluded_root_directory_is_rejected(tmp_path: Path, name: str) -> None:
    tree(tmp_path, f"import «{name}».Helper\nimport Ssz.Orphan\n")
    excluded = tmp_path / name
    excluded.mkdir()
    (excluded / "Helper.lean").write_text("def helper := 1\n")
    result = check(tmp_path)
    assert result.returncode != 0
    assert "import from excluded root directory" in result.stderr


@pytest.mark.parametrize("header", ["import\n", "/- unterminated", "public import Ssz.Orphan\n"])
def test_invalid_header_is_not_treated_as_complete(tmp_path: Path, header: str) -> None:
    tree(tmp_path, header)
    result = check(tmp_path)
    assert result.returncode != 0
    assert "cannot parse import header" in result.stderr

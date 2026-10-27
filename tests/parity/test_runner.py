"""Nonempty, well-formed inputs are required for a successful Lean conformance run."""

import json
import subprocess
from pathlib import Path

import pytest

LEAN_BINARY = Path(__file__).resolve().parents[2] / "lean/.lake/build/bin/conformance"
pytestmark = pytest.mark.skipif(not LEAN_BINARY.exists(), reason="Lean checker is not built")
ROOT = "0x01" + "00" * 31
CASE = {
    "name": "boolean",
    "typeDescriptor": {"kind": "Boolean"},
    "wellFormed": True,
    "value": True,
    "serialized": "0x01",
    "root": ROOT,
    "paths": [],
}
PAIR = {
    "name": "boolean-self",
    "left": {"kind": "Boolean"},
    "right": {"kind": "Boolean"},
    "compatible": True,
}


def run(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run([str(LEAN_BINARY), *args], capture_output=True, text=True, timeout=30)


@pytest.mark.parametrize(
    ("document", "message"),
    [
        (None, "expected a differential corpus object"),
        ([], "expected a differential corpus object"),
        ({}, "at least one"),
        ({"cases": [], "compatible": []}, "at least one"),
        ({"cases": False, "compatible": [PAIR]}, "cases must be an array"),
        ({"cases": [CASE], "compatible": None}, "compatible must be an array"),
        ({"case": [CASE]}, "unknown corpus section: case"),
    ],
)
def test_diff_rejects_empty_or_malformed_corpus(
    tmp_path: Path, document: object, message: str
) -> None:
    path = tmp_path / "corpus.json"
    path.write_text(json.dumps(document))
    result = run("--diff", str(path))
    assert result.returncode != 0
    assert message in result.stderr
    assert str(path) in result.stderr


@pytest.mark.parametrize(
    "document", [{"cases": [CASE]}, {"compatible": [PAIR]}, {"cases": [CASE], "compatible": [PAIR]}]
)
def test_diff_checks_present_sections(tmp_path: Path, document: object) -> None:
    path = tmp_path / "corpus.json"
    path.write_text(json.dumps(document))
    result = run("--diff", str(path))
    assert result.returncode == 0, result.stderr
    assert "checks passed, 0 failed" in result.stdout


def test_diff_syntax_error_identifies_input(tmp_path: Path) -> None:
    path = tmp_path / "malformed.json"
    path.write_text('{"cases":[')
    result = run("--diff", str(path))
    assert result.returncode != 0
    assert str(path) in result.stderr
    assert "checks passed" not in result.stdout


@pytest.mark.parametrize(
    "manifest",
    [
        None,
        "{",
        "null",
        "{}",
        '{"caseCount":"1"}',
        '{"caseCount":-1}',
        '{"caseCount":1.5}',
        '{"caseCount":0}',
    ],
)
def test_fixtures_require_valid_nonempty_manifest(tmp_path: Path, manifest: str | None) -> None:
    if manifest is not None:
        (tmp_path / "manifest.json").write_text(manifest)
    result = run(str(tmp_path))
    assert result.returncode != 0
    assert str(tmp_path / "manifest.json") in result.stderr


def test_fixture_count_and_content_are_checked(tmp_path: Path) -> None:
    (tmp_path / "manifest.json").write_text('{"caseCount":1}')
    result = run(str(tmp_path))
    assert result.returncode != 0
    assert "ran 0 cases" in result.stderr
    fixture = {**CASE, "valid": True, "_info": {"fixtureFormat": "ssz_test"}}
    (tmp_path / "boolean.json").write_text(json.dumps(fixture))
    result = run(str(tmp_path))
    assert result.returncode == 0, result.stderr
    assert "1 passed, 0 failed" in result.stdout
    fixture["serialized"] = "0x00"
    (tmp_path / "boolean.json").write_text(json.dumps(fixture))
    assert run(str(tmp_path)).returncode != 0

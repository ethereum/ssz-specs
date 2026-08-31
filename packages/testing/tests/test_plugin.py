"""What the fill plugin collects, what it remembers per test, and what it deletes."""

import json
from pathlib import Path

import pytest

from ssz_testing.plugin import FixtureCollector

FILLER_MODULE = '''
"""Two tests, one of which never calls the filler."""

from ssz import Uint8
from ssz_testing import SSZTestFiller


def test_writes_a_vector(ssz_test: SSZTestFiller) -> None:
    """An honest value."""
    ssz_test(type_name="Uint8", value=Uint8(1))


def test_writes_nothing(ssz_test: SSZTestFiller) -> None:
    """A test that asks for the filler and never calls it."""
'''

DESCRIPTION_MODULE = '''
"""Every combination of class docstring and function docstring."""

import pytest

from ssz import Uint8
from ssz_testing import SSZTestFiller


class TestDocumented:
    """The class documentation."""

    def test_documented(self, ssz_test: SSZTestFiller) -> None:
        """The function documentation."""
        ssz_test(type_name="Uint8", value=Uint8(1))

    def test_undocumented(self, ssz_test: SSZTestFiller) -> None:
        ssz_test(type_name="Uint8", value=Uint8(2))


def test_documented(ssz_test: SSZTestFiller) -> None:
    """The function documentation."""
    ssz_test(type_name="Uint8", value=Uint8(3))


def test_undocumented(ssz_test: SSZTestFiller) -> None:
    ssz_test(type_name="Uint8", value=Uint8(4))


@pytest.mark.parametrize("number", [5, 6])
def test_parametrized(ssz_test: SSZTestFiller, number: int) -> None:
    """Two cases of one function."""
    ssz_test(type_name="Uint8", value=Uint8(number))
'''


@pytest.fixture
def project(pytester: pytest.Pytester) -> pytest.Pytester:
    """A project shaped like the repository: fillers, a unit test, and a test outside tests/."""
    pytester.makeini("[pytest]\ntestpaths = tests\n")
    pytester.makepyfile(
        **{
            "tests/fillers/test_two": FILLER_MODULE,
            "tests/test_unit": "def test_unit() -> None:\n    pass\n",
            "test_outside": "def test_outside() -> None:\n    pass\n",
        }
    )
    return pytester


def fill(project: pytest.Pytester, *arguments: str) -> pytest.RunResult:
    """Run the plugin over the project the way the fill command does."""
    return project.runpytest("-p", "ssz_testing.plugin", *arguments)


def test_each_test_reports_only_the_vector_it_wrote(project: pytest.Pytester) -> None:
    """A test that wrote nothing must not report the file the previous test wrote."""
    record = project.inline_run("-p", "ssz_testing.plugin", "--clean")
    reported = {
        report.nodeid: dict(report.user_properties)
        for report in record.getreports("pytest_runtest_logreport")
        if report.when == "call"
    }

    vector = project.path / "fixtures" / "ssz" / "test_two" / "test_writes_a_vector.json"
    assert reported["tests/fillers/test_two.py::test_writes_a_vector"] == {
        "fixture_path_absolute": str(vector),
        "fixture_path_relative": "ssz/test_two/test_writes_a_vector.json",
        "fixture_format": "ssz_test",
    }
    assert reported["tests/fillers/test_two.py::test_writes_nothing"] == {}


def test_a_preview_deletes_nothing(project: pytest.Pytester) -> None:
    """--collect-only and --help preview a fill, so the vectors of the last real fill survive."""
    fill(project, "--clean").assert_outcomes(passed=2)
    vector = project.path / "fixtures" / "ssz" / "test_two" / "test_writes_a_vector.json"
    assert vector.exists()

    assert fill(project, "--clean", "--collect-only").ret == pytest.ExitCode.OK
    assert vector.exists()

    fill(project, "--clean", "--help")
    assert vector.exists()


def test_an_output_directory_the_project_does_not_contain_is_refused(
    project: pytest.Pytester,
) -> None:
    """--clean removes the whole tree, so a path reaching outside the root is refused."""
    elsewhere = project.path.parent / "not-the-project"
    elsewhere.mkdir()
    (elsewhere / "irreplaceable.txt").write_text("keep me", encoding="utf-8")

    refused = fill(project, "--clean", f"--output={elsewhere}")

    assert refused.ret == pytest.ExitCode.USAGE_ERROR
    assert (elsewhere / "irreplaceable.txt").exists()

    # The root itself holds the project, so it is refused for the same reason.
    assert fill(project, "--clean", "--output=.").ret == pytest.ExitCode.USAGE_ERROR
    assert (project.path / "pyproject.toml").exists() or (project.path / "tox.ini").exists()


def test_the_collection_filter_follows_the_root_not_the_directory_it_was_run_from(
    project: pytest.Pytester, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Filling from a subdirectory skips the unit tests, exactly as filling from the root does."""
    fill(project, "--clean", "--collect-only", "-q").stdout.fnmatch_lines(["2 tests collected*"])

    # From anywhere but the root, pytest collects the directory it was run from instead.
    monkeypatch.chdir(project.path / "tests")

    fill(project, "--clean", "--collect-only", "-q").stdout.fnmatch_lines(["2 tests collected*"])


def test_the_filter_leaves_paths_outside_the_tests_directory_alone(
    project: pytest.Pytester,
) -> None:
    """The filter narrows tests/ to tests/fillers/, and says nothing about anything else."""
    fill(project, "--clean", "test_outside.py").assert_outcomes(passed=1)


def test_a_non_empty_output_directory_is_never_written_over(project: pytest.Pytester) -> None:
    """Vectors are overwritten only when --clean asks for it, and the leftovers are named."""
    fill(project, "--clean").assert_outcomes(passed=2)

    refused = fill(project)
    assert refused.ret == pytest.ExitCode.USAGE_ERROR
    refused.stderr.fnmatch_lines(["*is not empty*Contains: ssz.*"])

    fill(project, "--clean").assert_outcomes(passed=2)


def test_a_long_list_of_leftovers_is_cut_short(project: pytest.Pytester) -> None:
    """More leftovers than the message shows are stood for by an ellipsis."""
    for index in range(6):
        (project.path / "fixtures" / f"leftover-{index}").mkdir(parents=True)

    refused = fill(project)

    assert refused.ret == pytest.ExitCode.USAGE_ERROR
    refused.stderr.fnmatch_lines(["*Contains: *, ...*"])


def test_an_empty_output_directory_needs_no_cleaning(project: pytest.Pytester) -> None:
    """An output directory holding nothing is already what --clean would make of it."""
    (project.path / "fixtures").mkdir()

    fill(project).assert_outcomes(passed=2)


def test_a_test_carries_its_documentation_into_its_vector(project: pytest.Pytester) -> None:
    """The description is the class and function docstrings, or a note that both are absent."""
    project.makepyfile(**{"tests/fillers/test_described": DESCRIPTION_MODULE})

    fill(project, "--clean").assert_outcomes(passed=8)

    written = json.loads(
        (project.path / "fixtures" / "ssz" / "test_described")
        .joinpath("test_documented.json")
        .read_text(encoding="utf-8")
    )
    descriptions = {test_id: entry["_info"]["description"] for test_id, entry in written.items()}
    assert descriptions == {
        "tests/fillers/test_described.py::TestDocumented::test_documented[ssz_test]": (
            "Test class documentation:\nThe class documentation.\n\nThe function documentation."
        ),
        "tests/fillers/test_described.py::test_documented[ssz_test]": "The function documentation.",
    }

    undocumented = json.loads(
        (project.path / "fixtures" / "ssz" / "test_described")
        .joinpath("test_undocumented.json")
        .read_text(encoding="utf-8")
    )
    assert undocumented["tests/fillers/test_described.py::test_undocumented[ssz_test]"]["_info"][
        "description"
    ] == ("No description available - add a docstring to the python test class or function.")
    assert (
        undocumented[
            "tests/fillers/test_described.py::TestDocumented::test_undocumented[ssz_test]"
        ]["_info"]["description"]
        == "Test class documentation:\nThe class documentation."
    )


def test_every_case_of_one_function_shares_one_file(project: pytest.Pytester) -> None:
    """Parametrization picks the entries inside a file, never the file."""
    project.makepyfile(**{"tests/fillers/test_described": DESCRIPTION_MODULE})

    fill(project, "--clean").assert_outcomes(passed=8)

    written = json.loads(
        (project.path / "fixtures" / "ssz" / "test_described" / "test_parametrized.json").read_text(
            encoding="utf-8"
        )
    )
    assert sorted(written) == [
        "tests/fillers/test_described.py::test_parametrized[5][ssz_test]",
        "tests/fillers/test_described.py::test_parametrized[6][ssz_test]",
    ]


def test_a_test_outside_the_filler_tree_has_nowhere_to_write(tmp_path: Path) -> None:
    """The output path is derived from the path under tests/fillers, so only those have one."""
    collector = FixtureCollector(tmp_path)

    with pytest.raises(ValueError, match="is not under tests/fillers"):
        collector.fixture_output_file("tests/test_unit.py::test_unit", "ssz_test")

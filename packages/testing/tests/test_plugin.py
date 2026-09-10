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
    ssz_test(case_id="uint8/one", type_name="Uint8", value=Uint8(1))


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
        ssz_test(case_id="documented/in_class", type_name="Uint8", value=Uint8(1))

    def test_undocumented(self, ssz_test: SSZTestFiller) -> None:
        ssz_test(case_id="undocumented/in_class", type_name="Uint8", value=Uint8(2))


def test_documented(ssz_test: SSZTestFiller) -> None:
    """The function documentation."""
    ssz_test(case_id="documented/at_module", type_name="Uint8", value=Uint8(3))


def test_undocumented(ssz_test: SSZTestFiller) -> None:
    ssz_test(case_id="undocumented/at_module", type_name="Uint8", value=Uint8(4))


@pytest.mark.parametrize("number", [5, 6])
def test_parametrized(ssz_test: SSZTestFiller, number: int) -> None:
    """Two cases of one function, each naming itself."""
    ssz_test(case_id=f"parametrized/{number}", type_name="Uint8", value=Uint8(number))
'''


SHAPE_COLLISION_MODULE = '''
"""One type name over two different shapes."""

from ssz import Container, Uint8, Uint16
from ssz_testing import SSZTestFiller


class Narrow(Container):
    """A one-byte field."""

    a: Uint8


class Wide(Container):
    """The same field, two bytes wide."""

    a: Uint16


def test_narrow(ssz_test: SSZTestFiller) -> None:
    """The first claim on the name."""
    ssz_test(case_id="shape/narrow", type_name="Shape", value=Narrow())


def test_wide(ssz_test: SSZTestFiller) -> None:
    """A second shape under the name the first claimed."""
    ssz_test(case_id="shape/wide", type_name="Shape", value=Wide())
'''

SHAPE_AGREEMENT_MODULE = '''
"""Two spellings of one shape, emitted under the one name they share."""

from ssz import Container, Uint8
from ssz_testing import SSZTestFiller


class Here(Container):
    """A one-byte field."""

    a: Uint8


class Elsewhere(Container):
    """The same declaration, written a second time."""

    a: Uint8


def test_here(ssz_test: SSZTestFiller) -> None:
    """The first of the two."""
    ssz_test(case_id="shape/here", type_name="Shape", value=Here())


def test_elsewhere(ssz_test: SSZTestFiller) -> None:
    """The second, claiming the same name for the same shape."""
    ssz_test(case_id="shape/elsewhere", type_name="Shape", value=Elsewhere())
'''

REPEATED_CALL_MODULE = '''
"""One test function filling a family of vectors in a loop."""

from ssz import Uint16
from ssz_testing import SSZTestFiller


def test_many_calls_one_function(ssz_test: SSZTestFiller) -> None:
    """Three values, each under its own case id."""
    for number in (1, 2, 3):
        ssz_test(case_id=f"uint16/{number}", type_name="Uint16", value=Uint16(number))
'''

DUPLICATE_CASE_ID_MODULE = '''
"""Two fillers reaching for one case id."""

from ssz import Uint16
from ssz_testing import SSZTestFiller


def test_first(ssz_test: SSZTestFiller) -> None:
    """The first claim on the id."""
    ssz_test(case_id="uint16/one", type_name="Uint16", value=Uint16(1))


def test_second(ssz_test: SSZTestFiller) -> None:
    """A second vector under the id the first claimed."""
    ssz_test(case_id="uint16/one", type_name="Uint16", value=Uint16(2))
'''

MALFORMED_CASE_ID_MODULE = '''
"""A case id spelled as the node id it replaces."""

from ssz import Uint16
from ssz_testing import SSZTestFiller


def test_malformed(ssz_test: SSZTestFiller) -> None:
    """An id a consumer could not print in a failure report."""
    ssz_test(
        case_id="tests/fillers/test_malformed.py::test_malformed",
        type_name="Uint16",
        value=Uint16(1),
    )
'''

RENAMED_MODULE = '''
"""One case, filled by a function that gets renamed between fills."""

from ssz import Uint64
from ssz_testing import SSZTestFiller


def test_{filler_name}(ssz_test: SSZTestFiller) -> None:
    """The largest uint64."""
    ssz_test(case_id="uint64/max", type_name="Uint64", value=Uint64(2**64 - 1))
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


@pytest.mark.parametrize("distribution_option", ["-n2", "--dist=load"])
def test_a_distributed_fill_is_refused(project: pytest.Pytester, distribution_option: str) -> None:
    """Every worker cleans the output directory, so the vectors the others wrote would go."""
    fill(project, "--clean").assert_outcomes(passed=2)
    vector = project.path / "fixtures" / "ssz" / "test_two" / "test_writes_a_vector.json"

    refused = fill(project, "--clean", distribution_option)

    assert refused.ret == pytest.ExitCode.USAGE_ERROR
    refused.stderr.fnmatch_lines(["*does not run distributed*"])
    assert vector.exists()


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
    descriptions = {case_id: entry["_info"]["description"] for case_id, entry in written.items()}
    assert descriptions == {
        "documented/in_class": (
            "Test class documentation:\nThe class documentation.\n\nThe function documentation."
        ),
        "documented/at_module": "The function documentation.",
    }

    undocumented = json.loads(
        (project.path / "fixtures" / "ssz" / "test_described")
        .joinpath("test_undocumented.json")
        .read_text(encoding="utf-8")
    )
    assert undocumented["undocumented/at_module"]["_info"]["description"] == (
        "No description available - add a docstring to the python test class or function."
    )
    assert (
        undocumented["undocumented/in_class"]["_info"]["description"]
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
    assert sorted(written) == ["parametrized/5", "parametrized/6"]
    assert {entry["_info"]["generatedBy"] for entry in written.values()} == {
        "tests/fillers/test_described.py::test_parametrized[5]",
        "tests/fillers/test_described.py::test_parametrized[6]",
    }


INDENTED_DESCRIPTION_MODULE = """
def test_indented(ssz_test):
    \"\"\"A summary line.

    A continuation line, indented in the source.
    \"\"\"
    from ssz.uint import Uint8

    ssz_test(case_id="uint8/indented", type_name="Uint8", value=Uint8(1))
"""


def test_a_description_carries_no_source_indentation(project: pytest.Pytester) -> None:
    """From Python 3.13 the compiler dedents docstrings, so a vector must not depend on it."""
    project.makepyfile(**{"tests/fillers/test_indented": INDENTED_DESCRIPTION_MODULE})

    fill(project, "--clean").assert_outcomes(passed=3)

    written = json.loads(
        (project.path / "fixtures" / "ssz" / "test_indented")
        .joinpath("test_indented.json")
        .read_text(encoding="utf-8")
    )
    description = next(iter(written.values()))["_info"]["description"]
    assert description == "A summary line.\n\nA continuation line, indented in the source."


def test_one_function_may_fill_a_family_of_vectors(project: pytest.Pytester) -> None:
    """An id names a vector rather than a test, so a loop writes one entry per iteration."""
    project.makepyfile(**{"tests/fillers/test_repeated": REPEATED_CALL_MODULE})

    fill(project, "--clean").assert_outcomes(passed=3)

    written = json.loads(
        (
            project.path
            / "fixtures"
            / "ssz"
            / "test_repeated"
            / "test_many_calls_one_function.json"
        ).read_text(encoding="utf-8")
    )
    assert sorted(written) == ["uint16/1", "uint16/2", "uint16/3"]


def test_two_vectors_under_one_case_id_fail_the_fill(project: pytest.Pytester) -> None:
    """An id is how a consumer names a case, so a second vector under one names both producers."""
    project.makepyfile(**{"tests/fillers/test_duplicate": DUPLICATE_CASE_ID_MODULE})

    refused = fill(project, "--clean")

    refused.assert_outcomes(passed=3, failed=1)
    refused.stdout.fnmatch_lines(
        [
            "E*ValueError: case id 'uint16/one' names two different vectors:",
            "E*tests/fillers/test_duplicate.py::test_first",
            "E*tests/fillers/test_duplicate.py::test_second",
        ]
    )


def test_a_case_id_that_is_not_slash_separated_words_is_refused(project: pytest.Pytester) -> None:
    """A vector is language-neutral, so its id may not spell out this repository's source layout."""
    project.makepyfile(**{"tests/fillers/test_malformed": MALFORMED_CASE_ID_MODULE})

    refused = fill(project, "--clean")

    refused.assert_outcomes(passed=2, failed=1)
    refused.stdout.fnmatch_lines(["E*is not spelled as slash-separated lowercase words*"])


def test_an_authored_id_survives_renaming_the_filler(project: pytest.Pytester) -> None:
    """The author names a case, so renaming the function that fills it renames nothing."""
    renamed = project.path / "fixtures" / "ssz" / "test_renamed"
    project.makepyfile(
        **{"tests/fillers/test_renamed": RENAMED_MODULE.format(filler_name="uint64_at_its_top")}
    )
    fill(project, "--clean").assert_outcomes(passed=3)
    before = json.loads((renamed / "test_uint64_at_its_top.json").read_text(encoding="utf-8"))

    project.makepyfile(
        **{"tests/fillers/test_renamed": RENAMED_MODULE.format(filler_name="the_largest_uint64")}
    )
    fill(project, "--clean").assert_outcomes(passed=3)
    after = json.loads((renamed / "test_the_largest_uint64.json").read_text(encoding="utf-8"))

    assert list(before) == list(after) == ["uint64/max"]
    assert before["uint64/max"]["_info"]["testId"] == after["uint64/max"]["_info"]["testId"]
    assert after["uint64/max"]["_info"]["generatedBy"] == (
        "tests/fillers/test_renamed.py::test_the_largest_uint64"
    )


def test_a_vector_records_the_filler_that_produced_it(project: pytest.Pytester) -> None:
    """The node id stays on as provenance, so a maintainer can find the filler behind a case."""
    fill(project, "--clean").assert_outcomes(passed=2)

    written = json.loads(
        (project.path / "fixtures" / "ssz" / "test_two" / "test_writes_a_vector.json").read_text(
            encoding="utf-8"
        )
    )
    assert written["uint8/one"]["_info"]["generatedBy"] == (
        "tests/fillers/test_two.py::test_writes_a_vector"
    )


def test_a_test_outside_the_filler_tree_has_nowhere_to_write(tmp_path: Path) -> None:
    """The output path is derived from the path under tests/fillers, so only those have one."""
    collector = FixtureCollector(tmp_path)

    with pytest.raises(ValueError, match="is not under tests/fillers"):
        collector.fixture_output_file("tests/test_unit.py::test_unit", "ssz_test")


def test_a_vector_file_ends_with_a_newline(project: pytest.Pytester) -> None:
    """A vector is a POSIX text file, so its last line is terminated like any other."""
    fill(project, "--clean").assert_outcomes(passed=2)

    vector = project.path / "fixtures" / "ssz" / "test_two" / "test_writes_a_vector.json"
    assert vector.read_text(encoding="utf-8").endswith("}\n")


def test_one_type_name_for_two_shapes_fails_the_fill(project: pytest.Pytester) -> None:
    """A name indexes a vector, so a second declaration under one is refused."""
    project.makepyfile(**{"tests/fillers/test_collision": SHAPE_COLLISION_MODULE})

    refused = fill(project, "--clean")

    refused.assert_outcomes(passed=3, failed=1)
    refused.stdout.fnmatch_lines(
        [
            "*ValueError: type name 'Shape' stands for two different declarations:*",
            '*test_collision.py::test_narrow: *"name": "a", "type": *"bits": 8*',
            '*test_collision.py::test_wide: *"name": "a", "type": *"bits": 16*',
        ]
    )


def test_two_spellings_of_one_shape_share_a_name(project: pytest.Pytester) -> None:
    """The claim is held against the declared shape, not against the class that declared it."""
    project.makepyfile(**{"tests/fillers/test_agreement": SHAPE_AGREEMENT_MODULE})

    fill(project, "--clean").assert_outcomes(passed=4)

"""Pytest plugin for generating SSZ conformance test fixtures."""

import json
import shutil
from collections import defaultdict
from pathlib import Path
from typing import Any

import pytest

from ssz_testing.fixtures import FIXTURE_FORMATS, FixtureInfo


class FixtureCollector:
    """Collects generated fixtures and writes them to disk."""

    def __init__(self, output_directory: Path):
        """Initialize the fixture collector."""
        self.output_directory = output_directory
        self.fixtures: list[tuple[str, Any, str]] = []

    def fixture_output_file(self, test_nodeid: str, fixture_format: str) -> Path:
        """
        Compute the fixture file for one test function.

        Raises if the test file is not under the filler tests.
        """
        # A nodeid is the file, then the names within it, then the parametrization.
        # The file is named for the function, so every case of one function shares one file.
        test_file_path, _, name_within_file = test_nodeid.partition("::")
        base_function_name = name_within_file.split("[")[0].rpartition("::")[2]

        try:
            relative_path = Path(test_file_path).relative_to("tests/fillers")
        except ValueError as exception:
            raise ValueError(
                f"cannot derive a fixture output path for '{test_nodeid}': "
                f"test file '{test_file_path}' is not under tests/fillers"
            ) from exception

        test_path = relative_path.with_suffix("")

        format_directory = fixture_format.removesuffix("_test")
        return self.output_directory / format_directory / test_path / f"{base_function_name}.json"

    def add_fixture(self, fixture_format: str, fixture: Any, item: pytest.Item) -> None:
        """Add a fixture to the collection, and record its path on the test that produced it."""
        self.fixtures.append((fixture_format, fixture, item.nodeid))

        # The path belongs to this test, so it is stashed on the item rather than on the
        # session-wide config, which would hand it to every test that runs afterwards.
        fixture_path = self.fixture_output_file(item.nodeid, fixture_format)
        item.stash[FIXTURE_PATH_ABSOLUTE_KEY] = str(fixture_path.absolute())
        item.stash[FIXTURE_PATH_RELATIVE_KEY] = str(fixture_path.relative_to(self.output_directory))
        item.stash[FIXTURE_FORMAT_KEY] = fixture_format

    def write_fixtures(self) -> None:
        """Write all collected fixtures to disk, grouped by test function."""
        grouped: dict[Path, list[tuple[str, Any, str]]] = defaultdict(list)

        for fixture_format, fixture, test_nodeid in self.fixtures:
            output_file = self.fixture_output_file(test_nodeid, fixture_format)
            grouped[output_file].append((fixture_format, fixture, test_nodeid))

        for output_file, fixtures_list in grouped.items():
            output_file.parent.mkdir(parents=True, exist_ok=True)

            all_tests = {}
            for fixture_format, fixture, test_nodeid in fixtures_list:
                test_id = f"{test_nodeid}[{fixture_format}]"
                all_tests[test_id] = fixture.json_dict_with_info()

            with output_file.open("w") as output_handle:
                json.dump(all_tests, output_handle, indent=4)


FIXTURE_COLLECTOR_KEY: pytest.StashKey[FixtureCollector] = pytest.StashKey()
"""Stash key for the session's fixture collector."""

FIXTURE_PATH_ABSOLUTE_KEY: pytest.StashKey[str] = pytest.StashKey()
"""Item stash key for the absolute path of a test's fixture file."""

FIXTURE_PATH_RELATIVE_KEY: pytest.StashKey[str] = pytest.StashKey()
"""Item stash key for a test's fixture path relative to the output directory."""

FIXTURE_FORMAT_KEY: pytest.StashKey[str] = pytest.StashKey()
"""Item stash key for a test's fixture format name."""


def pytest_addoption(parser: pytest.Parser) -> None:
    """Add command-line options for fixture generation."""
    group = parser.getgroup("fill", "SSZ fixture generation")
    group.addoption(
        "--output",
        action="store",
        default="fixtures",
        help="Output directory for generated fixtures",
    )
    group.addoption(
        "--clean",
        action="store_true",
        default=False,
        help="Clean output directory before generating",
    )


def pytest_ignore_collect(collection_path: Path, config: pytest.Config) -> bool | None:
    """
    Ignore paths outside the filler tests.

    Skipping unit tests during fill cuts collection overhead sharply.
    The tests live under the configured root, not under wherever the command was typed.
    """
    try:
        relative_path = collection_path.relative_to(config.rootpath / "tests")
    except ValueError:
        # Not under tests/, let pytest handle it normally.
        return None

    if str(relative_path).startswith("fillers"):
        return None

    # Anything else under tests/ is skipped during fill.
    if relative_path.parts:
        return True

    return None


def pytest_sessionstart(session: pytest.Session) -> None:
    """
    Setup the fixture generation session.

    Not the configure hook, which also runs for --collect-only and --help.
    Those preview a fill rather than perform one, and must leave the last fill's vectors alone.
    """
    config = session.config
    if config.option.collectonly:
        return

    # Resolved against the configured root, so --output means the same from any directory.
    root_directory = config.rootpath.resolve()
    output_directory = (root_directory / config.getoption("--output")).resolve()

    # --clean deletes the whole tree, so a path that is not somewhere below the root is refused.
    if not output_directory.is_relative_to(root_directory) or output_directory == root_directory:
        raise pytest.UsageError(
            f"Output directory '{output_directory}' must be a directory under '{root_directory}'. "
            "--clean removes it in full, so a path outside the project is refused."
        )

    if output_directory.exists() and any(output_directory.iterdir()):
        if not config.getoption("--clean"):
            leftover_fixture_paths = list(output_directory.iterdir())
            leftover_names_preview = ", ".join(
                leftover_path.name for leftover_path in leftover_fixture_paths[:5]
            )
            if len(leftover_fixture_paths) > 5:
                leftover_names_preview += ", ..."
            # A usage error is how a hook refuses the run, and it exits with that code.
            raise pytest.UsageError(
                f"Output directory '{output_directory}' is not empty. "
                f"Contains: {leftover_names_preview}. Use --clean to remove all existing files "
                "or specify a different output directory."
            )
        shutil.rmtree(output_directory)

    output_directory.mkdir(parents=True, exist_ok=True)

    config.stash[FIXTURE_COLLECTOR_KEY] = FixtureCollector(output_directory)


def pytest_sessionfinish(session: pytest.Session, exitstatus: int) -> None:
    """Write all collected fixtures at the end of the session."""
    if FIXTURE_COLLECTOR_KEY in session.config.stash:
        session.config.stash[FIXTURE_COLLECTOR_KEY].write_fixtures()


@pytest.hookimpl(tryfirst=True, hookwrapper=True)
def pytest_runtest_makereport(item: pytest.Item, call: pytest.CallInfo[None]) -> Any:
    """Make each test's fixture json path available to the test report."""
    outcome = yield
    report = outcome.get_result()

    if call.when == "call":
        stash = item.stash
        if FIXTURE_PATH_ABSOLUTE_KEY in stash and FIXTURE_PATH_RELATIVE_KEY in stash:
            report.user_properties.append(
                ("fixture_path_absolute", stash[FIXTURE_PATH_ABSOLUTE_KEY])
            )
            report.user_properties.append(
                ("fixture_path_relative", stash[FIXTURE_PATH_RELATIVE_KEY])
            )
        if FIXTURE_FORMAT_KEY in stash:
            report.user_properties.append(("fixture_format", stash[FIXTURE_FORMAT_KEY]))


@pytest.fixture
def test_case_description(request: pytest.FixtureRequest) -> str:
    """Extract and combine docstrings from test class and function."""
    description_unavailable = (
        "No description available - add a docstring to the python test class or function."
    )
    test_class_doc = ""
    test_function_doc = ""

    if hasattr(request.node, "cls") and request.cls:
        test_class_doc = f"Test class documentation:\n{request.cls.__doc__}"
    if hasattr(request.node, "function") and request.function.__doc__:
        test_function_doc = f"{request.function.__doc__}"

    if not test_class_doc and not test_function_doc:
        return description_unavailable

    combined_docstring = f"{test_class_doc}\n\n{test_function_doc}".strip()
    return combined_docstring


def base_spec_filler_parametrizer(spec_class: Any) -> Any:
    """Build a pytest fixture whose value fills and collects a fixture for the spec class."""

    @pytest.fixture(
        scope="function",
        name=spec_class.format_name,
    )
    def base_spec_filler_parametrizer_func(
        request: pytest.FixtureRequest,
        test_case_description: str,
    ) -> Any:
        """Fixture whose value builds the spec, generates, and collects the result."""

        def fill_and_collect(**spec_fields: Any) -> Any:
            test_spec = spec_class(**spec_fields)
            generated_fixture = test_spec.generate()

            filled_fixture = generated_fixture.with_info(
                info=FixtureInfo(
                    test_id=request.node.nodeid,
                    description=test_case_description,
                    fixture_format=spec_class.format_name,
                )
            )

            request.config.stash[FIXTURE_COLLECTOR_KEY].add_fixture(
                fixture_format=spec_class.format_name,
                fixture=filled_fixture,
                item=request.node,
            )
            return filled_fixture

        return fill_and_collect

    return base_spec_filler_parametrizer_func


# Register one filler fixture per SSZ format from the canonical registry.
# A new format needs no edit here.
for fixture_format_class in FIXTURE_FORMATS:
    globals()[fixture_format_class.format_name] = base_spec_filler_parametrizer(
        fixture_format_class
    )

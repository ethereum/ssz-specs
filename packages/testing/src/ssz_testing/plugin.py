"""Pytest plugin for generating SSZ conformance test fixtures."""

import hashlib
import json
import re
import shutil
from dataclasses import dataclass
from importlib.metadata import version
from inspect import cleandoc
from pathlib import Path
from typing import Any, Final

import pytest

from ssz_testing import FIXTURE_FORMATS
from ssz_testing.fixtures import BaseConsensusFixture, FixtureInfo, TypeDescriptor

CASE_ID_PATTERN: Final = re.compile(r"[a-z0-9]+(?:_[a-z0-9]+)*(?:/[a-z0-9]+(?:_[a-z0-9]+)*)*")
"""A case id: slash-separated segments of lowercase words, such as `uint64/max`."""

FIXTURE_FORMAT_VERSION: Final = 1
"""Shape of the emitted tree, bumped whenever a consumer has to change to keep reading it."""

GENERATOR: Final = "eth-ssz-specs"
"""What produced the vectors, named in the manifest so a consumer can say where they came from."""


def case_tags(item: pytest.Item) -> tuple[str, ...]:
    """The theme of the filler that authored a case, and every tag the filler declared on it."""
    filler_module = Path(item.nodeid.partition("::")[0]).stem.removeprefix("test_")
    declared = {tag for marker in item.iter_markers("tags") for tag in marker.args}
    return tuple(sorted(declared | {filler_module.replace("_", "-")}))


def json_document(payload: Any) -> str:
    """The text one emitted JSON file holds: indented, and terminated like any POSIX line."""
    return json.dumps(payload, indent=4) + "\n"


@dataclass(frozen=True, slots=True)
class CollectedCase:
    """One filled vector, with the file it is written to and what the index says about it."""

    fixture: BaseConsensusFixture
    case_id: str
    tags: tuple[str, ...]
    output_file: Path


class FixtureCollector:
    """Collects generated fixtures and writes them to disk."""

    def __init__(self, output_directory: Path):
        """Initialize the fixture collector."""
        self.output_directory = output_directory
        self.cases: list[CollectedCase] = []
        self.type_declarations: dict[str, tuple[str, TypeDescriptor]] = {}
        self.case_producers: dict[str, str] = {}

    def fixture_output_file(
        self,
        fixture: BaseConsensusFixture,
        test_nodeid: str,
        fixture_format: str,
        case_id: str,
    ) -> Path:
        """
        The file one vector is written to, named by its case id under its kind and its validity.

        A dash joins the id's segments, a character no case id holds, so no two ids name one file.

        Raises:
            ValueError: When the test does not sit under the filler tests.
        """
        test_file_path, _, _ = test_nodeid.partition("::")
        if not Path(test_file_path).is_relative_to("tests/fillers"):
            raise ValueError(
                f"cannot derive a fixture output path for '{test_nodeid}': "
                f"test file '{test_file_path}' is not under tests/fillers"
            )

        return (
            self.output_directory
            / fixture_format.removesuffix("_test")
            / fixture.case_kind()
            / ("valid" if fixture.valid else "invalid")
            / f"{case_id.replace('/', '-')}.json"
        )

    def claim_type_names(self, fixture: BaseConsensusFixture, test_nodeid: str) -> None:
        """
        Hold every type name the run emits to one declaration, a name being how a vector is indexed.

        Args:
            fixture: The fixture whose type names are being claimed.
            test_nodeid: The test that produced it, named in the refusal.

        Raises:
            ValueError: When an earlier vector emitted this name for a different declaration.
        """
        for type_name, declared in fixture.declared_types().items():
            claimed_by, claimed = self.type_declarations.setdefault(
                type_name, (test_nodeid, declared)
            )
            if claimed != declared:
                raise ValueError(
                    f"type name '{type_name}' stands for two different declarations:\n"
                    f"  {claimed_by}: {json.dumps(claimed.to_json(exclude_none=True))}\n"
                    f"  {test_nodeid}: {json.dumps(declared.to_json(exclude_none=True))}"
                )

    def claim_case_id(self, case_id: str, test_nodeid: str) -> None:
        """
        Hold every case id the run emits to one vector, it being how a consumer names the case.

        Args:
            case_id: The identifier the filler authored for this case.
            test_nodeid: The test that produced it, named in the refusal.

        Raises:
            ValueError: When the id is not spelled as slash-separated lowercase words.
            ValueError: When an earlier vector was already emitted under this id.
        """
        if not CASE_ID_PATTERN.fullmatch(case_id):
            raise ValueError(
                f"case id '{case_id}' is not spelled as slash-separated lowercase words, "
                "the way 'uint64/max' and 'bitlist16/invalid/over_limit' are"
            )
        claimed_by = self.case_producers.get(case_id)
        if claimed_by is not None:
            raise ValueError(
                f"case id '{case_id}' names two different vectors:\n  {claimed_by}\n  {test_nodeid}"
            )
        self.case_producers[case_id] = test_nodeid

    def add_fixture(
        self, fixture_format: str, fixture: Any, item: pytest.Item, case_id: str
    ) -> None:
        """
        Add a fixture to the collection, and record its path on the test that produced it.

        Raises:
            ValueError: If the case id is malformed, or already names another vector.
            ValueError: If one type name stands for two different declarations.
        """
        self.claim_case_id(case_id, item.nodeid)
        self.claim_type_names(fixture, item.nodeid)

        fixture_path = self.fixture_output_file(fixture, item.nodeid, fixture_format, case_id)
        self.cases.append(
            CollectedCase(
                fixture=fixture,
                case_id=case_id,
                tags=case_tags(item),
                output_file=fixture_path,
            )
        )

        # Stashed on the item, not the session-wide config, which would leak to later tests.
        item.stash[FIXTURE_PATH_ABSOLUTE_KEY] = str(fixture_path.absolute())
        item.stash[FIXTURE_PATH_RELATIVE_KEY] = str(fixture_path.relative_to(self.output_directory))
        item.stash[FIXTURE_FORMAT_KEY] = fixture_format

    def write_fixtures(self) -> None:
        """Write every vector to its own file, then the index and the manifest describing them."""
        index_rows = []
        for case in sorted(self.cases, key=lambda collected: collected.output_file):
            case.output_file.parent.mkdir(parents=True, exist_ok=True)
            document = json_document(case.fixture.json_dict_with_info())
            case.output_file.write_text(document, encoding="utf-8")
            index_rows.append(
                {
                    "id": case.case_id,
                    "path": case.output_file.relative_to(self.output_directory).as_posix(),
                    "typeName": case.fixture.case_type_name(),
                    "kind": case.fixture.case_kind(),
                    "valid": case.fixture.valid,
                    "tags": list(case.tags),
                    "sha256": hashlib.sha256(document.encode("utf-8")).hexdigest(),
                }
            )

        (self.output_directory / "index.json").write_text(
            json_document({"cases": index_rows}), encoding="utf-8"
        )
        (self.output_directory / "manifest.json").write_text(
            json_document(
                {
                    "formatVersion": FIXTURE_FORMAT_VERSION,
                    "specVersion": version("eth-ssz-specs"),
                    "generator": GENERATOR,
                    "caseCount": len(index_rows),
                }
            ),
            encoding="utf-8",
        )


_VECTOR_DOCUMENT: Final = Path(__file__).parent / "fixtures_readme.md"
"""How to read a vector, copied into every fill as the output directory's README."""

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


def pytest_configure(config: pytest.Config) -> None:
    """Refuse a distributed fill, where each worker would clean away what the others wrote."""
    if getattr(config.option, "numprocesses", None) or getattr(config.option, "dist", "no") != "no":
        raise pytest.UsageError(
            "fill does not run distributed: every worker cleans the output directory and "
            "writes only the vectors it filled. Drop -n and --dist."
        )


def pytest_ignore_collect(collection_path: Path, config: pytest.Config) -> bool | None:
    """Ignore paths outside the filler tests, which sit under the configured root."""
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
    """Set up the session here, since the configure hook also runs for a preview."""
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
            leftover_fixture_paths = sorted(output_directory.iterdir())
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

    # The output directory is gitignored, and --clean removes it whole.
    # The document is copied in on every fill rather than tracked where it is read.
    shutil.copyfile(_VECTOR_DOCUMENT, output_directory / "README.md")

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

    # The compiler dedents docstrings from Python 3.13 on, so a vector must not depend on it.
    if hasattr(request.node, "cls") and request.cls and request.cls.__doc__:
        test_class_doc = f"Test class documentation:\n{cleandoc(request.cls.__doc__)}"
    if hasattr(request.node, "function") and request.function.__doc__:
        test_function_doc = cleandoc(request.function.__doc__)

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

        def fill_and_collect(*, case_id: str, **spec_fields: Any) -> Any:
            test_spec = spec_class(**spec_fields)
            generated_fixture = test_spec.generate()

            filled_fixture = generated_fixture.with_info(
                info=FixtureInfo(
                    test_id=case_id,
                    generated_by=request.node.nodeid,
                    description=test_case_description,
                    fixture_format=spec_class.format_name,
                )
            )

            request.config.stash[FIXTURE_COLLECTOR_KEY].add_fixture(
                fixture_format=spec_class.format_name,
                fixture=filled_fixture,
                item=request.node,
                case_id=case_id,
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

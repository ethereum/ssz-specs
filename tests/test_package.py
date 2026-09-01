"""Unit tests for what the package itself publishes: its exports and its module map."""

from __future__ import annotations

import ast
import importlib.metadata
import pathlib
import re

import pytest

import ssz

# The map in the package docstring, one module per indented line.
MAP_ENTRIES = re.findall(r"^    (\w+) {2,}\S", ssz.__doc__ or "", re.MULTILINE)

# The directory the package ships from, taken from where its own modules were loaded.
PACKAGE = pathlib.Path(next(iter(ssz.__path__)))

# Every module that ships, which is what the map must account for.
SHIPPED = sorted(path.stem for path in PACKAGE.glob("*.py") if path.stem != "__init__")


def test_the_map_lists_every_module_that_ships() -> None:
    """A module added without a line in the map leaves a reader nowhere to find it."""
    assert sorted(MAP_ENTRIES) == SHIPPED


def test_the_map_names_nothing_that_does_not_ship() -> None:
    """A line left behind by a deleted module sends a reader to a file that is gone."""
    assert set(MAP_ENTRIES) <= set(SHIPPED)


def test_the_map_runs_in_dependency_order() -> None:
    """
    The map is a reading order, so nothing may appear before what it is built on.

    An alphabetical listing inverts a third of these pairs.
    """
    position = {name: index for index, name in enumerate(MAP_ENTRIES)}
    for name in MAP_ENTRIES:
        tree = ast.parse((PACKAGE / f"{name}.py").read_text())
        for node in tree.body:
            if not isinstance(node, ast.ImportFrom) or not node.module:
                continue
            if not node.module.startswith("ssz."):
                continue
            dependency = node.module.split(".", 1)[1]
            if dependency in position:
                assert position[dependency] < position[name], (
                    f"{name} is listed before {dependency}, which it imports"
                )


@pytest.mark.parametrize(
    "name",
    [
        # The constants and functions the specification's merkleization section names.
        "BYTES_PER_CHUNK",
        "BITS_PER_CHUNK",
        "merkleize",
        "mix_in_length",
        "mix_in_selector",
        "hash_tree_root",
        "chunk_count",
        # The progressive shapes, from EIP-7916 and EIP-7495.
        "merkleize_progressive",
        "mix_in_active_fields",
    ],
)
def test_the_words_the_spec_merkleizes_with_are_exported(name: str) -> None:
    """
    A reader looking up a name from the specification must find it on the package.

    A name reachable only by knowing which module holds it cannot be looked up at all.
    """
    assert name in ssz.__all__
    assert hasattr(ssz, name)


def test_every_exported_name_resolves() -> None:
    """An export that names nothing breaks a star-import rather than one lookup."""
    for name in ssz.__all__:
        assert hasattr(ssz, name), name


def test_the_exports_are_sorted() -> None:
    """A sorted list is the one order two people adding a name will not conflict over."""
    assert list(ssz.__all__) == sorted(ssz.__all__)


def test_the_type_marker_ships_with_the_package() -> None:
    """Without the marker a consumer's type checker reads every export as untyped."""
    assert (PACKAGE / "py.typed").is_file()


# Names a module defines without a leading underscore, and deliberately does not publish.
# Every one is machinery another module reaches for, not vocabulary the specification uses.
UNPUBLISHED = {
    "INTERN_BELOW",
    "PARANOID_ROOTS",
    "StrictBaseModel",
    "ZERO_CHUNK",
    "field_names",
    "layout_chunks",
    "mix_in",
    "offset_table_spans",
    "progressive_container_plan",
    "wrapping_schema",
}


def module_level_public_names() -> set[str]:
    """Every name a shipped module binds at its top level without a leading underscore."""
    found: set[str] = set()
    for path in PACKAGE.glob("*.py"):
        if path.stem == "__init__":
            continue
        for node in ast.parse(path.read_text()).body:
            if isinstance(node, ast.FunctionDef | ast.ClassDef):
                found.add(node.name)
            elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
                found.add(node.target.id)
            elif isinstance(node, ast.Assign):
                found |= {t.id for t in node.targets if isinstance(t, ast.Name)}
    return {name for name in found if not name.startswith("_")}


def test_every_public_name_is_published_or_listed_as_unpublished() -> None:
    """A name left in neither set is a decision nobody made, which is how a surface drifts."""
    assert module_level_public_names() - set(ssz.__all__) == UNPUBLISHED


def test_nothing_listed_as_unpublished_is_also_published() -> None:
    """A name in both sets means the list stopped describing the package."""
    assert UNPUBLISHED.isdisjoint(ssz.__all__)


def test_the_version_matches_the_distribution() -> None:
    """A version read from anywhere but the distribution is one that can disagree with it."""
    assert ssz.__version__ == importlib.metadata.version("eth-ssz-specs")

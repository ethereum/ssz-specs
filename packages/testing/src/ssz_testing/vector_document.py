"""The document shipped beside the vectors, its open counts written from what the fill wrote."""

import re
from collections.abc import Sequence
from pathlib import Path
from typing import TYPE_CHECKING, Final

if TYPE_CHECKING:
    from ssz_testing.plugin import CollectedCase

_DOCUMENT: Final = Path(__file__).parent / "fixtures_readme.md"
"""How to read a vector, written into every fill as the output directory's README."""

_TABLED_REASON: Final = re.compile(r"^\| `([A-Z][A-Z_]*)` \|", re.MULTILINE)
"""A refusal name, which only a row of the document's reason tables opens with."""


def _refusal_names(cases: "Sequence[CollectedCase]") -> list[str]:
    """The name each refused vector carries, which is the whole contract of a negative case."""
    return [
        case.fixture.rejection_reason.name
        for case in cases
        if case.fixture.rejection_reason is not None
    ]


def _stated_counts(cases: "Sequence[CollectedCase]") -> dict[str, str]:
    """What the fill just wrote, keyed by the line of the document each count is written over."""
    accepted = sum(1 for case in cases if case.fixture.valid)
    union_roots = sum(
        1
        for case in cases
        if "root" in case.fixture.json_dict
        and any(declared.holds_a_union for declared in case.fixture.declared_types().values())
    )
    # No refusal name is that row's alone, so a filler themes the cases belonging to it.
    element_minimum = sum(1 for case in cases if "element-minimum" in case.tags)
    list_table = sum(
        1 for name in _refusal_names(cases) if name in {"OFFSET_BELOW_TABLE", "OFFSET_UNALIGNED"}
    )
    return {
        "<!-- case count -->": (
            f"{len(cases)} cases: {accepted} an implementation must accept, "
            f"{len(cases) - accepted} it must refuse."
        ),
        "<!-- union roots -->": str(union_roots),
        "<!-- element minimum cases -->": str(element_minimum),
        "<!-- list table cases -->": str(list_table),
    }


def counted_document(cases: "Sequence[CollectedCase]") -> str:
    """
    The shipped document, with what the fill just wrote standing in for the counts it leaves open.

    Raises:
        ValueError: When the document holds no placeholder for one of those counts.
        ValueError: When a vector was refused under a name no table of the document lists.
    """
    document = _DOCUMENT.read_text(encoding="utf-8")
    for placeholder, counted in _stated_counts(cases).items():
        if placeholder not in document:
            raise ValueError(f"'{_DOCUMENT.name}' holds no '{placeholder}' line")
        document = document.replace(placeholder, counted, 1)

    # Only this direction: which documented names go unemitted is a claim about the whole suite.
    undocumented = set(_refusal_names(cases)) - set(_TABLED_REASON.findall(document))
    if undocumented:
        raise ValueError(
            f"'{_DOCUMENT.name}' tables no refusal named "
            f"{', '.join(sorted(undocumented))}, and this fill emitted it"
        )
    return document

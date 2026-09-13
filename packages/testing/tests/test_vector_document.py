"""What the shipped document states about the corpus, and when it refuses to state it."""

import re
from pathlib import Path
from typing import Final
from unittest.mock import patch

import pytest

from ssz import Uint8, ValueFault
from ssz_testing import vector_document
from ssz_testing.plugin import CollectedCase
from ssz_testing.serialization import SSZFixture
from ssz_testing.vector_document import _DOCUMENT, _TABLED_REASON, _stated_counts, counted_document

FILLER_REASON: Final = re.compile(r"\b(?:ValueFault|TypeFault|JsonFault)\.([A-Z][A-Z_]*)\b")
"""A refusal name as a filler declares it, which is the name its vector then carries."""

REPOSITORY_ROOT = Path(__file__).parents[3]


def test_a_document_naming_no_count_fails_the_fill(tmp_path: Path) -> None:
    """A document edited past its placeholder would ship no counts, so it stops the fill."""
    uncounted = tmp_path / "uncounted.md"
    uncounted.write_text("A document answering nothing the fill asks it.\n", encoding="utf-8")

    with pytest.raises(ValueError, match="holds no"):
        with patch.object(vector_document, "_DOCUMENT", uncounted):
            counted_document([])


def test_a_refusal_the_document_tables_nowhere_fails_the_fill(tmp_path: Path) -> None:
    """A reason a decoder must name is a reason the document names, so an untabled one stops it."""
    stub = tmp_path / "stub.md"
    # Every placeholder the fill asks for, so the count check passes and the reason check runs.
    answered = " ".join(_stated_counts([]))
    stub.write_text(
        f"{answered}\n| Name | The input |\n| --- | --- |\n| `LIMIT` | Holds too many. |\n",
        encoding="utf-8",
    )
    refused = CollectedCase(
        fixture=SSZFixture(
            ssz_type=Uint8,
            type_name="Uint8",
            serialized="0x",
            rejection_reason=ValueFault.SCOPE,
        ),
        case_id="uint8/short",
        tags=(),
        output_file=Path("uint8-short.json"),
    )

    with pytest.raises(ValueError, match="tables no refusal named SCOPE"):
        with patch.object(vector_document, "_DOCUMENT", stub):
            counted_document([refused])


def test_every_reason_the_document_tables_is_one_a_filler_emits() -> None:
    """The tables claim to hold only reasons this suite reaches, which one fill cannot check."""
    named = {
        name
        for filler in (REPOSITORY_ROOT / "tests" / "fillers").rglob("*.py")
        for name in FILLER_REASON.findall(filler.read_text(encoding="utf-8"))
    }

    tabled = set(_TABLED_REASON.findall(_DOCUMENT.read_text(encoding="utf-8")))
    assert tabled == named

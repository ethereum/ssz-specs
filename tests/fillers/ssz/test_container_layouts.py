"""SSZ conformance test vectors for the offset table a container's variable fields sit behind."""

from typing import ClassVar

import pytest

from ssz import Container, List, Uint8, Uint16, Uint32, Uint64
from ssz_testing import SSZTestFiller

pytestmark = pytest.mark.tags("offsets")


class SampleUint64List6(List[Uint64]):
    """Bounded list of eight-byte elements, the first variable field of the pairs below."""

    LIMIT: ClassVar[int] = 6


class SampleUint16List5(List[Uint16]):
    """Bounded list of two-byte elements, the second variable field of the pairs below."""

    LIMIT: ClassVar[int] = 5


class SampleTwoOffsets(Container):
    """A fixed field before two variable ones, whose offsets are adjacent in the table."""

    head: Uint8
    first: SampleUint64List6
    second: SampleUint16List5


class SampleSpacedOffsets(Container):
    """A fixed field between the two variable ones, so their offsets are not adjacent."""

    head: Uint8
    first: SampleUint64List6
    middle: Uint32
    second: SampleUint16List5
    tail: Uint16


class SampleLeadingOffset(Container):
    """A variable field first, so the encoding opens on an offset and a fixed field follows."""

    first: SampleUint16List5
    tail: Uint32


class SampleLoneOffset(Container):
    """One variable field and nothing else, so the fixed part is exactly one offset."""

    only: SampleUint64List6


class SampleInnerOffsets(Container):
    """A variable-size container, itself a fixed field before one offset."""

    tag: Uint16
    items: SampleUint16List5


class SampleNestedOffsets(Container):
    """A variable-size container between two fixed fields, its own table nested behind an offset."""

    head: Uint8
    inner: SampleInnerOffsets
    tail: Uint32


FIRST_ELEMENTS = [
    Uint64(0x1122334455667788),
    Uint64(0x99AABBCCDDEEFF00),
    Uint64(0x0102030405060708),
]
"""Three eight-byte elements, the payload every non-empty first field below carries."""

SECOND_ELEMENTS = [Uint16(0xBEEF), Uint16(0xCAFE)]
"""Two two-byte elements, the payload every non-empty second field below carries."""


def test_two_offsets_both_filled(ssz_test: SSZTestFiller) -> None:
    """
    A container whose two variable fields both carry a payload round-trips unchanged.

    Given
    -----
    - a container of a one-byte field and two variable fields, its fixed part nine bytes.
    - a first field of three eight-byte elements, and a second of two two-byte elements.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the decoded value equals the original.
    - the first offset is nine, where the fixed part ends.
    - the second offset is thirty-three, the first offset plus the twenty-four bytes before it.
    """
    ssz_test(
        case_id="container_layout/two_offsets/both_filled",
        type_name="SampleTwoOffsets",
        value=SampleTwoOffsets(
            head=Uint8(0x2A),
            first=SampleUint64List6(data=FIRST_ELEMENTS),
            second=SampleUint16List5(data=SECOND_ELEMENTS),
        ),
    )


@pytest.mark.tags("empty")
def test_two_offsets_both_empty(ssz_test: SSZTestFiller) -> None:
    """
    A container whose two variable fields are both empty round-trips unchanged.

    Given
    -----
    - a container of a one-byte field and two variable fields, its fixed part nine bytes.
    - both variable fields empty, so neither contributes a byte to the payload.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the decoded value equals the original.
    - both offsets are nine, since an empty field advances the running sum by nothing.
    - the encoding is the fixed part alone.
    """
    ssz_test(
        case_id="container_layout/two_offsets/both_empty",
        type_name="SampleTwoOffsets",
        value=SampleTwoOffsets(
            head=Uint8(0x2A),
            first=SampleUint64List6(data=[]),
            second=SampleUint16List5(data=[]),
        ),
    )


@pytest.mark.tags("empty")
def test_two_offsets_first_empty(ssz_test: SSZTestFiller) -> None:
    """
    A container whose first variable field is empty round-trips unchanged.

    Given
    -----
    - a container of a one-byte field and two variable fields, its fixed part nine bytes.
    - an empty first field, and a second field of two two-byte elements.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the decoded value equals the original.
    - both offsets are nine, and the second field begins where the first would have.
    - two equal offsets are the only way to say the field between them is empty.
    """
    ssz_test(
        case_id="container_layout/two_offsets/first_empty",
        type_name="SampleTwoOffsets",
        value=SampleTwoOffsets(
            head=Uint8(0x2A),
            first=SampleUint64List6(data=[]),
            second=SampleUint16List5(data=SECOND_ELEMENTS),
        ),
    )


@pytest.mark.tags("empty")
def test_two_offsets_second_empty(ssz_test: SSZTestFiller) -> None:
    """
    A container whose second variable field is empty round-trips unchanged.

    Given
    -----
    - a container of a one-byte field and two variable fields, its fixed part nine bytes.
    - a first field of three eight-byte elements, and an empty second field.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the decoded value equals the original.
    - the second offset is thirty-three, which is also where the encoding ends.
    - the last field is closed by the budget, so an empty one leaves no byte behind it.
    """
    ssz_test(
        case_id="container_layout/two_offsets/second_empty",
        type_name="SampleTwoOffsets",
        value=SampleTwoOffsets(
            head=Uint8(0x2A),
            first=SampleUint64List6(data=FIRST_ELEMENTS),
            second=SampleUint16List5(data=[]),
        ),
    )


def test_fixed_field_between_offsets(ssz_test: SSZTestFiller) -> None:
    """
    A container with a fixed field between its variable ones round-trips unchanged.

    Given
    -----
    - a container of five fields, the second and fourth variable, its fixed part fifteen bytes.
    - a four-byte field between the two offsets, and a two-byte field after both.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the decoded value equals the original.
    - the first offset is fifteen, the width of the whole fixed part and not of the table.
    - the second offset sits at byte nine, four bytes of fixed field away from the first.
    """
    ssz_test(
        case_id="container_layout/fixed_field_between_offsets",
        type_name="SampleSpacedOffsets",
        value=SampleSpacedOffsets(
            head=Uint8(0x2A),
            first=SampleUint64List6(data=FIRST_ELEMENTS),
            middle=Uint32(0xDDCCBBAA),
            second=SampleUint16List5(data=SECOND_ELEMENTS),
            tail=Uint16(0x1234),
        ),
    )


def test_leading_offset(ssz_test: SSZTestFiller) -> None:
    """
    A container whose first field is variable round-trips unchanged.

    Given
    -----
    - a container of a variable field and then a four-byte fixed field.
    - a first field of two two-byte elements.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the decoded value equals the original.
    - the encoding opens on the offset, not on a field's own bytes.
    - the offset is eight, so the fixed field after it still comes first on the wire.
    """
    ssz_test(
        case_id="container_layout/leading_offset",
        type_name="SampleLeadingOffset",
        value=SampleLeadingOffset(
            first=SampleUint16List5(data=SECOND_ELEMENTS),
            tail=Uint32(0xDDCCBBAA),
        ),
    )


def test_lone_offset(ssz_test: SSZTestFiller) -> None:
    """
    A container holding one variable field and nothing else round-trips unchanged.

    Given
    -----
    - a container of a single variable field, so its fixed part is one offset.
    - a field of three eight-byte elements.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the decoded value equals the original.
    - the offset is four, the width of the offset itself.
    - the payload runs from there to the end of the budget.
    """
    ssz_test(
        case_id="container_layout/lone_offset",
        type_name="SampleLoneOffset",
        value=SampleLoneOffset(only=SampleUint64List6(data=FIRST_ELEMENTS)),
    )


@pytest.mark.tags("multi-level")
def test_nested_variable_container(ssz_test: SSZTestFiller) -> None:
    """
    A container holding a variable-size container round-trips unchanged.

    Given
    -----
    - an outer container of a one-byte field, a variable-size container, and a four-byte field.
    - an inner container of a two-byte field and a variable field of two two-byte elements.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the decoded value equals the original.
    - the outer offset is nine, and the inner one is six, each counted from its own container.
    - the inner offset is relative to where the inner encoding begins, not to the outer one.
    """
    ssz_test(
        case_id="container_layout/nested_variable_container",
        type_name="SampleNestedOffsets",
        value=SampleNestedOffsets(
            head=Uint8(0x2A),
            inner=SampleInnerOffsets(
                tag=Uint16(0x1234),
                items=SampleUint16List5(data=SECOND_ELEMENTS),
            ),
            tail=Uint32(0xDDCCBBAA),
        ),
    )

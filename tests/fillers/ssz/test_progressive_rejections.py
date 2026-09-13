"""SSZ conformance test vectors for encodings the progressive types refuse."""

from typing import ClassVar

from ssz import (
    List,
    ProgressiveContainer,
    ProgressiveList,
    Uint8,
    Uint16,
    Uint64,
)
from ssz_testing import ExpectedRejection, SSZTestFiller, ValueFault


class SampleUint64ProgressiveList(ProgressiveList[Uint64]):
    """Progressive list of eight-byte elements, so its budget divides by eight."""

    ELEMENT_TYPE = Uint64


class SampleUint16List4(List[Uint16]):
    """Bounded list of two-byte elements, used as a variable-size field."""

    LIMIT: ClassVar[int] = 4
    ELEMENT_TYPE = Uint16


class SampleSquare(ProgressiveContainer):
    """EIP-7495's own example: a two-byte field, a gap, then a one-byte field."""

    ACTIVE_FIELDS = (1, 0, 1)

    side: Uint16
    color: Uint8


class SampleBoundedListField(ProgressiveContainer):
    """Fixed field, a gap, then a bounded list, so the shape needs one offset."""

    ACTIVE_FIELDS = (1, 0, 1)

    head: Uint64
    body: SampleUint16List4


def test_progressive_list_decode_failure_budget_not_divided(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a progressive list of fixed-width elements from a partial element is rejected.

    Given
    -----
    - a progressive list of eight-byte elements, which carries no length prefix.
    - twelve bytes, which is one whole element and half of another.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the budget does not divide by the element width.
    """
    ssz_test(
        case_id="progressive_list/invalid/budget_not_divided",
        type_name="SampleUint64ProgressiveList",
        value=SampleUint64ProgressiveList(data=[]),
        raw_bytes="0x000102030405060708090a0b",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE_UNDIVIDED,
            exact_message="a budget of 12 does not divide by an element width of 8",
        ),
    )


def test_progressive_container_decode_failure_truncated_field(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a progressive container whose fixed part stops mid-field is rejected.

    Given
    -----
    - a three-byte fixed-size shape leading with a two-byte field.
    - a single byte, which ends inside that first field.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that one byte is not the three the shape spans.
    """
    ssz_test(
        case_id="progressive_container/invalid/truncated_field",
        type_name="SampleSquare",
        value=SampleSquare(side=Uint16(0x1234), color=Uint8(0x56)),
        raw_bytes="0x34",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            exact_message="SampleSquare spans 3 bytes, and the budget is 1",
        ),
    )


def test_progressive_container_decode_failure_first_offset_overlap(
    ssz_test: SSZTestFiller,
) -> None:
    """
    Decoding a progressive container whose first offset points into its fixed part is rejected.

    Given
    -----
    - a shape whose fixed part is twelve bytes: an eight-byte field and one offset.
    - an offset of eleven, which lands on the last byte of the offset itself.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the first offset must end the fixed part exactly.
    """
    ssz_test(
        case_id="progressive_container/invalid/first_offset_overlap",
        type_name="SampleBoundedListField",
        value=SampleBoundedListField(head=Uint64(7), body=SampleUint16List4(data=[])),
        raw_bytes="0x07000000000000000b000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.FIRST_OFFSET,
            exact_message="the first offset is 11, and the fixed part ends at 12",
        ),
    )

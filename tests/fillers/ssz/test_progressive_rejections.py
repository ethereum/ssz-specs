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


class SampleUint16ProgressiveList(ProgressiveList[Uint16]):
    """Progressive list of two-byte elements, used as a variable-size element."""

    ELEMENT_TYPE = Uint16


class SampleNestedProgressiveList(ProgressiveList[SampleUint16ProgressiveList]):
    """Progressive list of variable-size elements, encoded behind an offset table."""

    ELEMENT_TYPE = SampleUint16ProgressiveList


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


def test_progressive_list_decode_failure_first_offset_below_table(
    ssz_test: SSZTestFiller,
) -> None:
    """
    Decoding a progressive list whose first offset lands inside the table is rejected.

    Given
    -----
    - a progressive list of variable-size elements, whose count comes from the first offset.
    - a first offset of two, which is below the four bytes one table entry takes.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the first offset is below the table's own width.
    """
    ssz_test(
        case_id="progressive_list/invalid/first_offset_below_table",
        type_name="SampleNestedProgressiveList",
        value=SampleNestedProgressiveList(data=[]),
        raw_bytes="0x0200000001000200",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.OFFSET_BELOW_TABLE,
            exact_message="the first offset 2 is below the table's own width of 4",
        ),
    )


def test_progressive_list_decode_failure_offsets_out_of_order(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a progressive list whose offsets descend is rejected.

    Given
    -----
    - a first offset of eight, which declares a table of two entries.
    - a second offset of four, which sits below the offset before it.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected before any body is read.
    - the reason is that an offset is above the one after it, at element zero.
    """
    ssz_test(
        case_id="progressive_list/invalid/offsets_out_of_order",
        type_name="SampleNestedProgressiveList",
        value=SampleNestedProgressiveList(data=[]),
        raw_bytes="0x080000000400000001000200",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.OFFSET_UNORDERED,
            exact_message="[0]: offset 8 is above the offset after it, 4",
        ),
    )


def test_progressive_list_decode_failure_offset_past_budget(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a progressive list whose last offset overruns the input is rejected.

    Given
    -----
    - a first offset of eight, which declares a table of two entries.
    - a second offset of sixteen, in an input of twelve bytes.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected before any body is read.
    - the reason is that an offset runs past the budget, at element one.
    """
    ssz_test(
        case_id="progressive_list/invalid/offset_past_budget",
        type_name="SampleNestedProgressiveList",
        value=SampleNestedProgressiveList(data=[]),
        raw_bytes="0x080000001000000001000200",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.OFFSET_PAST_SCOPE,
            exact_message="[1]: offset 16 runs past the budget of 12",
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
    - the reason is that the stream ran out while the leading field was being read.
    """
    ssz_test(
        case_id="progressive_container/invalid/truncated_field",
        type_name="SampleSquare",
        value=SampleSquare(side=Uint16(0x1234), color=Uint8(0x56)),
        raw_bytes="0x34",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.TRUNCATED,
            exact_message="side: Uint16 needs 2 bytes, the input holds 1",
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

"""SSZ conformance vectors for a list offset table that does not hold."""

from typing import ClassVar

import pytest

from ssz import ByteList, List, ProgressiveList
from ssz_testing import ExpectedRejection, SSZTestFiller, ValueFault

pytestmark = pytest.mark.tags("offsets")


class OffsetTableByteList8(ByteList):
    """Byte list of up to 8 bytes, the short variable-size element these tables index."""

    LIMIT: ClassVar[int] = 8


class OffsetTableList4(List[OffsetTableByteList8]):
    """Variable-length list of up to 4 variable-size elements, encoded behind an offset table."""

    LIMIT: ClassVar[int] = 4
    ELEMENT_TYPE = OffsetTableByteList8


class OffsetTableProgressiveList(ProgressiveList[OffsetTableByteList8]):
    """The same elements with no capacity, which encodes to the very same offset table."""

    ELEMENT_TYPE = OffsetTableByteList8


LIST_DECODER = OffsetTableList4(data=[OffsetTableByteList8(data=b"\xaa\xbb")])
"""A well-formed list, present only so a decode-failure case names the class that refuses."""

PROGRESSIVE_LIST_DECODER = OffsetTableProgressiveList(data=[OffsetTableByteList8(data=b"\xaa\xbb")])
"""The same, for the shape that declares no capacity."""


def test_list_offset_budget_below_one_offset(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a list of variable-size elements from a budget too small for one offset is rejected.

    Given
    -----
    - a list whose elements are variable-size, so its encoding leads with an offset table.
    - the input bytes 0x000000, three bytes where the narrowest table takes four.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the budget does not hold one offset.
    - an empty input is not this case: it holds no table and decodes to the empty list.
    """
    ssz_test(
        case_id="bytelist8_list4/invalid/budget_below_one_offset",
        type_name="OffsetTableList4",
        value=LIST_DECODER,
        raw_bytes="0x000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE_TOO_SMALL,
            exact_message="OffsetTableList4 needs at least 4 bytes, and the budget is 3",
        ),
    )


@pytest.mark.tags("boundary")
def test_list_first_offset_zero(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a list whose first offset is zero is rejected.

    Given
    -----
    - a list whose elements are variable-size.
    - the input bytes 0x00000000, one offset of zero.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the first offset is below the table's own width.
    - zero is a multiple of four, so only the below-table rule is broken here.
    """
    ssz_test(
        case_id="bytelist8_list4/invalid/first_offset_zero",
        type_name="OffsetTableList4",
        value=LIST_DECODER,
        raw_bytes="0x00000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.OFFSET_BELOW_TABLE,
            exact_message="the first offset 0 is below the table's own width of 4",
        ),
    )


def test_list_first_offset_below_table(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a list whose first offset points into its own table is rejected.

    Given
    -----
    - a list whose elements are variable-size.
    - the input bytes 0x01000000, a first offset of one.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the first offset is below the table's own width.
    - one is also not a multiple of four, and the below-table rule is checked first.
    """
    ssz_test(
        case_id="bytelist8_list4/invalid/first_offset_below_table",
        type_name="OffsetTableList4",
        value=LIST_DECODER,
        raw_bytes="0x01000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.OFFSET_BELOW_TABLE,
            exact_message="the first offset 1 is below the table's own width of 4",
        ),
    )


def test_list_first_offset_unaligned(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a list whose first offset is not a whole number of offsets is rejected.

    Given
    -----
    - a list whose elements are variable-size.
    - the input bytes 0x06000000aabbccdd, a first offset of six within a budget of eight.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the first offset is not a multiple of the offset width.
    - six is above the table's width and within the budget, so this rule alone is broken.
    """
    ssz_test(
        case_id="bytelist8_list4/invalid/first_offset_unaligned",
        type_name="OffsetTableList4",
        value=LIST_DECODER,
        raw_bytes="0x06000000aabbccdd",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.OFFSET_UNALIGNED,
            exact_message="the first offset 6 is not a multiple of 4",
        ),
    )


def test_list_first_offset_past_budget(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a list whose first offset runs past the end of the input is rejected.

    Given
    -----
    - a list whose elements are variable-size.
    - the input bytes 0x08000000, a first offset of eight within a budget of four.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the offset runs past the budget.
    - the count of two the offset implies is within the capacity, and is read only after this.
    - the refusal carries no path, the table itself being what broke.
    """
    ssz_test(
        case_id="bytelist8_list4/invalid/first_offset_past_budget",
        type_name="OffsetTableList4",
        value=LIST_DECODER,
        raw_bytes="0x08000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.OFFSET_PAST_SCOPE,
            exact_message="offset 8 runs past the budget of 4",
        ),
    )


@pytest.mark.tags("limit")
def test_list_first_offset_over_limit(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a list whose first offset implies more elements than the capacity is rejected.

    Given
    -----
    - a list holding at most four elements.
    - a first offset of twenty within a budget of twenty, implying five elements.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the implied count exceeds the capacity.
    - the count is checked before the rest of the table is read, so no input allocates past it.
    """
    ssz_test(
        case_id="bytelist8_list4/invalid/first_offset_over_limit",
        type_name="OffsetTableList4",
        value=LIST_DECODER,
        raw_bytes="0x1400000000000000000000000000000000000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.LIMIT,
            exact_message="OffsetTableList4 holds at most 4 elements, got 5",
        ),
    )


def test_list_offsets_unordered(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a list whose table descends between two elements is rejected.

    Given
    -----
    - a list whose elements are variable-size.
    - a table of 12, 15 and 13 within a budget of sixteen, the middle pair descending.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that an offset is above the offset after it.
    - the pair is not the last, whose partner is the budget and whose rule is another.
    - the refusal names the element the descending offset opens.
    """
    ssz_test(
        case_id="bytelist8_list4/invalid/offsets_unordered",
        type_name="OffsetTableList4",
        value=LIST_DECODER,
        raw_bytes="0x0c0000000f0000000d000000aabbccdd",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.OFFSET_UNORDERED,
            exact_message="[1]: offset 15 is above the offset after it, 13",
        ),
    )


def test_list_last_offset_past_budget(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a list whose last offset runs past the budget is rejected.

    Given
    -----
    - a list whose elements are variable-size.
    - a table of 8 and 12 within a budget of ten, the last body opening past the end.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the last offset runs past the budget, which closes the last pair.
    - the whole table is settled first, so the earlier body's impossible span is never read.
    - the refusal names the element whose offset ran past.
    """
    ssz_test(
        case_id="bytelist8_list4/invalid/last_offset_past_budget",
        type_name="OffsetTableList4",
        value=LIST_DECODER,
        raw_bytes="0x080000000c000000aabb",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.OFFSET_PAST_SCOPE,
            exact_message="[1]: offset 12 runs past the budget of 10",
        ),
    )


@pytest.mark.tags("boundary")
def test_progressive_list_first_offset_zero(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a progressive list whose first offset is zero is rejected.

    Given
    -----
    - a progressive list of the same variable-size element, with no capacity.
    - the input bytes 0x00000000, one offset of zero.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the first offset is below the table's own width.
    - the two shapes encode alike, so declaring no capacity relaxes no offset rule.
    """
    ssz_test(
        case_id="bytelist8_progressive_list/invalid/first_offset_zero",
        type_name="OffsetTableProgressiveList",
        value=PROGRESSIVE_LIST_DECODER,
        raw_bytes="0x00000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.OFFSET_BELOW_TABLE,
            exact_message="the first offset 0 is below the table's own width of 4",
        ),
    )


def test_progressive_list_last_offset_past_budget(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a progressive list whose last offset runs past the budget is rejected.

    Given
    -----
    - a progressive list of the same variable-size element, with no capacity.
    - a table of 8 and 12 within a budget of ten, the last body opening past the end.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the last offset runs past the budget.
    - the bounded list refuses these very bytes the same way, down to the path it names.
    """
    ssz_test(
        case_id="bytelist8_progressive_list/invalid/last_offset_past_budget",
        type_name="OffsetTableProgressiveList",
        value=PROGRESSIVE_LIST_DECODER,
        raw_bytes="0x080000000c000000aabb",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.OFFSET_PAST_SCOPE,
            exact_message="[1]: offset 12 runs past the budget of 10",
        ),
    )

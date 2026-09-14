"""SSZ conformance test vectors for the bound a progressive shape may declare."""

from typing import ClassVar, Final

import pytest

from ssz import Boolean, List, ProgressiveBitList, ProgressiveList, Uint16, Uint64
from ssz_testing import ExpectedRejection, SSZTestFiller, ValueFault

pytestmark = pytest.mark.tags("limit", "boundary")

A_BOUND_ON_A_PROGRESSIVE_SHAPE_IS_UNLISTED: Final = (
    "EIP-7916 gives the progressive shapes no capacity: an implementation that ignores the "
    "limit key builds the unbounded type the rest of the declaration spells, and accepts "
    "this input"
)
"""What the specification says about a payload a declared bound is the only reason to refuse."""

THREE_ELEMENT_ROOT: Final = "0x7e0adeccea8b17f07c3d1531a414d0b1f25543d5ddd519604ce30d5af83b1859"
"""Three eight-byte chunks on the spine under a mixed-in count of three, bound or not."""


class BoundedUint64ProgressiveList(ProgressiveList[Uint64]):
    """Progressive list of eight-byte integers bounded at three elements."""

    LIMIT: ClassVar[int] = 3


class FreeUint64ProgressiveList(ProgressiveList[Uint64]):
    """The same shape with no bound, the reference every byte and every root is read against."""


class ZeroBoundProgressiveList(ProgressiveList[Uint64]):
    """Progressive list bounded at zero, which admits the empty value and no other."""

    LIMIT: ClassVar[int] = 0


class BoundedProgressiveBitList(ProgressiveBitList):
    """Progressive bitlist bounded at four bits, the delimiter counting as none of them."""

    LIMIT: ClassVar[int] = 4


class SampleUint16List4(List[Uint16]):
    """Bounded list of two-byte elements, used as a variable-size element."""

    LIMIT: ClassVar[int] = 4


class BoundedVariableProgressiveList(ProgressiveList[SampleUint16List4]):
    """Progressive list of variable-size elements bounded at two, counted off the offset table."""

    LIMIT: ClassVar[int] = 2


def test_a_progressive_list_holds_the_count_its_bound_names(ssz_test: SSZTestFiller) -> None:
    """
    A progressive list bounded at three elements holds three of them.

    Given
    -----
    - a progressive list of eight-byte integers bounded at three elements.
    - three elements, the most that bound admits.

    When
    ----
    - the value is encoded and merkleized.

    Then
    ----
    - the declaration stands, a bound being a count rule this shape may carry.
    - it encodes to the twenty-four bytes the elements pack into, with no length prefix.
    - the root is the spine the three chunks hang on, under a mixed-in count of three.
    """
    ssz_test(
        case_id="progressive_limit/uint64_list3/at_the_bound",
        type_name="BoundedUint64ProgressiveList",
        value=BoundedUint64ProgressiveList.of(1, 2, 3),
        expected_root=THREE_ELEMENT_ROOT,
    )


def test_a_bound_moves_neither_the_encoding_nor_the_root(ssz_test: SSZTestFiller) -> None:
    """
    The same three elements under no bound encode and merkleize identically.

    Given
    -----
    - a progressive list of eight-byte integers declaring no bound.
    - the three elements the bounded shape beside it holds.

    When
    ----
    - the value is encoded and merkleized.

    Then
    ----
    - the bytes are the bytes of the bounded vector, to the byte.
    - the root is the root of the bounded vector, since the spine is laid out from the data.
    - so an implementation that ignores the limit key still passes both vectors.
    """
    ssz_test(
        case_id="progressive_limit/uint64_list3/unbounded_twin",
        type_name="FreeUint64ProgressiveList",
        value=FreeUint64ProgressiveList.of(1, 2, 3),
        expected_root=THREE_ELEMENT_ROOT,
    )


def test_a_progressive_list_refuses_a_count_past_its_bound(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a progressive list from a budget holding more elements than its bound is rejected.

    Given
    -----
    - a progressive list of eight-byte integers bounded at three elements.
    - thirty-two bytes, which divide into four whole elements.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the count comes off the budget, and is judged before a single element is read.
    - the specification bounds this shape nowhere, and the vector says so.
    """
    ssz_test(
        case_id="progressive_limit/uint64_list3/invalid/past_the_bound",
        type_name="BoundedUint64ProgressiveList",
        value=BoundedUint64ProgressiveList(),
        raw_bytes="0x" + "00" * 32,
        expected_rejection=ExpectedRejection(
            reason=ValueFault.LIMIT,
            exact_message="BoundedUint64ProgressiveList holds at most 3 elements, got 4",
        ),
        stricter_than_spec=A_BOUND_ON_A_PROGRESSIVE_SHAPE_IS_UNLISTED,
    )


def test_a_count_read_off_an_offset_table_is_held_to_the_bound(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a progressive list of variable-size elements past its bound is rejected.

    Given
    -----
    - a progressive list of variable-size elements bounded at two.
    - a first offset of twelve, which names a table of three entries.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the count comes off the first offset, not off the budget.
    - it is judged before the rest of the table is read, so the claim costs four bytes.
    - the specification bounds this shape nowhere, and the vector says so.
    """
    ssz_test(
        case_id="progressive_limit/variable_list2/invalid/past_the_bound",
        type_name="BoundedVariableProgressiveList",
        value=BoundedVariableProgressiveList(),
        raw_bytes="0x0c0000000c0000000c000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.LIMIT,
            exact_message="BoundedVariableProgressiveList holds at most 2 elements, got 3",
        ),
        stricter_than_spec=A_BOUND_ON_A_PROGRESSIVE_SHAPE_IS_UNLISTED,
    )


def test_a_progressive_list_bounded_at_zero_refuses_one_element(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a progressive list bounded at zero from one element is rejected.

    Given
    -----
    - a progressive list of eight-byte integers bounded at zero elements.
    - eight bytes, which are one whole element.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - a bound of zero is a count and not an omission, so it bounds.
    - the specification bounds this shape nowhere, and the vector says so.
    """
    ssz_test(
        case_id="progressive_limit/uint64_list0/invalid/one_element",
        type_name="ZeroBoundProgressiveList",
        value=ZeroBoundProgressiveList(),
        raw_bytes="0x0000000000000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.LIMIT,
            exact_message="ZeroBoundProgressiveList holds at most 0 elements, got 1",
        ),
        stricter_than_spec=A_BOUND_ON_A_PROGRESSIVE_SHAPE_IS_UNLISTED,
    )


def test_a_progressive_bitlist_counts_data_bits_against_its_bound(ssz_test: SSZTestFiller) -> None:
    """
    A progressive bitlist bounded at four bits holds four, the delimiter counting as none.

    Given
    -----
    - a progressive bitlist bounded at four bits.
    - the byte 0x1f, four set bits with the delimiter at position four.

    When
    ----
    - the input is decoded, then re-encoded and merkleized.

    Then
    ----
    - the four data bits are accepted, so the bound admits the count it names.
    - the delimiter shares the byte with them and is counted as none of them.
    """
    ssz_test(
        case_id="progressive_limit/bitlist4/at_the_bound",
        type_name="BoundedProgressiveBitList",
        value=BoundedProgressiveBitList(data=[Boolean(bit) for bit in (1, 1, 1, 1)]),
        expected_root="0xc0257dfcaae97d91a93ff541b158be0d5532b41f9ae406f94fcf51b6a8361a54",
    )


def test_a_progressive_bitlist_refuses_a_bit_past_its_bound(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a progressive bitlist from one bit past its bound is rejected.

    Given
    -----
    - a progressive bitlist bounded at four bits.
    - the byte 0x2f, the same byte with the delimiter moved out to position five.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - it spans the same one byte the accepted encoding does, so a width check admits it.
    - the delimiter is what gives the count, and the count is judged before any bit is built.
    - the specification bounds this shape nowhere, and the vector says so.
    """
    ssz_test(
        case_id="progressive_limit/bitlist4/invalid/past_the_bound",
        type_name="BoundedProgressiveBitList",
        value=BoundedProgressiveBitList(),
        raw_bytes="0x2f",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.LIMIT,
            exact_message="BoundedProgressiveBitList holds at most 4 bits, got 5",
        ),
        stricter_than_spec=A_BOUND_ON_A_PROGRESSIVE_SHAPE_IS_UNLISTED,
    )

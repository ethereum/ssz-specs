"""SSZ conformance vectors holding every offset to its neighbours, not only to the table's ends."""

from typing import ClassVar

import pytest

from ssz import ByteList, Container, List, ProgressiveList, Vector
from ssz_testing import ExpectedRejection, SSZTestFiller, ValueFault

pytestmark = pytest.mark.tags("offsets")


class InteriorByteList8(ByteList):
    """Byte list of up to 8 bytes, the innermost variable-size value these tables reach."""

    LIMIT: ClassVar[int] = 8


class InteriorPair(Container):
    """Struct of two variable-size fields, so its own two offsets make 8 its narrowest encoding."""

    head: InteriorByteList8
    tail: InteriorByteList8


class InteriorTriple(Container):
    """Struct of three variable-size fields, whose middle offset has a neighbour on either side."""

    first: InteriorPair
    middle: InteriorPair
    last: InteriorPair


class InteriorPairList4(List[InteriorPair]):
    """List of up to 4 of those structs, each body having 8 bytes as its own smallest span."""

    LIMIT: ClassVar[int] = 4
    ELEMENT_TYPE = InteriorPair


class InteriorPairVector2(Vector[InteriorPair]):
    """Vector of exactly 2 of them, whose count is declared rather than read off the table."""

    LENGTH: ClassVar[int] = 2
    ELEMENT_TYPE = InteriorPair


class InteriorPairProgressiveList(ProgressiveList[InteriorPair]):
    """The same elements with no capacity, which encodes to the very same offset table."""

    ELEMENT_TYPE = InteriorPair


def empty_pair() -> InteriorPair:
    """One of those structs holding two empty byte lists, which is its eight-byte minimum."""
    return InteriorPair(head=InteriorByteList8(), tail=InteriorByteList8())


TRIPLE_DECODER = InteriorTriple(first=empty_pair(), middle=empty_pair(), last=empty_pair())
"""One value of that shape, present only to name the decoder every three-offset case runs."""

PAIR_LIST_DECODER = InteriorPairList4(data=[empty_pair(), empty_pair()])
"""A well-formed list of two of those structs, present only to name the decoder that refuses."""

PAIR_VECTOR_DECODER = InteriorPairVector2(data=[empty_pair(), empty_pair()])
"""The same for the shape whose count is declared."""

PAIR_PROGRESSIVE_LIST_DECODER = InteriorPairProgressiveList(data=[empty_pair(), empty_pair()])
"""The same for the shape that declares no capacity."""


def test_middle_offset_moved_forward(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a struct whose middle offset stands above the one after it is rejected.

    Given
    -----
    - a struct of three variable-size fields, whose table of three offsets spans twelve bytes.
    - a table of 12, 32 and 28 within a budget of 36, the middle entry reaching past the last.
    - three well-formed bodies of eight bytes each, which the table would carve up wrongly.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that an offset stands above the one after it.
    - the first offset ends the fixed part, and the last one is inside the budget.
    - so neither rule that guards an end of the table is what refuses this.
    - the name of the field whose body the middle offset opens prefixes the refusal.
    """
    ssz_test(
        case_id="interior_offset/pair_triple/invalid/middle_moved_forward",
        type_name="InteriorTriple",
        value=TRIPLE_DECODER,
        raw_bytes="0x0c000000200000001c000000080000000800000008000000080000000800000008000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.OFFSET_UNORDERED,
            exact_message="middle: offset 32 is above the offset after it, 28",
        ),
    )


def test_middle_offset_moved_back(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a struct whose middle offset falls below the one before it is rejected.

    Given
    -----
    - a struct of three variable-size fields, whose table of three offsets spans twelve bytes.
    - a table of 12, 8 and 28 within a budget of 36, the middle entry landing inside the table.
    - three well-formed bodies of eight bytes each, which the table would carve up wrongly.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that an offset stands above the one after it.
    - the pair at fault is the first, whose span would run backwards by four bytes.
    - the name of the field whose body that span belongs to prefixes the refusal.
    """
    ssz_test(
        case_id="interior_offset/pair_triple/invalid/middle_moved_back",
        type_name="InteriorTriple",
        value=TRIPLE_DECODER,
        raw_bytes="0x0c000000080000001c000000080000000800000008000000080000000800000008000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.OFFSET_UNORDERED,
            exact_message="first: offset 12 is above the offset after it, 8",
        ),
    )


def test_middle_offset_equal_to_the_first(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a struct whose middle offset repeats the one before it is rejected by the element.

    Given
    -----
    - a struct of three variable-size fields, each of them at least eight bytes wide.
    - a table of 12, 12 and 28 within a budget of 36, the first two entries equal.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - two equal offsets are an empty span, which the rule on the table admits.
    - so the table is settled, and the refusal comes from the field that span was handed to.
    - the reason is that the element needs more bytes than the span gives it.
    - a decoder that read equal offsets as descending would refuse this by the other name.
    """
    ssz_test(
        case_id="interior_offset/pair_triple/invalid/middle_equal_to_first",
        type_name="InteriorTriple",
        value=TRIPLE_DECODER,
        raw_bytes="0x0c0000000c0000001c000000080000000800000008000000080000000800000008000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE_TOO_SMALL,
            exact_message="first: InteriorPair needs at least 8 bytes, and the budget is 0",
        ),
    )


def test_middle_offset_equal_to_the_last(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a struct whose middle offset repeats the one after it is rejected by the element.

    Given
    -----
    - a struct of three variable-size fields, each of them at least eight bytes wide.
    - a table of 12, 28 and 28 within a budget of 36, the last two entries equal.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the empty span falls on the middle field this time, and the table is settled all the same.
    - the reason is that the element needs more bytes than the span gives it.
    - the first field is handed sixteen bytes, and is never read, the table being settled whole.
    """
    ssz_test(
        case_id="interior_offset/pair_triple/invalid/middle_equal_to_last",
        type_name="InteriorTriple",
        value=TRIPLE_DECODER,
        raw_bytes="0x0c0000001c0000001c000000080000000800000008000000080000000800000008000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE_TOO_SMALL,
            exact_message="middle: InteriorPair needs at least 8 bytes, and the budget is 0",
        ),
    )


def test_list_span_below_element_minimum(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a list whose first two offsets are closer than one element can be is rejected.

    Given
    -----
    - a list of structs whose narrowest encoding is the eight bytes of their own two offsets.
    - a table of 8 and 12 within a budget of 20, so the first body is given four bytes.
    - a second body of eight well-formed bytes, so only the first span is short.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the element needs more bytes than the span between the two offsets.
    - the whole budget is ample, so this is the element's own minimum and not the list's.
    - the position of the element the short span belongs to prefixes the refusal.
    """
    ssz_test(
        case_id="interior_offset/pair_list4/invalid/span_below_element_minimum",
        type_name="InteriorPairList4",
        value=PAIR_LIST_DECODER,
        raw_bytes="0x080000000c000000080000000800000008000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE_TOO_SMALL,
            exact_message="[0]: InteriorPair needs at least 8 bytes, and the budget is 4",
        ),
    )


def test_vector_span_below_element_minimum(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a vector whose two offsets are closer than one element can be is rejected.

    Given
    -----
    - a vector of exactly two of those structs, whose table therefore spans eight bytes.
    - the very bytes the list case refuses, which are a well-formed table for this count too.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the element needs more bytes than the span between the two offsets.
    - a declared count reads the same table a first offset of eight implies for a list.
    - it holds that table to the same element minimum.
    """
    ssz_test(
        case_id="interior_offset/pair_vector2/invalid/span_below_element_minimum",
        type_name="InteriorPairVector2",
        value=PAIR_VECTOR_DECODER,
        raw_bytes="0x080000000c000000080000000800000008000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE_TOO_SMALL,
            exact_message="[0]: InteriorPair needs at least 8 bytes, and the budget is 4",
        ),
    )


def test_progressive_list_span_below_element_minimum(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a progressive list whose two offsets are closer than one element can be is rejected.

    Given
    -----
    - a progressive list of the same structs, with no capacity of its own.
    - the very bytes the bounded list refuses.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the element needs more bytes than the span between the two offsets.
    - declaring no capacity relaxes no minimum an element brings with it.
    """
    ssz_test(
        case_id="interior_offset/pair_progressive_list/invalid/span_below_element_minimum",
        type_name="InteriorPairProgressiveList",
        value=PAIR_PROGRESSIVE_LIST_DECODER,
        raw_bytes="0x080000000c000000080000000800000008000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE_TOO_SMALL,
            exact_message="[0]: InteriorPair needs at least 8 bytes, and the budget is 4",
        ),
    )

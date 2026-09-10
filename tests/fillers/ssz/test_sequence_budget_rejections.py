"""SSZ rejection vectors for byte budgets and element counts over fixed-size elements."""

from typing import ClassVar

import pytest

from ssz import ByteList, Container, List, Uint16, Uint32, Uint64, Vector
from ssz_testing import ExpectedRejection, SSZTestFiller, ValueFault

pytestmark = pytest.mark.tags("boundary")


class BudgetUint16List8(List[Uint16]):
    """List of up to eight two-byte elements, so a budget divides by two or by nothing."""

    LIMIT: ClassVar[int] = 8


class BudgetUint64List4(List[Uint64]):
    """List of up to four eight-byte elements, where an even budget can still fail to divide."""

    LIMIT: ClassVar[int] = 4


class BudgetUint32List3(List[Uint32]):
    """List of up to three four-byte elements, so a fourth whole element breaks the limit."""

    LIMIT: ClassVar[int] = 3


class BudgetUint16Vector4(Vector[Uint16]):
    """Vector of exactly four two-byte elements, spanning eight bytes and no other count."""

    LENGTH: ClassVar[int] = 4


class BudgetByteList33(ByteList):
    """Byte list capped one byte past a Merkle chunk, so the limit is not a power of two."""

    LIMIT: ClassVar[int] = 33


class BudgetFixedPair(Container):
    """Fixed-size struct spanning six bytes, a four-byte field ahead of a two-byte one."""

    first: Uint32
    second: Uint16


def test_list_of_two_byte_elements_odd_budget(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a list of two-byte elements from an odd number of bytes is rejected.

    Given
    -----
    - a list type holding up to eight two-byte elements.
    - the input bytes 0x0100020003, five bytes, which hold two elements and half of a third.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the budget does not divide by the element width.
    """
    ssz_test(
        case_id="uint16_list8/invalid/budget_undivided",
        type_name="BudgetUint16List8",
        value=BudgetUint16List8(),
        raw_bytes="0x0100020003",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE_UNDIVIDED,
            exact_message="a budget of 5 does not divide by an element width of 2",
        ),
    )


def test_list_of_eight_byte_elements_undivided_budget(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a list of eight-byte elements from an even budget that is not a multiple is rejected.

    Given
    -----
    - a list type holding up to four eight-byte elements.
    - twelve input bytes, an even count holding one element and half of a second.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the budget does not divide by the element width, not that it is odd.
    """
    ssz_test(
        case_id="uint64_list4/invalid/budget_undivided",
        type_name="BudgetUint64List4",
        value=BudgetUint64List4(),
        raw_bytes="0x0100000000000000" + "02000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE_UNDIVIDED,
            exact_message="a budget of 12 does not divide by an element width of 8",
        ),
    )


@pytest.mark.tags("limit")
def test_list_holds_one_whole_element_past_its_limit(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a list from a budget holding more whole elements than its limit allows is rejected.

    Given
    -----
    - a list type holding up to three four-byte elements.
    - sixteen input bytes, which divide into four whole elements.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the recovered element count exceeds the limit.
    """
    ssz_test(
        case_id="uint32_list3/invalid/over_limit",
        type_name="BudgetUint32List3",
        value=BudgetUint32List3(),
        raw_bytes="0x01000000020000000300000004000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.LIMIT,
            exact_message="BudgetUint32List3 holds at most 3 elements, got 4",
        ),
    )


def test_vector_given_fewer_bytes_than_its_length(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a fixed-size vector from fewer bytes than its length requires is rejected.

    Given
    -----
    - a vector type holding exactly four two-byte elements, spanning eight bytes.
    - six input bytes, one whole element short.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the budget is not the width the vector spans.
    """
    ssz_test(
        case_id="uint16_vector4/invalid/budget_too_small",
        type_name="BudgetUint16Vector4",
        value=BudgetUint16Vector4(),
        raw_bytes="0x010002000300",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            exact_message="BudgetUint16Vector4 spans 8 bytes, and the budget is 6",
        ),
    )


def test_vector_given_more_bytes_than_its_length(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a fixed-size vector from more bytes than its length requires is rejected.

    Given
    -----
    - a vector type holding exactly four two-byte elements, spanning eight bytes.
    - ten input bytes, one whole element too many.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the budget is not the width the vector spans.
    """
    ssz_test(
        case_id="uint16_vector4/invalid/budget_too_large",
        type_name="BudgetUint16Vector4",
        value=BudgetUint16Vector4(),
        raw_bytes="0x01000200030004000500",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            exact_message="BudgetUint16Vector4 spans 8 bytes, and the budget is 10",
        ),
    )


@pytest.mark.tags("limit")
def test_byte_list_given_one_byte_past_its_limit(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a byte list from one byte more than its limit allows is rejected.

    Given
    -----
    - a byte list type capped at thirty-three bytes, one past a Merkle chunk.
    - thirty-four input bytes.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the byte count exceeds the limit.
    """
    ssz_test(
        case_id="byte_list33/invalid/over_limit",
        type_name="BudgetByteList33",
        value=BudgetByteList33(),
        raw_bytes="0x" + "".join(f"{byte:02x}" for byte in range(34)),
        expected_rejection=ExpectedRejection(
            reason=ValueFault.LIMIT,
            exact_message="BudgetByteList33 holds at most 33 bytes, got 34",
        ),
    )


def test_fixed_size_container_given_more_bytes_than_its_width(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a fixed-size container from more bytes than its own width is rejected.

    Given
    -----
    - a container type spanning six bytes, a four-byte field ahead of a two-byte one.
    - eight input bytes, two past that width.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the container reads both fields, then measures the budget against what it read.
    - the reason is that the budget is not the width the container spans.
    """
    ssz_test(
        case_id="fixed_pair/invalid/budget_too_large",
        type_name="BudgetFixedPair",
        value=BudgetFixedPair(first=Uint32(0), second=Uint16(0)),
        raw_bytes="0x010000000200ffff",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            exact_message="BudgetFixedPair spans 6 bytes, and the budget is 8",
        ),
    )


def test_fixed_size_container_given_fewer_bytes_than_its_width(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a fixed-size container from fewer bytes than its own width is rejected.

    Given
    -----
    - a container type spanning six bytes, a four-byte field ahead of a two-byte one.
    - five input bytes, one short of that width.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the container reads its fields before it can measure the budget, so the second field
      runs out first and the refusal names it rather than the container.
    - the reason is that the stream ended inside a field, not that the budget is wrong.
    """
    ssz_test(
        case_id="fixed_pair/invalid/truncated_field",
        type_name="BudgetFixedPair",
        value=BudgetFixedPair(first=Uint32(0), second=Uint16(0)),
        raw_bytes="0x0100000002",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.TRUNCATED,
            exact_message="second: Uint16 needs 2 bytes, the input holds 1",
        ),
    )

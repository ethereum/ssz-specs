"""SSZ conformance vectors for basic and fixed-width inputs a decoder has to refuse."""

from typing import ClassVar

import pytest

from ssz import Boolean, ByteList, ByteVector, Uint16, Uint64, Vector
from ssz_testing import ExpectedRejection, SSZTestFiller, ValueFault

pytestmark = pytest.mark.tags("boundary")


class Bytes4(ByteVector):
    LENGTH: ClassVar[int] = 4


class ByteList4(ByteList):
    """Byte list capped at four bytes, small enough to hand it one byte past the cap."""

    LIMIT: ClassVar[int] = 4


class BooleanVector3(Vector[Boolean]):
    """Three booleans, so a refusal of the middle one carries the element path."""

    LENGTH: ClassVar[int] = 3


def test_uint16_one_byte_short(ssz_test: SSZTestFiller) -> None:
    """
    A two-byte unsigned integer given one byte is rejected.

    Given
    -----
    - the type Uint16, which spans two bytes.
    - the input byte 0x01, one byte short of that.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the type's width and the budget disagree.
    """
    ssz_test(
        case_id="uint16/invalid/one_byte_short",
        type_name="Uint16",
        value=Uint16(0),
        raw_bytes="0x01",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            message_substring="spans 2 bytes, and the budget is 1",
        ),
    )


def test_uint16_one_byte_long(ssz_test: SSZTestFiller) -> None:
    """
    A two-byte unsigned integer given three bytes is rejected.

    Given
    -----
    - the type Uint16, which spans two bytes.
    - the input bytes 0x010203, one byte past that.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the type's width and the budget disagree.
    - no prefix of the input is read as a value and the rest discarded.
    """
    ssz_test(
        case_id="uint16/invalid/one_byte_long",
        type_name="Uint16",
        value=Uint16(0),
        raw_bytes="0x010203",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            message_substring="spans 2 bytes, and the budget is 3",
        ),
    )


def test_uint64_one_byte_short(ssz_test: SSZTestFiller) -> None:
    """
    An eight-byte unsigned integer given seven bytes is rejected.

    Given
    -----
    - the type Uint64, which spans eight bytes.
    - the input bytes 0x01020304050607, one byte short of that.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the type's width and the budget disagree.
    - the missing byte is not read as a zero.
    """
    ssz_test(
        case_id="uint64/invalid/one_byte_short",
        type_name="Uint64",
        value=Uint64(0),
        raw_bytes="0x01020304050607",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            message_substring="spans 8 bytes, and the budget is 7",
        ),
    )


def test_uint64_one_byte_long(ssz_test: SSZTestFiller) -> None:
    """
    An eight-byte unsigned integer given nine bytes is rejected.

    Given
    -----
    - the type Uint64, which spans eight bytes.
    - the input bytes 0x010203040506070809, one byte past that.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the type's width and the budget disagree.
    - the trailing byte is not discarded.
    """
    ssz_test(
        case_id="uint64/invalid/one_byte_long",
        type_name="Uint64",
        value=Uint64(0),
        raw_bytes="0x010203040506070809",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            message_substring="spans 8 bytes, and the budget is 9",
        ),
    )


def test_boolean_byte_two(ssz_test: SSZTestFiller) -> None:
    """
    A boolean encoded as 0x02 is rejected.

    Given
    -----
    - the type Boolean, whose only encodings are 0x00 and 0x01.
    - the input byte 0x02, which a decoder reading the byte for truth accepts as true.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the byte is neither zero nor one.
    """
    ssz_test(
        case_id="boolean/invalid/byte_two",
        type_name="Boolean",
        value=Boolean(False),
        raw_bytes="0x02",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.NOT_A_BIT,
            message_substring="a boolean is 0 or 1, got 0x02",
        ),
    )


def test_boolean_high_bit_only(ssz_test: SSZTestFiller) -> None:
    """
    A boolean encoded as 0x80 is rejected.

    Given
    -----
    - the type Boolean, whose only encodings are 0x00 and 0x01.
    - the input byte 0x80, which a decoder masking the low bit reads as false.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the byte is neither zero nor one.
    """
    ssz_test(
        case_id="boolean/invalid/high_bit_only",
        type_name="Boolean",
        value=Boolean(False),
        raw_bytes="0x80",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.NOT_A_BIT,
            message_substring="a boolean is 0 or 1, got 0x80",
        ),
    )


def test_boolean_all_bits_set(ssz_test: SSZTestFiller) -> None:
    """
    A boolean encoded as 0xff is rejected.

    Given
    -----
    - the type Boolean, whose only encodings are 0x00 and 0x01.
    - the input byte 0xff, which a decoder masking the low bit reads as true.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the byte is neither zero nor one.
    """
    ssz_test(
        case_id="boolean/invalid/all_bits_set",
        type_name="Boolean",
        value=Boolean(False),
        raw_bytes="0xff",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.NOT_A_BIT,
            message_substring="a boolean is 0 or 1, got 0xff",
        ),
    )


@pytest.mark.tags("empty")
def test_boolean_empty_input(ssz_test: SSZTestFiller) -> None:
    """
    A boolean given no bytes at all is rejected.

    Given
    -----
    - the type Boolean, which spans one byte.
    - an empty input.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the type's width and the budget disagree.
    - the absent byte is not read as false.
    """
    ssz_test(
        case_id="boolean/invalid/empty_input",
        type_name="Boolean",
        value=Boolean(False),
        raw_bytes="0x",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            message_substring="spans 1 bytes, and the budget is 0",
        ),
    )


def test_boolean_one_byte_long(ssz_test: SSZTestFiller) -> None:
    """
    A boolean given two bytes is rejected.

    Given
    -----
    - the type Boolean, which spans one byte.
    - the input bytes 0x0001, whose first byte alone would decode as false.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the type's width and the budget disagree.
    - the second byte is not discarded.
    """
    ssz_test(
        case_id="boolean/invalid/one_byte_long",
        type_name="Boolean",
        value=Boolean(False),
        raw_bytes="0x0001",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            message_substring="spans 1 bytes, and the budget is 2",
        ),
    )


def test_byte_vector_one_byte_short(ssz_test: SSZTestFiller) -> None:
    """
    A four-byte byte vector given three bytes is rejected.

    Given
    -----
    - a byte vector of length four.
    - the input bytes 0xdeadbe, one byte short of that.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the type's width and the budget disagree.
    - the input is not padded out to the declared length.
    """
    ssz_test(
        case_id="bytes4/invalid/one_byte_short",
        type_name="Bytes4",
        value=Bytes4(b"\x00\x00\x00\x00"),
        raw_bytes="0xdeadbe",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            message_substring="spans 4 bytes, and the budget is 3",
        ),
    )


def test_byte_vector_one_byte_long(ssz_test: SSZTestFiller) -> None:
    """
    A four-byte byte vector given five bytes is rejected.

    Given
    -----
    - a byte vector of length four.
    - the input bytes 0xdeadbeef00, one byte past that.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the type's width and the budget disagree.
    - the input is not truncated to the declared length.
    """
    ssz_test(
        case_id="bytes4/invalid/one_byte_long",
        type_name="Bytes4",
        value=Bytes4(b"\x00\x00\x00\x00"),
        raw_bytes="0xdeadbeef00",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            message_substring="spans 4 bytes, and the budget is 5",
        ),
    )


@pytest.mark.tags("limit")
def test_byte_list_over_limit(ssz_test: SSZTestFiller) -> None:
    """
    A byte list given one byte past its limit is rejected.

    Given
    -----
    - a byte list capped at four bytes.
    - the input bytes 0x0102030405, which hold five.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the byte count exceeds the limit.
    """
    ssz_test(
        case_id="bytelist4/invalid/over_limit",
        type_name="ByteList4",
        value=ByteList4(data=b""),
        raw_bytes="0x0102030405",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.LIMIT,
            message_substring="holds at most 4 bytes, got 5",
        ),
    )


def test_boolean_element_of_vector(ssz_test: SSZTestFiller) -> None:
    """
    A vector holding a byte that is not a boolean is rejected at that element.

    Given
    -----
    - a vector of three booleans.
    - the input bytes 0x000200, whose middle byte is neither zero nor one.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the byte is neither zero nor one.
    - the refusal names the element it came from.
    """
    ssz_test(
        case_id="boolean_vector3/invalid/element_not_a_bit",
        type_name="BooleanVector3",
        value=BooleanVector3(data=[Boolean(False), Boolean(False), Boolean(False)]),
        raw_bytes="0x000200",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.NOT_A_BIT,
            message_substring="[1]: a boolean is 0 or 1, got 0x02",
        ),
    )

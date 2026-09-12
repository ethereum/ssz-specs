"""SSZ conformance test vectors for the JSON documents that render no value of their type."""

import pytest

from ssz import (
    BitList,
    ByteVector,
    CompatibleUnion,
    Container,
    ProgressiveContainer,
    Uint8,
    Uint16,
)
from ssz_testing import JsonFault, JsonMappingFiller

pytestmark = pytest.mark.tags("json")

UNION_REFUSES_EVERY_DOCUMENT = "Input should be an instance of SSZType"
"""The refusal a union draws here, its option field being one no JSON value satisfies."""


class RefusalBitList20(BitList):
    """Up to twenty bits, closed by a delimiter bit."""

    LIMIT = 20


class RefusalByteVector4(ByteVector):
    """Four bytes of opaque data."""

    LENGTH = 4


class RefusalPoint(Container):
    """Two numbers under names, which the mapping writes as an object of two entries."""

    x: Uint16
    y: Uint16


class RefusalCorner(ProgressiveContainer):
    """Two numbers holding layout positions 0 and 2, per EIP-7495."""

    ACTIVE_FIELDS = (1, 0, 1)

    x: Uint16
    y: Uint16


class RefusalEdge(ProgressiveContainer):
    """The compatible option, holding positions 1 and 2."""

    ACTIVE_FIELDS = (0, 1, 1)

    length: Uint16
    y: Uint16


class RefusalShape(CompatibleUnion):
    """A union of two shapes, whose declared selectors are 1 and 2."""

    OPTIONS = {1: RefusalCorner, 2: RefusalEdge}


def test_a_bit_list_closing_without_a_delimiter(ssz_json_test: JsonMappingFiller) -> None:
    """
    A bit list whose hex sets no delimiter bit is no rendering of a value.

    Given
    -----
    - the document "0x00", read against a bit list admitting up to twenty bits.

    When
    ----
    - a parser reads it through the JSON mapping.

    Then
    ----
    - the document is refused, the hex being the encoding an SSZ stream would carry.
    - that encoding recovers a bit count from the highest set bit, and this one sets none.
    """
    ssz_json_test(
        case_id="json_refusal/bit_list/invalid/no_delimiter",
        type_name="RefusalBitList20",
        ssz_type=RefusalBitList20,
        document="0x00",
        rejection_reason=JsonFault.BITFIELD_DELIMITER,
        message_substring="the encoding sets no delimiter bit",
    )


def test_a_bit_list_padded_past_its_delimiter(ssz_json_test: JsonMappingFiller) -> None:
    """
    A bit list whose hex carries zero bytes past its delimiter is no rendering of a value.

    Given
    -----
    - the document "0x0d00", which is the three bits 1, 0, 1 under a second, empty byte.

    When
    ----
    - a parser reads it through the JSON mapping.

    Then
    ----
    - the document is refused, "0x0d" already spelling those three bits.
    - accepting both would give one value two renderings.
    """
    ssz_json_test(
        case_id="json_refusal/bit_list/invalid/trailing_zeros",
        type_name="RefusalBitList20",
        ssz_type=RefusalBitList20,
        document="0x0d00",
        rejection_reason=JsonFault.BITFIELD_TRAILING_ZEROS,
        message_substring="zero bytes past the delimiter",
    )


def test_a_byte_vector_of_the_wrong_length(ssz_json_test: JsonMappingFiller) -> None:
    """
    A hex byte string of a length the type does not have is no rendering of a value.

    Given
    -----
    - the document "0x0102", read against a fixed array of four bytes.

    When
    ----
    - a parser reads it through the JSON mapping.

    Then
    ----
    - the document is refused, a fixed array spanning exactly the bytes it declares.
    """
    ssz_json_test(
        case_id="json_refusal/byte_vector/invalid/wrong_length",
        type_name="RefusalByteVector4",
        ssz_type=RefusalByteVector4,
        document="0x0102",
        rejection_reason=JsonFault.HEX_LENGTH,
        message_substring="RefusalByteVector4 holds exactly 4 bytes, got 2",
    )


def test_a_hex_byte_string_holding_a_non_hex_digit(ssz_json_test: JsonMappingFiller) -> None:
    """
    A hex byte string holding a character outside 0-9a-f is no rendering of a value.

    Given
    -----
    - the document "0x0102030z", four bytes wide but for the letter z in its last position.

    When
    ----
    - a parser reads it through the JSON mapping.

    Then
    ----
    - the document is refused, the string standing for the bytes an SSZ stream would carry.
    """
    ssz_json_test(
        case_id="json_refusal/byte_vector/invalid/not_hex_digits",
        type_name="RefusalByteVector4",
        ssz_type=RefusalByteVector4,
        document="0x0102030z",
        rejection_reason=JsonFault.HEX_DIGITS,
        message_substring="reads a string as hex digits, and this one holds something else",
    )


def test_a_uint_above_the_width_it_declares(ssz_json_test: JsonMappingFiller) -> None:
    """
    Decimal digits standing for a number wider than the uint are no rendering of a value.

    Given
    -----
    - the document "256", read against a one-byte uint, which holds 0 through 255.

    When
    ----
    - a parser reads it through the JSON mapping.

    Then
    ----
    - the document is refused, the string spelling a number the type cannot hold.
    """
    ssz_json_test(
        case_id="json_refusal/uint8/invalid/above_the_width",
        type_name="Uint8",
        ssz_type=Uint8,
        document="256",
        rejection_reason=JsonFault.UINT_RANGE,
        message_substring="Input should be less than 256",
    )


def test_a_container_leaving_out_a_declared_field(ssz_json_test: JsonMappingFiller) -> None:
    """
    An object naming no value for a declared field is no rendering of a struct.

    Given
    -----
    - the document {"x": "1"}, read against a struct declaring both x and y.

    When
    ----
    - a parser reads it through the JSON mapping.

    Then
    ----
    - the document is refused, every field of the schema being present with a value.
    - a zero standing in for the absent field would read one document as two values.
    """
    ssz_json_test(
        case_id="json_refusal/container/invalid/missing_field",
        type_name="RefusalPoint",
        ssz_type=RefusalPoint,
        document={"x": "1"},
        rejection_reason=JsonFault.MISSING_FIELD,
        message_substring="the document leaves y of RefusalPoint without a value",
    )


def test_a_union_naming_an_undeclared_selector(ssz_json_test: JsonMappingFiller) -> None:
    """
    An object whose selector names no option is no rendering of a union value.

    Given
    -----
    - the document carrying selector 3, read against a union declaring 1 and 2.

    When
    ----
    - a parser reads it through the JSON mapping.

    Then
    ----
    - the document is refused, a reader taking the tree shape from the selector.
    - this implementation reads no union document at all, so the selector is never reached.
    """
    ssz_json_test(
        case_id="json_refusal/compatible_union/invalid/undeclared_selector",
        type_name="RefusalShape",
        ssz_type=RefusalShape,
        document={"selector": "3", "data": {"x": "1", "y": "2"}},
        rejection_reason=JsonFault.UNDECLARED_SELECTOR,
        message_substring=UNION_REFUSES_EVERY_DOCUMENT,
    )

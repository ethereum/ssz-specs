"""SSZ conformance test vectors for the one shape the JSON mapping gives a struct: an object."""

import pytest

from ssz import ByteVector, Container, ProgressiveContainer, Uint16
from ssz_testing import JsonFault, JsonMappingFiller

pytestmark = pytest.mark.tags("json")

NOT_AN_OBJECT = "Input should be an object"
"""Substring every refusal below carries, the mapping's verdict as this parser words it."""


class StructShapeBytes4(ByteVector):
    """Four bytes of opaque data, the field whose own rendering is a hex string."""

    LENGTH = 4


class StructShapePoint(Container):
    """A number and four bytes, spanning six bytes on the wire."""

    a: Uint16
    b: StructShapeBytes4


class StructShapeCorner(ProgressiveContainer):
    """The same two fields at layout positions 0 and 2, per EIP-7495."""

    ACTIVE_FIELDS = (1, 0, 1)

    a: Uint16
    b: StructShapeBytes4


def test_a_container_written_as_its_own_encoding(ssz_json_test: JsonMappingFiller) -> None:
    """
    A struct's SSZ encoding as a hex string is no rendering of that struct.

    Given
    -----
    - the document "0x0100deadbeef", which is what the two fields 1 and 0xdeadbeef encode to.

    When
    ----
    - a parser reads it through the JSON mapping.

    Then
    ----
    - the document is refused, the mapping writing a struct as an object.
    - a hex string is a byte array's rendering, not a struct's.
    """
    ssz_json_test(
        case_id="json_struct/container/invalid/hex_string",
        type_name="StructShapePoint",
        ssz_type=StructShapePoint,
        document="0x0100deadbeef",
        rejection_reason=JsonFault.STRUCT_NOT_AN_OBJECT,
        message_substring=NOT_AN_OBJECT,
    )


def test_a_progressive_container_written_as_its_own_encoding(
    ssz_json_test: JsonMappingFiller,
) -> None:
    """
    A progressive struct is written as an object too, its layout changing nothing here.

    Given
    -----
    - the document "0x0100deadbeef", the same six bytes the flat struct of these fields encodes to.

    When
    ----
    - a parser reads it through the JSON mapping.

    Then
    ----
    - the document is refused, on the same grounds the flat struct refuses it.
    """
    ssz_json_test(
        case_id="json_struct/progressive_container/invalid/hex_string",
        type_name="StructShapeCorner",
        ssz_type=StructShapeCorner,
        document="0x0100deadbeef",
        rejection_reason=JsonFault.STRUCT_NOT_AN_OBJECT,
        message_substring=NOT_AN_OBJECT,
    )

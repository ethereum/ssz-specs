"""SSZ conformance test vectors for the elements of a sequence, written and read back."""

import pytest

from ssz import Boolean, ByteVector, Container, List, ProgressiveList, Uint16, Vector
from ssz_testing import JsonMappingFiller

pytestmark = pytest.mark.tags("json")


class JsonSequenceBooleanList8(List[Boolean]):
    """Up to eight bits held one element each, against the bit list that packs them into bytes."""

    LIMIT = 8


class JsonSequenceBooleanVector4(Vector[Boolean]):
    """Exactly four bits held one element each."""

    LENGTH = 4


class JsonSequenceBooleanProgressiveList(ProgressiveList[Boolean]):
    """Any number of bits held one element each, per EIP-7916."""


class JsonSequenceBytes4(ByteVector):
    """Four bytes of opaque data, the element whose own rendering is a hex string."""

    LENGTH = 4


class JsonSequenceBytes4List4(List[JsonSequenceBytes4]):
    """Up to four of those byte arrays."""

    LIMIT = 4


class JsonSequencePoint(Container):
    """Two numbers under names, the element whose own rendering is an object."""

    x: Uint16
    y: Uint16


class JsonSequencePointList4(List[JsonSequencePoint]):
    """Up to four of those structs."""

    LIMIT = 4


def test_a_list_of_booleans(ssz_json_test: JsonMappingFiller) -> None:
    """
    A bounded sequence of booleans is an array of bare true and false literals.

    Given
    -----
    - the eight bits 1, 0, 1, 1, 0, 0, 0, 1 in a list admitting up to eight.

    When
    ----
    - the value is written through the JSON mapping, and the document read back.

    Then
    ----
    - the document is the array [true, false, true, true, false, false, false, true].
    - the elements are bare literals, where a bit list of the same bits is one hex string.
    - the document reads back as the value it was written from.
    """
    ssz_json_test(
        case_id="json_sequence/boolean_list",
        type_name="JsonSequenceBooleanList8",
        ssz_type=JsonSequenceBooleanList8,
        value=JsonSequenceBooleanList8(
            data=[Boolean(bit) for bit in (1, 0, 1, 1, 0, 0, 0, 1)],
        ),
        document=[True, False, True, True, False, False, False, True],
    )


def test_a_vector_of_booleans(ssz_json_test: JsonMappingFiller) -> None:
    """
    A fixed sequence of booleans is an array of bare literals too, its length showing nowhere.

    Given
    -----
    - the four bits 1, 0, 0, 1 in a vector of exactly four.

    When
    ----
    - the value is written through the JSON mapping, and the document read back.

    Then
    ----
    - the document is the array [true, false, false, true].
    - the document reads back as the value it was written from.
    """
    ssz_json_test(
        case_id="json_sequence/boolean_vector",
        type_name="JsonSequenceBooleanVector4",
        ssz_type=JsonSequenceBooleanVector4,
        value=JsonSequenceBooleanVector4(data=[Boolean(bit) for bit in (1, 0, 0, 1)]),
        document=[True, False, False, True],
    )


def test_a_progressive_list_of_booleans(ssz_json_test: JsonMappingFiller) -> None:
    """
    An unbounded sequence of booleans is written the same way, per EIP-7916.

    Given
    -----
    - the three bits 0, 1, 1 in a progressive list.

    When
    ----
    - the value is written through the JSON mapping, and the document read back.

    Then
    ----
    - the document is the array [false, true, true].
    - the document reads back as the value it was written from.
    """
    ssz_json_test(
        case_id="json_sequence/boolean_progressive_list",
        type_name="JsonSequenceBooleanProgressiveList",
        ssz_type=JsonSequenceBooleanProgressiveList,
        value=JsonSequenceBooleanProgressiveList(data=[Boolean(bit) for bit in (0, 1, 1)]),
        document=[False, True, True],
    )


def test_a_list_of_byte_vectors(ssz_json_test: JsonMappingFiller) -> None:
    """
    Each fixed byte array element keeps its own hex string, the array joining none of them.

    Given
    -----
    - two four-byte arrays in a list admitting up to four.

    When
    ----
    - the value is written through the JSON mapping, and the document read back.

    Then
    ----
    - the document is ["0xdeadbeef", "0x00112233"], against the one hex string a byte list writes.
    - the document reads back as the value it was written from.
    """
    ssz_json_test(
        case_id="json_sequence/byte_vector_list",
        type_name="JsonSequenceBytes4List4",
        ssz_type=JsonSequenceBytes4List4,
        value=JsonSequenceBytes4List4(
            data=[JsonSequenceBytes4(b"\xde\xad\xbe\xef"), JsonSequenceBytes4(b"\x00\x11\x22\x33")],
        ),
        document=["0xdeadbeef", "0x00112233"],
    )


def test_a_list_of_containers(ssz_json_test: JsonMappingFiller) -> None:
    """
    Each struct element keeps its own object, and reads back from it.

    Given
    -----
    - two structs of two numbers each, in a list admitting up to four.

    When
    ----
    - the value is written through the JSON mapping, and the document read back.

    Then
    ----
    - the document is [{"x": "1", "y": "2"}, {"x": "3", "y": "4"}].
    - the document reads back as the value it was written from.
    """
    ssz_json_test(
        case_id="json_sequence/container_list",
        type_name="JsonSequencePointList4",
        ssz_type=JsonSequencePointList4,
        value=JsonSequencePointList4(
            data=[
                JsonSequencePoint(x=Uint16(1), y=Uint16(2)),
                JsonSequencePoint(x=Uint16(3), y=Uint16(4)),
            ],
        ),
        document=[{"x": "1", "y": "2"}, {"x": "3", "y": "4"}],
    )

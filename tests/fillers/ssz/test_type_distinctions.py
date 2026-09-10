"""SSZ conformance test vectors for the types the spec keeps apart, and for every default value."""

from typing import ClassVar

import pytest

from ssz import (
    BitList,
    BitVector,
    Boolean,
    ByteList,
    ByteVector,
    Container,
    List,
    ProgressiveList,
    Uint8,
    Uint64,
    Vector,
)
from ssz_testing import SSZTestFiller


class Bytes4(ByteVector):
    """Four-byte fixed byte array, the alias half of the ByteVector against Vector pair."""

    LENGTH: ClassVar[int] = 4


class Bytes32(ByteVector):
    """Thirty-two-byte fixed byte array, exactly one Merkle chunk."""

    LENGTH: ClassVar[int] = 32


class SampleBooleanVector8(Vector[Boolean]):
    """Eight booleans, one byte each, against the bitvector that packs the same bits."""

    LENGTH: ClassVar[int] = 8


class SampleBitVector8(BitVector):
    """Eight bits packed into one byte, against the boolean vector holding the same bits."""

    LENGTH: ClassVar[int] = 8


class SampleBitVector12(BitVector):
    """Twelve bits, whose two encoded bytes leave four padding bits clear."""

    LENGTH: ClassVar[int] = 12


class SampleBooleanList8(List[Boolean]):
    """Up to eight booleans, one byte each, against the bitlist holding the same bits."""

    LIMIT: ClassVar[int] = 8
    ELEMENT_TYPE = Boolean


class SampleBitList8(BitList):
    """Up to eight packed bits, against the boolean list holding the same bits."""

    LIMIT: ClassVar[int] = 8


class SampleUint8Vector4(Vector[Uint8]):
    """Four one-byte uints, the spelled-out form of the four-byte byte vector."""

    LENGTH: ClassVar[int] = 4


class SampleBytes32Vector2(Vector[Bytes32]):
    """Two composite elements, one Merkle leaf each, whose default is the element default twice."""

    LENGTH: ClassVar[int] = 2


class SampleUint64List8(List[Uint64]):
    """Up to eight eight-byte elements, a variable-size shape whose default is empty."""

    LIMIT: ClassVar[int] = 8
    ELEMENT_TYPE = Uint64


class SampleByteList32(ByteList):
    """Up to thirty-two bytes, a variable-size byte string whose default is empty."""

    LIMIT: ClassVar[int] = 32


class SampleUint64ProgressiveList(ProgressiveList[Uint64]):
    """Progressive list of eight-byte elements, with no capacity."""

    ELEMENT_TYPE = Uint64


class SampleMixedContainer(Container):
    """Container whose two fixed-size fields sit either side of a variable-size one."""

    head: Uint64
    body: SampleUint64List8
    tail: Bytes4


DISTINCT_BITS = (True, False, True, True, False, False, False, True)
"""The eight logical bits both halves of a boolean-against-bit pair are filled with."""


@pytest.mark.tags("distinction")
def test_boolean_vector_against_bitvector(ssz_test: SSZTestFiller) -> None:
    """
    A vector of booleans spends a byte on every element, unlike the bitvector beside it.

    Given
    -----
    - eight booleans, the bits 1, 0, 1, 1, 0, 0, 0, 1, held in a Vector[Boolean, 8].

    When
    ----
    - the value is encoded, decoded, and rooted.

    Then
    ----
    - the encoding is eight bytes, one per element, rather than the bitvector's single byte.
    - the eight packed bytes fill one chunk, so the root is that chunk unhashed.
    - the root differs from the bitvector root over the same bits.
    """
    ssz_test(
        case_id="distinction/boolean_vector8/one_byte_per_element",
        type_name="SampleBooleanVector8",
        value=SampleBooleanVector8(data=[Boolean(bit) for bit in DISTINCT_BITS]),
    )


@pytest.mark.tags("distinction")
def test_bitvector_against_boolean_vector(ssz_test: SSZTestFiller) -> None:
    """
    A bitvector spends a bit on every element, unlike the boolean vector beside it.

    Given
    -----
    - eight bits, 1, 0, 1, 1, 0, 0, 0, 1, held in a BitVector[8].

    When
    ----
    - the value is encoded, decoded, and rooted.

    Then
    ----
    - the encoding is the single byte 0x8d, the bits packed least significant first.
    - that byte fills one chunk, so the root is that chunk unhashed.
    - the root differs from the boolean vector root over the same bits.
    """
    ssz_test(
        case_id="distinction/bitvector8/one_bit_per_element",
        type_name="SampleBitVector8",
        value=SampleBitVector8(data=[Boolean(bit) for bit in DISTINCT_BITS]),
    )


@pytest.mark.tags("distinction")
def test_boolean_list_against_bitlist(ssz_test: SSZTestFiller) -> None:
    """
    A list of booleans spends a byte on every element, and needs no delimiter.

    Given
    -----
    - eight booleans, the bits 1, 0, 1, 1, 0, 0, 0, 1, held in a List[Boolean, 8].

    When
    ----
    - the value is encoded, decoded, and rooted.

    Then
    ----
    - the encoding is eight bytes, one per element, with the length carried by the byte count.
    - the eight packed bytes fill one chunk, the limit of a list of eight booleans.
    - the length 8 is mixed into that chunk, and the root differs from the bitlist root.
    """
    ssz_test(
        case_id="distinction/boolean_list8/one_byte_per_element",
        type_name="SampleBooleanList8",
        value=SampleBooleanList8(data=[Boolean(bit) for bit in DISTINCT_BITS]),
    )


@pytest.mark.tags("distinction")
def test_bitlist_against_boolean_list(ssz_test: SSZTestFiller) -> None:
    """
    A bitlist spends a bit on every element, and carries its length in a delimiter bit.

    Given
    -----
    - eight bits, 1, 0, 1, 1, 0, 0, 0, 1, held in a BitList[8].

    When
    ----
    - the value is encoded, decoded, and rooted.

    Then
    ----
    - the encoding is 0x8d followed by 0x01, the delimiter spilling into a second byte.
    - the packed byte fills one chunk, the limit of a bitlist of eight bits.
    - the length 8 is mixed into that chunk, and the root differs from the boolean list root.
    """
    ssz_test(
        case_id="distinction/bitlist8/one_bit_per_element",
        type_name="SampleBitList8",
        value=SampleBitList8(data=[Boolean(bit) for bit in DISTINCT_BITS]),
    )


@pytest.mark.tags("distinction")
def test_uint8_vector_alias_of_byte_vector(ssz_test: SSZTestFiller) -> None:
    """
    A vector of one-byte uints is the spelled-out form of a byte vector, not a distinct type.

    Given
    -----
    - the bytes 0xde, 0xad, 0xbe, 0xef held in a Vector[Uint8, 4].

    When
    ----
    - the value is encoded, decoded, and rooted.

    Then
    ----
    - the encoding is the four bytes themselves.
    - the four packed bytes fill one chunk, so the root is that chunk unhashed.
    - both encoding and root equal those of the byte vector beside it.
    """
    ssz_test(
        case_id="distinction/uint8_vector4/alias_of_byte_vector",
        type_name="SampleUint8Vector4",
        value=SampleUint8Vector4(data=[Uint8(0xDE), Uint8(0xAD), Uint8(0xBE), Uint8(0xEF)]),
    )


@pytest.mark.tags("distinction")
def test_byte_vector_alias_of_uint8_vector(ssz_test: SSZTestFiller) -> None:
    """
    A byte vector is the shorthand for a vector of one-byte uints, and shares its representation.

    Given
    -----
    - the bytes 0xde, 0xad, 0xbe, 0xef held in a ByteVector[4].

    When
    ----
    - the value is encoded, decoded, and rooted.

    Then
    ----
    - the encoding is the four bytes themselves.
    - the four bytes fill one chunk, so the root is that chunk unhashed.
    - both encoding and root equal those of the uint8 vector beside it.
    """
    ssz_test(
        case_id="distinction/bytes4/alias_of_uint8_vector",
        type_name="Bytes4",
        value=Bytes4(bytes.fromhex("deadbeef")),
    )


@pytest.mark.tags("default")
def test_default_uint(ssz_test: SSZTestFiller) -> None:
    """
    The default of an unsigned integer is zero.

    Given
    -----
    - the default value an eight-byte uint hands out.

    When
    ----
    - the value is encoded, decoded, and rooted.

    Then
    ----
    - the encoding is eight zero bytes.
    - the eight bytes fill one chunk, so the root is that chunk unhashed.
    """
    ssz_test(case_id="default/uint64", type_name="Uint64", value=Uint64.default())


@pytest.mark.tags("default")
def test_default_boolean(ssz_test: SSZTestFiller) -> None:
    """
    The default of a boolean is false.

    Given
    -----
    - the default value a boolean hands out.

    When
    ----
    - the value is encoded, decoded, and rooted.

    Then
    ----
    - the encoding is the byte 0x00.
    - the single byte fills one chunk, so the root is the zero chunk.
    """
    ssz_test(case_id="default/boolean", type_name="Boolean", value=Boolean.default())


@pytest.mark.tags("default")
def test_default_fixed_byte_array(ssz_test: SSZTestFiller) -> None:
    """
    The default of a fixed byte array is every byte zero.

    Given
    -----
    - the default value a thirty-two-byte byte vector hands out.

    When
    ----
    - the value is encoded, decoded, and rooted.

    Then
    ----
    - the encoding is thirty-two zero bytes.
    - those bytes are exactly one chunk, so the root is the zero chunk.
    """
    ssz_test(case_id="default/bytes32", type_name="Bytes32", value=Bytes32.default())


@pytest.mark.tags("default")
def test_default_bitvector(ssz_test: SSZTestFiller) -> None:
    """
    The default of a bitvector is every bit clear.

    Given
    -----
    - the default value a twelve-bit bitvector hands out.

    When
    ----
    - the value is encoded, decoded, and rooted.

    Then
    ----
    - the encoding is two zero bytes, the four padding bits clear along with the twelve.
    - those bytes fill one chunk, so the root is the zero chunk.
    """
    ssz_test(
        case_id="default/bitvector12",
        type_name="SampleBitVector12",
        value=SampleBitVector12.default(),
    )


@pytest.mark.tags("default")
def test_default_fixed_size_vector(ssz_test: SSZTestFiller) -> None:
    """
    The default of a vector is the element default, once per position.

    Given
    -----
    - the default value a vector of two thirty-two-byte elements hands out.

    When
    ----
    - the value is encoded, decoded, and rooted.

    Then
    ----
    - the encoding is sixty-four zero bytes, each element defaulted in place.
    - the two composite elements are two leaves, so the root hashes two zero chunks together.
    """
    ssz_test(
        case_id="default/bytes32_vector2",
        type_name="SampleBytes32Vector2",
        value=SampleBytes32Vector2.default(),
    )


@pytest.mark.tags("default")
def test_default_variable_size_list(ssz_test: SSZTestFiller) -> None:
    """
    The default of a list is empty, holding no element at all.

    Given
    -----
    - the default value a list of up to eight eight-byte elements hands out.

    When
    ----
    - the value is encoded, decoded, and rooted.

    Then
    ----
    - the encoding is empty.
    - no leaf holds an element, and the limit of two chunks pads to two, giving the zero subtree.
    - the length 0 is mixed into that subtree root.
    """
    ssz_test(
        case_id="default/uint64_list8",
        type_name="SampleUint64List8",
        value=SampleUint64List8.default(),
    )


@pytest.mark.tags("default")
def test_default_byte_list(ssz_test: SSZTestFiller) -> None:
    """
    The default of a byte list is empty, holding no byte at all.

    Given
    -----
    - the default value a byte list of up to thirty-two bytes hands out.

    When
    ----
    - the value is encoded, decoded, and rooted.

    Then
    ----
    - the encoding is empty.
    - no leaf holds a byte, and the limit of one chunk gives the zero chunk.
    - the length 0 is mixed into that chunk.
    """
    ssz_test(
        case_id="default/bytelist32",
        type_name="SampleByteList32",
        value=SampleByteList32.default(),
    )


@pytest.mark.tags("default")
def test_default_container(ssz_test: SSZTestFiller) -> None:
    """
    The default of a container is one field default per field, variable-size fields included.

    Given
    -----
    - the default value a container of a uint, a list and a byte vector hands out.

    When
    ----
    - the value is encoded, decoded, and rooted.

    Then
    ----
    - the encoding is the sixteen-byte fixed part alone, the list contributing only its offset.
    - that offset is 16, pointing one past the fixed part, where the empty list would begin.
    - the three fields are three leaves, padded to four, and the root hashes that tree.
    """
    ssz_test(
        case_id="default/mixed_container",
        type_name="SampleMixedContainer",
        value=SampleMixedContainer.default(),
    )


@pytest.mark.tags("default")
def test_default_progressive_list(ssz_test: SSZTestFiller) -> None:
    """
    The default of a progressive list is empty, the same as every other unbounded shape.

    Given
    -----
    - the default value a progressive list of eight-byte elements hands out.

    When
    ----
    - the value is encoded, decoded, and rooted.

    Then
    ----
    - the encoding is empty.
    - the spine holds no level, so the root is the zero terminator with the length 0 mixed in.
    """
    ssz_test(
        case_id="default/uint64_progressive_list",
        type_name="SampleUint64ProgressiveList",
        value=SampleUint64ProgressiveList.default(),
    )

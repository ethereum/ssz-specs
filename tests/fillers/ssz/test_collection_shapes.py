"""SSZ: how a vector's length and a list's limit shape the tree over its elements."""

from typing import ClassVar

import pytest

from ssz import BitVector, Boolean, ByteList, ByteVector, List, Uint8, Uint64, Uint256, Vector
from ssz_testing import SSZTestFiller


class ShapeUint8Vector31(Vector[Uint8]):
    """One byte shy of a chunk. The final byte of the single chunk is zero padding."""

    LENGTH: ClassVar[int] = 31


class ShapeUint8Vector32(Vector[Uint8]):
    """Exactly one chunk of bytes, so the root is the packed data itself."""

    LENGTH: ClassVar[int] = 32


class ShapeUint8Vector33(Vector[Uint8]):
    """One byte past a chunk. The spilled byte forces a second leaf."""

    LENGTH: ClassVar[int] = 33


class ShapeBytes32(ByteVector):
    """The declared alias of a 32-element uint8 vector, filled to pin the two as equivalent."""

    LENGTH: ClassVar[int] = 32


class ShapeUint64Vector12(Vector[Uint64]):
    """96 bytes of packing: three leaves under a tree padded to four."""

    LENGTH: ClassVar[int] = 12


class ShapeUint256Vector5(Vector[Uint256]):
    """One chunk per element: five leaves under a tree padded to eight."""

    LENGTH: ClassVar[int] = 5


class ShapeBooleanVector40(Vector[Boolean]):
    """Forty booleans at one byte each, which is 40 bytes and not the 5 of a bitvector."""

    LENGTH: ClassVar[int] = 40


class ShapeBitVector40(BitVector):
    """Forty bits at one bit each, held next to the boolean vector of the same length."""

    LENGTH: ClassVar[int] = 40


class ShapeUint64Vector6(Vector[Uint64]):
    """Two full chunks of packing, used as the composite element of the shapes below."""

    LENGTH: ClassVar[int] = 6


class ShapeNestedVector3(Vector[ShapeUint64Vector6]):
    """Three element roots, not packed bytes, under a tree padded to four."""

    LENGTH: ClassVar[int] = 3


class ShapeUint64List8(List[Uint64]):
    """Eight uint64 at most, a limit of exactly two chunks."""

    LIMIT: ClassVar[int] = 8
    ELEMENT_TYPE = Uint64


class ShapeUint64List12(List[Uint64]):
    """Twelve uint64 at most, a limit of three chunks that the tree pads to four."""

    LIMIT: ClassVar[int] = 12
    ELEMENT_TYPE = Uint64


class ShapeNestedList3(List[ShapeUint64Vector6]):
    """Three composite elements at most, a limit the tree pads to four."""

    LIMIT: ClassVar[int] = 3
    ELEMENT_TYPE = ShapeUint64Vector6


class ShapeByteList80(ByteList):
    """Eighty bytes at most, a limit of three chunks that the tree pads to four."""

    LIMIT: ClassVar[int] = 80


REPDIGITS = [Uint64(0x1111111111111111 * digit) for digit in range(1, 13)]
"""Twelve distinct non-zero uint64, every byte of each one set."""


NESTED_ELEMENTS = [
    ShapeUint64Vector6(data=[Uint64(0xAA00000000000000 + position) for position in group])
    for group in (range(1, 7), range(7, 13), range(13, 19))
]
"""Three composite elements, the eighteen uint64 across them all distinct and non-zero."""


@pytest.mark.tags("boundary")
def test_uint8_vector_one_byte_shy_of_a_chunk(ssz_test: SSZTestFiller) -> None:
    """
    A 31-element uint8 vector merkleizes to a stable root.

    Given
    -----
    - a uint8 vector of 31 ascending non-zero elements.
    - 31 bytes of data and one byte of zero padding inside a single chunk.

    When
    ----
    - the value is encoded, merkleized and then decoded.

    Then
    ----
    - the encoding is the 31 packed bytes.
    - the root is the single padded chunk.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="collection_shape/uint8_vector31/ascending",
        type_name="ShapeUint8Vector31",
        value=ShapeUint8Vector31(data=[Uint8(index + 1) for index in range(31)]),
    )


@pytest.mark.tags("boundary")
def test_uint8_vector_filling_one_chunk(ssz_test: SSZTestFiller) -> None:
    """
    A 32-element uint8 vector merkleizes to a stable root.

    Given
    -----
    - a uint8 vector of 32 ascending non-zero elements.
    - data that fills exactly one chunk with no padding.

    When
    ----
    - the value is encoded, merkleized and then decoded.

    Then
    ----
    - the encoding is the 32 packed bytes.
    - the root is those bytes unhashed.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="collection_shape/uint8_vector32/ascending",
        type_name="ShapeUint8Vector32",
        value=ShapeUint8Vector32(data=[Uint8(index + 1) for index in range(32)]),
    )


@pytest.mark.tags("boundary")
def test_uint8_vector_one_byte_past_a_chunk(ssz_test: SSZTestFiller) -> None:
    """
    A 33-element uint8 vector merkleizes to a stable root.

    Given
    -----
    - a uint8 vector of 33 ascending non-zero elements.
    - one byte that spills into a second, almost empty chunk.

    When
    ----
    - the value is encoded, merkleized and then decoded.

    Then
    ----
    - the encoding is the 33 packed bytes.
    - the root joins the full chunk with the chunk holding one byte.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="collection_shape/uint8_vector33/ascending",
        type_name="ShapeUint8Vector33",
        value=ShapeUint8Vector33(data=[Uint8(index + 1) for index in range(33)]),
    )


@pytest.mark.tags("boundary")
def test_byte_vector_matching_the_uint8_vector(ssz_test: SSZTestFiller) -> None:
    """
    A 32-byte vector merkleizes to the root of the uint8 vector holding the same bytes.

    Given
    -----
    - a 32-byte vector holding the ascending bytes 1 through 32.
    - a uint8 vector of length 32 filled with those same elements.

    When
    ----
    - the value is encoded, merkleized and then decoded.

    Then
    ----
    - the encoding equals the uint8 vector's encoding.
    - the root equals the uint8 vector's root, the two being aliases of one type.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="collection_shape/bytevector32/ascending",
        type_name="ShapeBytes32",
        value=ShapeBytes32(bytes(range(1, 33))),
    )


@pytest.mark.tags("boundary")
def test_uint64_vector_with_a_padded_chunk_count(ssz_test: SSZTestFiller) -> None:
    """
    A 12-element uint64 vector merkleizes to a stable root.

    Given
    -----
    - a uint64 vector of 12 distinct elements with every byte set.
    - 96 bytes of packing, three leaves under a tree padded to four.

    When
    ----
    - the value is encoded, merkleized and then decoded.

    Then
    ----
    - the encoding is the 96 packed bytes.
    - the root joins the three data leaves against one zero leaf.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="collection_shape/uint64_vector12/repdigits",
        type_name="ShapeUint64Vector12",
        value=ShapeUint64Vector12(data=REPDIGITS),
    )


@pytest.mark.tags("boundary")
def test_uint256_vector_of_chunk_wide_elements(ssz_test: SSZTestFiller) -> None:
    """
    A five-element uint256 vector merkleizes to a stable root.

    Given
    -----
    - a uint256 vector of five distinct elements just below the type's maximum.
    - one element per chunk, five leaves under a tree padded to eight.

    When
    ----
    - the value is encoded, merkleized and then decoded.

    Then
    ----
    - the encoding is the 160 packed bytes.
    - the root joins the five data leaves against three zero leaves.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="collection_shape/uint256_vector5/near_max",
        type_name="ShapeUint256Vector5",
        value=ShapeUint256Vector5(data=[Uint256(2**256 - offset) for offset in range(1, 6)]),
    )


def test_boolean_vector_is_a_byte_per_element(ssz_test: SSZTestFiller) -> None:
    """
    A 40-element boolean vector merkleizes to a stable root.

    Given
    -----
    - a boolean vector of 40 elements, every third one set.
    - one byte per element, so 40 bytes across two leaves.

    When
    ----
    - the value is encoded, merkleized and then decoded.

    Then
    ----
    - the encoding is 40 bytes of 0x00 and 0x01, not the 5 bytes a bitvector packs them into.
    - the root differs from the bitvector of the same length and the same bits.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="collection_shape/boolean_vector40/every_third",
        type_name="ShapeBooleanVector40",
        value=ShapeBooleanVector40(data=[Boolean(index % 3 == 0) for index in range(40)]),
    )


def test_bitvector_beside_the_boolean_vector(ssz_test: SSZTestFiller) -> None:
    """
    A 40-bit bitvector merkleizes to a stable root.

    Given
    -----
    - a bitvector of 40 bits, every third one set.
    - the same bits the boolean vector of that length holds.

    When
    ----
    - the value is encoded, merkleized and then decoded.

    Then
    ----
    - the encoding is 5 packed bytes in a single leaf.
    - the root differs from the boolean vector of the same length and the same bits.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="collection_shape/bitvector40/every_third",
        type_name="ShapeBitVector40",
        value=ShapeBitVector40(data=[Boolean(index % 3 == 0) for index in range(40)]),
    )


@pytest.mark.tags("multi-level")
def test_vector_of_composite_elements(ssz_test: SSZTestFiller) -> None:
    """
    A three-element vector of uint64 vectors merkleizes to a stable root.

    Given
    -----
    - a vector of three elements, each itself a uint64 vector of six distinct elements.
    - three element roots, not packed bytes, under a tree padded to four.

    When
    ----
    - the value is encoded, merkleized and then decoded.

    Then
    ----
    - the encoding is the 144 bytes of the three fixed-size elements, with no offset table.
    - the root joins the three element roots against one zero leaf.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="collection_shape/nested_uint64_vector3/at_full",
        type_name="ShapeNestedVector3",
        value=ShapeNestedVector3(data=NESTED_ELEMENTS),
    )


@pytest.mark.tags("limit")
def test_uint64_list_filled_to_its_limit(ssz_test: SSZTestFiller) -> None:
    """
    A uint64 list filled to its eight-element limit merkleizes to a stable root.

    Given
    -----
    - a uint64 list capped at eight elements, holding eight distinct ones.
    - 64 bytes of packing, two leaves under a tree of exactly two.

    When
    ----
    - the value is encoded, merkleized and then decoded.

    Then
    ----
    - the encoding is the 64 packed bytes.
    - the root mixes the element count eight into the two-leaf tree.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="collection_shape/uint64_list8/at_limit",
        type_name="ShapeUint64List8",
        value=ShapeUint64List8(data=REPDIGITS[:8]),
    )


@pytest.mark.tags("limit")
def test_uint64_list_one_element_short_of_its_limit(ssz_test: SSZTestFiller) -> None:
    """
    A uint64 list one element short of its limit merkleizes to a stable root.

    Given
    -----
    - a uint64 list capped at eight elements, holding the first seven of them.
    - 56 bytes of packing, still two leaves, with eight zero bytes inside the second.

    When
    ----
    - the value is encoded, merkleized and then decoded.

    Then
    ----
    - the encoding is the 56 packed bytes.
    - the root mixes the element count seven in, so it differs from the filled list's.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="collection_shape/uint64_list8/one_short",
        type_name="ShapeUint64List8",
        value=ShapeUint64List8(data=REPDIGITS[:7]),
    )


@pytest.mark.tags("boundary", "limit")
def test_uint64_list_whose_limit_pads_the_tree(ssz_test: SSZTestFiller) -> None:
    """
    A uint64 list whose limit is three chunks merkleizes to a stable root.

    Given
    -----
    - a uint64 list capped at twelve elements, filled to that limit.
    - 96 bytes of packing, three leaves under a tree padded to four.

    When
    ----
    - the value is encoded, merkleized and then decoded.

    Then
    ----
    - the encoding is the 96 packed bytes, the same as the uint64 vector of that length.
    - the root differs from that vector's, the list mixing its element count in.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="collection_shape/uint64_list12/at_limit",
        type_name="ShapeUint64List12",
        value=ShapeUint64List12(data=REPDIGITS),
    )


@pytest.mark.tags("limit", "multi-level")
def test_list_of_composite_elements_filled_to_its_limit(ssz_test: SSZTestFiller) -> None:
    """
    A list of uint64 vectors filled to its three-element limit merkleizes to a stable root.

    Given
    -----
    - a list capped at three elements, each itself a uint64 vector of six distinct elements.
    - three element roots under a tree padded to four.

    When
    ----
    - the value is encoded, merkleized and then decoded.

    Then
    ----
    - the encoding is the 144 bytes of the three fixed-size elements, with no offset table.
    - the root mixes the element count three into the padded four-leaf tree.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="collection_shape/nested_uint64_list3/at_limit",
        type_name="ShapeNestedList3",
        value=ShapeNestedList3(data=NESTED_ELEMENTS),
    )


@pytest.mark.tags("boundary", "limit")
def test_byte_list_filled_to_its_limit(ssz_test: SSZTestFiller) -> None:
    """
    A byte list filled to its eighty-byte limit merkleizes to a stable root.

    Given
    -----
    - a byte list capped at eighty bytes, holding the ascending bytes 1 through 80.
    - three leaves, the last holding sixteen bytes, under a tree padded to four.

    When
    ----
    - the value is encoded, merkleized and then decoded.

    Then
    ----
    - the encoding is the 80 bytes themselves.
    - the root joins the three data leaves against one zero leaf, with the length mixed in.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="collection_shape/bytelist80/at_limit",
        type_name="ShapeByteList80",
        value=ShapeByteList80(data=bytes(range(1, 81))),
    )

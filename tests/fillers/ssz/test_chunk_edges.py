"""SSZ: round-trip vectors for bitfields and byte arrays that span more than one chunk."""

from typing import ClassVar

import pytest

from ssz import (
    BITS_PER_CHUNK,
    BYTES_PER_CHUNK,
    BitList,
    BitVector,
    Boolean,
    ByteList,
    ByteVector,
)
from ssz_testing import SSZTestFiller

pytestmark = pytest.mark.tags("boundary")


def every_third_bit(count: int) -> list[Boolean]:
    """Bits with every third one set, a pattern whose period divides no chunk width."""
    return [Boolean(index % 3 == 0) for index in range(count)]


def counting_bytes(count: int) -> bytes:
    """Bytes counting up from 0xa0, each one non-zero, high bit set, and unlike its neighbours."""
    return bytes(range(0xA0, 0xA0 + count))


class ChunkEdgeBitList512(BitList):
    """BitList spanning exactly two chunks, a capacity that needs no zero padding."""

    LIMIT: ClassVar[int] = BITS_PER_CHUNK * 2


class ChunkEdgeBitList640(BitList):
    """BitList spanning two chunks and a half, so three leaves pad out to four."""

    LIMIT: ClassVar[int] = BITS_PER_CHUNK * 2 + BITS_PER_CHUNK // 2


class ChunkEdgeBitVector513(BitVector):
    """BitVector one bit past two chunks, so three leaves pad out to four."""

    LENGTH: ClassVar[int] = BITS_PER_CHUNK * 2 + 1


class ChunkEdgeBytes1(ByteVector):
    """Narrowest byte vector, one data byte against a chunk of padding."""

    LENGTH: ClassVar[int] = 1


class ChunkEdgeBytes31(ByteVector):
    """Byte vector one byte shy of a chunk."""

    LENGTH: ClassVar[int] = BYTES_PER_CHUNK - 1


class ChunkEdgeBytes33(ByteVector):
    """Byte vector one byte past a chunk, its second leaf all but one byte of padding."""

    LENGTH: ClassVar[int] = BYTES_PER_CHUNK + 1


class ChunkEdgeBytes96(ByteVector):
    """Byte vector of exactly three chunks, so its leaves pad out to four."""

    LENGTH: ClassVar[int] = BYTES_PER_CHUNK * 3


class ChunkEdgeByteList96(ByteList):
    """ByteList capped at three chunks, a capacity every case below pads out to four."""

    LIMIT: ClassVar[int] = BYTES_PER_CHUNK * 3


@pytest.mark.tags("limit", "multi-level")
def test_bitlist_filled_to_a_two_chunk_limit(ssz_test: SSZTestFiller) -> None:
    """
    A bitlist filled to a two-chunk limit merkleizes to a stable root.

    Given
    -----
    - a bitlist capped at two chunks of bits, filled to its limit.
    - a bit pattern that leaves the two data chunks unequal.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root matches the expected two-leaf layout with the bit count mixed in.
    """
    ssz_test(
        case_id="chunk_edge/bitlist512/at_limit",
        type_name="ChunkEdgeBitList512",
        value=ChunkEdgeBitList512(data=every_third_bit(ChunkEdgeBitList512.LIMIT)),
    )


@pytest.mark.tags("multi-level")
def test_bitlist_one_bit_short_of_a_two_chunk_limit(ssz_test: SSZTestFiller) -> None:
    """
    A bitlist one bit short of its limit merkleizes to a root of its own.

    Given
    -----
    - the same bitlist one bit short of its limit, that final bit being clear either way.
    - leaves therefore identical to the case filled to the limit.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - only the mixed-in bit count separates this root from the one at the limit.
    """
    ssz_test(
        case_id="chunk_edge/bitlist512/one_bit_short",
        type_name="ChunkEdgeBitList512",
        value=ChunkEdgeBitList512(data=every_third_bit(ChunkEdgeBitList512.LIMIT - 1)),
    )


@pytest.mark.tags("limit", "multi-level")
def test_bitlist_filled_to_a_limit_of_two_chunks_and_a_half(ssz_test: SSZTestFiller) -> None:
    """
    A bitlist whose limit is no whole number of chunks merkleizes to a stable root.

    Given
    -----
    - a bitlist capped at two chunks and a half of bits, filled to its limit.
    - three data leaves, the last of them half data and half padding.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root matches a four-leaf tree, the fourth leaf zero.
    """
    ssz_test(
        case_id="chunk_edge/bitlist640/at_limit",
        type_name="ChunkEdgeBitList640",
        value=ChunkEdgeBitList640(data=every_third_bit(ChunkEdgeBitList640.LIMIT)),
    )


@pytest.mark.tags("multi-level")
def test_bitlist_holding_one_bit_past_the_first_chunk(ssz_test: SSZTestFiller) -> None:
    """
    A bitlist holding one bit past its first chunk merkleizes to a stable root.

    Given
    -----
    - the same bitlist holding one bit more than a single chunk of bits.
    - two data leaves under a capacity of three.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root matches a four-leaf tree, the last two leaves zero.
    """
    ssz_test(
        case_id="chunk_edge/bitlist640/spills_one_bit",
        type_name="ChunkEdgeBitList640",
        value=ChunkEdgeBitList640(data=every_third_bit(BITS_PER_CHUNK + 1)),
    )


@pytest.mark.tags("multi-level")
def test_bitvector_one_bit_past_two_chunks(ssz_test: SSZTestFiller) -> None:
    """
    A bitvector one bit past two chunks merkleizes to a stable root.

    Given
    -----
    - a 513-bit vector, its final bit alone in the third leaf.
    - a bit pattern that leaves the three data chunks unequal.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root matches a four-leaf tree, the fourth leaf zero and no count mixed in.
    """
    ssz_test(
        case_id="chunk_edge/bitvector513/every_third_bit",
        type_name="ChunkEdgeBitVector513",
        value=ChunkEdgeBitVector513(data=every_third_bit(ChunkEdgeBitVector513.LENGTH)),
    )


def test_byte_vector_of_a_single_byte(ssz_test: SSZTestFiller) -> None:
    """
    A one-byte vector merkleizes to a stable root.

    Given
    -----
    - a byte vector holding one non-zero byte.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root is that byte followed by a chunk's worth of zero padding.
    """
    ssz_test(
        case_id="chunk_edge/bytes1/counting",
        type_name="ChunkEdgeBytes1",
        value=ChunkEdgeBytes1(counting_bytes(ChunkEdgeBytes1.LENGTH)),
    )


def test_byte_vector_one_byte_shy_of_a_chunk(ssz_test: SSZTestFiller) -> None:
    """
    A 31-byte vector merkleizes to a stable root.

    Given
    -----
    - a byte vector one byte shy of a chunk, holding no zero byte of its own.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root is the data followed by the single pad byte that completes the chunk.
    """
    ssz_test(
        case_id="chunk_edge/bytes31/counting",
        type_name="ChunkEdgeBytes31",
        value=ChunkEdgeBytes31(counting_bytes(ChunkEdgeBytes31.LENGTH)),
    )


@pytest.mark.tags("multi-level")
def test_byte_vector_one_byte_past_a_chunk(ssz_test: SSZTestFiller) -> None:
    """
    A 33-byte vector merkleizes to a stable root.

    Given
    -----
    - a byte vector one byte past a chunk.
    - a second leaf holding one data byte and 31 of padding.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root matches the expected two-leaf layout.
    """
    ssz_test(
        case_id="chunk_edge/bytes33/counting",
        type_name="ChunkEdgeBytes33",
        value=ChunkEdgeBytes33(counting_bytes(ChunkEdgeBytes33.LENGTH)),
    )


@pytest.mark.tags("multi-level")
def test_byte_vector_of_three_whole_chunks(ssz_test: SSZTestFiller) -> None:
    """
    A 96-byte vector merkleizes to a stable root.

    Given
    -----
    - a byte vector of exactly three chunks, none of them padded.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root matches a four-leaf tree, the fourth leaf zero and no count mixed in.
    """
    ssz_test(
        case_id="chunk_edge/bytes96/counting",
        type_name="ChunkEdgeBytes96",
        value=ChunkEdgeBytes96(counting_bytes(ChunkEdgeBytes96.LENGTH)),
    )


@pytest.mark.tags("limit", "multi-level")
def test_byte_list_filled_to_a_three_chunk_limit(ssz_test: SSZTestFiller) -> None:
    """
    A byte list filled to a three-chunk limit merkleizes to a stable root.

    Given
    -----
    - a byte list capped at three chunks, filled to its limit.
    - the same bytes the 96-byte vector above holds.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the mixed-in byte count separates this root from the vector's over the same leaves.
    """
    ssz_test(
        case_id="chunk_edge/bytelist96/at_limit",
        type_name="ChunkEdgeByteList96",
        value=ChunkEdgeByteList96(data=counting_bytes(ChunkEdgeByteList96.LIMIT)),
    )


@pytest.mark.tags("multi-level")
def test_byte_list_one_byte_short_of_its_limit(ssz_test: SSZTestFiller) -> None:
    """
    A byte list one byte short of its limit merkleizes to a stable root.

    Given
    -----
    - the same byte list one byte short of its limit.
    - three data leaves, the last of them a single pad byte short of full.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root matches a four-leaf tree, the fourth leaf zero.
    """
    ssz_test(
        case_id="chunk_edge/bytelist96/one_byte_short",
        type_name="ChunkEdgeByteList96",
        value=ChunkEdgeByteList96(data=counting_bytes(ChunkEdgeByteList96.LIMIT - 1)),
    )


@pytest.mark.tags("multi-level")
def test_byte_list_holding_exactly_one_chunk(ssz_test: SSZTestFiller) -> None:
    """
    A byte list holding exactly one chunk merkleizes to a stable root.

    Given
    -----
    - the same byte list holding one whole chunk of bytes.
    - a single data leaf under a capacity of three.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root matches a four-leaf tree, the last three leaves zero.
    """
    ssz_test(
        case_id="chunk_edge/bytelist96/one_chunk",
        type_name="ChunkEdgeByteList96",
        value=ChunkEdgeByteList96(data=counting_bytes(BYTES_PER_CHUNK)),
    )


@pytest.mark.tags("multi-level")
def test_byte_list_holding_one_byte_past_a_chunk(ssz_test: SSZTestFiller) -> None:
    """
    A byte list holding one byte past a chunk merkleizes to a stable root.

    Given
    -----
    - the same byte list holding one byte more than a whole chunk.
    - a second data leaf holding one byte and 31 of padding.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root matches a four-leaf tree, the last two leaves zero.
    """
    ssz_test(
        case_id="chunk_edge/bytelist96/one_byte_over_a_chunk",
        type_name="ChunkEdgeByteList96",
        value=ChunkEdgeByteList96(data=counting_bytes(BYTES_PER_CHUNK + 1)),
    )

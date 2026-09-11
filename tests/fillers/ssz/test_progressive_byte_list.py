"""SSZ conformance test vectors for the EIP-7916 ProgressiveByteList alias."""

from itertools import accumulate
from typing import Final

import pytest

from ssz import BYTES_PER_CHUNK, ProgressiveByteList
from ssz_testing import SSZTestFiller

pytestmark = pytest.mark.tags("boundary")

SPINE_LEVEL_CHUNKS: Final = tuple(4**level for level in range(3))
"""Chunks each of the first three spine levels holds, every level four times the one before."""

FULL_LEVEL_BYTES: Final = tuple(
    chunks * BYTES_PER_CHUNK for chunks in accumulate(SPINE_LEVEL_CHUNKS)
)
"""Byte counts that leave a level exactly full and the next one unopened: 32, 160 and 672."""


class SampleProgressiveByteList(ProgressiveByteList):
    """Progressive list of opaque bytes, which is what EIP-7916 aliases under its own name."""


def counting_bytes(count: int) -> list[int]:
    """Byte values offset by the chunk they sit in, so no two chunks below hold the same bytes."""
    return [(index + index // BYTES_PER_CHUNK + 1) % 256 for index in range(count)]


@pytest.mark.tags("empty")
def test_progressive_byte_list_empty(ssz_test: SSZTestFiller) -> None:
    """
    An empty progressive byte list round-trips unchanged.

    Given
    -----
    - a progressive byte list holding no bytes.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is empty.
    - the JSON mapping is the bare hex string `0x`.
    - the root is the zero terminator with a zero count mixed in.
    """
    ssz_test(
        case_id="progressive_byte_list/empty",
        type_name="SampleProgressiveByteList",
        value=SampleProgressiveByteList(data=[]),
    )


def test_progressive_byte_list_single_byte(ssz_test: SSZTestFiller) -> None:
    """
    A progressive byte list holding one byte round-trips unchanged.

    Given
    -----
    - a progressive byte list holding a single byte.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is that one byte, with no length prefix.
    - the root hashes one padded chunk against the terminator.
    """
    ssz_test(
        case_id="progressive_byte_list/single_byte",
        type_name="SampleProgressiveByteList",
        value=SampleProgressiveByteList(data=counting_bytes(1)),
    )


def test_progressive_byte_list_fills_the_first_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive byte list filling the first spine level round-trips unchanged.

    Given
    -----
    - 32 bytes, which pack into the single chunk the first level holds.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the packed data needs no padding.
    - the second level stays unopened, so the terminator sits beside the first chunk.
    """
    ssz_test(
        case_id="progressive_byte_list/fills_first_level",
        type_name="SampleProgressiveByteList",
        value=SampleProgressiveByteList(data=counting_bytes(FULL_LEVEL_BYTES[0])),
    )


def test_progressive_byte_list_opens_the_second_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive byte list one byte past the first level round-trips unchanged.

    Given
    -----
    - 33 bytes, one past the single chunk the first level holds.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the spare byte opens the second level, whose four chunks pad out around it.
    - the first chunk keeps the position it held one byte earlier.
    """
    ssz_test(
        case_id="progressive_byte_list/opens_second_level",
        type_name="SampleProgressiveByteList",
        value=SampleProgressiveByteList(data=counting_bytes(FULL_LEVEL_BYTES[0] + 1)),
    )


def test_progressive_byte_list_fills_the_second_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive byte list filling the second spine level round-trips unchanged.

    Given
    -----
    - 160 bytes, which pack into the five chunks the first two levels hold together.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - both levels are full, so neither carries a padded chunk.
    - the third level stays unopened.
    """
    ssz_test(
        case_id="progressive_byte_list/fills_second_level",
        type_name="SampleProgressiveByteList",
        value=SampleProgressiveByteList(data=counting_bytes(FULL_LEVEL_BYTES[1])),
    )


def test_progressive_byte_list_opens_the_third_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive byte list one byte past the second level round-trips unchanged.

    Given
    -----
    - 161 bytes, one past the five chunks the first two levels hold together.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the spare byte opens the third level, whose sixteen chunks pad out around it.
    """
    ssz_test(
        case_id="progressive_byte_list/opens_third_level",
        type_name="SampleProgressiveByteList",
        value=SampleProgressiveByteList(data=counting_bytes(FULL_LEVEL_BYTES[1] + 1)),
    )


def test_progressive_byte_list_fills_the_third_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive byte list filling the third spine level round-trips unchanged.

    Given
    -----
    - 672 bytes, which pack into the twenty-one chunks the first three levels hold together.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - all three levels are full, so none carries a padded chunk.
    - the fourth level stays unopened.
    """
    ssz_test(
        case_id="progressive_byte_list/fills_third_level",
        type_name="SampleProgressiveByteList",
        value=SampleProgressiveByteList(data=counting_bytes(FULL_LEVEL_BYTES[2])),
    )


def test_progressive_byte_list_opens_the_fourth_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive byte list one byte past the third level round-trips unchanged.

    Given
    -----
    - 673 bytes, one past the twenty-one chunks the first three levels hold together.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the spare byte opens the fourth level, whose sixty-four chunks pad out around it.
    - the twenty-one chunks already placed keep their positions.
    """
    ssz_test(
        case_id="progressive_byte_list/opens_fourth_level",
        type_name="SampleProgressiveByteList",
        value=SampleProgressiveByteList(data=counting_bytes(FULL_LEVEL_BYTES[2] + 1)),
    )

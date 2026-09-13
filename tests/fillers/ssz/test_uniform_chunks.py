"""SSZ: hash_tree_root vectors for the fold a level of identical nodes takes."""

from typing import ClassVar

import pytest

from ssz import (
    BYTES_PER_CHUNK,
    List,
    ProgressiveList,
    Uint8,
    Uint64,
    Vector,
)
from ssz_testing import SSZTestFiller

pytestmark = pytest.mark.tags("boundary", "multi-level")

MAX_BYTE = 0xFF
"""The byte a fork's maximum value fills every packed chunk with."""

MAX_UINT64 = Uint64(2**64 - 1)
"""One element of the byte above, so a sequence of them packs into identical chunks."""


def repeated(byte: int, count: int) -> list[Uint8]:
    """One byte repeated, packing into chunks that are all equal and none of them zero."""
    return [Uint8(byte)] * count


def alternating(chunk_count: int) -> list[Uint8]:
    """Chunk-wide runs of two bytes in turn, so no two neighbouring chunks are equal."""
    return [
        Uint8(0xAA if index % 2 == 0 else 0xBB)
        for index in range(chunk_count)
        for _ in range(BYTES_PER_CHUNK)
    ]


def palindrome() -> list[Uint8]:
    """Four chunk-wide runs reading the same both ways, so the first equals the last."""
    return [Uint8(byte) for byte in (0xAA, 0xBB, 0xBB, 0xAA) for _ in range(BYTES_PER_CHUNK)]


class UniformUint8Vector128(Vector[Uint8]):
    """Four chunks of packing, enough for one pairing to leave a level of two."""

    LENGTH: ClassVar[int] = 128


class UniformUint8Vector96(Vector[Uint8]):
    """Three chunks of packing, a count no level of a four-leaf tree can match."""

    LENGTH: ClassVar[int] = 96


class UniformUint64List16(List[Uint64]):
    """Sixteen eight-byte elements, four chunks of capacity and four chunks of data."""

    LIMIT: ClassVar[int] = 16
    ELEMENT_TYPE = Uint64


class UniformUint8List1024(List[Uint8]):
    """A cap of thirty-two chunks, four times the data every case below puts in it."""

    LIMIT: ClassVar[int] = 1024
    ELEMENT_TYPE = Uint8


class UniformUint64ProgressiveList(ProgressiveList[Uint64]):
    """Progressive list of eight-byte elements, four to a chunk."""

    ELEMENT_TYPE = Uint64


def test_alternating_chunks_fold_from_the_level_above_the_leaves(
    ssz_test: SSZTestFiller,
) -> None:
    """
    A byte vector of two chunks in turn merkleizes to a stable root.

    Given
    -----
    - a 128-byte vector packed into four chunks, alternating between two bytes.
    - a leaf level that is not uniform, over a level of two equal parent digests.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root matches the expected layout.
    - the leaves are paired off in the ordinary way, and the level above them folds,
      so the fold reads digests rather than the packed leaves.
    """
    ssz_test(
        case_id="uniform/vector_uint8_128/alternating_chunks",
        type_name="UniformUint8Vector128",
        value=UniformUint8Vector128(data=alternating(4)),
        expected_root="0xfba116ac959e6263dc673b50c23e100e2db9c062206ca6f53478d0721e201cc3",
    )


def test_matching_outer_chunks_are_not_a_uniform_level(ssz_test: SSZTestFiller) -> None:
    """
    A byte vector whose first and last chunks agree merkleizes to a stable root.

    Given
    -----
    - a 128-byte vector packed into four chunks reading the same in either direction.
    - a leaf level spanning its data tree whose ends match and whose middle does not.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root matches the expected layout.
    - no level folds, because two matching ends are not a level of one repeated value.
    """
    ssz_test(
        case_id="uniform/vector_uint8_128/matching_outer_chunks",
        type_name="UniformUint8Vector128",
        value=UniformUint8Vector128(data=palindrome()),
        expected_root="0x91eee2614081ab02041d5f7d60dcfd48a02e4d03acb1e5fcfdb618c9b002c010",
    )


def test_three_identical_chunks_never_span_their_data_tree(ssz_test: SSZTestFiller) -> None:
    """
    A byte vector of three identical chunks merkleizes to a stable root.

    Given
    -----
    - a 96-byte vector packed into three chunks, every byte the maximum.
    - a chunk count short of the four-leaf tree it is padded out to.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root matches the expected layout.
    - no level folds, because a uniform level short of its data tree meets a zero
      subtree as a sibling above it, and zero does not fold.
    """
    ssz_test(
        case_id="uniform/vector_uint8_96/all_max",
        type_name="UniformUint8Vector96",
        value=UniformUint8Vector96(data=repeated(MAX_BYTE, 96)),
        expected_root="0x4a6ba660d16b4dde152d00ba82cdde34827411f341c56b102e7962410924ad36",
    )


@pytest.mark.tags("limit")
def test_list_filled_to_capacity_folds_below_its_length_mixin(ssz_test: SSZTestFiller) -> None:
    """
    A list filled to a capacity its data spans exactly merkleizes to a stable root.

    Given
    -----
    - a list of eight-byte elements capped at sixteen, holding sixteen maximum values.
    - four identical chunks under a capacity of exactly four chunks.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root matches the expected layout.
    - the leaf level folds twice with no padding above it, and the element count is
      mixed in over the folded root.
    """
    ssz_test(
        case_id="uniform/list_uint64_16/at_limit_all_max",
        type_name="UniformUint64List16",
        value=UniformUint64List16(data=[MAX_UINT64] * 16),
        expected_root="0x6ba737db8a58f331db600d5b4707dc397602d67d7ef23ab31778e05334292d66",
    )


@pytest.mark.tags("limit")
def test_alternating_data_walks_then_folds_then_pads(ssz_test: SSZTestFiller) -> None:
    """
    A list of two chunks in turn, far below its capacity, merkleizes to a stable root.

    Given
    -----
    - a byte list capped at thirty-two chunks, holding eight chunks alternating between
      two bytes.
    - a leaf level that is not uniform, over a level of four equal parent digests.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root matches the expected layout.
    - all three shapes the walk can take appear in one root: the leaves are paired off,
      the level above them folds twice up to the data tree, and the result is hashed
      against an all-zero subtree twice to reach the full width.
    """
    ssz_test(
        case_id="uniform/list_uint8_1024/alternating_under_a_wide_limit",
        type_name="UniformUint8List1024",
        value=UniformUint8List1024(data=alternating(8)),
        expected_root="0xe0dc9721fb99314edd9363bc3e5152ce8038878513a154ac62f3253c3cefb1f5",
    )


def test_a_filled_progressive_level_folds_inside_the_spine(ssz_test: SSZTestFiller) -> None:
    """
    A progressive list filling its four-chunk level merkleizes to a stable root.

    Given
    -----
    - a progressive list of eight-byte elements holding twenty maximum values.
    - five chunks, which is one chunk in the first spine level and four in the second,
      filling that second level exactly.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root matches the expected layout.
    - the first level is a lone leaf and needs no hashing, the second level folds twice
      as a uniform leaf level, and the spine is closed by the zero node below them.
    """
    ssz_test(
        case_id="uniform/progressive_list_uint64/filled_second_level",
        type_name="UniformUint64ProgressiveList",
        value=UniformUint64ProgressiveList(data=[MAX_UINT64] * 20),
        expected_root="0x12fe7b4734b0fc5daf6c8a214a76fda7a25c061dec0caf3ab8739ab9e49d829a",
    )

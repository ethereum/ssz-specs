"""Unit tests for SSZ Merkleization primitives and the hash_tree_root dispatch."""

from __future__ import annotations

from collections.abc import Iterable, Sequence
from hashlib import sha256

import pytest

from ssz import (
    ZERO_ROOT,
    BaseByteList,
    BaseBytes,
    Chunk,
    Root,
    SSZTypeError,
    SSZValueError,
    Uint8,
    Uint16,
    Uint32,
    Uint64,
    Uint128,
    Uint256,
)
from ssz.bitfields import BaseBitlist, BaseBitvector, ProgressiveBitlist
from ssz.boolean import Boolean
from ssz.collections import List, ProgressiveList, Vector
from ssz.container import Container
from ssz.merkleization import (
    _next_pow2,
    _zero_tree_root,
    hash_tree_root,
    merkleize,
    merkleize_progressive,
    mix_in_length,
)


def h(a: bytes, b: bytes) -> Root:
    """Pairwise SHA-256 of two 32-byte nodes; used to build expected roots."""
    return Root(sha256(a + b).digest())


def pad(payload: bytes) -> Chunk:
    """Right-pad a payload to 32 bytes."""
    return Chunk(payload.ljust(32, b"\x00"))


def merge(leaf: Chunk, branch: Iterable[Root]) -> Root:
    """Walk a single leaf up a chain of right siblings, hashing left at each step."""
    running_node = Root(leaf)
    for sibling in branch:
        running_node = h(running_node, sibling)
    return running_node


# Sample chunks for testing, sample_chunks[i] = chunk(i)
sample_chunks = [Chunk(i.to_bytes(32, "little")) for i in range(16)]

# Pre-calculate zero-tree roots for assertions
# Z[0] = ZERO_ROOT, Z[1] = h(Z[0], Z[0]), Z[2] = h(Z[1], Z[1]), etc.
Z = [ZERO_ROOT]
for _ in range(20):
    Z.append(h(Z[-1], Z[-1]))


def chunk_run(count: int) -> list[Chunk]:
    """Numbered chunks wide enough for the progressive levels; chunk_run(n)[i] = chunk(i)."""
    return [Chunk(i.to_bytes(32, "little")) for i in range(count)]


def perfect_tree_root(leaves: Sequence[Chunk], width: int) -> Root:
    """
    Root of a perfect binary tree of the given power-of-two width.

    Missing leaves are materialized as real zero chunks and every layer is hashed
    explicitly, so the expected value never reuses the zero-subtree cache the
    implementation relies on.
    """
    level: list[bytes] = [*leaves, *([ZERO_ROOT] * (width - len(leaves)))]
    while len(level) > 1:
        level = [h(level[i], level[i + 1]) for i in range(0, len(level), 2)]
    return Root(level[0])


def naive_merkleize_progressive(chunks: Sequence[Chunk], num_leaves: int = 1) -> Root:
    """
    Transcribe the EIP-7916 definition literally, as an independent oracle.

    Each level pads its own chunks out to its power-of-two width and hashes that
    perfect tree; the remaining chunks recurse into a level four times as wide.
    An exhausted input terminates the spine with a plain zero leaf.
    """
    if len(chunks) == 0:
        return ZERO_ROOT
    return h(
        perfect_tree_root(chunks[:num_leaves], _next_pow2(num_leaves)),
        naive_merkleize_progressive(chunks[num_leaves:], num_leaves * 4),
    )


# Chunk counts straddling every progressive level boundary.
#
# A level opens only once every level before it is full, so the cumulative
# capacities are 1, 5, 21, and 85 chunks:
#
#     level   width   chunks added   chunks total
#     1       1       1              1
#     2       4       4              5
#     3       16      16             21
#     4       64      64             85
#
# Each boundary is probed one below, exactly at, and one above.
PROGRESSIVE_CHUNK_COUNTS = [0, 1, 2, 4, 5, 6, 20, 21, 22, 84, 85, 86]


@pytest.mark.parametrize(
    "x, expected",
    [
        (0, 1),  # Edge case: 0 should result in 1
        (1, 1),  # A power of two
        (2, 2),  # A power of two
        (3, 4),  # A number between powers of two
        (4, 4),  # A power of two
        (5, 8),
        (7, 8),
        (8, 8),
        (9, 16),
        (1023, 1024),
        (1024, 1024),  # A larger power of two
    ],
)
def test_next_pow2(x: int, expected: int) -> None:
    """Returns the smallest power of two at or above the input, with 1 for 0 and 1."""
    assert _next_pow2(x) == expected


def test_merkleize_empty_no_limit() -> None:
    """Merkleizing an empty list with no limit returns the all-zero leaf."""
    assert merkleize([]) == ZERO_ROOT


@pytest.mark.parametrize(
    "limit, expected_zero_root",
    [
        (0, Z[0]),  # limit=0 -> width=1 -> root is Z[0]
        (1, Z[0]),  # limit=1 -> width=1 -> root is Z[0]
        (2, Z[1]),  # limit=2 -> width=2 -> root is Z[1]
        (3, Z[2]),  # limit=3 -> width=4 -> root is Z[2]
        (7, Z[3]),  # limit=7 -> width=8 -> root is Z[3]
        (8, Z[3]),
    ],
)
def test_merkleize_empty_with_limit(limit: int, expected_zero_root: Root) -> None:
    """Empty input with a limit yields the zero-subtree root at the rounded-up width."""
    assert merkleize([], limit=limit) == expected_zero_root


def test_merkleize_single_chunk() -> None:
    """The root of a single chunk is the chunk itself."""
    assert merkleize([sample_chunks[1]]) == sample_chunks[1]


def test_merkleize_power_of_two_chunks() -> None:
    """A power-of-two leaf count needs no padding."""
    # Test with 2 chunks
    assert merkleize([sample_chunks[0], sample_chunks[1]]) == h(sample_chunks[0], sample_chunks[1])
    # Test with 4 chunks
    root_4 = h(h(sample_chunks[0], sample_chunks[1]), h(sample_chunks[2], sample_chunks[3]))
    assert merkleize(sample_chunks[0:4]) == root_4


def test_merkleize_non_power_of_two_chunks() -> None:
    """A non-power-of-two leaf count pads to the next power of two."""
    # Test with 3 chunks (pads to 4)
    expected_root_3_chunks = h(h(sample_chunks[0], sample_chunks[1]), h(sample_chunks[2], Z[0]))
    assert merkleize(sample_chunks[0:3]) == expected_root_3_chunks
    # Test with 5 chunks (pads to 8)
    h01 = h(sample_chunks[0], sample_chunks[1])
    h23 = h(sample_chunks[2], sample_chunks[3])
    h4z = h(sample_chunks[4], Z[0])
    # The remaining leaves are zero, so their parent is h(Z[0], Z[0]) = Z[1]
    expected_root_5_chunks = h(h(h01, h23), h(h4z, Z[1]))
    assert merkleize(sample_chunks[0:5]) == expected_root_5_chunks


def test_merkleize_with_limit_padding() -> None:
    """A limit larger than the leaf count widens the tree to the next power of two of the limit."""
    # 3 chunks, but limit is 8 (pads to width 8)
    h01 = h(sample_chunks[0], sample_chunks[1])
    h2z = h(sample_chunks[2], Z[0])
    # The parent of h01 and h2z
    left_branch = h(h01, h2z)
    # The right branch is a zero-tree of width 4, so its root is Z[2].
    right_branch = Z[2]
    expected_root = h(left_branch, right_branch)
    assert merkleize(sample_chunks[0:3], limit=8) == expected_root


def test_merkleize_error_on_exceeding_limit() -> None:
    """Raises when the chunk count exceeds the limit."""
    with pytest.raises(SSZValueError) as exception_info:
        merkleize(sample_chunks[0:5], limit=4)
    assert str(exception_info.value) == "merkleize: input exceeds limit"


def test_mix_in_length() -> None:
    """Mixes the length encoded as little-endian uint256 into the root."""
    root = Root(sample_chunks[0])
    length = 12345
    length_bytes = Chunk(length.to_bytes(32, "little"))
    expected_root = h(root, length_bytes)
    assert mix_in_length(root, length) == expected_root


def test_mix_in_length_zero() -> None:
    """Zero is a valid length."""
    root = Root(sample_chunks[0])
    length = 0
    length_bytes = Chunk(length.to_bytes(32, "little"))
    expected_root = h(root, length_bytes)
    assert mix_in_length(root, length) == expected_root


def test_mix_in_length_error_on_negative() -> None:
    """Rejects negative lengths."""
    with pytest.raises(SSZValueError):
        mix_in_length(Root(sample_chunks[0]), -1)


def test_zero_tree_root_internal() -> None:
    """Returns the cached zero-subtree root at depths within the cache."""
    assert _zero_tree_root(1) == Z[0]
    assert _zero_tree_root(2) == Z[1]
    assert _zero_tree_root(4) == Z[2]
    assert _zero_tree_root(8) == Z[3]
    assert _zero_tree_root(16) == Z[4]


def test_merkleize_progressive_empty_is_the_plain_zero_chunk() -> None:
    """An empty input terminates the spine with the zero leaf, not a zero subtree."""
    assert merkleize_progressive([]) == ZERO_ROOT
    # The terminator stands for a level holding no data, so it has no width to pad out.
    # Any zero subtree of depth one or more would be the wrong terminator.
    assert all(merkleize_progressive([]) != zero_subtree for zero_subtree in Z[1:])


@pytest.mark.parametrize(
    "chunk_count, expected_root",
    [
        # One chunk fills level 1 (width 1); level 2 is already the terminator.
        #
        #     root = h(chunk(0), 0)
        (1, h(sample_chunks[0], Z[0])),
        # Two chunks open level 2 (width 4) with a single occupant padded out to it.
        #
        #     root = h(chunk(0), h(h(h(chunk(1), 0), Z[1]), 0))
        (2, h(sample_chunks[0], h(h(h(sample_chunks[1], Z[0]), Z[1]), Z[0]))),
        # Four chunks leave one slot of level 2 (width 4) empty.
        (
            4,
            h(
                sample_chunks[0],
                h(h(h(sample_chunks[1], sample_chunks[2]), h(sample_chunks[3], Z[0])), Z[0]),
            ),
        ),
        # Five chunks fill the widths 1 and 4 exactly; the width-16 level is the terminator.
        (
            5,
            h(
                sample_chunks[0],
                h(
                    h(
                        h(sample_chunks[1], sample_chunks[2]),
                        h(sample_chunks[3], sample_chunks[4]),
                    ),
                    Z[0],
                ),
            ),
        ),
        # Six chunks open level 3 (width 16) with one occupant, padded up four layers.
        (
            6,
            h(
                sample_chunks[0],
                h(
                    h(h(sample_chunks[1], sample_chunks[2]), h(sample_chunks[3], sample_chunks[4])),
                    h(merge(sample_chunks[5], Z[0:4]), Z[0]),
                ),
            ),
        ),
    ],
)
def test_merkleize_progressive_small_inputs_known_roots(
    chunk_count: int, expected_root: Root
) -> None:
    """Short inputs match roots spelled out by hand from the 1 / 4 / 16 level widths."""
    assert merkleize_progressive(chunk_run(chunk_count)) == expected_root


def test_merkleize_progressive_three_levels_exactly_full() -> None:
    """Twenty-one chunks fill widths 1, 4, and 16 exactly, so width 64 is the terminator."""
    chunks = chunk_run(21)
    # Tree:
    #
    #     root
    #      /\
    #     /  \
    #   c[0] /\
    #       /  \
    #  c[1..5] /\
    #         /  \
    #   c[5..21]  0
    level_1 = Root(chunks[0])
    level_4 = perfect_tree_root(chunks[1:5], 4)
    level_16 = perfect_tree_root(chunks[5:21], 16)
    assert merkleize_progressive(chunks) == h(level_1, h(level_4, h(level_16, Z[0])))


def test_merkleize_progressive_opens_the_fourth_level() -> None:
    """One chunk past the 21-chunk boundary opens width 64 with a single occupant."""
    chunks = chunk_run(22)
    level_1 = Root(chunks[0])
    level_4 = perfect_tree_root(chunks[1:5], 4)
    level_16 = perfect_tree_root(chunks[5:21], 16)
    # A lone occupant of width 64 pads up six layers before joining the spine.
    level_64 = merge(chunks[21], Z[0:6])
    assert merkleize_progressive(chunks) == h(level_1, h(level_4, h(level_16, h(level_64, Z[0]))))


def test_merkleize_progressive_four_levels_exactly_full() -> None:
    """Eighty-five chunks fill widths 1, 4, 16, and 64 exactly, per the EIP diagram."""
    chunks = chunk_run(85)
    level_1 = Root(chunks[0])
    level_4 = perfect_tree_root(chunks[1:5], 4)
    level_16 = perfect_tree_root(chunks[5:21], 16)
    level_64 = perfect_tree_root(chunks[21:85], 64)
    assert merkleize_progressive(chunks) == h(level_1, h(level_4, h(level_16, h(level_64, Z[0]))))


def test_merkleize_progressive_opens_the_fifth_level() -> None:
    """One chunk past the 85-chunk boundary opens width 256, padded up eight layers."""
    chunks = chunk_run(86)
    level_1 = Root(chunks[0])
    level_4 = perfect_tree_root(chunks[1:5], 4)
    level_16 = perfect_tree_root(chunks[5:21], 16)
    level_64 = perfect_tree_root(chunks[21:85], 64)
    level_256 = merge(chunks[85], Z[0:8])
    assert merkleize_progressive(chunks) == h(
        level_1, h(level_4, h(level_16, h(level_64, h(level_256, Z[0]))))
    )


@pytest.mark.parametrize("chunk_count", PROGRESSIVE_CHUNK_COUNTS)
def test_merkleize_progressive_matches_naive_definition(chunk_count: int) -> None:
    """Every level boundary agrees with the naive transcription of the EIP definition."""
    chunks = chunk_run(chunk_count)
    assert merkleize_progressive(chunks) == naive_merkleize_progressive(chunks)


@pytest.mark.parametrize("chunk_count", [340, 341, 342])
def test_merkleize_progressive_matches_naive_definition_at_fifth_boundary(
    chunk_count: int,
) -> None:
    """The 341-chunk boundary that opens width 1024 also agrees with the definition."""
    chunks = chunk_run(chunk_count)
    assert merkleize_progressive(chunks) == naive_merkleize_progressive(chunks)


def test_merkleize_progressive_sweeps_every_count_through_the_fourth_level() -> None:
    """Every count from zero to eighty-nine agrees with the definition, not just boundaries."""
    for chunk_count in range(90):
        chunks = chunk_run(chunk_count)
        assert merkleize_progressive(chunks) == naive_merkleize_progressive(chunks)


def test_merkleize_progressive_accepts_a_wider_starting_level() -> None:
    """A caller-supplied starting width places the first chunks in a wider subtree."""
    chunks = chunk_run(6)
    # Starting at width 4 skips the width-1 level entirely: chunks 0..3 fill the
    # first subtree and chunks 4..5 open the next one at width 16.
    assert merkleize_progressive(chunks, num_leaves=4) == h(
        perfect_tree_root(chunks[0:4], 4),
        h(perfect_tree_root(chunks[4:6], 16), Z[0]),
    )


def test_merkleize_progressive_positions_are_stable_as_data_grows() -> None:
    """Appending a chunk extends the spine downward and moves nothing already placed."""
    five_chunks, six_chunks = chunk_run(5), chunk_run(6)
    # Both roots reuse the very same level-1 and level-4 subtrees.
    # Only the terminator is replaced, by the newly opened level-16 subtree.
    level_1 = Root(five_chunks[0])
    level_4 = perfect_tree_root(five_chunks[1:5], 4)
    assert merkleize_progressive(five_chunks) == h(level_1, h(level_4, Z[0]))
    assert merkleize_progressive(six_chunks) == h(
        level_1, h(level_4, h(perfect_tree_root(six_chunks[5:6], 16), Z[0]))
    )


class Bytes48(BaseBytes):
    """Test-local fixed-size byte array of 48 bytes."""

    LENGTH = 48


class Bytes96(BaseBytes):
    """Test-local fixed-size byte array of 96 bytes spanning three chunks."""

    LENGTH = 96


class ByteList7(BaseByteList):
    """Byte list with a single-chunk capacity of 7 bytes."""

    LIMIT = 7


class ByteList10(BaseByteList):
    """Byte list with a single-chunk capacity of 10 bytes."""

    LIMIT = 10


class ByteList32(BaseByteList):
    """Byte list whose capacity exactly fills one chunk."""

    LIMIT = 32


class ByteList50(BaseByteList):
    """Byte list spanning two chunks of capacity."""

    LIMIT = 50


class ByteList256(BaseByteList):
    """Byte list with capacity for eight chunks."""

    LIMIT = 256


class ByteList2048(BaseByteList):
    """Byte list with capacity for sixty-four chunks."""

    LIMIT = 2048


class Bitvector1(BaseBitvector):
    """Single-bit bitvector."""

    LENGTH = 1


class Bitvector3(BaseBitvector):
    """Three-bit bitvector inside one byte."""

    LENGTH = 3


class Bitvector8(BaseBitvector):
    """Bitvector aligned to one byte."""

    LENGTH = 8


class Bitvector9(BaseBitvector):
    """Bitvector spilling into a second byte."""

    LENGTH = 9


class Bitvector256(BaseBitvector):
    """Bitvector whose data fills exactly one 32-byte chunk."""

    LENGTH = 256


class Bitvector512(BaseBitvector):
    """Bitvector whose data fills exactly two chunks."""

    LENGTH = 512


class Bitlist3(BaseBitlist):
    """Bitlist limit of three bits."""

    LIMIT = 3


class Bitlist8(BaseBitlist):
    """Bitlist limit of eight bits."""

    LIMIT = 8


class Bitlist256(BaseBitlist):
    """Bitlist whose data root fits one chunk."""

    LIMIT = 256


class Bitlist512(BaseBitlist):
    """Bitlist whose data root spans two chunks."""

    LIMIT = 512


class Uint16Vector1(Vector[Uint16]):
    """Single-element vector of Uint16."""

    LENGTH = 1


class Uint16Vector2(Vector[Uint16]):
    """Two-element vector of Uint16."""

    LENGTH = 2


class Uint16Vector16(Vector[Uint16]):
    """Sixteen-element vector of Uint16 filling exactly one chunk."""

    LENGTH = 16


class ChunkVector3(Vector[Chunk]):
    """Vector of three composite Chunk elements."""

    LENGTH = 3


class Uint16List32(List[Uint16]):
    """List of Uint16 with a 32-element limit."""

    LIMIT = 32


class Uint16List1024(List[Uint16]):
    """List of Uint16 with a 1024-element limit used as a container field."""

    LIMIT = 1024


class Uint32List128(List[Uint32]):
    """List of Uint32 with a 128-element limit."""

    LIMIT = 128


class ChunkList32(List[Chunk]):
    """List of composite Chunk elements with a 32-element limit."""

    LIMIT = 32


class SingleField(Container):
    """Container holding a single basic field."""

    A: Uint8


class Small(Container):
    """Container with two byte-aligned fields fitting in one chunk each."""

    A: Uint16
    B: Uint16


class Fixed(Container):
    """Container with three fixed-size fields needing tree padding."""

    A: Uint8
    B: Uint64
    C: Uint32


class Var(Container):
    """Container with a variable-size middle field."""

    A: Uint16
    B: Uint16List1024
    C: Uint8


class FixedVector4(Vector[Fixed]):
    """Vector of four fixed-size containers."""

    LENGTH = 4


class VarVector2(Vector[Var]):
    """Vector of two variable-size containers."""

    LENGTH = 2


class Uint8ProgressiveList(ProgressiveList[Uint8]):
    """Progressive list of Uint8, one byte per element."""


class Uint16ProgressiveList(ProgressiveList[Uint16]):
    """Progressive list of Uint16, used standalone and as a nested element type."""


class BooleanProgressiveList(ProgressiveList[Boolean]):
    """Progressive list of Boolean, one byte per element."""


class ChunkProgressiveList(ProgressiveList[Chunk]):
    """Progressive list of composite 32-byte vectors."""


class SmallProgressiveList(ProgressiveList[Small]):
    """Progressive list of two-field containers."""


class NestedProgressiveList(ProgressiveList[Uint16ProgressiveList]):
    """Progressive list whose elements are themselves progressive lists."""


class ProgressiveVar(Container):
    """Container with a progressive list as its variable-size middle field."""

    A: Uint16
    B: Uint16ProgressiveList
    C: Uint8


class EmptyContainer(Container):
    """Container with zero fields."""


def le_padded(integer_value: int, byte_length: int) -> Chunk:
    """Encode an integer little-endian and right-pad to one chunk."""
    return pad(integer_value.to_bytes(byte_length, "little"))


@pytest.mark.parametrize(
    "uint_type, byte_length, integer_value",
    [
        (Uint8, 1, 0x00),
        (Uint8, 1, 0x01),
        (Uint8, 1, 0xAB),
        (Uint8, 1, 0xFF),
        (Uint16, 2, 0x0000),
        (Uint16, 2, 0xABCD),
        (Uint16, 2, 0xFFFF),
        (Uint32, 4, 0x00000000),
        (Uint32, 4, 0x01234567),
        (Uint32, 4, 0xFFFFFFFF),
        (Uint64, 8, 0x0000000000000000),
        (Uint64, 8, 0x0123456789ABCDEF),
        (Uint64, 8, 0xFFFFFFFFFFFFFFFF),
        (Uint128, 16, 0x00000000000000000000000000000000),
        (Uint128, 16, 0x0123456789ABCDEF0123456789ABCDEF),
        (Uint128, 16, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
        # A uint256 fills exactly one 32-byte chunk, so its root is that chunk verbatim.
        (Uint256, 32, 0x0000000000000000000000000000000000000000000000000000000000000000),
        (Uint256, 32, 0x0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF),
        (Uint256, 32, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
    ],
)
def test_hash_tree_root_uints(uint_type: type, byte_length: int, integer_value: int) -> None:
    """Unsigned integers hash as their little-endian bytes padded to one chunk."""
    assert hash_tree_root(uint_type(integer_value)) == le_padded(integer_value, byte_length)


@pytest.mark.parametrize(
    "boolean, expected_byte",
    [
        (Boolean(False), b"\x00"),
        (Boolean(True), b"\x01"),
    ],
)
def test_hash_tree_root_boolean(boolean: Boolean, expected_byte: bytes) -> None:
    """Boolean hashes to a single byte padded to one chunk."""
    assert hash_tree_root(boolean) == pad(expected_byte)


@pytest.mark.parametrize(
    "payload, expected_root",
    [
        # Empty: zero chunks merkleizes to the all-zero leaf.
        (b"", Z[0]),
        # One byte fits in one chunk and is its own root.
        (b"\xab", pad(b"\xab")),
        # 31 bytes still hash to a single padded chunk.
        (b"\xff" * 31, pad(b"\xff" * 31)),
        # 32 bytes are exactly one chunk and are their own root.
        (b"\xff" * 32, Root(b"\xff" * 32)),
        # 33 bytes form two chunks; the second is padded.
        (b"\xff" * 32 + b"\x01", h(b"\xff" * 32, pad(b"\x01"))),
        # 64 bytes form two full chunks hashed together.
        (b"\xaa" * 32 + b"\xbb" * 32, h(b"\xaa" * 32, b"\xbb" * 32)),
    ],
)
def test_hash_tree_root_bytes_known_vectors(payload: bytes, expected_root: Root) -> None:
    """Raw byte payloads hash to the merkle root of their packed chunks."""
    assert hash_tree_root(payload) == expected_root


def test_hash_tree_root_bytevector_single_chunk() -> None:
    """A 32-byte vector is exactly one chunk and is its own root."""
    raw_bytes = bytes(range(32))
    assert hash_tree_root(Chunk(raw_bytes)) == Chunk(raw_bytes)


def test_hash_tree_root_bytevector_two_chunks() -> None:
    """A 48-byte vector hashes its two chunks together; the trailing chunk is padded."""
    raw_bytes = bytes(range(48))
    expected_root = h(raw_bytes[:32], pad(raw_bytes[32:]))
    assert hash_tree_root(Bytes48(raw_bytes)) == expected_root


def test_hash_tree_root_bytevector_three_chunks() -> None:
    """A 96-byte vector merkleizes its three chunks with a zero pad to width four."""
    raw_bytes = bytes(range(96))
    left = h(raw_bytes[0:32], raw_bytes[32:64])
    right = h(raw_bytes[64:96], Z[0])
    assert hash_tree_root(Bytes96(raw_bytes)) == h(left, right)


def test_hash_tree_root_bytelist_empty_single_chunk_capacity() -> None:
    """An empty list with single-chunk capacity mixes a zero chunk with length zero."""
    expected_root = h(Z[0], pad(b"\x00"))
    assert hash_tree_root(ByteList10(data=b"")) == expected_root


def test_hash_tree_root_bytelist_empty_large_capacity() -> None:
    """An empty list with 64-chunk capacity uses the depth-6 zero root before mix-in."""
    expected_root = h(Z[6], pad(b"\x00"))
    assert hash_tree_root(ByteList2048(data=b"")) == expected_root


@pytest.mark.parametrize(
    "list_cls, payload, expected_root",
    [
        # Small list fits in one chunk; data root is the padded payload.
        (
            ByteList7,
            b"\x00\x01\x02\x03\x04\x05\x06",
            h(pad(b"\x00\x01\x02\x03\x04\x05\x06"), pad(b"\x07")),
        ),
        # Two-chunk capacity holds a 50-byte payload that spans both chunks.
        (
            ByteList50,
            bytes(range(50)),
            h(
                h(bytes(range(32)), pad(bytes(range(32, 50)))),
                pad(b"\x32"),
            ),
        ),
        # Eight-chunk capacity with six bytes pads the lone data chunk to depth three.
        (
            ByteList256,
            b"\x00\x01\x02\x03\x04\x05",
            h(
                merge(pad(b"\x00\x01\x02\x03\x04\x05"), [Z[0], Z[1], Z[2]]),
                pad(b"\x06"),
            ),
        ),
        # Capacity boundary: a full single chunk of data uses the chunk as the data root.
        (
            ByteList32,
            bytes(range(32)),
            h(Chunk(bytes(range(32))), pad(b"\x20")),
        ),
    ],
)
def test_hash_tree_root_bytelist_various(
    list_cls: type[BaseByteList], payload: bytes, expected_root: Root
) -> None:
    """Variable-length byte lists merkleize their packed data then mix in the length."""
    assert hash_tree_root(list_cls(data=payload)) == expected_root


def _bools(*values: int) -> list[Boolean]:
    """Build a typed boolean sequence from 0/1 integers."""
    return [Boolean(bool(bit)) for bit in values]


@pytest.mark.parametrize(
    "bv_cls, bits, expected_payload",
    [
        # Single bit set produces 0x01 padded.
        (Bitvector1, _bools(1), b"\x01"),
        # Three bits 0,1,0 produce 0b010 = 0x02 padded.
        (Bitvector3, _bools(0, 1, 0), b"\x02"),
        # Eight ones fill one byte at 0xff.
        (Bitvector8, _bools(*([1] * 8)), b"\xff"),
        # Nine ones spill into a second byte at 0x01.
        (Bitvector9, _bools(*([1] * 9)), b"\xff\x01"),
    ],
)
def test_hash_tree_root_bitvector_single_chunk(
    bv_cls: type[BaseBitvector],
    bits: list[Boolean],
    expected_payload: bytes,
) -> None:
    """Small bitvectors merkleize to a single padded chunk of their packed bytes."""
    bv = bv_cls(data=bits)
    assert bv.encode_bytes() == expected_payload
    assert hash_tree_root(bv) == pad(expected_payload)


def test_hash_tree_root_bitvector_one_chunk_boundary() -> None:
    """A 256-bit vector of ones packs into exactly one all-ones chunk."""
    bv = Bitvector256(data=_bools(*([1] * 256)))
    assert hash_tree_root(bv) == Chunk(b"\xff" * 32)


def test_hash_tree_root_bitvector_two_chunks() -> None:
    """A 512-bit vector of ones hashes two all-ones chunks together."""
    bv = Bitvector512(data=_bools(*([1] * 512)))
    assert hash_tree_root(bv) == h(b"\xff" * 32, b"\xff" * 32)


@pytest.mark.parametrize(
    "bl_cls, bits, expected_data_root, expected_length",
    [
        # Bitlist[3] with 0,1,0 has data byte 0x02 and length 3.
        (Bitlist3, _bools(0, 1, 0), pad(b"\x02"), 3),
        # Bitlist[8] with all ones has data byte 0xff and length 8.
        (Bitlist8, _bools(*([1] * 8)), pad(b"\xff"), 8),
        # Bitlist[8] empty: data root is the zero chunk and length is 0.
        (Bitlist8, _bools(), Z[0], 0),
    ],
)
def test_hash_tree_root_bitlist_small(
    bl_cls: type[BaseBitlist],
    bits: list[Boolean],
    expected_data_root: Root,
    expected_length: int,
) -> None:
    """Short bitlists hash the data chunk and mix in the bit count."""
    bl = bl_cls(data=bits)
    expected_root = h(expected_data_root, pad(expected_length.to_bytes(32, "little")))
    assert hash_tree_root(bl) == expected_root


def test_hash_tree_root_bitlist_chunk_boundary() -> None:
    """A bitlist whose data fills exactly one chunk mixes its 256-bit length in."""
    bl = Bitlist256(data=_bools(*([1] * 256)))
    expected_root = h(b"\xff" * 32, pad((256).to_bytes(32, "little")))
    assert hash_tree_root(bl) == expected_root


def test_hash_tree_root_bitlist_two_chunks() -> None:
    """A bitlist whose data spans two chunks merkleizes them and mixes in 512."""
    bl = Bitlist512(data=_bools(*([1] * 512)))
    base = h(b"\xff" * 32, b"\xff" * 32)
    expected_root = h(base, pad((512).to_bytes(32, "little")))
    assert hash_tree_root(bl) == expected_root


def test_hash_tree_root_vector_basic_single_chunk() -> None:
    """A vector of two Uint16 fits in one chunk; the root is the padded payload."""
    vector = Uint16Vector2(data=[Uint16(0x4567), Uint16(0x0123)])
    assert hash_tree_root(vector) == pad(b"\x67\x45\x23\x01")


def test_hash_tree_root_vector_basic_chunk_boundary() -> None:
    """A vector of sixteen Uint16 fills exactly one 32-byte chunk."""
    vector = Uint16Vector16(data=[Uint16(i) for i in range(16)])
    packed_bytes = b"".join(i.to_bytes(2, "little") for i in range(16))
    assert hash_tree_root(vector) == Chunk(packed_bytes)


def test_hash_tree_root_vector_single_element() -> None:
    """A one-element vector of Uint16 yields the padded little-endian element."""
    vector = Uint16Vector1(data=[Uint16(0xABCD)])
    assert hash_tree_root(vector) == pad(b"\xcd\xab")


def test_hash_tree_root_vector_composite_elements() -> None:
    """A vector of three Chunk leaves merkleizes its element roots padded to width four."""
    leaf_a = Chunk(b"\xbb\xaa" + b"\x00" * 30)
    leaf_b = Chunk(b"\xad\xc0" + b"\x00" * 30)
    leaf_c = Chunk(b"\xff\xee" + b"\x00" * 30)
    vector = ChunkVector3(data=[leaf_a, leaf_b, leaf_c])
    assert hash_tree_root(vector) == h(h(leaf_a, leaf_b), h(leaf_c, Z[0]))


def test_hash_tree_root_list_basic_small_limit() -> None:
    """A list of three Uint16 with capacity for 32 elements packs into a two-chunk tree."""
    test_list = Uint16List32(data=[Uint16(0xAABB), Uint16(0xC0AD), Uint16(0xEEFF)])
    base = h(pad(b"\xbb\xaa\xad\xc0\xff\xee"), Z[0])
    expected_root = h(base, pad(b"\x03"))
    assert hash_tree_root(test_list) == expected_root


def test_hash_tree_root_list_basic_large_limit() -> None:
    """A list of three Uint32 with capacity 128 pads up four levels then mixes in the length."""
    test_list = Uint32List128(data=[Uint32(0xAABB), Uint32(0xC0AD), Uint32(0xEEFF)])
    base = merge(pad(b"\xbb\xaa\x00\x00\xad\xc0\x00\x00\xff\xee\x00\x00"), Z[0:4])
    expected_root = h(base, pad(b"\x03"))
    assert hash_tree_root(test_list) == expected_root


def test_hash_tree_root_list_basic_empty() -> None:
    """An empty list with a large capacity uses the all-zero subtree at the capacity depth."""
    test_list = Uint32List128(data=[])
    expected_root = h(Z[4], pad(b"\x00"))
    assert hash_tree_root(test_list) == expected_root


def test_hash_tree_root_list_composite_elements() -> None:
    """A list of three Chunk elements merkleizes leaves to capacity depth then mixes length."""
    leaf_a = Chunk(b"\xbb\xaa" + b"\x00" * 30)
    leaf_b = Chunk(b"\xad\xc0" + b"\x00" * 30)
    leaf_c = Chunk(b"\xff\xee" + b"\x00" * 30)
    test_list = ChunkList32(data=[leaf_a, leaf_b, leaf_c])
    base = h(h(leaf_a, leaf_b), h(leaf_c, Z[0]))
    merkle = merge(base, Z[2:5])
    expected_root = h(merkle, pad(b"\x03"))
    assert hash_tree_root(test_list) == expected_root


def test_hash_tree_root_progressive_list_empty() -> None:
    """An empty progressive list mixes a zero count into the plain zero terminator."""
    # The data root is the terminator itself, and a zero count encodes to a zero chunk,
    # so the result is h(0, 0) — reached through the mix-in, never through tree padding.
    assert hash_tree_root(Uint8ProgressiveList(data=[])) == h(ZERO_ROOT, pad(b"\x00"))
    assert hash_tree_root(Uint8ProgressiveList(data=[])) == Z[1]


def test_hash_tree_root_progressive_list_basic_single_chunk() -> None:
    """Three Uint16 pack into one chunk hashed with the terminator, then the count."""
    values = Uint16ProgressiveList(data=[Uint16(0xAABB), Uint16(0xC0AD), Uint16(0xEEFF)])
    data_root = h(pad(b"\xbb\xaa\xad\xc0\xff\xee"), Z[0])
    assert hash_tree_root(values) == h(data_root, pad(b"\x03"))


def test_hash_tree_root_progressive_list_boolean_elements() -> None:
    """Boolean elements take the basic arm and pack one byte each."""
    values = BooleanProgressiveList(data=[Boolean(True), Boolean(False), Boolean(True)])
    assert hash_tree_root(values) == h(h(pad(b"\x01\x00\x01"), Z[0]), pad(b"\x03"))


@pytest.mark.parametrize(
    "element_count, expected_data_root",
    [
        # 32 bytes fill level 1 (width 1) exactly: the lone chunk meets the terminator.
        (32, h(Chunk(bytes(range(32))), Z[0])),
        # 33 bytes open level 2 (width 4): chunk 1 pads up two layers, then terminates.
        (33, h(Chunk(bytes(range(32))), h(merge(pad(b"\x20"), Z[0:2]), Z[0]))),
    ],
)
def test_hash_tree_root_progressive_list_packed_chunk_boundary(
    element_count: int, expected_data_root: Root
) -> None:
    """Crossing a chunk boundary opens the next spine level, not a wider single tree."""
    values = Uint8ProgressiveList(data=[Uint8(i) for i in range(element_count)])
    expected_root = h(expected_data_root, pad(element_count.to_bytes(32, "little")))
    assert hash_tree_root(values) == expected_root


def test_hash_tree_root_progressive_list_mixes_in_the_element_count() -> None:
    """The mixed-in count is the element count, not the chunk count the data occupies."""
    values = Uint8ProgressiveList(data=[Uint8(i) for i in range(33)])
    data_root = h(Chunk(bytes(range(32))), h(merge(pad(b"\x20"), Z[0:2]), Z[0]))
    # 33 elements occupy 2 chunks; only the element count may be mixed in.
    assert hash_tree_root(values) == mix_in_length(data_root, 33)
    assert hash_tree_root(values) != mix_in_length(data_root, 2)


def test_hash_tree_root_progressive_list_composite_containers() -> None:
    """Container elements contribute their own roots as the spine's leaves."""
    leaf_0 = h(pad(b"\x01\x00"), pad(b"\x02\x00"))
    leaf_1 = h(pad(b"\x03\x00"), pad(b"\x04\x00"))
    leaf_2 = h(pad(b"\x05\x00"), pad(b"\x06\x00"))
    values = SmallProgressiveList(
        data=[
            Small(A=Uint16(1), B=Uint16(2)),
            Small(A=Uint16(3), B=Uint16(4)),
            Small(A=Uint16(5), B=Uint16(6)),
        ]
    )
    # Leaf 0 fills width 1; leaves 1 and 2 occupy half of width 4.
    data_root = h(leaf_0, h(h(h(leaf_1, leaf_2), Z[1]), Z[0]))
    assert hash_tree_root(values) == h(data_root, pad(b"\x03"))


def test_hash_tree_root_progressive_list_byte_vector_elements() -> None:
    """A fixed byte vector is composite: each element root is one leaf of the spine."""
    leaf_a = Chunk(b"\xbb\xaa" + b"\x00" * 30)
    leaf_b = Chunk(b"\xad\xc0" + b"\x00" * 30)
    data_root = h(leaf_a, h(merge(leaf_b, Z[0:2]), Z[0]))
    values = ChunkProgressiveList(data=[leaf_a, leaf_b])
    assert hash_tree_root(values) == h(data_root, pad(b"\x02"))


def test_hash_tree_root_progressive_list_of_progressive_lists() -> None:
    """Nested progressive lists contribute their own length-mixed roots as leaves."""
    inner_populated = Uint16ProgressiveList(data=[Uint16(1), Uint16(2)])
    inner_empty = Uint16ProgressiveList(data=[])
    leaf_0 = h(h(pad(b"\x01\x00\x02\x00"), Z[0]), pad(b"\x02"))
    # An empty inner list roots to h(0, 0) — the same value as the depth-one zero subtree.
    leaf_1 = Z[1]
    data_root = h(leaf_0, h(merge(leaf_1, Z[0:2]), Z[0]))
    values = NestedProgressiveList(data=[inner_populated, inner_empty])
    assert hash_tree_root(values) == h(data_root, pad(b"\x02"))


def test_hash_tree_root_container_with_populated_progressive_list_field() -> None:
    """A progressive list field contributes its data root with the element count."""
    container = ProgressiveVar(
        A=Uint16(0xABCD),
        B=Uint16ProgressiveList(data=[Uint16(1), Uint16(2), Uint16(3)]),
        C=Uint8(0xFF),
    )
    field_b = h(h(pad(b"\x01\x00\x02\x00\x03\x00"), Z[0]), pad(b"\x03"))
    left = h(pad(b"\xcd\xab"), field_b)
    right = h(pad(b"\xff"), Z[0])
    assert hash_tree_root(container) == h(left, right)


def test_hash_tree_root_container_with_empty_progressive_list_field() -> None:
    """An empty progressive list field contributes the zero-terminated root with count zero."""
    container = ProgressiveVar(A=Uint16(0xABCD), B=Uint16ProgressiveList(data=()), C=Uint8(0xFF))
    left = h(pad(b"\xcd\xab"), h(ZERO_ROOT, pad(b"\x00")))
    right = h(pad(b"\xff"), Z[0])
    assert hash_tree_root(container) == h(left, right)


def test_hash_tree_root_progressive_bitlist_empty() -> None:
    """An empty progressive bitlist mixes a zero count into the plain zero terminator."""
    assert hash_tree_root(ProgressiveBitlist(data=())) == h(ZERO_ROOT, pad(b"\x00"))
    assert hash_tree_root(ProgressiveBitlist(data=())) == Z[1]


def test_hash_tree_root_progressive_bitlist_small() -> None:
    """Three bits pack into one chunk hashed with the terminator, then the bit count."""
    bitlist = ProgressiveBitlist(data=_bools(0, 1, 0))
    assert hash_tree_root(bitlist) == h(h(pad(b"\x02"), Z[0]), pad(b"\x03"))


@pytest.mark.parametrize(
    "bit_count, expected_data_root",
    [
        # 255 bits leave the top bit of the final byte clear, still one chunk at width 1.
        (255, h(Chunk(b"\xff" * 31 + b"\x7f"), Z[0])),
        # 256 bits fill the chunk exactly, still one chunk at width 1.
        (256, h(Chunk(b"\xff" * 32), Z[0])),
        # 257 bits spill one bit into a second chunk, opening level 2 at width 4.
        (257, h(Chunk(b"\xff" * 32), h(merge(pad(b"\x01"), Z[0:2]), Z[0]))),
    ],
)
def test_hash_tree_root_progressive_bitlist_chunk_boundary(
    bit_count: int, expected_data_root: Root
) -> None:
    """Bit packing crosses a chunk boundary at 257 bits and opens the next level."""
    bitlist = ProgressiveBitlist(data=_bools(*([1] * bit_count)))
    expected_root = h(expected_data_root, pad(bit_count.to_bytes(32, "little")))
    assert hash_tree_root(bitlist) == expected_root


def test_hash_tree_root_progressive_bitlist_mixes_in_the_bit_count() -> None:
    """The mixed-in count is the bit count, not the number of packed chunks."""
    bitlist = ProgressiveBitlist(data=_bools(*([1] * 256)))
    data_root = h(Chunk(b"\xff" * 32), Z[0])
    assert hash_tree_root(bitlist) == mix_in_length(data_root, 256)
    assert hash_tree_root(bitlist) != mix_in_length(data_root, 1)


def test_progressive_and_bounded_list_share_bytes_but_not_roots() -> None:
    """The two list shapes serialize identically and merkleize differently."""
    elements = [Uint16(1), Uint16(2), Uint16(3)]
    progressive = Uint16ProgressiveList(data=elements)
    # A 1024-element limit pads its tree out to 64 chunks, where the progressive
    # tree stops at the single chunk the data actually needs.
    bounded = Uint16List1024(data=elements)
    assert progressive.encode_bytes() == bounded.encode_bytes()
    assert hash_tree_root(progressive) != hash_tree_root(bounded)


def test_progressive_and_bounded_bitlist_share_bytes_but_not_roots() -> None:
    """The two bitlist shapes encode identically and merkleize differently."""
    bits = _bools(0, 1, 0)
    progressive = ProgressiveBitlist(data=bits)
    bounded = Bitlist256(data=bits)
    assert progressive.encode_bytes() == bounded.encode_bytes()
    assert hash_tree_root(progressive) != hash_tree_root(bounded)


def test_hash_tree_root_progressive_list_distinguishes_by_length() -> None:
    """Trailing zero elements change the mixed-in count and therefore the root."""
    short_list = Uint16ProgressiveList(data=(Uint16(1), Uint16(2)))
    long_list = Uint16ProgressiveList(data=(Uint16(1), Uint16(2), Uint16(0)))
    assert hash_tree_root(short_list) != hash_tree_root(long_list)


def test_hash_tree_root_container_empty() -> None:
    """A container with no fields hashes to the empty-input merkle root."""
    assert hash_tree_root(EmptyContainer()) == Z[0]


def test_hash_tree_root_container_single_field() -> None:
    """A container with one basic field hashes that field as its only leaf."""
    container = SingleField(A=Uint8(0xAB))
    assert hash_tree_root(container) == pad(b"\xab")


def test_hash_tree_root_container_two_fields() -> None:
    """A container with two basic fields hashes each as its own leaf."""
    container = Small(A=Uint16(0x4567), B=Uint16(0x0123))
    assert hash_tree_root(container) == h(pad(b"\x67\x45"), pad(b"\x23\x01"))


def test_hash_tree_root_container_three_fields_pads_to_four() -> None:
    """A three-field container pads its leaves with one zero chunk to width four."""
    container = Fixed(A=Uint8(0xAB), B=Uint64(0xAABBCCDDEEFF0011), C=Uint32(0x12345678))
    left = h(pad(b"\xab"), pad(b"\x11\x00\xff\xee\xdd\xcc\xbb\xaa"))
    right = h(pad(b"\x78\x56\x34\x12"), Z[0])
    assert hash_tree_root(container) == h(left, right)


def test_hash_tree_root_container_with_empty_list_field() -> None:
    """An empty variable-size field contributes its own zero-tree root with length zero."""
    container = Var(A=Uint16(0xABCD), B=Uint16List1024(data=()), C=Uint8(0xFF))
    expected_b = h(Z[6], pad(b"\x00"))
    left = h(pad(b"\xcd\xab"), expected_b)
    right = h(pad(b"\xff"), Z[0])
    assert hash_tree_root(container) == h(left, right)


def test_hash_tree_root_container_with_populated_list_field() -> None:
    """A populated variable-size field contributes its data root with the element count."""
    container = Var(
        A=Uint16(0xABCD),
        B=Uint16List1024(data=(Uint16(1), Uint16(2), Uint16(3))),
        C=Uint8(0xFF),
    )
    base = merge(pad(b"\x01\x00\x02\x00\x03\x00"), Z[0:6])
    expected_b = h(base, pad(b"\x03"))
    left = h(pad(b"\xcd\xab"), expected_b)
    right = h(pad(b"\xff"), Z[0])
    assert hash_tree_root(container) == h(left, right)


def test_hash_tree_root_vector_of_composite_containers() -> None:
    """A fixed-length vector of containers hashes the per-element roots into a balanced tree."""

    def fixed_root(a: bytes, b: bytes, c: bytes) -> Root:
        return h(h(pad(a), pad(b)), h(pad(c), Z[0]))

    fixed_vector = FixedVector4(
        data=[
            Fixed(A=Uint8(0xCC), B=Uint64(0x4242424242424242), C=Uint32(0x13371337)),
            Fixed(A=Uint8(0xDD), B=Uint64(0x3333333333333333), C=Uint32(0xABCDABCD)),
            Fixed(A=Uint8(0xEE), B=Uint64(0x4444444444444444), C=Uint32(0x00112233)),
            Fixed(A=Uint8(0xFF), B=Uint64(0x5555555555555555), C=Uint32(0x44556677)),
        ]
    )
    element_root_0 = fixed_root(b"\xcc", b"\x42" * 8, b"\x37\x13\x37\x13")
    element_root_1 = fixed_root(b"\xdd", b"\x33" * 8, b"\xcd\xab\xcd\xab")
    element_root_2 = fixed_root(b"\xee", b"\x44" * 8, b"\x33\x22\x11\x00")
    element_root_3 = fixed_root(b"\xff", b"\x55" * 8, b"\x77\x66\x55\x44")
    assert hash_tree_root(fixed_vector) == h(
        h(element_root_0, element_root_1), h(element_root_2, element_root_3)
    )


def test_hash_tree_root_vector_of_variable_containers() -> None:
    """A vector of variable-size containers still hashes the per-element roots."""

    def var_root(a: bytes, payload: bytes, count: int, c: bytes) -> Root:
        base = merge(pad(payload), Z[0:6])
        b_root = h(base, pad(count.to_bytes(32, "little")))
        return h(h(pad(a), b_root), h(pad(c), Z[0]))

    variable_vector = VarVector2(
        data=[
            Var(
                A=Uint16(0xDEAD),
                B=Uint16List1024(data=(Uint16(1), Uint16(2), Uint16(3))),
                C=Uint8(0x11),
            ),
            Var(
                A=Uint16(0xBEEF),
                B=Uint16List1024(data=(Uint16(4), Uint16(5), Uint16(6))),
                C=Uint8(0x22),
            ),
        ]
    )
    element_root_0 = var_root(b"\xad\xde", b"\x01\x00\x02\x00\x03\x00", 3, b"\x11")
    element_root_1 = var_root(b"\xef\xbe", b"\x04\x00\x05\x00\x06\x00", 3, b"\x22")
    assert hash_tree_root(variable_vector) == h(element_root_0, element_root_1)


@pytest.mark.parametrize(
    "unsupported_value",
    [
        42,
        "hello",
        [1, 2, 3],
        {"k": 1},
        (1, 2),
        3.14,
        None,
    ],
    ids=["int", "str", "list", "dict", "tuple", "float", "none"],
)
def test_hash_tree_root_unsupported_type_raises(unsupported_value: object) -> None:
    """The dispatch fallback rejects values without a registered handler."""
    with pytest.raises(SSZTypeError) as exception_info:
        hash_tree_root(unsupported_value)
    assert str(exception_info.value) == (
        f"hash_tree_root: unsupported value type {type(unsupported_value).__name__}"
    )


def test_hash_tree_root_is_deterministic() -> None:
    """Repeated calls on equal inputs return byte-identical roots."""
    first_list = Uint16List1024(data=(Uint16(1), Uint16(2), Uint16(3)))
    second_list = Uint16List1024(data=(Uint16(1), Uint16(2), Uint16(3)))
    assert hash_tree_root(first_list) == hash_tree_root(second_list)


def test_hash_tree_root_distinguishes_by_length() -> None:
    """Variable-length types with the same data but different lengths produce different roots."""
    short_list = Uint16List1024(data=(Uint16(1), Uint16(2)))
    long_list = Uint16List1024(data=(Uint16(1), Uint16(2), Uint16(0)))
    assert hash_tree_root(short_list) != hash_tree_root(long_list)

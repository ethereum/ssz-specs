"""Unit tests for SSZ Merkleization primitives and the hash_tree_root dispatch."""

from __future__ import annotations

from collections.abc import Iterable, Sequence
from hashlib import sha256

import pytest

from ssz import (
    ZERO_ROOT,
    ByteList,
    ByteVector,
    Chunk,
    Root,
    SSZType,
    SSZTypeError,
    SSZValueError,
    Uint8,
    Uint16,
    Uint32,
    Uint64,
    Uint128,
    Uint256,
    roots,
)
from ssz.bitfields import BitList, BitVector, ProgressiveBitList
from ssz.boolean import Boolean
from ssz.chunks import BYTES_PER_CHUNK, next_pow2
from ssz.collections import List, ProgressiveList, Vector
from ssz.container import Container, ProgressiveContainer
from ssz.layout import _pack_basic_elements, _pack_bytes, merkle_layout
from ssz.mixins import mix_in_active_fields, mix_in_length, mix_in_selector
from ssz.roots import hash_tree_root, layout_chunks
from ssz.trees import merkleize, merkleize_progressive
from ssz.uint import BaseUint
from ssz.union import CompatibleUnion


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
        perfect_tree_root(chunks[:num_leaves], next_pow2(num_leaves)),
        naive_merkleize_progressive(chunks[num_leaves:], num_leaves * 4),
    )


def active_fields_word(active_fields: Sequence[int]) -> Chunk:
    """
    Pack a field layout into the single 32-byte word EIP-7495 mixes into the root.

    Position i sets bit i % 8 of byte i // 8, so position 0 is the lowest bit of the
    first byte. The indexing is spelled out byte by byte rather than reusing the
    implementation's big-integer shift, so the expectation is derived independently.
    """
    word = bytearray(BYTES_PER_CHUNK)
    for position, bit in enumerate(active_fields):
        if bit:
            word[position // 8] |= 1 << (position % 8)
    return Chunk(bytes(word))


def expected_progressive_container_root(
    leaves: Sequence[Chunk], active_fields: Sequence[int]
) -> Root:
    """
    Root of a progressive container, from its explicit leaf list and its layout.

    The leaf list is written out by the caller: a field root at every set position and
    a zero chunk at every gap. It is then fed to the naive transcription of the
    progressive recursion, and the packed layout word is hashed in on top.
    """
    return h(naive_merkleize_progressive(leaves), active_fields_word(active_fields))


# Chunk counts straddling every progressive level boundary.
#
# A level opens only once every level before it is full.
# The cumulative capacities are 1, 5, 21, and 85 chunks:
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
    assert next_pow2(x) == expected


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
    assert str(exception_info.value) == "5 chunks exceed a limit of 4"


@pytest.mark.parametrize("limit", [-1, -64])
def test_merkleize_refuses_a_capacity_that_is_no_capacity(limit: int) -> None:
    """A negative bound counts no leaves, and an empty input does not excuse it."""
    # Rounding a negative bound up lands on a one-leaf tree, which is a root for a
    # capacity the caller never asked for.
    with pytest.raises(SSZValueError, match=rf"^0 chunks exceed a limit of {limit}$"):
        merkleize([], limit=limit)


# Chunk counts and capacities for an all-zero payload.
# These are the shapes where the closed form for a zero tree and the layer walk agree.
#
# A uniform level collapses only where it spans its own data tree.
# A count below the capacity, or one that is no power of two, falls short of that.
# No collapse reaches such a shape, and the walk had to hash it out node by node.
ALL_ZERO_SHAPES = [
    pytest.param(1, None, id="one_chunk_no_limit"),
    pytest.param(2, None, id="full_level_no_limit"),
    pytest.param(3, None, id="partial_level_no_limit"),
    pytest.param(1, 1, id="one_chunk_at_capacity"),
    pytest.param(1, 4, id="one_chunk_under_capacity"),
    pytest.param(4, 4, id="full_level_at_capacity"),
    pytest.param(3, 8, id="partial_level_under_capacity"),
    pytest.param(7, 7, id="partial_level_at_an_odd_capacity"),
    pytest.param(5, 64, id="partial_level_far_under_capacity"),
    pytest.param(2795, 4096, id="wide_partial_level"),
]


@pytest.mark.parametrize("chunk_count, limit", ALL_ZERO_SHAPES)
def test_merkleize_all_zero_payload_is_the_tree_a_walk_over_it_builds(
    chunk_count: int, limit: int | None
) -> None:
    """Zero data under zero padding roots where hashing every layer of it lands."""
    zero_chunks = [ZERO_ROOT] * chunk_count
    # The capacity sets the width, and its absence leaves the data to set it.
    width = next_pow2(chunk_count if limit is None else limit)
    assert merkleize(zero_chunks, limit=limit) == perfect_tree_root(zero_chunks, width)


@pytest.mark.parametrize(
    "nonzero_position",
    [
        pytest.param(0, id="first_chunk"),
        pytest.param(1, id="second_chunk"),
        pytest.param(4, id="last_chunk"),
    ],
)
def test_merkleize_a_payload_zero_but_for_one_chunk_is_not_a_zero_tree(
    nonzero_position: int,
) -> None:
    """One chunk of data anywhere in a zero payload keeps the whole root off the zero tree."""
    # Five chunks under a capacity of eight: a partial level, and no power of two either.
    chunks: list[Chunk] = [ZERO_ROOT] * 5
    chunks[nonzero_position] = Chunk(b"\xff" * 32)
    assert merkleize(chunks, limit=8) == perfect_tree_root(chunks, 8)
    # A zero prefix is not a zero payload, wherever the data that follows it sits.
    assert merkleize(chunks, limit=8) != Z[3]


@pytest.mark.parametrize(
    "limit",
    [
        pytest.param(None, id="no_limit"),
        pytest.param(1, id="one_leaf"),
        pytest.param(2, id="two_leaves"),
        pytest.param(3, id="an_odd_capacity"),
        pytest.param(4, id="a_full_level"),
        pytest.param(5, id="one_past_a_level"),
        pytest.param(8, id="eight_leaves"),
        pytest.param(16, id="sixteen_leaves"),
        pytest.param(64, id="sixty_four_leaves"),
        pytest.param(1024, id="a_wide_capacity"),
    ],
)
def test_merkleize_lands_where_a_layer_walk_lands_at_every_count(limit: int | None) -> None:
    """
    Every shape a shortcut can fire on roots where hashing each layer by hand roots.

    Three payloads, chosen so that each shortcut is reached and left:

        distinct chunks   no shortcut fires, and the layer walk runs to the top
        one repeated      the uniform level collapses, wherever it spans its data tree
        all zero          the closed form answers without walking at all

    The oracle materializes every padding leaf and hashes every layer, so it shares no
    step with the shortcuts it stands against.
    A shortcut that ever disagreed with it would be a wrong root, which is a chain split.
    """
    highest = 33 if limit is None else limit
    for count in range(highest + 1):
        payloads = {
            "distinct": [Chunk(i.to_bytes(32, "little")) for i in range(count)],
            "repeated": [sample_chunks[1]] * count,
            "zero": [ZERO_ROOT] * count,
        }
        width = next_pow2(count if limit is None else limit)
        for name, payload in payloads.items():
            assert merkleize(payload, limit=limit) == perfect_tree_root(payload, width), (
                f"{name} payload of {count} chunks under a capacity of {limit}"
            )


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


@pytest.mark.parametrize(
    "active_fields, expected_word",
    [
        # An empty layout sets no bit, so the mixed-in word is all zero.
        # No progressive container may declare it; the primitive is still defined on it.
        pytest.param([], b"", id="empty"),
        pytest.param([1], b"\x01", id="one_position_set"),
        pytest.param([0, 1], b"\x02", id="second_position_set"),
        pytest.param([0, 0, 1], b"\x04", id="third_position_set"),
        # The EIP's own two layouts: bits 0 and 2, then bits 1 and 2.
        pytest.param([1, 0, 1], b"\x05", id="square_layout"),
        pytest.param([0, 1, 1], b"\x06", id="circle_layout"),
        # Bits 0, 3 and 5 give 1 + 8 + 32.
        pytest.param([1, 0, 0, 1, 0, 1], b"\x29", id="multiple_gaps"),
        pytest.param([1] * 8, b"\xff", id="first_byte_full"),
        # Position 8 is the lowest bit of the second byte, not the highest of the first.
        pytest.param([1] * 9, b"\xff\x01", id="spills_into_second_byte"),
        pytest.param([*([0] * 255), 1], b"\x00" * 31 + b"\x80", id="last_position_of_the_word"),
    ],
)
def test_mix_in_active_fields_packs_the_layout_into_one_word(
    active_fields: Sequence[int], expected_word: bytes
) -> None:
    """The layout mixes in as one 32-byte word, one bit per position, lowest bit first."""
    root = Root(sample_chunks[1])
    assert mix_in_active_fields(root, active_fields) == h(root, pad(expected_word))


def test_mix_in_active_fields_fills_the_word_at_256_positions() -> None:
    """A layout occupying all 256 positions leaves no padding in the mixed-in word."""
    root = Root(sample_chunks[1])
    # Every bit of every byte is set, so the word is 32 bytes of 0xff with nothing padded.
    assert mix_in_active_fields(root, [1] * 256) == h(root, Chunk(b"\xff" * 32))


def test_mix_in_active_fields_zero_pads_a_layout_below_256_positions() -> None:
    """A layout narrower than the word is zero-padded up to it, not scaled to fit."""
    root = Root(sample_chunks[1])
    narrow_layout = [1]
    padded_layout = [1, *([0] * 255)]
    assert mix_in_active_fields(root, narrow_layout) == h(root, pad(b"\x01"))
    assert mix_in_active_fields(root, padded_layout) == mix_in_active_fields(root, narrow_layout)


def test_mix_in_active_fields_separates_two_layouts_over_one_root() -> None:
    """The same tree under two layouts yields two roots, which is the point of the mix-in."""
    root = Root(sample_chunks[1])
    assert mix_in_active_fields(root, [1, 0, 1]) != mix_in_active_fields(root, [1, 1, 1])


@pytest.mark.parametrize(
    "selector, expected_word",
    [
        # The lowest selector a union may declare.
        pytest.param(1, b"\x01", id="lowest_selector"),
        pytest.param(2, b"\x02", id="second_selector"),
        pytest.param(64, b"\x40", id="mid_range"),
        # The highest selector a union may declare: the high bit stays reserved.
        pytest.param(127, b"\x7f", id="highest_selector"),
    ],
)
def test_mix_in_selector_packs_the_selector_into_one_word(
    selector: int, expected_word: bytes
) -> None:
    """
    The selector occupies a full 32-byte chunk, not the single byte it takes on the wire.

    The EIP writes hash(root, selector) with the uint8 serialization of the selector, and
    the operand is nonetheless one whole chunk: every other mix-in hashes two 32-byte
    nodes, and a one-byte right operand would not be a node at all.
    """
    root = Root(sample_chunks[1])
    # The word is the selector little-endian in the first byte, then 31 zero bytes.
    assert mix_in_selector(root, selector) == h(root, pad(expected_word))


def test_mix_in_selector_uses_a_full_thirty_two_byte_operand() -> None:
    """The second operand is written out byte for byte, to pin the width down."""
    root = Root(sample_chunks[1])
    selector_word = Chunk(b"\x01" + b"\x00" * 31)
    assert len(selector_word) == BYTES_PER_CHUNK
    assert mix_in_selector(root, 1) == h(root, selector_word)
    # A one-byte operand would give a different digest, so the width is not incidental.
    assert mix_in_selector(root, 1) != Root(sha256(root + b"\x01").digest())


@pytest.mark.parametrize("selector", [-1, 256, 1000])
def test_mix_in_selector_rejects_a_value_wider_than_a_byte(selector: int) -> None:
    """The operand holds one byte, so a wider value has nowhere to go."""
    with pytest.raises(SSZValueError, match=r"does not fit one byte$"):
        mix_in_selector(Root(sample_chunks[1]), selector)


def test_mix_in_selector_separates_two_selectors_over_one_root() -> None:
    """One root under two selectors yields two roots, which is the point of the mix-in."""
    root = Root(sample_chunks[1])
    assert mix_in_selector(root, 1) != mix_in_selector(root, 2)
    assert mix_in_selector(root, 1) != mix_in_selector(root, 127)


@pytest.mark.parametrize("depth", range(5))
def test_empty_payload_takes_the_cached_zero_tree_root(depth: int) -> None:
    """The cached zero-subtree shortcut agrees with hashing 2**depth zero leaves by hand."""
    assert merkleize([], limit=2**depth) == Z[depth]


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


@pytest.mark.parametrize(
    "chunk_count",
    # One level open, then each cumulative capacity probed at and past its boundary, up to
    # the level that holds 1024 chunks.
    [1, 2, 5, 6, 20, 21, 22, 84, 85, 86, 340, 341, 342, 1023, 1024, 1025],
)
def test_merkleize_progressive_over_an_all_zero_payload_matches_the_definition(
    chunk_count: int,
) -> None:
    """A spine of zero levels is still the spine the definition builds, level by level."""
    # Every level of this payload is all zero.
    # Each subtree root has a closed form and none of them is walked.
    # The spine above them has to come out unchanged regardless.
    zero_chunks = [ZERO_ROOT] * chunk_count
    assert merkleize_progressive(zero_chunks) == naive_merkleize_progressive(zero_chunks)


def test_merkleize_progressive_accepts_a_wider_starting_level() -> None:
    """A caller-supplied starting width places the first chunks in a wider subtree."""
    chunks = chunk_run(6)
    # Starting at width 4 skips the width-1 level entirely.
    # Chunks 0..3 fill the first subtree and chunks 4..5 open the next one at width 16.
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


class Bytes48(ByteVector):
    """Test-local fixed-size byte array of 48 bytes."""

    LENGTH = 48


class Bytes96(ByteVector):
    """Test-local fixed-size byte array of 96 bytes spanning three chunks."""

    LENGTH = 96


class ByteList7(ByteList):
    """Byte list with a single-chunk capacity of 7 bytes."""

    LIMIT = 7


class ByteList10(ByteList):
    """Byte list with a single-chunk capacity of 10 bytes."""

    LIMIT = 10


class ByteList32(ByteList):
    """Byte list whose capacity exactly fills one chunk."""

    LIMIT = 32


class ByteList50(ByteList):
    """Byte list spanning two chunks of capacity."""

    LIMIT = 50


class ByteList256(ByteList):
    """Byte list with capacity for eight chunks."""

    LIMIT = 256


class ByteList2048(ByteList):
    """Byte list with capacity for sixty-four chunks."""

    LIMIT = 2048


class BitVector1(BitVector):
    """Single-bit bitvector."""

    LENGTH = 1


class BitVector3(BitVector):
    """Three-bit bitvector inside one byte."""

    LENGTH = 3


class BitVector8(BitVector):
    """BitVector aligned to one byte."""

    LENGTH = 8


class BitVector9(BitVector):
    """BitVector spilling into a second byte."""

    LENGTH = 9


class BitVector256(BitVector):
    """BitVector whose data fills exactly one 32-byte chunk."""

    LENGTH = 256


class BitVector512(BitVector):
    """BitVector whose data fills exactly two chunks."""

    LENGTH = 512


class BitList3(BitList):
    """BitList limit of three bits."""

    LIMIT = 3


class BitList8(BitList):
    """BitList limit of eight bits."""

    LIMIT = 8


class BitList256(BitList):
    """BitList whose data root fits one chunk."""

    LIMIT = 256


class BitList512(BitList):
    """BitList whose data root spans two chunks."""

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


class OneFieldProgressive(ProgressiveContainer):
    """Progressive container occupying the single position its layout declares."""

    ACTIVE_FIELDS = (1,)

    A: Uint16


class GappedProgressive(ProgressiveContainer):
    """EIP-7495's Square: a field at position 0, a gap, then a field at position 2."""

    ACTIVE_FIELDS = (1, 0, 1)

    A: Uint16
    B: Uint8


class LeadingGapProgressive(ProgressiveContainer):
    """EIP-7495's Circle: a leading gap, then fields at positions 1 and 2."""

    ACTIVE_FIELDS = (0, 1, 1)

    A: Uint16
    B: Uint8


class TwoLeadingGapsProgressive(ProgressiveContainer):
    """Two leading gaps, so the sole field is merkleized at position two."""

    ACTIVE_FIELDS = (0, 0, 1)

    C: Uint32


class MultiGapProgressive(ProgressiveContainer):
    """Three fields separated by gaps of differing widths."""

    ACTIVE_FIELDS = (1, 0, 0, 1, 0, 1)

    A: Uint8
    B: Uint16
    C: Uint32


class BoundaryOneProgressive(ProgressiveContainer):
    """One position: the leaves fill the width-one level exactly."""

    ACTIVE_FIELDS = (1,)

    A: Uint8


class BoundaryFiveProgressive(ProgressiveContainer):
    """Five positions: the leaves fill the width-one and width-four levels exactly."""

    ACTIVE_FIELDS = (1, 0, 0, 0, 1)

    A: Uint8
    B: Uint8


class BoundaryTwentyOneProgressive(ProgressiveContainer):
    """Twenty-one positions: the leaves fill the first three levels exactly."""

    ACTIVE_FIELDS = (1, *([0] * 19), 1)

    A: Uint8
    B: Uint8


class BoundaryTwentyTwoProgressive(ProgressiveContainer):
    """Twenty-two positions: one leaf past the third level, opening the width-64 level."""

    ACTIVE_FIELDS = (1, *([0] * 20), 1)

    A: Uint8
    B: Uint8


class BoundedListFieldProgressive(ProgressiveContainer):
    """Progressive container whose second field is a bounded list."""

    ACTIVE_FIELDS = (1, 0, 1)

    A: Uint16
    B: Uint16List1024


class ProgressiveListFieldProgressive(ProgressiveContainer):
    """Progressive container whose second field is a progressive list."""

    ACTIVE_FIELDS = (1, 1)

    A: Uint16
    B: Uint16ProgressiveList


class ProgressiveBitListFieldProgressive(ProgressiveContainer):
    """Progressive container whose second field is a progressive bitlist."""

    ACTIVE_FIELDS = (1, 0, 1)

    A: Uint8
    B: ProgressiveBitList


class NestedProgressive(ProgressiveContainer):
    """Progressive container holding another progressive container as a field."""

    ACTIVE_FIELDS = (1, 0, 1)

    A: Uint8
    B: GappedProgressive


class GappedList4(List[GappedProgressive]):
    """Bounded list of progressive containers, four at most."""

    LIMIT = 4


class GappedProgressiveList(ProgressiveList[GappedProgressive]):
    """Progressive list of progressive containers."""


class ContainerWithProgressive(Container):
    """Ordinary container holding a progressive container as its second field."""

    A: Uint8
    B: GappedProgressive


class ThreeByteContainer(Container):
    """Bounded container of three single-byte fields, the shape a progressive one mirrors."""

    A: Uint8
    B: Uint8
    C: Uint8


class ThreeSetProgressive(ProgressiveContainer):
    """Three positions, all occupied: the version before a field was dropped."""

    ACTIVE_FIELDS = (1, 1, 1)

    A: Uint8
    B: Uint8
    C: Uint8


class MiddleGapProgressive(ProgressiveContainer):
    """The same three positions after the middle field was dropped."""

    ACTIVE_FIELDS = (1, 0, 1)

    A: Uint8
    C: Uint8


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
    list_cls: type[ByteList], payload: bytes, expected_root: Root
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
        (BitVector1, _bools(1), b"\x01"),
        # Three bits 0,1,0 produce 0b010 = 0x02 padded.
        (BitVector3, _bools(0, 1, 0), b"\x02"),
        # Eight ones fill one byte at 0xff.
        (BitVector8, _bools(*([1] * 8)), b"\xff"),
        # Nine ones spill into a second byte at 0x01.
        (BitVector9, _bools(*([1] * 9)), b"\xff\x01"),
    ],
)
def test_hash_tree_root_bitvector_single_chunk(
    bv_cls: type[BitVector],
    bits: list[Boolean],
    expected_payload: bytes,
) -> None:
    """Small bitvectors merkleize to a single padded chunk of their packed bytes."""
    bv = bv_cls(data=bits)
    assert bv.encode_bytes() == expected_payload
    assert hash_tree_root(bv) == pad(expected_payload)


def test_hash_tree_root_bitvector_one_chunk_boundary() -> None:
    """A 256-bit vector of ones packs into exactly one all-ones chunk."""
    bv = BitVector256(data=_bools(*([1] * 256)))
    assert hash_tree_root(bv) == Chunk(b"\xff" * 32)


def test_hash_tree_root_bitvector_two_chunks() -> None:
    """A 512-bit vector of ones hashes two all-ones chunks together."""
    bv = BitVector512(data=_bools(*([1] * 512)))
    assert hash_tree_root(bv) == h(b"\xff" * 32, b"\xff" * 32)


@pytest.mark.parametrize(
    "bl_cls, bits, expected_data_root, expected_length",
    [
        # BitList[3] with 0,1,0 has data byte 0x02 and length 3.
        (BitList3, _bools(0, 1, 0), pad(b"\x02"), 3),
        # BitList[8] with all ones has data byte 0xff and length 8.
        (BitList8, _bools(*([1] * 8)), pad(b"\xff"), 8),
        # BitList[8] empty: data root is the zero chunk and length is 0.
        (BitList8, _bools(), Z[0], 0),
    ],
)
def test_hash_tree_root_bitlist_small(
    bl_cls: type[BitList],
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
    bl = BitList256(data=_bools(*([1] * 256)))
    expected_root = h(b"\xff" * 32, pad((256).to_bytes(32, "little")))
    assert hash_tree_root(bl) == expected_root


def test_hash_tree_root_bitlist_two_chunks() -> None:
    """A bitlist whose data spans two chunks merkleizes them and mixes in 512."""
    bl = BitList512(data=_bools(*([1] * 512)))
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
    # The data root is the terminator itself, and a zero count encodes to a zero chunk.
    # The result is h(0, 0) — reached through the mix-in, never through tree padding.
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
    assert hash_tree_root(ProgressiveBitList(data=())) == h(ZERO_ROOT, pad(b"\x00"))
    assert hash_tree_root(ProgressiveBitList(data=())) == Z[1]


def test_hash_tree_root_progressive_bitlist_small() -> None:
    """Three bits pack into one chunk hashed with the terminator, then the bit count."""
    bitlist = ProgressiveBitList(data=_bools(0, 1, 0))
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
    bitlist = ProgressiveBitList(data=_bools(*([1] * bit_count)))
    expected_root = h(expected_data_root, pad(bit_count.to_bytes(32, "little")))
    assert hash_tree_root(bitlist) == expected_root


def test_hash_tree_root_progressive_bitlist_mixes_in_the_bit_count() -> None:
    """The mixed-in count is the bit count, not the number of packed chunks."""
    bitlist = ProgressiveBitList(data=_bools(*([1] * 256)))
    data_root = h(Chunk(b"\xff" * 32), Z[0])
    assert hash_tree_root(bitlist) == mix_in_length(data_root, 256)
    assert hash_tree_root(bitlist) != mix_in_length(data_root, 1)


def test_progressive_and_bounded_list_share_bytes_but_not_roots() -> None:
    """The two list shapes serialize identically and merkleize differently."""
    elements = [Uint16(1), Uint16(2), Uint16(3)]
    progressive = Uint16ProgressiveList(data=elements)
    # A 1024-element limit pads its tree out to 64 chunks.
    # There the progressive tree stops at the single chunk the data actually needs.
    bounded = Uint16List1024(data=elements)
    assert progressive.encode_bytes() == bounded.encode_bytes()
    assert hash_tree_root(progressive) != hash_tree_root(bounded)


def test_progressive_and_bounded_bitlist_share_bytes_but_not_roots() -> None:
    """The two bitlist shapes encode identically and merkleize differently."""
    bits = _bools(0, 1, 0)
    progressive = ProgressiveBitList(data=bits)
    bounded = BitList256(data=bits)
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


def test_hash_tree_root_progressive_container_single_field() -> None:
    """One leaf fills the width-one level, and the layout word is mixed in above it."""
    # leaves = [root(A)], so the spine is h(leaf, terminator) and the word is 0x01.
    value = OneFieldProgressive(A=Uint16(0xABCD))
    assert hash_tree_root(value) == h(h(pad(b"\xcd\xab"), Z[0]), pad(b"\x01"))


def test_hash_tree_root_progressive_container_interior_gap() -> None:
    """A cleared position contributes a zero leaf, which is what holds position two put."""
    # leaves = [root(A), 0, root(B)]:
    #   level 1 (width 1)  takes leaf 0,
    #   level 2 (width 4)  takes the zero leaf and root(B), padded out to four,
    #   level 3            is the terminator.
    value = GappedProgressive(A=Uint16(0x1234), B=Uint8(0x56))
    level_1 = pad(b"\x34\x12")
    level_4 = h(h(Z[0], pad(b"\x56")), Z[1])
    assert hash_tree_root(value) == h(h(level_1, h(level_4, Z[0])), pad(b"\x05"))


def test_hash_tree_root_progressive_container_two_leading_gaps() -> None:
    """Leading gaps put zero leaves at the front, so the sole field sits at position two."""
    # leaves = [0, 0, root(C)], so the width-one level holds a zero leaf of its own.
    value = TwoLeadingGapsProgressive(C=Uint32(0x11223344))
    level_4 = h(h(Z[0], pad(b"\x44\x33\x22\x11")), Z[1])
    assert hash_tree_root(value) == h(h(Z[0], h(level_4, Z[0])), pad(b"\x04"))


@pytest.mark.parametrize(
    "value, expected_leaves",
    [
        pytest.param(
            OneFieldProgressive(A=Uint16(0xABCD)),
            [pad(b"\xcd\xab")],
            id="single_position",
        ),
        pytest.param(
            GappedProgressive(A=Uint16(0x1234), B=Uint8(0x56)),
            [pad(b"\x34\x12"), ZERO_ROOT, pad(b"\x56")],
            id="interior_gap",
        ),
        pytest.param(
            LeadingGapProgressive(A=Uint16(0x1234), B=Uint8(0x56)),
            [ZERO_ROOT, pad(b"\x34\x12"), pad(b"\x56")],
            id="leading_gap",
        ),
        pytest.param(
            TwoLeadingGapsProgressive(C=Uint32(0x11223344)),
            [ZERO_ROOT, ZERO_ROOT, pad(b"\x44\x33\x22\x11")],
            id="two_leading_gaps",
        ),
        pytest.param(
            MultiGapProgressive(A=Uint8(1), B=Uint16(0x0203), C=Uint32(0x04050607)),
            [
                pad(b"\x01"),
                ZERO_ROOT,
                ZERO_ROOT,
                pad(b"\x03\x02"),
                ZERO_ROOT,
                pad(b"\x07\x06\x05\x04"),
            ],
            id="multiple_gaps",
        ),
    ],
)
def test_hash_tree_root_progressive_container_from_explicit_leaves(
    value: ProgressiveContainer, expected_leaves: list[Chunk]
) -> None:
    """Field roots land at set positions and zero chunks at gaps, one leaf per position."""
    assert len(expected_leaves) == len(type(value).ACTIVE_FIELDS)
    assert hash_tree_root(value) == expected_progressive_container_root(
        expected_leaves, type(value).ACTIVE_FIELDS
    )


@pytest.mark.parametrize(
    "value, expected_leaves",
    [
        # One leaf fills the width-one level exactly.
        pytest.param(
            BoundaryOneProgressive(A=Uint8(1)),
            [pad(b"\x01")],
            id="one_position",
        ),
        # Five leaves fill the width-one and width-four levels exactly.
        pytest.param(
            BoundaryFiveProgressive(A=Uint8(1), B=Uint8(2)),
            [pad(b"\x01"), ZERO_ROOT, ZERO_ROOT, ZERO_ROOT, pad(b"\x02")],
            id="five_positions",
        ),
        # Twenty-one leaves fill the first three levels exactly, so width 64 stays the terminator.
        pytest.param(
            BoundaryTwentyOneProgressive(A=Uint8(1), B=Uint8(2)),
            [pad(b"\x01"), *([ZERO_ROOT] * 19), pad(b"\x02")],
            id="twenty_one_positions",
        ),
        # One leaf past that boundary opens the width-64 level with a single occupant.
        pytest.param(
            BoundaryTwentyTwoProgressive(A=Uint8(1), B=Uint8(2)),
            [pad(b"\x01"), *([ZERO_ROOT] * 20), pad(b"\x02")],
            id="twenty_two_positions",
        ),
    ],
)
def test_hash_tree_root_progressive_container_level_boundaries(
    value: ProgressiveContainer, expected_leaves: list[Chunk]
) -> None:
    """A layout is as wide as its position count, so it crosses the spine's level widths."""
    # The gaps are real leaves: a 22-position layout occupies 22 leaves whatever its field count.
    assert len(expected_leaves) == len(type(value).ACTIVE_FIELDS)
    assert hash_tree_root(value) == expected_progressive_container_root(
        expected_leaves, type(value).ACTIVE_FIELDS
    )


def test_hash_tree_root_progressive_container_boundary_widths_differ() -> None:
    """The 21- and 22-position layouts straddle a level width, so their roots differ."""
    twenty_one = BoundaryTwentyOneProgressive(A=Uint8(1), B=Uint8(2))
    twenty_two = BoundaryTwentyTwoProgressive(A=Uint8(1), B=Uint8(2))
    assert twenty_one.encode_bytes() == twenty_two.encode_bytes()
    assert hash_tree_root(twenty_one) != hash_tree_root(twenty_two)


def test_hash_tree_root_progressive_container_with_bounded_list_field() -> None:
    """A bounded list field contributes its own length-mixed root as one leaf."""
    value = BoundedListFieldProgressive(
        A=Uint16(0xABCD),
        B=Uint16List1024(data=(Uint16(1), Uint16(2), Uint16(3))),
    )
    # The field's own root: its data padded to the 64-chunk capacity, then the element count.
    field_b = h(merge(pad(b"\x01\x00\x02\x00\x03\x00"), Z[0:6]), pad(b"\x03"))
    expected_leaves = [pad(b"\xcd\xab"), ZERO_ROOT, field_b]
    assert hash_tree_root(value) == expected_progressive_container_root(expected_leaves, [1, 0, 1])


def test_hash_tree_root_progressive_container_with_progressive_list_field() -> None:
    """A progressive list field contributes its data root with the element count mixed in."""
    value = ProgressiveListFieldProgressive(
        A=Uint16(0xABCD),
        B=Uint16ProgressiveList(data=[Uint16(1), Uint16(2), Uint16(3)]),
    )
    field_b = h(h(pad(b"\x01\x00\x02\x00\x03\x00"), Z[0]), pad(b"\x03"))
    assert hash_tree_root(value) == expected_progressive_container_root(
        [pad(b"\xcd\xab"), field_b], [1, 1]
    )


def test_hash_tree_root_progressive_container_with_empty_progressive_list_field() -> None:
    """An empty progressive list field contributes the zero terminator with a zero count."""
    value = ProgressiveListFieldProgressive(A=Uint16(0xABCD), B=Uint16ProgressiveList(data=()))
    field_b = h(ZERO_ROOT, pad(b"\x00"))
    assert hash_tree_root(value) == expected_progressive_container_root(
        [pad(b"\xcd\xab"), field_b], [1, 1]
    )


def test_hash_tree_root_progressive_container_with_progressive_bitlist_field() -> None:
    """A progressive bitlist field contributes its data root with the bit count mixed in."""
    value = ProgressiveBitListFieldProgressive(
        A=Uint8(0xFF), B=ProgressiveBitList(data=_bools(0, 1, 0))
    )
    field_b = h(h(pad(b"\x02"), Z[0]), pad(b"\x03"))
    assert hash_tree_root(value) == expected_progressive_container_root(
        [pad(b"\xff"), ZERO_ROOT, field_b], [1, 0, 1]
    )


def test_hash_tree_root_progressive_container_inside_a_progressive_container() -> None:
    """A nested progressive field hands its own layout-mixed root up as one leaf."""
    inner = GappedProgressive(A=Uint16(0x1234), B=Uint8(0x56))
    inner_root = expected_progressive_container_root(
        [pad(b"\x34\x12"), ZERO_ROOT, pad(b"\x56")], [1, 0, 1]
    )
    value = NestedProgressive(A=Uint8(1), B=inner)
    assert hash_tree_root(value) == expected_progressive_container_root(
        [pad(b"\x01"), ZERO_ROOT, inner_root], [1, 0, 1]
    )


def test_hash_tree_root_bounded_list_of_progressive_containers() -> None:
    """Progressive containers are composite elements: each contributes one leaf."""
    element_roots = [
        expected_progressive_container_root(
            [pad(bytes([side])), ZERO_ROOT, pad(bytes([color]))], [1, 0, 1]
        )
        for side, color in ((1, 2), (3, 4))
    ]
    value = GappedList4(
        data=[
            GappedProgressive(A=Uint16(1), B=Uint8(2)),
            GappedProgressive(A=Uint16(3), B=Uint8(4)),
        ]
    )
    # Two leaves in a four-element capacity, then the element count.
    assert hash_tree_root(value) == h(h(h(element_roots[0], element_roots[1]), Z[1]), pad(b"\x02"))


def test_hash_tree_root_progressive_list_of_progressive_containers() -> None:
    """The progressive list places the same element roots on the spine instead."""
    element_roots = [
        expected_progressive_container_root(
            [pad(bytes([side])), ZERO_ROOT, pad(bytes([color]))], [1, 0, 1]
        )
        for side, color in ((1, 2), (3, 4))
    ]
    value = GappedProgressiveList(
        data=[
            GappedProgressive(A=Uint16(1), B=Uint8(2)),
            GappedProgressive(A=Uint16(3), B=Uint8(4)),
        ]
    )
    assert hash_tree_root(value) == h(naive_merkleize_progressive(element_roots), pad(b"\x02"))


def test_hash_tree_root_container_holding_a_progressive_container() -> None:
    """An ordinary container merkleizes the progressive field's root as an ordinary leaf."""
    inner_root = expected_progressive_container_root(
        [pad(b"\x34\x12"), ZERO_ROOT, pad(b"\x56")], [1, 0, 1]
    )
    value = ContainerWithProgressive(
        A=Uint8(1), B=GappedProgressive(A=Uint16(0x1234), B=Uint8(0x56))
    )
    assert hash_tree_root(value) == h(pad(b"\x01"), inner_root)


def test_progressive_container_field_positions_are_stable_across_layouts() -> None:
    """Two layouts sharing a position put that field's leaf at the very same index."""
    square = GappedProgressive(A=Uint16(0x1234), B=Uint8(0x56))
    circle = LeadingGapProgressive(A=Uint16(0x1234), B=Uint8(0x56))
    color_leaf = pad(b"\x56")
    # The leaf lists are written out position by position, from each layout's bits.
    square_leaves = [pad(b"\x34\x12"), ZERO_ROOT, color_leaf]
    circle_leaves = [ZERO_ROOT, pad(b"\x34\x12"), color_leaf]
    # The shared field occupies index 2 of both lists, so its position in the tree is the same.
    assert square_leaves[2] == circle_leaves[2] == color_leaf
    assert hash_tree_root(square) == expected_progressive_container_root(square_leaves, [1, 0, 1])
    assert hash_tree_root(circle) == expected_progressive_container_root(circle_leaves, [0, 1, 1])
    # The bytes cannot tell the two shapes apart; only the mixed-in layout can.
    assert square.encode_bytes() == circle.encode_bytes()
    assert hash_tree_root(square) != hash_tree_root(circle)


def test_progressive_container_gap_and_zero_field_share_leaves_but_not_roots() -> None:
    """A dropped field and a field holding zero build one tree, and the layout separates them."""
    # A zero Uint8 roots to the zero chunk, so both shapes present the same three leaves.
    with_zero_field = ThreeSetProgressive(A=Uint8(1), B=Uint8(0), C=Uint8(0))
    with_gap = MiddleGapProgressive(A=Uint8(1), C=Uint8(0))
    shared_leaves = [pad(b"\x01"), ZERO_ROOT, ZERO_ROOT]
    shared_data_root = naive_merkleize_progressive(shared_leaves)
    assert hash_tree_root(with_zero_field) == h(shared_data_root, pad(b"\x07"))
    assert hash_tree_root(with_gap) == h(shared_data_root, pad(b"\x05"))
    assert hash_tree_root(with_zero_field) != hash_tree_root(with_gap)


def test_progressive_and_bounded_container_share_bytes_but_not_roots() -> None:
    """The two struct shapes serialize identically and merkleize differently."""
    progressive = ThreeSetProgressive(A=Uint8(1), B=Uint8(2), C=Uint8(3))
    bounded = ThreeByteContainer(A=Uint8(1), B=Uint8(2), C=Uint8(3))
    leaves = [pad(b"\x01"), pad(b"\x02"), pad(b"\x03")]
    assert progressive.encode_bytes() == bounded.encode_bytes()
    # The bounded shape hashes a width-four tree.
    # The progressive shape hashes a spine of three leaves.
    # It mixes its layout in on top of that.
    assert hash_tree_root(bounded) == h(h(leaves[0], leaves[1]), h(leaves[2], Z[0]))
    assert hash_tree_root(progressive) == h(naive_merkleize_progressive(leaves), pad(b"\x07"))
    assert hash_tree_root(bounded) != hash_tree_root(progressive)


memo_in_force = pytest.mark.skipif(
    roots.PARANOID_ROOTS,
    reason="PARANOID_ROOTS recomputes every remembered root, which is the behaviour "
    + "this test observes the absence of",
)
"""Marks a test that observes the memo being reused, which paranoid mode suspends."""


INTERIOR_GAP_LEAVES = [pad(b"\x34\x12"), ZERO_ROOT, pad(b"\x56")]
"""The two fields of the tests below at positions 0 and 2, as (1, 0, 1) places them."""

LEADING_GAP_LEAVES = [ZERO_ROOT, pad(b"\x34\x12"), pad(b"\x56")]
"""The same two fields at positions 1 and 2, as (0, 1, 1) places them."""


def test_a_root_follows_a_layout_reassigned_after_the_type_was_declared() -> None:
    """A layout is a class attribute, so it can be rewritten, and the root has to follow."""
    # The layout decides where each field is hashed and the word mixed in on top.
    # Neither is a property of the type: a type only holds whatever layout it is holding now.

    class Reassigned(ProgressiveContainer):
        ACTIVE_FIELDS = (1, 0, 1)

        head: Uint16
        tail: Uint8

    before = hash_tree_root(Reassigned(head=Uint16(0x1234), tail=Uint8(0x56)))
    assert before == expected_progressive_container_root(INTERIOR_GAP_LEAVES, (1, 0, 1))

    # The same two fields, each moved one position along.
    Reassigned.ACTIVE_FIELDS = (0, 1, 1)
    # A value built after the rewrite, because one rooted before it answers from its memo.
    fresh = Reassigned(head=Uint16(0x1234), tail=Uint8(0x56))
    assert hash_tree_root(fresh) == expected_progressive_container_root(
        LEADING_GAP_LEAVES, (0, 1, 1)
    )
    assert hash_tree_root(fresh) != before


@pytest.mark.parametrize(
    "reassigned_layout, expected_counts",
    [
        pytest.param(
            (1, 1, 1), "sets 3 positions, and the struct declares 2", id="position_gained"
        ),
        pytest.param((1,), "sets 1 positions, and the struct declares 2", id="position_lost"),
    ],
)
def test_a_layout_that_stopped_pairing_with_the_fields_is_refused_by_name(
    reassigned_layout: tuple[int, ...], expected_counts: str
) -> None:
    """A declaration checks this pairing; merkleization cannot assume it still holds."""
    # A rewritten layout can set more positions than there are fields, or fewer.
    # Pairing them off regardless would hash a field at a position no declaration gave it.

    class Drifted(ProgressiveContainer):
        ACTIVE_FIELDS = (1, 0, 1)

        head: Uint16
        tail: Uint8

    Drifted.ACTIVE_FIELDS = reassigned_layout
    with pytest.raises(
        SSZTypeError,
        match=rf"^the layout {expected_counts}$",
    ) as exception_info:
        hash_tree_root(Drifted(head=Uint16(1), tail=Uint8(2)))
    # The refusal carries the layout in force, not the one the declaration approved.
    assert exception_info.value.fields["layout"] == reassigned_layout


def test_a_layout_and_its_field_names_settle_the_positions_by_themselves() -> None:
    """Two shapes agreeing on both root alike; two agreeing on the name alone do not."""
    # A root is the field positions and the layout word.
    # A type name enters neither.
    # Two shapes over one layout and one field list are meant to reach one root.

    class LeftShape(ProgressiveContainer):
        ACTIVE_FIELDS = (1, 0, 1)

        head: Uint16
        tail: Uint8

    class RightShape(ProgressiveContainer):
        ACTIVE_FIELDS = (1, 0, 1)

        head: Uint16
        tail: Uint8

    interior_gap = expected_progressive_container_root(INTERIOR_GAP_LEAVES, (1, 0, 1))
    assert hash_tree_root(LeftShape(head=Uint16(0x1234), tail=Uint8(0x56))) == interior_gap
    assert hash_tree_root(RightShape(head=Uint16(0x1234), tail=Uint8(0x56))) == interior_gap
    # Whatever two shapes share, the field values still decide the root.
    assert hash_tree_root(RightShape(head=Uint16(0x1234), tail=Uint8(0x57))) != interior_gap

    class OtherLayout(ProgressiveContainer):
        """The same field names over a layout that places them one position along."""

        ACTIVE_FIELDS = (0, 1, 1)

        head: Uint16
        tail: Uint8

    # One name over two layouts, the field names held identical, so only the layout differs.
    LeftShape.__name__ = OtherLayout.__name__ = "Shape"
    value = LeftShape(head=Uint16(0x1234), tail=Uint8(0x56))
    twin = OtherLayout(head=Uint16(0x1234), tail=Uint8(0x56))
    # The bytes cannot tell the two apart, exactly as for the two shapes of the EIP.
    assert value.encode_bytes() == twin.encode_bytes()
    assert hash_tree_root(value) == interior_gap
    assert hash_tree_root(twin) == expected_progressive_container_root(
        LEADING_GAP_LEAVES, (0, 1, 1)
    )


@memo_in_force
def test_a_layout_rewritten_under_a_rooted_value_leaves_a_stale_root() -> None:
    """
    A known limitation, pinned rather than hidden.

    A remembered root is kept under a witness of the value: its version and its fields.
    The layout of the type holding it is not in there, so a layout rewritten afterwards is
    invisible to the memo, and the value goes on answering with the root it took under the
    layout it no longer has. A value built after the rewrite roots correctly.
    """

    class Restaled(ProgressiveContainer):
        ACTIVE_FIELDS = (1, 0, 1)

        head: Uint16
        tail: Uint8

    value = Restaled(head=Uint16(0x1234), tail=Uint8(0x56))
    remembered = hash_tree_root(value)

    Restaled.ACTIVE_FIELDS = (0, 1, 1)
    correct = expected_progressive_container_root(LEADING_GAP_LEAVES, (0, 1, 1))
    assert hash_tree_root(value) == remembered != correct
    assert hash_tree_root(Restaled(head=Uint16(0x1234), tail=Uint8(0x56))) == correct


@memo_in_force
def test_a_capacity_rewritten_under_a_rooted_value_leaves_a_stale_root() -> None:
    """
    The same limitation as the layout above, on the other input a type contributes.

    A capacity sets the width of the tree, so rewriting it moves the root exactly as
    rewriting a layout does.
    The witness holds neither, so a value rooted before the rewrite keeps answering with
    the tree it no longer has:

        Restaled bounded at 4  ->  a two-level tree
        rewritten to 64        ->  a six-level tree, for values built afterwards

    Pinned here so the two halves of one limitation are documented together.
    """

    class Restaled(List[Uint64]):
        LIMIT = 4

    value = Restaled(data=(Uint64(1), Uint64(2)))
    remembered = hash_tree_root(value)

    Restaled.LIMIT = 64
    correct = hash_tree_root(Restaled(data=(Uint64(1), Uint64(2))))
    assert hash_tree_root(value) == remembered != correct


@memo_in_force
def test_a_leaf_typed_slot_holding_a_value_with_an_interior_leaves_a_stale_root() -> None:
    """
    The residual risk in dropping leaf fields from the witness, pinned rather than hidden.

    A witness skips the fields whose declared type is an immutable leaf, since eight of
    them on each of sixty-four validators would cost five hundred reads for nothing.
    That rests on a slot holding what it declares, which validation guarantees and
    unvalidated construction does not:

        declared  state_root: Bytes32   ->  skipped, having no interior to change
        actual    a container           ->  an interior the witness never looks at

    So a mutation inside such a value moves the root and never reaches the witness.
    A value built the ordinary way cannot reach this, the declared type being enforced.
    """

    class Inner(Container):
        x: Uint64

    class Header(Container):
        slot: Uint64
        state_root: Bytes32

    inner = Inner(x=Uint64(1))
    value = Header.model_construct(slot=Uint64(9), state_root=inner)
    remembered = hash_tree_root(value)

    inner.x = Uint64(2)
    correct = hash_tree_root(Header.model_construct(slot=Uint64(9), state_root=Inner(x=Uint64(2))))
    assert hash_tree_root(value) == remembered != correct


def test_paranoid_roots_catches_a_root_left_behind_by_a_rewritten_layout(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The mode that recomputes every remembered root sees the layout the witness cannot."""

    class Repinned(ProgressiveContainer):
        ACTIVE_FIELDS = (1, 0, 1)

        head: Uint16
        tail: Uint8

    value = Repinned(head=Uint16(0x1234), tail=Uint8(0x56))
    hash_tree_root(value)

    Repinned.ACTIVE_FIELDS = (0, 1, 1)
    monkeypatch.setattr(roots, "PARANOID_ROOTS", True)
    with pytest.raises(SSZValueError, match=r"^stale remembered root for Repinned$"):
        hash_tree_root(value)


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
    assert str(exception_info.value) == (f"{type(unsupported_value).__name__} has no Merkle layout")


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


class UnionSquare(ProgressiveContainer):
    """EIP-7495's Square, used as the first option of the EIP-8016 example union."""

    ACTIVE_FIELDS = (1, 0, 1)

    side: Uint16
    color: Uint8


class UnionCircle(ProgressiveContainer):
    """EIP-7495's Circle, the second option: it shares position 2 with Square."""

    ACTIVE_FIELDS = (0, 1, 1)

    radius: Uint16
    color: Uint8


class UnionShape(CompatibleUnion):
    """EIP-8016's own example, extended with the highest legal selector over Square."""

    OPTIONS = {1: UnionSquare, 2: UnionCircle, 127: UnionSquare}


class UnionSquareProgressiveList(ProgressiveList[UnionSquare]):
    """Progressive list of Square, a variable-size union option."""


class UnionCircleProgressiveList(ProgressiveList[UnionCircle]):
    """Progressive list of Circle: compatible with the Square list, element for element."""


class UnionShapeList(CompatibleUnion):
    """Union whose two options differ only in the element type of a progressive list."""

    OPTIONS = {1: UnionSquareProgressiveList, 2: UnionCircleProgressiveList}


class UnionSquareOnly(CompatibleUnion):
    """Single-option union, so a union of unions has a second member to hold."""

    OPTIONS = {5: UnionSquare}


class NestedUnionShape(CompatibleUnion):
    """Union of unions: each option is itself a compatible union."""

    OPTIONS = {1: UnionShape, 2: UnionSquareOnly}


class UnionShapeHolder(Container):
    """Ordinary container whose second field is a union."""

    tag: Uint8
    body: UnionShape


class UnionShapeProgressiveHolder(ProgressiveContainer):
    """Progressive container whose second field is a union, behind a gap."""

    ACTIVE_FIELDS = (1, 0, 1)

    tag: Uint8
    body: UnionShape


SQUARE_LEAVES = [pad(b"\x34\x12"), ZERO_ROOT, pad(b"\x42")]
"""Square(side=0x1234, color=0x42) as one leaf per position of the layout [1, 0, 1]."""

CIRCLE_LEAVES = [ZERO_ROOT, pad(b"\x34\x12"), pad(b"\x42")]
"""Circle(radius=0x1234, color=0x42) as one leaf per position of the layout [0, 1, 1]."""


def test_hash_tree_root_compatible_union_square_option() -> None:
    """The root of the option alone, with the selector hashed in above it."""
    value = UnionShape(selector=Uint8(1), data=UnionSquare(side=Uint16(0x1234), color=Uint8(0x42)))
    square_root = expected_progressive_container_root(SQUARE_LEAVES, [1, 0, 1])
    assert hash_tree_root(value) == h(square_root, pad(b"\x01"))


def test_hash_tree_root_compatible_union_circle_option() -> None:
    """The second option roots through its own layout, then through its own selector."""
    value = UnionShape(
        selector=Uint8(2), data=UnionCircle(radius=Uint16(0x1234), color=Uint8(0x42))
    )
    circle_root = expected_progressive_container_root(CIRCLE_LEAVES, [0, 1, 1])
    assert hash_tree_root(value) == h(circle_root, pad(b"\x02"))


def test_hash_tree_root_compatible_union_highest_selector() -> None:
    """Selector 127 packs into the same word as any other, with bit seven of byte zero set."""
    value = UnionShape(
        selector=Uint8(127), data=UnionSquare(side=Uint16(0x1234), color=Uint8(0x42))
    )
    square_root = expected_progressive_container_root(SQUARE_LEAVES, [1, 0, 1])
    assert hash_tree_root(value) == h(square_root, pad(b"\x7f"))


def test_hash_tree_root_compatible_union_is_the_option_root_with_the_selector_mixed_in() -> None:
    """The definition, stated as such: mix_in_selector over the root of the held value."""
    square = UnionSquare(side=Uint16(0x1234), color=Uint8(0x42))
    value = UnionShape(selector=Uint8(1), data=square)
    assert hash_tree_root(value) == mix_in_selector(hash_tree_root(square), 1)
    # The union contributes nothing else: no length, no option count, no layout word.
    assert hash_tree_root(value) != hash_tree_root(square)


def test_hash_tree_root_compatible_union_same_option_under_two_selectors() -> None:
    """One payload under two selectors yields two roots, though the trees below are one."""
    square = UnionSquare(side=Uint16(0x1234), color=Uint8(0x42))
    under_one = UnionShape(selector=Uint8(1), data=square)
    under_127 = UnionShape(selector=Uint8(127), data=square)
    assert hash_tree_root(under_one.data) == hash_tree_root(under_127.data)
    assert hash_tree_root(under_one) != hash_tree_root(under_127)


def test_hash_tree_root_compatible_union_empty_list_options_collide_below_the_selector() -> None:
    """
    The security consideration of EIP-8016, in full.

    Two options differ only in the element type of a progressive list. An empty list
    roots the same whatever it would have held, so the two payloads present identical
    inner roots. Only the selector separates the two union values, which is exactly what
    the mix-in is there for.
    """
    empty_squares = UnionSquareProgressiveList(data=[])
    empty_circles = UnionCircleProgressiveList(data=[])
    # Both are the zero terminator with a zero count mixed in, reached by two paths.
    assert hash_tree_root(empty_squares) == h(ZERO_ROOT, pad(b"\x00"))
    assert hash_tree_root(empty_squares) == hash_tree_root(empty_circles)

    under_one = UnionShapeList(selector=Uint8(1), data=empty_squares)
    under_two = UnionShapeList(selector=Uint8(2), data=empty_circles)
    # The wire bytes are one byte each and differ only in that byte, as the roots do.
    assert under_one.encode_bytes().hex() == "01"
    assert under_two.encode_bytes().hex() == "02"
    assert hash_tree_root(under_one) == h(hash_tree_root(empty_squares), pad(b"\x01"))
    assert hash_tree_root(under_two) == h(hash_tree_root(empty_circles), pad(b"\x02"))
    assert hash_tree_root(under_one) != hash_tree_root(under_two)


def test_hash_tree_root_compatible_union_populated_list_option() -> None:
    """A populated option contributes its own length-mixed root before the selector."""
    square_root = expected_progressive_container_root(SQUARE_LEAVES, [1, 0, 1])
    value = UnionShapeList(
        selector=Uint8(1),
        data=UnionSquareProgressiveList(data=[UnionSquare(side=Uint16(0x1234), color=Uint8(0x42))]),
    )
    # One composite leaf on the spine, then the element count, then the selector.
    list_root = mix_in_length(naive_merkleize_progressive([square_root]), 1)
    assert hash_tree_root(value) == h(list_root, pad(b"\x01"))


def test_hash_tree_root_compatible_union_of_unions() -> None:
    """Each level mixes in its own selector, innermost first."""
    value = NestedUnionShape(
        selector=Uint8(1),
        data=UnionShape(
            selector=Uint8(2), data=UnionCircle(radius=Uint16(0x1234), color=Uint8(0x42))
        ),
    )
    circle_root = expected_progressive_container_root(CIRCLE_LEAVES, [0, 1, 1])
    assert hash_tree_root(value) == h(h(circle_root, pad(b"\x02")), pad(b"\x01"))


def test_hash_tree_root_container_holding_a_compatible_union() -> None:
    """A container merkleizes the union's selector-mixed root as an ordinary leaf."""
    square = UnionSquare(side=Uint16(0x1234), color=Uint8(0x42))
    value = UnionShapeHolder(tag=Uint8(0xFF), body=UnionShape(selector=Uint8(1), data=square))
    union_root = h(expected_progressive_container_root(SQUARE_LEAVES, [1, 0, 1]), pad(b"\x01"))
    assert hash_tree_root(value) == h(pad(b"\xff"), union_root)


def test_hash_tree_root_progressive_container_holding_a_compatible_union() -> None:
    """The union's root is the leaf at position 2, and the gap keeps its zero leaf."""
    square = UnionSquare(side=Uint16(0x1234), color=Uint8(0x42))
    value = UnionShapeProgressiveHolder(
        tag=Uint8(0xFF), body=UnionShape(selector=Uint8(1), data=square)
    )
    union_root = h(expected_progressive_container_root(SQUARE_LEAVES, [1, 0, 1]), pad(b"\x01"))
    assert hash_tree_root(value) == expected_progressive_container_root(
        [pad(b"\xff"), ZERO_ROOT, union_root], [1, 0, 1]
    )


def test_compatible_union_options_share_their_bytes_and_not_their_roots() -> None:
    """The two options encode to the same payload and merkleize under different selectors."""
    square = UnionShape(selector=Uint8(1), data=UnionSquare(side=Uint16(0x1234), color=Uint8(0x42)))
    circle = UnionShape(
        selector=Uint8(2), data=UnionCircle(radius=Uint16(0x1234), color=Uint8(0x42))
    )
    assert square.encode_bytes()[1:] == circle.encode_bytes()[1:]
    assert hash_tree_root(square) != hash_tree_root(circle)


class Uint8Vector4(Vector[Uint8]):
    """Vector of four Uint8, four of the thirty-two bytes a single chunk holds."""

    LENGTH = 4


class Uint8List4(List[Uint8]):
    """List of at most four Uint8, so its data tree is one chunk deep."""

    LIMIT = 4


class ByteList8(ByteList):
    """Byte list with an eight-byte capacity, so its data tree is one chunk deep."""

    LIMIT = 8


class Bytes48Vector4(Vector[Bytes48]):
    """Vector of four 48-byte arrays, so the vector's tree is four two-chunk leaves."""

    LENGTH = 4


class Roster(Container):
    """A fixed set of fingerprints, then the one that stands in for all of them."""

    fingerprints: Bytes48Vector4
    combined: Bytes48


ALL_ZERO_DEFAULT_ROOT = "0x" + "00" * 32
"""Root of every default that occupies exactly one zero chunk and mixes nothing in."""

ZERO_PAIR_DEFAULT_ROOT = "0xf5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b"
"""Root of two zero nodes hashed together, which two unrelated defaults both reach."""


def default_root_hex(value: SSZType) -> str:
    """Return the hash tree root of a value as a 0x-prefixed hex string."""
    return "0x" + hash_tree_root(value).hex()


@pytest.mark.parametrize(
    "default_value",
    [
        # A uint of any width is zero, and its little-endian bytes pad out to one zero chunk.
        pytest.param(Uint8(), id="uint8"),
        pytest.param(Uint64(), id="uint64"),
        # A uint256 fills the chunk exactly, and every byte of it is still zero.
        pytest.param(Uint256(), id="uint256"),
        # False packs to one zero byte, padded to the same chunk.
        pytest.param(Boolean(), id="boolean"),
        # Eight clear bits pack to one zero byte; no length is mixed in for a bitvector.
        pytest.param(BitVector8(), id="bitvector_8"),
        # Four zero Uint8 pack to four zero bytes inside the one chunk they share.
        pytest.param(Uint8Vector4(), id="vector_uint8_4"),
    ],
)
def test_default_root_is_the_zero_chunk_for_a_single_chunk_fixed_shape(
    default_value: SSZType,
) -> None:
    """A default that fits one chunk and mixes nothing in roots to that all-zero chunk."""
    assert default_root_hex(default_value) == ALL_ZERO_DEFAULT_ROOT
    assert hash_tree_root(default_value) == ZERO_ROOT


def test_default_root_of_a_two_chunk_byte_array() -> None:
    """A 48-byte default is two zero chunks, hashed together into one node."""
    # 48 zero bytes span two chunks, the second half-padded, and both are all zero.
    assert hash_tree_root(Bytes48()) == h(ZERO_ROOT, ZERO_ROOT)
    assert default_root_hex(Bytes48()) == ZERO_PAIR_DEFAULT_ROOT


@pytest.mark.parametrize(
    "default_value",
    [
        # A bounded list under a one-chunk capacity: zero data chunks, then a zero count.
        pytest.param(Uint8List4(), id="list_uint8_4"),
        pytest.param(BitList8(), id="bitlist_8"),
        pytest.param(ByteList8(), id="byte_list_8"),
        # The unbounded shapes terminate their spine with the plain zero leaf instead.
        pytest.param(Uint8ProgressiveList(), id="progressive_list_uint8"),
        pytest.param(ProgressiveBitList(), id="progressive_bitlist"),
    ],
)
def test_default_root_of_an_empty_variable_size_shape(default_value: SSZType) -> None:
    """An empty default is the zero data root with a zero length mixed in on top."""
    assert hash_tree_root(default_value) == mix_in_length(ZERO_ROOT, 0)
    assert default_root_hex(default_value) == ZERO_PAIR_DEFAULT_ROOT


def test_two_unrelated_defaults_reach_one_root_by_two_different_paths() -> None:
    """
    The 48-byte array and the empty list share a root, and nothing links the two.

    - The byte array is two zero chunks hashed together, with no mix-in at all.
    - The empty list is the zero node with a zero length mixed into it.

    Both land on h(0, 0), which is why each is pinned on its own above rather than
    through one shared constant.
    """
    assert hash_tree_root(Bytes48()) == h(ZERO_ROOT, ZERO_ROOT)
    assert hash_tree_root(Uint8List4()) == mix_in_length(ZERO_ROOT, 0)
    assert hash_tree_root(Bytes48()) == hash_tree_root(Uint8List4()) == Z[1]


def test_default_root_of_a_container_of_byte_arrays() -> None:
    """A roster's default: four zeroed fingerprints in a vector, then one zeroed one."""
    # Each 48-byte default roots to h(0, 0).
    # The vector hashes four of those into a width-four tree.
    # The container hashes that against the combined one's root.
    fingerprint_root = h(ZERO_ROOT, ZERO_ROOT)
    fingerprints_root = h(
        h(fingerprint_root, fingerprint_root), h(fingerprint_root, fingerprint_root)
    )
    assert hash_tree_root(Roster.default()) == h(fingerprints_root, fingerprint_root)
    assert default_root_hex(Roster.default()) == (
        "0xbe9a6010451d97ebf5a77af290008a2d79750bb0c4e3aa947e96438a1cfcc5b0"
    )
    # The default is an ordinary value, so it survives an encode and decode round trip.
    assert Roster.decode_bytes(Roster.default().encode_bytes()) == Roster.default()


def test_default_root_of_a_progressive_container_with_a_gap() -> None:
    """A gapped layout's default: three zero leaves, and the layout word mixed in."""
    # Every field default roots to the zero chunk whatever its width.
    # The leaves are indistinguishable from the gap's own zero leaf.
    # Only the layout word separates them.
    assert GappedProgressive.ACTIVE_FIELDS == (1, 0, 1)
    assert hash_tree_root(GappedProgressive.default()) == expected_progressive_container_root(
        [ZERO_ROOT, ZERO_ROOT, ZERO_ROOT], [1, 0, 1]
    )
    assert default_root_hex(GappedProgressive.default()) == (
        "0x4207c70a4a3b37c984824376528c02dff67b022725f27b7ef21f461aa2baab82"
    )
    assert GappedProgressive.decode_bytes(GappedProgressive.default().encode_bytes()) == (
        GappedProgressive.default()
    )


def test_layout_of_a_container_takes_one_leaf_per_field() -> None:
    """A struct takes one leaf per field, bounded by the field count, with no word mixed in."""
    value = Small(A=Uint16(1), B=Uint16(2))
    layout = merkle_layout(value)
    assert layout.nested == (value.A, value.B)
    assert layout.packed == ()
    assert layout.limit == 2
    assert layout.mixin is None
    assert layout.leaf_count == 2
    assert layout_chunks(layout) == [pad(b"\x01\x00"), pad(b"\x02\x00")]


def test_layout_of_a_bounded_list_packs_its_elements_and_mixes_the_count_in() -> None:
    """Basic elements share a chunk.
    The declared capacity bounds the tree over them.
    """
    value = Uint16List32(data=(Uint16(1), Uint16(2)))
    layout = merkle_layout(value)
    # Packed leaves are plain 32-byte strings now, since nothing reads them but the hash.
    assert layout.packed == (b"\x01\x00\x02\x00".ljust(32, b"\x00"),)
    assert layout.nested is None
    # Two elements fill four bytes of one chunk.
    # That chunk is the only leaf there is.
    assert layout.leaf_count == 1
    # A capacity of 32 two-byte elements packs 16 per chunk.
    # The tree therefore holds two chunks of capacity.
    assert layout.limit == 2
    assert layout.mixin == pad(b"\x02")


def test_layout_of_a_progressive_container_keeps_a_leaf_for_every_position() -> None:
    """A cleared position keeps a leaf of its own, holding the all-zero chunk."""
    value = GappedProgressive(A=Uint16(0x1234), B=Uint8(0x56))
    layout = merkle_layout(value)
    assert layout.nested == (value.A, None, value.B)
    assert layout.leaf_count == 3
    # A spine grows with the data.
    # No declared capacity bounds it.
    assert layout.limit is None
    assert layout.mixin == active_fields_word((1, 0, 1))
    assert layout_chunks(layout) == [pad(b"\x34\x12"), ZERO_ROOT, pad(b"\x56")]


def test_a_layout_roots_only_the_leaves_a_range_asks_for() -> None:
    """A range keeps a proof from hashing the whole tree to reach one part of it."""
    value = ChunkVector3(data=(sample_chunks[0], sample_chunks[1], sample_chunks[2]))
    layout = merkle_layout(value)
    assert layout.leaf_count == 3
    assert layout_chunks(layout, 1, 3) == [sample_chunks[1], sample_chunks[2]]
    # A range starting past the last leaf is empty rather than an error.
    assert layout_chunks(layout, 3) == []


class GappedRunProgressive(ProgressiveContainer):
    """Two fields either side of a run of gaps, so one value can stand at both ends."""

    ACTIVE_FIELDS = (1, 0, 0, 0, 1)

    A: Chunk
    B: Chunk


def rooted_from_cold(vector: FixedVector4) -> Root:
    """Root these contents through a value sharing no element with the one given."""
    return hash_tree_root(FixedVector4.decode_bytes(vector.encode_bytes()))


def test_a_vector_of_one_repeated_value_roots_that_value_at_every_position() -> None:
    """One value at every position is one root at every leaf, and nothing else."""
    # This is the shape a vector's own default takes, which is what makes it worth stating.
    assert Bytes48Vector4().data[0] is Bytes48Vector4().data[3]

    fingerprint = Bytes48(b"\x03" * 48)
    uniform = Bytes48Vector4(data=[fingerprint] * 4)
    layout = merkle_layout(uniform)
    assert layout.nested is not None
    assert all(element is fingerprint for element in layout.nested)
    leaf = hash_tree_root(fingerprint)
    assert layout_chunks(layout) == [leaf] * 4
    assert hash_tree_root(uniform) == perfect_tree_root([leaf] * 4, 4)
    # Four equal values that are not one value reach the very same tree, leaf for leaf.
    distinct = Bytes48Vector4(data=[Bytes48(b"\x03" * 48) for _ in range(4)])
    assert distinct.data[0] is not distinct.data[3]
    assert hash_tree_root(distinct) == hash_tree_root(uniform)


def test_a_repeat_broken_in_the_middle_roots_every_position_on_its_own() -> None:
    """Ends that match say nothing about the middle: [a, b, a] is two roots, not one."""
    first, middle = sample_chunks[1], sample_chunks[2]
    value = ChunkVector3(data=[first, middle, first])
    layout = merkle_layout(value)
    # The ends are one value, so the whole range is walked as a run of one.
    assert layout.nested is not None and layout.nested[0] is layout.nested[2] is first
    # A chunk is its own root, so the leaves are the elements verbatim.
    assert layout_chunks(layout) == [first, middle, first]
    assert hash_tree_root(value) == perfect_tree_root([first, middle, first], 4)


def test_a_progressive_layout_holding_one_value_twice_keeps_its_gaps_zero() -> None:
    """A gap holds nothing, so a run of them takes neither neighbour's root."""
    fingerprint = Chunk(b"\x07" * 32)
    value = GappedRunProgressive(A=fingerprint, B=fingerprint)
    layout = merkle_layout(value)
    assert layout.nested == (fingerprint, None, None, None, fingerprint)
    expected_leaves = [fingerprint, ZERO_ROOT, ZERO_ROOT, ZERO_ROOT, fingerprint]
    assert layout_chunks(layout) == expected_leaves
    assert hash_tree_root(value) == expected_progressive_container_root(
        expected_leaves, GappedRunProgressive.ACTIVE_FIELDS
    )


def test_a_repeated_element_and_a_merely_equal_one_each_follow_the_value_standing_there() -> None:
    """
    One value at two positions is one root; two equal values are two roots that can part.

    The ends hold one object, so the whole sequence is walked as a run. Inside it stands a
    second value, equal to that one today and free to stop being so.
    """
    shared = Fixed(A=Uint8(1), B=Uint64(2), C=Uint32(3))
    twin = Fixed(A=Uint8(1), B=Uint64(2), C=Uint32(3))
    vector = FixedVector4(data=[shared, twin, twin, shared])
    assert vector[0] is vector[3] is shared
    assert twin == shared and twin is not shared
    before = hash_tree_root(vector)
    assert before == rooted_from_cold(vector)

    # The two equal values part company: only the one standing at positions 1 and 2 moves.
    twin.C = Uint32(9)
    assert hash_tree_root(vector) == rooted_from_cold(vector) != before

    # A write through the collection reaches the value held at both ends.
    parted = hash_tree_root(vector)
    vector[0].A = Uint8(9)
    assert vector[3].A == Uint8(9)
    assert hash_tree_root(vector) == rooted_from_cold(vector) != parted


class Bytes1(ByteVector):
    """Byte array of one byte: the narrowest leaf a fixed byte array can be."""

    LENGTH = 1


class Bytes31(ByteVector):
    """Byte array one byte short of a chunk, still a single leaf."""

    LENGTH = 31


class Bytes32(ByteVector):
    """Byte array filling a chunk exactly, the last width that is still one leaf."""

    LENGTH = 32


class Bytes33(ByteVector):
    """Byte array one byte past a chunk: two leaves and a hash above them."""

    LENGTH = 33


class Uint512(BaseUint):
    """Uint wide enough that its encoding spans two leaves."""

    BITS = 512


class MyUint64(Uint64):
    """User subclass of a declared width, reached by inheritance rather than registration."""


class MyBoolean(Boolean):
    """User subclass of the boolean."""


class MyBytes32(Bytes32):
    """User subclass of a chunk-wide byte array."""


class MyBytes48(Bytes48):
    """User subclass of a byte array too wide to be one leaf."""


def root_the_long_way(value: object) -> Root:
    """Root a value by the general path alone, with no short circuit in front of it."""
    layout = merkle_layout(value)
    chunks = layout_chunks(layout)
    if layout.limit is None:
        root = merkleize_progressive(chunks)
    else:
        root = merkleize(chunks, layout.limit)
    return root if layout.mixin is None else h(root, layout.mixin)


def every_shape() -> list[object]:
    """One value per type the library merkleizes, at the widths and edges that matter."""
    uint_values: list[object] = [
        uint_type(number)
        for uint_type in (Uint8, Uint16, Uint32, Uint64, Uint128, Uint256, MyUint64, Uint512)
        for number in (0, 1, 2**uint_type.BITS - 1)
    ]
    boolean_values: list[object] = [
        boolean_type(state) for boolean_type in (Boolean, MyBoolean) for state in (False, True)
    ]
    # Widths on both sides of the chunk boundary, and exactly upon it.
    byte_array_values: list[object] = [
        byte_array_type(byte * byte_array_type.LENGTH)
        for byte_array_type in (Bytes1, Bytes31, Bytes32, Bytes33, Bytes48, Bytes96)
        for byte in (b"\x00", b"\xff", b"\x5a")
    ]
    byte_array_values += [
        Chunk.zero(),
        Root(bytes(range(32))),
        MyBytes32(b"\x01" * 32),
        MyBytes48(b"\x02" * 48),
    ]
    # Plain bytes are not an SSZ type, but the layout accepts them.
    # One chunk or many, the short circuit must agree with the layout.
    raw_byte_values: list[object] = [b"\x01", b"\xff" * 32, bytes(range(33)), bytes(range(96))]
    composite_values: list[object] = [
        ByteList10(data=b""),
        ByteList10(data=b"\x01\x02\x03"),
        ByteList50(data=b"\x07" * 50),
        BitVector1(data=(Boolean(True),)),
        BitVector9(data=tuple(Boolean(index % 2 == 0) for index in range(9))),
        BitList8(data=()),
        BitList8(data=(Boolean(True), Boolean(False), Boolean(True))),
        ProgressiveBitList(data=tuple(Boolean(index % 3 == 0) for index in range(100))),
        Uint16Vector2(data=(Uint16(1), Uint16(2))),
        ChunkVector3(data=tuple(sample_chunks[:3])),
        Uint16List32(data=()),
        Uint16List32(data=(Uint16(1), Uint16(2))),
        ChunkList32(data=(sample_chunks[0],)),
        Uint8ProgressiveList(data=()),
        Uint8ProgressiveList(data=tuple(Uint8(index) for index in range(100))),
        ChunkProgressiveList(data=tuple(sample_chunks[:3])),
        EmptyContainer(),
        SingleField(A=Uint8(9)),
        Fixed(A=Uint8(1), B=Uint64(2), C=Uint32(3)),
        Var(A=Uint16(1), B=Uint16List1024(data=(Uint16(2),)), C=Uint8(3)),
        FixedVector4.default(),
        OneFieldProgressive(A=Uint16(5)),
        GappedProgressive(A=Uint16(0x1234), B=Uint8(0x56)),
        UnionShape(selector=Uint8(1), data=UnionSquare(side=Uint16(7), color=Uint8(8))),
        UnionShape(selector=Uint8(2), data=UnionCircle(radius=Uint16(7), color=Uint8(8))),
    ]
    return uint_values + boolean_values + byte_array_values + raw_byte_values + composite_values


def shape_id(value: object) -> str:
    """Name a parametrized case by the head of its repr."""
    return repr(value)[:40]


@pytest.mark.parametrize("value", every_shape(), ids=shape_id)
def test_the_root_of_a_value_is_the_root_its_layout_describes(value: object) -> None:
    """The leaf rule exists in two places. This is what stops the two drifting."""
    assert hash_tree_root(value) == root_the_long_way(value)


def test_an_encoding_of_no_bytes_roots_to_the_zero_chunk_either_way() -> None:
    """The one width where the two forms reach the zero root by different routes."""
    assert hash_tree_root(b"") == ZERO_ROOT
    assert root_the_long_way(b"") == ZERO_ROOT


def test_a_plain_integer_is_still_rejected_by_the_dispatch() -> None:
    """A type that only looks like an integer must still fall through to the dispatch."""
    for not_an_ssz_type in (7, True, 2**512):
        with pytest.raises(SSZTypeError):
            hash_tree_root(not_an_ssz_type)


@pytest.mark.parametrize(
    "element_type",
    [Boolean, Uint8, Uint16, Uint32, Uint64, Uint128, Uint256],
    ids=lambda element_type: element_type.__name__,
)
@pytest.mark.parametrize("count", [0, 1, 3, 32, 33, 100])
def test_packing_basic_elements_agrees_with_encoding_each_one(
    element_type: type[BaseUint | Boolean], count: int
) -> None:
    """Batched packing is the per-element encoding, chunk for chunk."""
    span = element_type.MAX_VALUE if issubclass(element_type, BaseUint) else 1
    # Zero, one and the maximum are forced to the front.
    # A wide type is never packed only at values a narrow one also holds.
    elements = [element_type((index * 7919) % (span + 1)) for index in range(count)]
    elements[:3] = [element_type(0), element_type(1), element_type(span)][:count]

    assert _pack_basic_elements(elements, element_type.get_byte_length()) == _pack_bytes(
        b"".join(element.encode_bytes() for element in elements)
    )

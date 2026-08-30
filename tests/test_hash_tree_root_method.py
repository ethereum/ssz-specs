"""
Tests for the hash_tree_root method every SSZ type carries.

The roots themselves are pinned elsewhere, through the module-level function.
This file pins that the method reaches those same roots.
It does so for every family, and across mutation, so the two spellings cannot drift apart.
"""

from collections.abc import Sequence
from hashlib import sha256

import pytest
from hypothesis import given, strategies as st

import ssz
from ssz import (
    ZERO_ROOT,
    BitList,
    BitVector,
    Boolean,
    Byte,
    ByteList,
    ByteVector,
    Chunk,
    CompatibleUnion,
    Container,
    List,
    ProgressiveBitList,
    ProgressiveContainer,
    ProgressiveList,
    Root,
    SSZType,
    SSZTypeError,
    Uint8,
    Uint16,
    Uint32,
    Uint64,
    Uint128,
    Uint256,
    Vector,
    hash_tree_root,
)
from ssz.mixins import mix_in_active_fields, mix_in_length, mix_in_selector
from ssz.trees import merkleize, merkleize_progressive


def pad(payload: bytes) -> Root:
    """
    Right-pad a payload to the 32 bytes one leaf holds.

    Typed as a root rather than a chunk, so a padded leaf composes with the mix-in helpers.
    Those helpers take the node whose root is hashed against a word.
    """
    return Root(payload.ljust(32, b"\x00"))


def h(left: bytes, right: bytes) -> Root:
    """Pairwise SHA-256 of two nodes, for building an expected root by hand."""
    return Root(sha256(left + right).digest())


def nested_roots(values: Sequence[SSZType]) -> list[Chunk]:
    """One leaf per nested value, each the free function's root for that value."""
    return [Chunk(hash_tree_root(value)) for value in values]


class Bytes4(ByteVector):
    """A four-byte array: well inside the single chunk it packs into."""

    LENGTH = 4


class Bytes32(ByteVector):
    """A 32-byte array: exactly one chunk, so its tree has no depth at all."""

    LENGTH = 32


class Bytes33(ByteVector):
    """A 33-byte array: one byte past the chunk boundary, so two leaves."""

    LENGTH = 33


class ByteList4(ByteList):
    """A byte list holding at most four bytes, a single chunk of capacity."""

    LIMIT = 4


class ByteList33(ByteList):
    """A byte list whose capacity crosses the chunk boundary by one byte."""

    LIMIT = 33


class BitVector8(BitVector):
    """Eight bits, one byte, one leaf."""

    LENGTH = 8


class BitVector257(BitVector):
    """One bit past the 256 a chunk holds, so two leaves."""

    LENGTH = 257


class BitList8(BitList):
    """At most eight bits, a single chunk of capacity."""

    LIMIT = 8


class Uint16Vector2(Vector[Uint16]):
    """Two 16-bit elements, four bytes packed into the one chunk they share."""

    LENGTH = 2


class Uint64List3(List[Uint64]):
    """Three 64-bit elements: 24 bytes, which round up to one chunk of capacity."""

    LIMIT = 3


class Uint64List4(List[Uint64]):
    """Four 64-bit elements: 32 bytes, the same one chunk of capacity as three."""

    LIMIT = 4


class Uint64List5(List[Uint64]):
    """Five 64-bit elements: 40 bytes, which round up to two chunks of capacity."""

    LIMIT = 5


class Uint64List8(List[Uint64]):
    """Eight 64-bit elements: 64 bytes, the same two chunks of capacity as five."""

    LIMIT = 8


class Uint64List12(List[Uint64]):
    """Twelve 64-bit elements: 96 bytes, which round up to three chunks of capacity."""

    LIMIT = 12


class Uint64List16(List[Uint64]):
    """Sixteen 64-bit elements: four chunks, the same four-leaf tree that three fill."""

    LIMIT = 16


class Uint16ProgressiveList(ProgressiveList[Uint16]):
    """A progressive list of 16-bit elements, bounded by nothing."""


class Pair(Container):
    """Two fixed-size fields, so the container's tree is one pair of leaves."""

    a: Uint16
    b: Uint32


class PairVector2(Vector[Pair]):
    """Two composite elements, each contributing its own root as a leaf."""

    LENGTH = 2


class PairList3(List[Pair]):
    """At most three composite elements, so the tree over them holds four leaves."""

    LIMIT = 3


class PairProgressiveList(ProgressiveList[Pair]):
    """Composite elements on a progressive spine."""


class Gapped(ProgressiveContainer):
    """A layout with a cleared middle position, which keeps a zero leaf of its own."""

    ACTIVE_FIELDS = (1, 0, 1)

    side: Uint16
    color: Uint8


class LeadingGap(ProgressiveContainer):
    """A layout sharing only position 2 with Gapped, so the two are union-compatible."""

    ACTIVE_FIELDS = (0, 1, 1)

    radius: Uint16
    color: Uint8


class Shape(CompatibleUnion):
    """A union over the two layouts above."""

    OPTIONS = {1: Gapped, 2: LeadingGap}


class Wrapper(Container):
    """A struct nesting one of every composite shape, to reach the method through depth."""

    numbers: Uint64List5
    shape: Shape
    flags: ProgressiveBitList


GAPPED = Gapped(side=Uint16(0x1234), color=Uint8(0x42))
"""The gapped progressive container used as a value and as a union option."""

LEADING_GAP = LeadingGap(radius=Uint16(0x1234), color=Uint8(0x42))
"""The other layout, holding the same numbers at different positions."""

GAPPED_ROOT = mix_in_active_fields(
    merkleize_progressive([pad(b"\x34\x12"), ZERO_ROOT, pad(b"\x42")]), (1, 0, 1)
)
"""Gapped's root: one leaf per position, the middle one zero, then the layout word."""

LEADING_GAP_ROOT = mix_in_active_fields(
    merkleize_progressive([ZERO_ROOT, pad(b"\x34\x12"), pad(b"\x42")]), (0, 1, 1)
)
"""LeadingGap's root: the same two field leaves, one position further along."""


# Every family, at the values that make its tree shape observable.
#
# Each row pairs a value with its root, derived here from the merkleization primitives.
# No expected value comes from the dispatch under test.
#
# So each row states three things, which is the whole of what a layout decides.
#
#     leaves : what the shape produces
#     tree   : what bounds them
#     mixin  : the word hashed on top
#
# That is also what makes this more than a second copy of the merkleization tests:
# a row cannot pass while both spellings agree on a wrong answer.
FAMILY_ROOTS = [
    # A basic type packs its fixed-width little-endian bytes into the one chunk it owns.
    pytest.param(Boolean(True), pad(b"\x01"), id="boolean_true"),
    pytest.param(Boolean(False), ZERO_ROOT, id="boolean_false"),
    pytest.param(Uint8(0xFF), pad(b"\xff"), id="uint8"),
    pytest.param(Uint16(0x1234), pad(b"\x34\x12"), id="uint16"),
    pytest.param(Uint32(0x1234), pad(b"\x34\x12"), id="uint32"),
    pytest.param(Uint64(0x1234), pad(b"\x34\x12"), id="uint64"),
    pytest.param(Uint128(0x1234), pad(b"\x34\x12"), id="uint128"),
    # A uint256 fills the chunk exactly, leaving no padding to hide a width mistake.
    pytest.param(Uint256(2**256 - 1), Root(b"\xff" * 32), id="uint256"),
    # The spec's opaque byte is the eight-bit uint under another name, and roots alike.
    pytest.param(Byte(0xFF), pad(b"\xff"), id="byte_alias"),
    # A fixed byte array packs the same way, over as many chunks as it spans.
    pytest.param(Bytes4(b"\xde\xad\xbe\xef"), pad(b"\xde\xad\xbe\xef"), id="byte_vector_4"),
    pytest.param(Bytes32(bytes(range(32))), Root(bytes(range(32))), id="byte_vector_32"),
    pytest.param(
        Bytes33(bytes(range(33))),
        h(Root(bytes(range(32))), pad(b"\x20")),
        id="byte_vector_33_two_chunks",
    ),
    # A chunk and a root are the library's own 32-byte arrays.
    # Both inherit the method from the byte-array base.
    # Each is exactly one chunk, so each roots to its own bytes.
    pytest.param(Chunk(bytes(range(32))), Root(bytes(range(32))), id="chunk"),
    pytest.param(Root(bytes(range(32))), Root(bytes(range(32))), id="root"),
    pytest.param(ZERO_ROOT, ZERO_ROOT, id="zero_root"),
    # A byte list mixes in its byte count, over a tree bounded by its capacity in chunks.
    pytest.param(ByteList4(data=b""), mix_in_length(ZERO_ROOT, 0), id="byte_list_empty"),
    pytest.param(
        ByteList4(data=b"\xde\xad\xbe\xef"),
        mix_in_length(pad(b"\xde\xad\xbe\xef"), 4),
        id="byte_list_full_to_limit",
    ),
    pytest.param(
        ByteList33(data=bytes(range(33))),
        mix_in_length(h(Root(bytes(range(32))), pad(b"\x20")), 33),
        id="byte_list_past_chunk_boundary",
    ),
    # A bitvector packs its bits lowest first and mixes nothing in.
    pytest.param(
        BitVector8(data=[Boolean(True), Boolean(False), Boolean(True)] + [Boolean(False)] * 5),
        pad(b"\x05"),
        id="bit_vector_8",
    ),
    pytest.param(
        BitVector257(data=[Boolean(False)] * 256 + [Boolean(True)]),
        h(ZERO_ROOT, pad(b"\x01")),
        id="bit_vector_257_two_chunks",
    ),
    # A bitlist mixes in its bit count, not its packed chunk count.
    pytest.param(BitList8(data=[]), mix_in_length(ZERO_ROOT, 0), id="bit_list_empty"),
    pytest.param(
        BitList8(data=[Boolean(True)]), mix_in_length(pad(b"\x01"), 1), id="bit_list_one_bit"
    ),
    pytest.param(
        BitList8(data=[Boolean(True)] * 8),
        mix_in_length(pad(b"\xff"), 8),
        id="bit_list_full_to_limit",
    ),
    # A progressive bitlist runs the same packing up a spine instead of a bounded tree.
    pytest.param(
        ProgressiveBitList(data=[]), mix_in_length(ZERO_ROOT, 0), id="progressive_bit_list_empty"
    ),
    pytest.param(
        ProgressiveBitList(data=[Boolean(True)] * 257),
        mix_in_length(merkleize_progressive([Chunk(b"\xff" * 32), Chunk(pad(b"\x01"))]), 257),
        id="progressive_bit_list_past_chunk_boundary",
    ),
    # A vector of basic elements packs them into one byte stream before chunking.
    pytest.param(
        Uint16Vector2(data=[Uint16(1), Uint16(2)]),
        pad(b"\x01\x00\x02\x00"),
        id="vector_basic",
    ),
    # A vector of composites takes one leaf per element root.
    pytest.param(
        PairVector2(data=[Pair(a=Uint16(1), b=Uint32(2)), Pair(a=Uint16(3), b=Uint32(4))]),
        h(h(pad(b"\x01"), pad(b"\x02")), h(pad(b"\x03"), pad(b"\x04"))),
        id="vector_composite",
    ),
    # A bounded list mixes in its element count over a tree bounded by chunk capacity.
    # An empty bounded list still pays for its capacity: two chunks of zero subtree.
    pytest.param(
        Uint64List5(data=[]), mix_in_length(merkleize([], 2), 0), id="list_empty_over_two_chunks"
    ),
    # A one-chunk capacity leaves the zero leaf itself, with no depth above it.
    pytest.param(Uint64List4(data=[]), mix_in_length(ZERO_ROOT, 0), id="list_empty_over_one_chunk"),
    pytest.param(
        Uint64List5(data=[Uint64(1)]),
        mix_in_length(merkleize([Chunk(pad(b"\x01"))], 2), 1),
        id="list_one_element",
    ),
    pytest.param(
        Uint64List5(data=[Uint64(index) for index in range(5)]),
        mix_in_length(
            merkleize(
                [
                    Chunk(pad(b"".join(index.to_bytes(8, "little") for index in range(4)))),
                    Chunk(pad((4).to_bytes(8, "little"))),
                ],
                2,
            ),
            5,
        ),
        id="list_full_to_limit_past_chunk_boundary",
    ),
    pytest.param(
        PairList3(data=[Pair(a=Uint16(1), b=Uint32(2))]),
        mix_in_length(merkleize(nested_roots([Pair(a=Uint16(1), b=Uint32(2))]), 3), 1),
        id="list_composite",
    ),
    # A progressive list runs the same leaves up a spine, with no capacity at all.
    pytest.param(
        Uint16ProgressiveList(data=[]), mix_in_length(ZERO_ROOT, 0), id="progressive_list_empty"
    ),
    pytest.param(
        Uint16ProgressiveList(data=[Uint16(index) for index in range(17)]),
        mix_in_length(
            merkleize_progressive(
                [
                    Chunk(pad(b"".join(index.to_bytes(2, "little") for index in range(16)))),
                    Chunk(pad((16).to_bytes(2, "little"))),
                ]
            ),
            17,
        ),
        id="progressive_list_past_chunk_boundary",
    ),
    # Two distinct elements, so a leaf swapped on this path cannot pass unnoticed.
    pytest.param(
        PairProgressiveList(data=[Pair(a=Uint16(1), b=Uint32(2)), Pair(a=Uint16(3), b=Uint32(4))]),
        mix_in_length(
            merkleize_progressive(
                nested_roots([Pair(a=Uint16(1), b=Uint32(2)), Pair(a=Uint16(3), b=Uint32(4))])
            ),
            2,
        ),
        id="progressive_list_composite",
    ),
    # A container takes one leaf per field, bounded by the field count, mixing nothing in.
    pytest.param(Pair(a=Uint16(1), b=Uint32(2)), h(pad(b"\x01"), pad(b"\x02")), id="container"),
    # A progressive container keeps a zero leaf at every cleared position.
    pytest.param(GAPPED, GAPPED_ROOT, id="progressive_container_with_a_gap"),
    pytest.param(LEADING_GAP, LEADING_GAP_ROOT, id="progressive_container_leading_gap"),
    # A union is the option's own root under one leaf of capacity, then the selector.
    pytest.param(
        Shape(selector=Uint8(1), data=GAPPED),
        mix_in_selector(GAPPED_ROOT, 1),
        id="compatible_union_first_option",
    ),
    pytest.param(
        Shape(selector=Uint8(2), data=LEADING_GAP),
        mix_in_selector(LEADING_GAP_ROOT, 2),
        id="compatible_union_second_option",
    ),
    # Depth: a struct whose three fields are a bounded list, a union, and a spine.
    pytest.param(
        Wrapper(
            numbers=Uint64List5(data=[Uint64(1)]),
            shape=Shape(selector=Uint8(2), data=LEADING_GAP),
            flags=ProgressiveBitList(data=[Boolean(True), Boolean(False)]),
        ),
        merkleize(
            [
                Chunk(mix_in_length(merkleize([Chunk(pad(b"\x01"))], 2), 1)),
                Chunk(mix_in_selector(LEADING_GAP_ROOT, 2)),
                Chunk(mix_in_length(merkleize_progressive([Chunk(pad(b"\x01"))]), 2)),
            ],
            3,
        ),
        id="nested_composites",
    ),
]


@pytest.mark.parametrize("value, expected_root", FAMILY_ROOTS)
def test_the_method_reaches_the_spec_root_for_every_family(
    value: SSZType, expected_root: Root
) -> None:
    """
    Every family roots through the method to the tree its layout describes.

    Three claims per row, and the second is what keeps the first honest.

    - The method reaches the same root the free function does, so the two never diverge.
    - That root is the one derived above from the merkleization primitives.
    - So a row cannot pass while both spellings agree on a wrong answer.
    - The result carries the root type, not the bare bytes, so a caller can pass it on.
    """
    root = value.hash_tree_root()
    assert root == hash_tree_root(value)
    assert root == expected_root
    assert type(root) is Root


@pytest.mark.parametrize(
    "narrow_type, wide_type",
    [
        # Eight-byte elements pack four to a chunk, so both of these bound one leaf.
        pytest.param(Uint64List3, Uint64List4, id="one_leaf"),
        # Both of these bound two.
        pytest.param(Uint64List5, Uint64List8, id="two_leaves"),
        # These two bound three chunks and four, which round up to the same four leaves.
        # So the shared width, not the chunk count, is what the root follows.
        pytest.param(Uint64List12, Uint64List16, id="four_leaves_from_unequal_chunk_counts"),
    ],
)
def test_two_limits_bounding_one_tree_width_root_alike(
    narrow_type: type[List[Uint64]], wide_type: type[List[Uint64]]
) -> None:
    """
    A limit reaches the root only through the width of the tree it bounds.

    That width is the next power of two at or above the limit counted in chunks.
    Two limits that round up to the same width bound the same tree.
    The same elements therefore root identically under both.
    The limit itself is not mixed in anywhere.
    """
    elements = [Uint64(1), Uint64(2), Uint64(3)]
    assert narrow_type(data=elements).hash_tree_root() == wide_type(data=elements).hash_tree_root()


def test_a_limit_bounding_a_wider_tree_changes_the_root() -> None:
    """A wider tree puts every leaf one level deeper, so the root moves."""
    elements = [Uint64(1), Uint64(2), Uint64(3)]
    # Four eight-byte elements fill one chunk; a fifth opens a second.
    assert (
        Uint64List4(data=elements).hash_tree_root() != Uint64List5(data=elements).hash_tree_root()
    )


def test_plain_bytes_root_through_the_function_and_carry_no_method() -> None:
    """
    Plain bytes merkleize, and are not an SSZ type, so only the function takes them.

    The free function stays public for exactly this reason.
    A bytes object cannot carry a method of the library's own.
    The handler registered for it has no declared type to hang one on.
    """
    payload = b"\xde\xad\xbe\xef"
    assert hash_tree_root(payload) == pad(payload)
    assert not hasattr(payload, "hash_tree_root")
    assert not isinstance(payload, SSZType)


@pytest.mark.parametrize(
    "unsupported",
    [
        pytest.param(object(), id="object"),
        # A string is not the bytes handler's input, however byte-like it reads.
        pytest.param("abcd", id="str"),
        pytest.param(7, id="int"),
        pytest.param(None, id="none"),
        pytest.param([Uint8(1)], id="list_of_ssz_values"),
    ],
)
def test_an_unsupported_value_still_reports_the_free_function_error(unsupported: object) -> None:
    """A type with no registered handler keeps the message it has always raised."""
    expected = f"{type(unsupported).__name__} has no Merkle layout"
    with pytest.raises(SSZTypeError, match=rf"^{expected}$"):
        hash_tree_root(unsupported)


def test_a_container_hashes_itself_by_the_root_the_method_reports() -> None:
    """
    A container's hash follows its own root, through the method that reports it.

    Equality is by field, and the root stands in for every field, so the two agree.
    This is the one place the method is reached from inside the library.
    """
    assert hash(GAPPED) == hash(GAPPED.hash_tree_root())
    assert hash(GAPPED) != hash(LEADING_GAP)


def test_an_in_place_append_moves_the_root_through_both_spellings() -> None:
    """
    A collection mutated in place roots as the value it now holds, not the one it held.

    Nothing caches a root today, and this pins that.

    - Every collection here is mutable unless its type says otherwise.
    - Assignment validation does not fire on an in-place append at all.
    - So a cache added later must arrive with an invalidation, or return a stale root.
    """
    numbers = Uint64List5(data=[Uint64(1)])
    before = numbers.hash_tree_root()

    numbers.append(Uint64(2))
    after = numbers.hash_tree_root()

    assert after != before
    assert after == hash_tree_root(numbers)
    # The mutated value roots as one built from the contents it now holds.
    assert after == Uint64List5(data=[Uint64(1), Uint64(2)]).hash_tree_root()


def test_an_in_place_element_write_moves_the_root_through_both_spellings() -> None:
    """An element replaced in place moves the root, and the two spellings still agree."""
    numbers = Uint64List5(data=[Uint64(1), Uint64(2)])
    before = numbers.hash_tree_root()

    numbers[0] = Uint64(9)
    after = numbers.hash_tree_root()

    assert after != before
    assert after == hash_tree_root(numbers)
    assert after == Uint64List5(data=[Uint64(9), Uint64(2)]).hash_tree_root()


def test_a_nested_collection_mutated_through_its_field_moves_the_struct_root() -> None:
    """A struct's root follows a field mutated in place, with no re-assignment of the field."""
    wrapper = Wrapper(
        numbers=Uint64List5(data=[Uint64(1)]),
        shape=Shape(selector=Uint8(1), data=GAPPED),
        flags=ProgressiveBitList(data=[]),
    )
    before = wrapper.hash_tree_root()

    wrapper.numbers.append(Uint64(2))

    assert wrapper.hash_tree_root() != before
    assert wrapper.hash_tree_root() == hash_tree_root(wrapper)


@given(values=st.lists(st.integers(min_value=0, max_value=2**16 - 1), max_size=100))
def test_a_progressive_list_agrees_with_the_function_at_every_spine_depth(
    values: list[int],
) -> None:
    """The two spellings agree at every element count, across every level the spine opens."""
    instance = Uint16ProgressiveList(data=[Uint16(value) for value in values])
    root = instance.hash_tree_root()
    assert root == hash_tree_root(instance)
    assert type(root) is Root


@given(
    pairs=st.lists(
        st.tuples(
            st.integers(min_value=0, max_value=2**16 - 1),
            st.integers(min_value=0, max_value=2**32 - 1),
        ),
        max_size=3,
    )
)
def test_a_list_of_composites_agrees_with_the_function_at_every_element_count(
    pairs: list[tuple[int, int]],
) -> None:
    """Nested leaves reach the method through the layout, at every count up to the limit."""
    instance = PairList3(data=[Pair(a=Uint16(a), b=Uint32(b)) for a, b in pairs])
    root = instance.hash_tree_root()
    assert root == hash_tree_root(instance)
    assert type(root) is Root


def test_the_function_is_part_of_the_public_surface() -> None:
    """
    The spec's own spelling is reachable from the package, not only from its module.

    A caller who prefers the function should not have to name the module it lives in.
    """
    assert "hash_tree_root" in ssz.__all__

"""Merkleization primitives and hash-tree-root dispatch for SSZ."""

from __future__ import annotations

import math
import os
from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass
from functools import cache, singledispatch
from hashlib import sha256
from itertools import accumulate, repeat
from typing import Final

from ssz.bitfields import BitList, BitVector, ProgressiveBitList
from ssz.boolean import Boolean
from ssz.byte_arrays import ByteList, ByteVector
from ssz.collections import List, ProgressiveList, Vector
from ssz.container import Container, ProgressiveContainer
from ssz.exceptions import SSZActiveFieldsError, SSZTypeError, SSZValueError
from ssz.ssz_base import SSZModel, SSZType
from ssz.uint import BaseUint
from ssz.union import CompatibleUnion

BYTES_PER_CHUNK: Final = 32
"""Width of a Merkle leaf chunk in bytes."""

BITS_PER_CHUNK: Final = BYTES_PER_CHUNK * 8
"""Width of a Merkle leaf chunk in bits."""

PARANOID_ROOTS: bool = os.environ.get("SSZ_PARANOID_ROOTS") == "1"
"""Whether every remembered root is recomputed and checked against the memo.

A proof built from the same layout agrees with a stale root while both are wrong, so
recomputing is the only evidence against one. Enable with SSZ_PARANOID_ROOTS=1.
"""


def _next_pow2(x: int) -> int:
    """
    Smallest power of two greater than or equal to x.

    Returns 1 when x is 0 or 1.
    """
    if x <= 1:
        return 1
    return 1 << (x - 1).bit_length()


class Chunk(ByteVector):
    """Fixed-size 32-byte unit of Merkle tree input data."""

    LENGTH = BYTES_PER_CHUNK


class Root(Chunk):
    """Merkle tree root, usable anywhere a chunk is expected."""

    LENGTH = 32


ZERO_ROOT: Final = Root.zero()
"""All-zero 32-byte root, used as the merkleization padding value."""

_ZERO_CHUNK: Final = bytes(BYTES_PER_CHUNK)
"""The zero chunk as plain bytes, since a typed chunk refuses to compare against them."""

_ZERO_ROOTS: Final[tuple[Root, ...]] = tuple(
    accumulate(
        repeat(None, 64),
        lambda previous, _: Root(sha256(previous + previous).digest()),
        initial=ZERO_ROOT,
    )
)
"""
Roots of perfect zero subtrees, indexed by depth.

- Index 0 is the all-zero leaf.
- Index d is the root of a perfect binary tree of 2**d zero leaves.

Depth 64 covers any chunk count the protocol uses.
"""


def _zero_tree_root(width: int) -> Root:
    """
    Root of an all-zero perfect binary tree with the given leaf count.

    The width must be a power of two.
    """
    # A single-leaf tree has no parent to hash; the root is the leaf itself.
    if width <= 1:
        return ZERO_ROOT
    # A perfect binary tree with 2**d leaves has depth d.
    #
    # Subtract one before taking bit_length so a power of two maps to its own depth.
    # - Width 2 -> depth 1,
    # - Width 4 -> depth 2,
    # - Width 1024 -> depth 10,
    # - And so on.
    depth = (width - 1).bit_length()
    # The cache stores the all-zero subtree root at every depth.
    # Index by depth to skip materializing 2**d zero leaves and the layers above them.
    return _ZERO_ROOTS[depth]


def merkleize(chunks: Sequence[bytes], limit: int | None = None) -> Root:
    r"""
    Compute the SSZ Merkle root over a chunk sequence.

    Tree layout for three leaves with no limit:

        leaves   :  c0     c1     c2     ZERO     (padded to next power of two)
                     \____/        \______/
                       h01        h(c2, ZERO)
                        \______________/
                              root

    When a limit is provided, the tree width is the next power of two of that limit.
    Missing leaves contribute pre-computed zero subtree roots instead of
    materialized zero chunks, so allocation stays proportional to actual data.

    Every node below the root is a plain 32-byte string.
    The root alone carries a type.
    It is the only node returned.

    Three shapes skip the layer walk:

    - An all-zero input roots to a zero tree, cached at every depth.
    - A level of one repeated value spanning its data tree has a root in closed form.
    - A single node with capacity above it pairs only against cached zero subtrees.

    A 65_536-leaf tree of one repeated chunk costs 16 hashes.
    Walking it would cost 65_535.

    Args:
        chunks: Leaf chunks, each exactly 32 bytes wide. A chunk of any other width is the
            caller's error and is not diagnosed here.
        limit: Optional leaf-count capacity; tree width is rounded up to the next power of two.

    Returns:
        The Merkle root.

    Raises:
        SSZValueError: If the chunk count exceeds the limit.
    """
    chunk_count = len(chunks)
    if chunk_count == 0:
        return _zero_tree_root(_next_pow2(limit)) if limit is not None else ZERO_ROOT
    if limit is None:
        width = _next_pow2(chunk_count)
    elif limit < chunk_count:
        raise SSZValueError("merkleize: input exceeds limit")
    else:
        width = _next_pow2(limit)
    # A one-leaf tree has no parent to hash: the leaf is the root.
    if width == 1:
        return Root._trusted(chunks[0])

    # Zero data under zero padding is a zero tree, at any width.
    # The fold below fires only from a level spanning its data tree, so a count short of a power
    # of two hashes its way up to one.
    # The first chunk rules out anything that starts with data, before the join copies it all.
    if bytes(chunks[0]) == _ZERO_CHUNK and b"".join(chunks) == _ZERO_CHUNK * chunk_count:
        return _zero_tree_root(width)

    # Width of the perfect subtree the data fills, where the layer walk ends.
    # Above it every height holds one real node beside an all-zero subtree.
    data_width = _next_pow2(chunk_count)

    # Walk one tree layer per outer iteration.
    level: list[bytes] = list(chunks)
    subtree_size = 1
    while len(level) > 1:
        # Pairing a uniform level yields the same value one size up.
        # The tail below folds it once per remaining height.
        #
        # Invariant: the level must also span its data tree.
        # A shorter one meets a zero subtree as a sibling above it.
        # Zero does not fold.
        #
        # The comparison goes through plain bytes.
        # A level mixes bare digests with typed leaves that refuse equality against bytes.
        if (
            len(level) * subtree_size == data_width
            and bytes(level[0]) == bytes(level[-1])
            and b"".join(level) == level[0] * len(level)
        ):
            break

        # An odd node count is missing exactly one right sibling, at the end of the level.
        # Supplying it here, rather than once per pair, keeps the branch out of the loop.
        if len(level) & 1:
            level.append(_zero_tree_root(subtree_size))
        level = [sha256(level[i] + level[i + 1]).digest() for i in range(0, len(level), 2)]
        subtree_size *= 2

    # Neither spine above this point branches.
    # A list per height would allocate only to carry a single node.
    #
    # - Up to the data tree, after a fold: every sibling is the node itself.
    # - Up to the full width: every sibling is the all-zero subtree beside the data.
    node = level[0]
    while subtree_size < data_width:
        node = sha256(node + node).digest()
        subtree_size *= 2
    while subtree_size < width:
        node = sha256(node + _zero_tree_root(subtree_size)).digest()
        subtree_size *= 2
    # Invariant: a width above one leaves at least one height.
    # One spine above therefore hashed.
    # A digest is exactly the chunk width.
    return Root._trusted(node)


def merkleize_progressive(chunks: Sequence[bytes], num_leaves: int = 1) -> Root:
    r"""
    Compute the progressive Merkle root over a chunk sequence, per EIP-7916.

    The tree is a right-leaning spine of binary subtrees, terminated by a zero node.
    The subtree at level n holds 4**(n - 1) chunks, counting levels from one.
    Capacity therefore grows with the data instead of with a declared bound.

    An 85-chunk input fills four levels exactly:

                           root
                            /\
                           /  \
         1: chunks[0 ..< 1]   /\
                             /  \
           4: chunks[1 ..< 5]   /\
                               /  \
           16: chunks[5 ..< 21]   /\
                                 /  \
            64: chunks[21 ..< 85]    0

    Each level is an ordinary binary subtree, and only the spine above them is new.
    A level short of its width pads with zero subtree roots, spending depth but no memory.

    # Layout

    A level opens only once every level before it is full:

        level   chunks added   chunks total   bytes total
        1       1              1              32
        2       4              5              160
        3       16             21             672
        4       64             85             2_720
        5       256            341            10_912

    After n levels the total is (4**n - 1) // 3 chunks.
    An empty input opens no level, so its root is the zero node itself.

    # Why positions stay put

    A chunk's generalized index follows from its own index alone.
    The indices below count the progressive root as one, leaving out the root above it
    that the length is mixed into:

        chunk 0  ->  2       chunk 5   ->  224
        chunk 1  ->  24      chunk 21  ->  1920

    Appending extends the spine downward and moves nothing already placed.
    A proof against one chunk therefore survives every later append.
    A bounded tree renumbers every leaf as soon as a new capacity changes its depth.

    Args:
        chunks: Leaf chunks, each exactly 32 bytes wide.
        num_leaves: Chunk capacity of the current level, quadrupling at each next level.
            Callers keep the default of one, and the recursion supplies the wider levels.

    Returns:
        The progressive Merkle root.
    """
    # An exhausted input terminates the spine with a zero node.
    #
    # The terminator is a plain zero leaf, not a zero subtree of some depth:
    # the level it stands for holds no data, so it has no width to pad out.
    # The deepest occupied level is padded; everything past it collapses to this one node.
    if len(chunks) == 0:
        return ZERO_ROOT

    # Left child: this level's chunks as a binary subtree, zero-padded to the level width.
    subtree_root = merkleize(chunks[:num_leaves], limit=num_leaves)

    # Right child: every chunk past this level, in a level four times as wide.
    successor_root = merkleize_progressive(chunks[num_leaves:], num_leaves * 4)

    # Invariant: a digest is exactly the chunk width.
    return Root._trusted(sha256(subtree_root + successor_root).digest())


def _mix_in(root: Root, word: Chunk) -> Root:
    """Hash a subtree root against the word its shape mixes in, as the right child."""
    # Invariant: a digest is exactly the chunk width.
    return Root._trusted(sha256(root + word).digest())


def length_word(length: int) -> Chunk:
    """
    The element count a variable-size shape mixes in, as one 32-byte little-endian word.

    Raises:
        SSZValueError: If the length is negative.
    """
    if length < 0:
        raise SSZValueError("length must be non-negative")
    # Invariant: to_bytes yields exactly the requested width, or raises OverflowError.
    return Chunk._trusted(length.to_bytes(BYTES_PER_CHUNK, "little"))


def active_fields_word(active_fields: Sequence[int]) -> Chunk:
    """
    The field layout a progressive container mixes in, as one 32-byte word.

    One bit per position, lowest bit first, so at most 256 positions fit the word:

        [1, 0, 1]  ->  05 00 00 ... 00

    The bound of 256 is enforced by the type that declares the layout, not here.
    """
    packed_bits = sum(1 << i for i, bit in enumerate(active_fields) if bit)
    # Invariant: to_bytes yields exactly the requested width, or raises OverflowError.
    return Chunk._trusted(packed_bits.to_bytes(BYTES_PER_CHUNK, "little"))


def selector_word(selector: int) -> Chunk:
    """
    The option selector a compatible union mixes in, as one 32-byte word.

    The spec writes the selector as a one-byte integer.
    A hash operand is one chunk, so the byte is zero-extended to 32:

        selector 1  ->  01 00 00 ... 00

    Raises:
        SSZValueError: If the selector does not fit one byte.
    """
    if not 0 <= selector <= 0xFF:
        raise SSZValueError(f"selector {selector} does not fit one byte")
    # Invariant: to_bytes yields exactly the requested width, or raises OverflowError.
    return Chunk._trusted(selector.to_bytes(BYTES_PER_CHUNK, "little"))


def mix_in_length(root: Root, length: int) -> Root:
    """
    Mix a length into a Merkle root via the SSZ uint256 little-endian encoding.

    Variable-length types append their declared length to disambiguate roots.
    Two lists with identical elements but different lengths must produce different roots.

    Args:
        root: Merkle root over the data chunks.
        length: Non-negative count to mix in.

    Returns:
        The length-mixed root.

    Raises:
        SSZValueError: If the length is negative.
    """
    return _mix_in(root, length_word(length))


def mix_in_active_fields(root: Root, active_fields: Sequence[int]) -> Root:
    """
    Mix a field layout into a Merkle root, per EIP-7495.

    The layout packs into a single 32-byte word, one bit per position, lowest bit first:

        [1, 0, 1]  ->  05 00 00 ... 00

    Mixing it in is what keeps a cleared position distinct from a field holding zero.
    Both leave a zero leaf, so the leaf tree alone cannot separate them.
    A version that drops a field would otherwise root exactly like one that zeroed it.

    Args:
        root: Merkle root over the field leaves.
        active_fields: One 0 or 1 per position. The bound of 256 is enforced by the
            type that declares the layout, not here.

    Returns:
        The layout-mixed root.
    """
    return _mix_in(root, active_fields_word(active_fields))


def mix_in_selector(root: Root, selector: int) -> Root:
    """
    Mix a type selector into a Merkle root, per EIP-8016.

    The spec writes the selector as a one-byte integer.
    A hash operand is one chunk, so the byte is zero-extended to 32:

        selector 1  ->  01 00 00 ... 00

    Mixing it in separates options that would otherwise root alike:

    - Two options holding equal data would otherwise root identically.
    - Two options differing only in a list's element type collide while that list is empty.

    Args:
        root: Merkle root of the value the union holds.
        selector: Selector of the option it holds.

    Returns:
        The selector-mixed root.

    Raises:
        SSZValueError: If the selector does not fit one byte.
    """
    return _mix_in(root, selector_word(selector))


def _pack_bytes(data: bytes) -> list[bytes]:
    """
    Right-pad serialized bytes to a chunk boundary and split into chunks.

    Layout for a 5-byte payload:

        bytes    :  01 02 03 04 05
        padded   :  01 02 03 04 05 00 00 ... 00     (zero-padded to 32 bytes)
        chunks   :  [ 01 02 03 04 05 00 ... 00 ]

    Inner chunks are already chunk-aligned.
    Only the trailing chunk is padded.
    Padding a full chunk returns it unchanged.
    Either branch therefore gives exactly 32 bytes.

    The chunks are plain bytes rather than a typed array.
    Nothing reads them except as a hash operand.
    Typing them would re-check a width the slice and the padding already fix.
    """
    return [
        data[i : i + BYTES_PER_CHUNK].ljust(BYTES_PER_CHUNK, b"\x00")
        for i in range(0, len(data), BYTES_PER_CHUNK)
    ]


def _pack_bits(bits: Sequence[Boolean]) -> list[bytes]:
    """
    Pack a boolean sequence into bytes, then into chunks for merkleization.

    The first input bit becomes the least significant bit of the first byte.
    Each next input bit moves up one position, wrapping to the next byte after eight.

    Layout for [1, 0, 1, 1]:

        bit position  :   7  6  5  4  3  2  1  0
        byte 0        :   0  0  0  0  1  1  0  1
                                      ^  ^  ^  ^
                                      3  2  1  0   <- input order

    The SSZ serialization delimiter and the length-mix are separate steps,
    handled by the caller when needed.
    """
    # Each bit is set in place, in a buffer already the width of the result.
    #
    # Accumulating one wide integer instead grows that integer with the data.
    # Every addition then costs more than the one before it.
    # Packing a long bitfield that way is quadratic in its bit count.
    packed = bytearray(math.ceil(len(bits) / 8))
    # Bit i lives in byte i // 8, at position i % 8 counted from the low end.
    for position, bit in enumerate(bits):
        if bit:
            packed[position >> 3] |= 1 << (position & 7)
    return _pack_bytes(bytes(packed))


def _pack_basic_elements(elements: Sequence[int], element_size: int) -> list[bytes]:
    """
    Serialize a sequence of basic elements, then split the result into chunks.

    Layout for [1, 2, 3] of a two-byte width:

        bytes   :  01 00    02 00    03 00
        chunks  :  [ 01 00 02 00 03 00 00 ... 00 ]

    Invariant: the width is the declared element type's, which every element was coerced
    to on the way in. Little-endian is written out rather than read from the host.
    """
    if element_size == 1:
        return _pack_bytes(bytes(elements))
    # A list rather than a generator, so the join can size its result in one pass.
    return _pack_bytes(b"".join([int.to_bytes(e, element_size, "little") for e in elements]))


@dataclass(frozen=True, slots=True)
class MerkleLayout:
    """
    The subtree one value merkleizes into, before any of it is hashed.

    Every shape reaches its root the same way, in the three steps below.

        shape                 leaves               tree                        mixed in
        Container             fields               bounded by the field count  -
        List                  elements or packing  bounded by the limit        count
        ProgressiveList       elements or packing  progressive spine           count
        ProgressiveContainer  layout positions     progressive spine           layout
        CompatibleUnion       the option it holds  bounded by one              selector

    Stating those steps rather than taking them is what lets a root and a proof share a rule.
    Leaves past the last one are the zero padding the tree shape supplies.
    """

    packed: tuple[bytes, ...]
    """Leaves as data, for a shape whose elements pack into chunks.

    An element of such a shape shares its chunk with its neighbours.
    The chunk is therefore the leaf, and nothing below it can be addressed.
    Empty when the shape nests values instead.
    """

    nested: tuple[SSZType | None, ...] | None
    """Leaves as values, one root each, or None for a shape that packs instead.

    A position carrying no value holds nothing, which merkleizes as a zero leaf.
    """

    limit: int | None
    """Chunk capacity of the bounded tree over the leaves, or None for a progressive spine."""

    mixin: Chunk | None
    """Word the subtree root is hashed against, or None when the shape mixes nothing in."""

    @classmethod
    def packing(
        cls, chunks: Sequence[bytes], *, limit: int | None, mixin: Chunk | None = None
    ) -> MerkleLayout:
        """A layout whose leaves are packed data."""
        return cls(packed=tuple(chunks), nested=None, limit=limit, mixin=mixin)

    @classmethod
    def nesting(
        cls, values: Iterable[SSZType | None], *, limit: int | None, mixin: Chunk | None = None
    ) -> MerkleLayout:
        """A layout whose leaves are the roots of nested values."""
        return cls(packed=(), nested=tuple(values), limit=limit, mixin=mixin)

    @property
    def leaf_count(self) -> int:
        """Leaves the shape produced, before any zero padding."""
        return len(self.packed) if self.nested is None else len(self.nested)

    def chunks(self, start: int = 0, stop: int | None = None) -> list[bytes]:
        """
        The leaves in a half-open range, as chunks.

        A nested value is rooted here rather than when the layout is built.
        A proof therefore hashes only the part of the tree it walks into.
        A root asks for every leaf, and hashes all of it.

        Every leaf is 32 bytes wide. A packed one carries no type, being only a hash
        operand.
        A nested one arrives as the root that rooting it produced.
        """
        if self.nested is None:
            return list(self.packed[start:stop])
        values = self.nested[start:stop]
        # Ends that differ rule out a repeat, so distinct leaves stay in the comprehension.
        if not values or values[0] is not values[-1]:
            return [ZERO_ROOT if value is None else hash_tree_root(value) for value in values]
        roots: list[bytes] = []
        previous = values[0]
        previous_root = ZERO_ROOT if previous is None else hash_tree_root(previous)
        for value in values:
            if value is not previous:
                previous = value
                previous_root = ZERO_ROOT if value is None else hash_tree_root(value)
            roots.append(previous_root)
        return roots


@singledispatch
def merkle_layout(value: object) -> MerkleLayout:
    """
    How one value merkleizes: its leaves, their tree shape, and the word mixed in.

    Raises:
        SSZTypeError: If the value's type has no registered handler.
    """
    raise SSZTypeError(f"hash_tree_root: unsupported value type {type(value).__name__}")


@merkle_layout.register(BaseUint)
@merkle_layout.register(Boolean)
@merkle_layout.register(ByteVector)
def _layout_packed_leaf(value: BaseUint | Boolean | ByteVector) -> MerkleLayout:
    # Each of these encodes to a fixed-width byte string with no length prefix.
    # The width is fixed.
    # The chunks it packs into are therefore the whole capacity.
    chunks = _pack_bytes(value.encode_bytes())
    return MerkleLayout.packing(chunks, limit=len(chunks))


@merkle_layout.register
def _layout_bytes(value: bytes) -> MerkleLayout:
    # Plain bytes are not an SSZ type.
    # They carry no capacity beyond the data itself.
    chunks = _pack_bytes(value)
    return MerkleLayout.packing(chunks, limit=len(chunks))


@merkle_layout.register
def _layout_bytelist(value: ByteList) -> MerkleLayout:
    serialized_bytes = value.encode_bytes()
    # The count mixed in is the byte count.
    # That is also the element count here.
    return MerkleLayout.packing(
        _pack_bytes(serialized_bytes),
        limit=math.ceil(type(value).declared_limit() / BYTES_PER_CHUNK),
        mixin=length_word(len(serialized_bytes)),
    )


@merkle_layout.register
def _layout_bitvector(value: BitVector) -> MerkleLayout:
    return MerkleLayout.packing(
        _pack_bits(value.data), limit=math.ceil(type(value).declared_length() / BITS_PER_CHUNK)
    )


@merkle_layout.register
def _layout_bitlist(value: BitList) -> MerkleLayout:
    return MerkleLayout.packing(
        _pack_bits(value.data),
        limit=math.ceil(type(value).declared_limit() / BITS_PER_CHUNK),
        mixin=length_word(len(value.data)),
    )


@merkle_layout.register
def _layout_progressive_bitlist(value: ProgressiveBitList) -> MerkleLayout:
    # The count mixed in is the bit count, not the number of packed chunks.
    return MerkleLayout.packing(
        _pack_bits(value.data), limit=None, mixin=length_word(len(value.data))
    )


# Registered by annotation, and singledispatch needs a class, not a subscripted generic.
@merkle_layout.register
def _layout_vector(value: Vector) -> MerkleLayout:
    cls = type(value)
    element_type, length = cls.ELEMENT_TYPE, cls.declared_length()
    if issubclass(element_type, (BaseUint, Boolean)):
        # Basic elements pack their serialized bytes into a single byte stream before chunking.
        element_size = element_type.get_byte_length()
        return MerkleLayout.packing(
            _pack_basic_elements(value.data, element_size),
            limit=math.ceil(length * element_size / BYTES_PER_CHUNK),
        )
    # Composite elements each contribute their own hash tree root as a leaf.
    return MerkleLayout.nesting(value, limit=length)


@merkle_layout.register
def _layout_list(value: List) -> MerkleLayout:
    cls = type(value)
    element_type, limit = cls.ELEMENT_TYPE, cls.declared_limit()
    mixin = length_word(len(value))
    if issubclass(element_type, (BaseUint, Boolean)):
        element_size = element_type.get_byte_length()
        return MerkleLayout.packing(
            _pack_basic_elements(value.data, element_size),
            limit=math.ceil(limit * element_size / BYTES_PER_CHUNK),
            mixin=mixin,
        )
    return MerkleLayout.nesting(value, limit=limit, mixin=mixin)


@merkle_layout.register
def _layout_progressive_list(value: ProgressiveList) -> MerkleLayout:
    element_type = type(value).ELEMENT_TYPE
    # No capacity bounds the chunk count: the tree grows to hold whatever was packed.
    #
    # The count mixed in is the element count, not the number of packed chunks.
    # A hundred eight-byte elements pack into 25 chunks, and 100 is the number mixed in.
    mixin = length_word(len(value))
    if issubclass(element_type, (BaseUint, Boolean)):
        return MerkleLayout.packing(
            _pack_basic_elements(value.data, element_type.get_byte_length()),
            limit=None,
            mixin=mixin,
        )
    return MerkleLayout.nesting(value, limit=None, mixin=mixin)


@merkle_layout.register
def _layout_progressive_container(value: ProgressiveContainer) -> MerkleLayout:
    # One leaf per layout position, not per field, though the spec's formula reads that way.
    # A cleared bit keeps its zero leaf, the gap that holds every other field still.
    cls = type(value)
    # A layout is declared as bits and never coerced, so a list of them arrives as one.
    layout = tuple(cls.ACTIVE_FIELDS)
    try:
        names, word = _progressive_container_plan(layout, _field_names(cls))
    except ValueError as mismatch:
        raise SSZActiveFieldsError(cls.__name__, layout, str(mismatch)) from mismatch
    return MerkleLayout.nesting(
        [None if name is None else getattr(value, name) for name in names],
        limit=None,
        mixin=word,
    )


@merkle_layout.register
def _layout_compatible_union(value: CompatibleUnion) -> MerkleLayout:
    # The union adds no leaf of its own: the option's own root is the whole tree below.
    # One leaf of capacity is a tree of no depth.
    # The contained root is therefore the left child itself.
    return MerkleLayout.nesting((value.data,), limit=1, mixin=selector_word(int(value.selector)))


@merkle_layout.register
def _layout_container(value: Container) -> MerkleLayout:
    names = _field_names(type(value))
    return MerkleLayout.nesting([getattr(value, name) for name in names], limit=len(names))


@cache
def _progressive_container_plan(
    active_fields: tuple[int, ...], field_names: tuple[str, ...]
) -> tuple[tuple[str | None, ...], Chunk]:
    """
    Which field sits at each position of a progressive layout, and the word mixed in.

    One entry per position, naming the field that sits there, or None for a gap.
    Neither answer reads the value, so both are worked out once per layout.

    Keyed by the layout and the field names, never by the type that declares them.
    ACTIVE_FIELDS is a plain class attribute, reassignable after the type is declared, and
    a root follows the reassignment.
    A key naming the type would answer with the layout that type used to have.
    The names beside it are rebuilt per root for the same reason.

    Raises:
        ValueError: If the layout and the fields do not pair up one to one. The caller
            names the type, which no plan depends on and so none is keyed by.
    """
    positions: list[str | None] = [None] * len(active_fields)
    active_positions = [position for position, bit in enumerate(active_fields) if bit]
    # The declaration checks this pairing too, and a reassigned layout arrives unchecked.
    if len(active_positions) != len(field_names):
        raise ValueError(
            f"the layout sets {len(active_positions)} positions, "
            + f"and the struct declares {len(field_names)}"
        )
    # Fields follow the set bits: the n-th field belongs at the n-th set position.
    for position, name in zip(active_positions, field_names, strict=True):
        positions[position] = name
    return tuple(positions), active_fields_word(active_fields)


_IMMUTABLE_LEAVES: Final = (BaseUint, Boolean, ByteVector)
"""The SSZ types that subclass an immutable builtin, whose roots cannot go stale."""


@cache
def _field_names(cls: type[SSZModel]) -> tuple[str, ...]:
    """
    Every field name, in the declaration order that is the canonical SSZ field order.

    Reading the model's own mapping goes through a property, and a layout wants the names
    twice: once to read the fields and once for the count that sizes the tree.
    """
    return tuple(cls.model_fields)


@cache
def _nested_field_names(cls: type[SSZModel]) -> tuple[str, ...]:
    """
    The fields of a struct that can hold a value with a root of its own.

    Leaf fields are dropped: reading eight of them on each of 64 validators would cost
    512 reads for nothing. A field with no single declared class is kept.
    """
    return tuple(
        name
        for name, field in cls.model_fields.items()
        if not (
            isinstance(field.annotation, type) and issubclass(field.annotation, _IMMUTABLE_LEAVES)
        )
    )


@singledispatch
def _root_witness(value: object) -> object:
    """
    A token that changes whenever this value's root could change.

    A root is reused only while an equal witness is rebuilt. Three things decide a root:

    - The type, fixed once declared.
    - Contents this value owns, whose mutation paths raise its version.
    - The nested values' own witnesses, by the same argument one level down.

    An unregistered shape gets a token equal to nothing, biasing it slow rather than wrong.
    """
    return object()


@cache
def _witness_rule(cls: type) -> Callable[..., object]:
    """
    The rule that witnesses one class, resolved from the registry above once per class.

    A rule follows from a class's bases alone, so the answer never changes.
    A warm root is little more than this walk, so it is walked once per class.
    """
    return _root_witness.dispatch(cls)


@_root_witness.register(BaseUint)
@_root_witness.register(Boolean)
@_root_witness.register(ByteVector)
def _witness_leaf(value: BaseUint | Boolean | ByteVector) -> object:
    """An immutable leaf cannot change, leaving one shared token to serve them all."""
    return None


@_root_witness.register(ByteList)
@_root_witness.register(BitVector)
@_root_witness.register(BitList)
@_root_witness.register(ProgressiveBitList)
def _witness_packed(value: ByteList | BitVector | BitList | ProgressiveBitList) -> object:
    """A packed shape roots from its own contents alone, which its version covers."""
    return (value._version, len(value.data))


@cache
def _element_witness_rule(
    cls: type[Vector[SSZType] | List[SSZType] | ProgressiveList[SSZType]],
) -> Callable[..., object] | None:
    """
    The rule that witnesses one element of this sequence, or None if the elements need none.

    A leaf element has no interior to change, so the sequence's own version covers it.

    Every validated element is exactly ELEMENT_TYPE, so one resolution serves the whole
    sequence. Construction that skips validation can still leave an element of another
    class, and only a rule that re-reads that class survives it:

    - A nested sequence or struct re-reads it, to find its own element type or field names.
    - A packed shape reads a version and a count, which suit any shape and describe few.

    So the packed rule is the one that is never pinned to a sequence, and its elements
    keep the rule their own class resolves to.
    """
    element_type = cls.ELEMENT_TYPE
    if not issubclass(element_type, SSZModel):
        return None
    rule = _witness_rule(element_type)
    return _root_witness if rule is _witness_packed else rule


@_root_witness.register(Vector)
@_root_witness.register(List)
@_root_witness.register(ProgressiveList)
def _witness_sequence(
    value: Vector[SSZType] | List[SSZType] | ProgressiveList[SSZType],
) -> object:
    """A sequence of composites carries its elements' witnesses, since each can mutate."""
    element_rule = _element_witness_rule(type(value))
    if element_rule is None:
        return (value._version, len(value.data))
    # Mapped rather than looped: a comprehension would capture the rule in a cell, and
    # building that cell would cost every packed sequence above, which reads no rule at all.
    return (value._version, tuple(map(element_rule, value.data)))


@_root_witness.register(Container)
@_root_witness.register(ProgressiveContainer)
@_root_witness.register(CompatibleUnion)
def _witness_fields(value: Container | ProgressiveContainer | CompatibleUnion) -> object:
    """
    A struct carries the witness of every field that can hold a root of its own.

    A struct of leaves alone carries its version, which every field replacement raises.
    """
    names = _nested_field_names(type(value))
    if not names:
        return value._version
    # A field may hold a subclass of its annotation, so the rule follows the value's own class.
    #
    # A list rather than a generator, so the tuple can size its result in one pass.
    fields = [getattr(value, name) for name in names]
    return (value._version, tuple([_witness_rule(type(field))(field) for field in fields]))


def _root_from_layout(value: object) -> Root:
    """
    Root a value from its layout, remembering nothing.

    Raises:
        SSZTypeError: If the value's type has no registered handler.
    """
    layout = merkle_layout(value)
    chunks = layout.chunks()
    # The two tree shapes are the only ones SSZ defines.
    # A layout names one of them.
    if layout.limit is None:
        root = merkleize_progressive(chunks)
    else:
        root = merkleize(chunks, layout.limit)
    # A shape that mixes a word in puts its contents on the left and the word on the right.
    return root if layout.mixin is None else _mix_in(root, layout.mixin)


def hash_tree_root(value: object) -> Root:
    """
    Compute the SSZ Merkle root of a value.

    A value whose whole encoding fits one chunk is its own root, once padded.
    A value that can hold one reports the root it last computed, until a mutation
    invalidates the witness it was taken under.

    Raises:
        SSZTypeError: If the value's type has no registered handler.
    """
    # A value of at most one chunk bounds its tree at one leaf.
    # A one-leaf tree has no parent to hash, leaving the padded encoding as the root.
    #
    # Invariant: the layout states this rule too, for the proof machinery to walk.
    # A test pins the two against each other for every type.
    #
    # The plain checks come first because a negative check against the abstract base
    # costs more than the root it decides.
    # A leaf needs no memo either.
    # It cannot go stale, having nowhere to keep one.
    if isinstance(value, int):
        # One conversion at the chunk width gives the encoding and its padding together.
        if isinstance(value, (BaseUint, Boolean)) and value.get_byte_length() <= BYTES_PER_CHUNK:
            return Root._trusted(value.to_bytes(BYTES_PER_CHUNK, "little"))
    # A byte array is its own encoding, needing only the padding.
    # Padding an empty one builds the zero chunk it roots to.
    elif isinstance(value, bytes):
        if len(value) <= BYTES_PER_CHUNK:
            return Root._trusted(value.ljust(BYTES_PER_CHUNK, b"\x00"))
    elif isinstance(value, SSZModel):
        witness = _witness_rule(type(value))(value)
        memo = value._root_memo
        if memo is not None and memo[0] == witness:
            if not PARANOID_ROOTS:
                return memo[1]
            recomputed = _root_from_layout(value)
            assert recomputed == memo[1], f"stale remembered root for {type(value).__name__}"
            return recomputed
        root = _root_from_layout(value)
        # A model declares no writable attributes, leaving the slot to be set directly.
        object.__setattr__(value, "_root_memo", (witness, root))
        return root

    return _root_from_layout(value)

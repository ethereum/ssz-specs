"""Merkleization primitives and hash-tree-root dispatch for SSZ."""

from __future__ import annotations

import math
from collections.abc import Iterable, Sequence
from dataclasses import dataclass
from functools import singledispatch
from hashlib import sha256
from itertools import accumulate, batched, repeat
from typing import Final

from ssz.bitfields import BitList, BitVector, ProgressiveBitList
from ssz.boolean import Boolean
from ssz.byte_arrays import ByteList, ByteVector
from ssz.collections import List, ProgressiveList, Vector
from ssz.container import Container, ProgressiveContainer
from ssz.exceptions import SSZTypeError, SSZValueError
from ssz.ssz_base import SSZType
from ssz.uint import BaseUint
from ssz.union import CompatibleUnion

BYTES_PER_CHUNK: Final = 32
"""Width of a Merkle leaf chunk in bytes."""

BITS_PER_CHUNK: Final = BYTES_PER_CHUNK * 8
"""Width of a Merkle leaf chunk in bits."""


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


def merkleize(chunks: Sequence[Chunk], limit: int | None = None) -> Root:
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

    Args:
        chunks: Leaf chunks, each exactly 32 bytes wide.
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
    if width == 1:
        return Root(chunks[0])

    # Walk one tree layer per outer iteration.
    # A missing right sibling pulls the all-zero subtree of the current size from the cache,
    # so unused zero leaves are never allocated.
    level: list[Chunk] = list(chunks)
    subtree_size = 1
    while subtree_size < width:
        next_level: list[Chunk] = []
        # Each pair holds the left and right child of one parent node.
        # An odd tail yields a length-one tuple.
        # Its missing right sibling is the all-zero subtree of the current size.
        for child_pair in batched(level, 2):
            left = child_pair[0]
            right = child_pair[1] if len(child_pair) == 2 else _zero_tree_root(subtree_size)
            next_level.append(Root(sha256(left + right).digest()))
        level = next_level
        subtree_size *= 2

    # Invariant: width is the next power of two of the leaf count or capacity,
    # so the loop above halves the level count down to exactly one root.
    assert len(level) == 1
    return Root(level[0])


def merkleize_progressive(chunks: Sequence[Chunk], num_leaves: int = 1) -> Root:
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

    return Root(sha256(subtree_root + successor_root).digest())


def _mix_in(root: Root, word: Chunk) -> Root:
    """Hash a subtree root against the word its shape mixes in, as the right child."""
    return Root(sha256(root + word).digest())


def length_word(length: int) -> Chunk:
    """
    The element count a variable-size shape mixes in, as one 32-byte little-endian word.

    Raises:
        SSZValueError: If the length is negative.
    """
    if length < 0:
        raise SSZValueError("length must be non-negative")
    return Chunk(length.to_bytes(BYTES_PER_CHUNK, "little"))


def active_fields_word(active_fields: Sequence[int]) -> Chunk:
    """
    The field layout a progressive container mixes in, as one 32-byte word.

    One bit per position, lowest bit first, so at most 256 positions fit the word:

        [1, 0, 1]  ->  05 00 00 ... 00

    The bound of 256 is enforced by the type that declares the layout, not here.
    """
    packed_bits = sum(1 << i for i, bit in enumerate(active_fields) if bit)
    return Chunk(packed_bits.to_bytes(BYTES_PER_CHUNK, "little"))


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
    return Chunk(selector.to_bytes(BYTES_PER_CHUNK, "little"))


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


def _pack_bytes(data: bytes) -> list[Chunk]:
    """
    Right-pad serialized bytes to a chunk boundary and split into chunks.

    Layout for a 5-byte payload:

        bytes    :  01 02 03 04 05
        padded   :  01 02 03 04 05 00 00 ... 00     (zero-padded to 32 bytes)
        chunks   :  [ Chunk(01 02 03 04 05 00 ...) ]

    Inner chunks are already chunk-aligned; only the trailing chunk is padded.
    """
    return [
        Chunk(data[i : i + BYTES_PER_CHUNK].ljust(BYTES_PER_CHUNK, b"\x00"))
        for i in range(0, len(data), BYTES_PER_CHUNK)
    ]


def _pack_bits(bits: Sequence[Boolean]) -> list[Chunk]:
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
    packed_bits = sum(1 << i for i, bit in enumerate(bits) if bit)
    return _pack_bytes(packed_bits.to_bytes(math.ceil(len(bits) / 8), "little"))


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

    packed: tuple[Chunk, ...]
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
        cls, chunks: Sequence[Chunk], *, limit: int | None, mixin: Chunk | None = None
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

    def chunks(self, start: int = 0, stop: int | None = None) -> list[Chunk]:
        """
        The leaves in a half-open range, as chunks.

        A nested value is rooted here rather than when the layout is built.
        A proof therefore hashes only the part of the tree it walks into.
        A root asks for every leaf, and hashes all of it.
        """
        if self.nested is None:
            return list(self.packed[start:stop])
        return [
            ZERO_ROOT if value is None else hash_tree_root(value)
            for value in self.nested[start:stop]
        ]


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
        limit=math.ceil(type(value).LIMIT / BYTES_PER_CHUNK),
        mixin=length_word(len(serialized_bytes)),
    )


@merkle_layout.register
def _layout_bitvector(value: BitVector) -> MerkleLayout:
    return MerkleLayout.packing(
        _pack_bits(value.data), limit=math.ceil(type(value).LENGTH / BITS_PER_CHUNK)
    )


@merkle_layout.register
def _layout_bitlist(value: BitList) -> MerkleLayout:
    return MerkleLayout.packing(
        _pack_bits(value.data),
        limit=math.ceil(type(value).LIMIT / BITS_PER_CHUNK),
        mixin=length_word(len(value.data)),
    )


@merkle_layout.register
def _layout_progressive_bitlist(value: ProgressiveBitList) -> MerkleLayout:
    # The count mixed in is the bit count, not the number of packed chunks.
    return MerkleLayout.packing(
        _pack_bits(value.data), limit=None, mixin=length_word(len(value.data))
    )


@merkle_layout.register
def _layout_vector(value: Vector) -> MerkleLayout:
    cls = type(value)
    element_type, length = cls.ELEMENT_TYPE, cls.LENGTH
    if issubclass(element_type, (BaseUint, Boolean)):
        # Basic elements pack their serialized bytes into a single byte stream before chunking.
        element_size = element_type.get_byte_length()
        return MerkleLayout.packing(
            _pack_bytes(b"".join(e.encode_bytes() for e in value)),
            limit=math.ceil(length * element_size / BYTES_PER_CHUNK),
        )
    # Composite elements each contribute their own hash tree root as a leaf.
    return MerkleLayout.nesting(value, limit=length)


@merkle_layout.register
def _layout_list(value: List) -> MerkleLayout:
    cls = type(value)
    element_type, limit = cls.ELEMENT_TYPE, cls.LIMIT
    mixin = length_word(len(value))
    if issubclass(element_type, (BaseUint, Boolean)):
        element_size = element_type.get_byte_length()
        return MerkleLayout.packing(
            _pack_bytes(b"".join(e.encode_bytes() for e in value)),
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
            _pack_bytes(b"".join(e.encode_bytes() for e in value)), limit=None, mixin=mixin
        )
    return MerkleLayout.nesting(value, limit=None, mixin=mixin)


@merkle_layout.register
def _layout_progressive_container(value: ProgressiveContainer) -> MerkleLayout:
    cls = type(value)
    # One leaf per layout position, not per field, though the spec's formula reads that way.
    # A cleared bit keeps its zero leaf, the gap that holds every other field still.
    positions: list[SSZType | None] = [None] * len(cls.ACTIVE_FIELDS)

    # Fields follow the set bits: the n-th field belongs at the n-th set position.
    # A strict pairing fails loudly rather than placing a field at the wrong one.
    active_positions = (i for i, bit in enumerate(cls.ACTIVE_FIELDS) if bit)
    for position, name in zip(active_positions, cls.model_fields, strict=True):
        positions[position] = getattr(value, name)

    return MerkleLayout.nesting(positions, limit=None, mixin=active_fields_word(cls.ACTIVE_FIELDS))


@merkle_layout.register
def _layout_compatible_union(value: CompatibleUnion) -> MerkleLayout:
    # The union adds no leaf of its own: the option's own root is the whole tree below.
    # One leaf of capacity is a tree of no depth.
    # The contained root is therefore the left child itself.
    return MerkleLayout.nesting((value.data,), limit=1, mixin=selector_word(int(value.selector)))


@merkle_layout.register
def _layout_container(value: Container) -> MerkleLayout:
    # Pydantic preserves declaration order, which is the canonical SSZ field order.
    cls = type(value)
    return MerkleLayout.nesting(
        (getattr(value, name) for name in cls.model_fields), limit=len(cls.model_fields)
    )


def hash_tree_root(value: object) -> Root:
    """
    Compute the SSZ Merkle root of a value.

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

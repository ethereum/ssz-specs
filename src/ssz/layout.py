"""What a value merkleizes into, stated before any of it is hashed."""

from __future__ import annotations

import math
from collections.abc import Iterable, Sequence
from dataclasses import dataclass
from functools import cache, singledispatch

from ssz.bitfields import BitList, BitVector, ProgressiveBitList
from ssz.boolean import Boolean
from ssz.byte_arrays import ByteList, ByteVector
from ssz.chunks import BITS_PER_CHUNK, BYTES_PER_CHUNK, Chunk
from ssz.collections import List, ProgressiveList, Vector
from ssz.container import Container, ProgressiveContainer
from ssz.exceptions import SSZTypeError, TypeFault
from ssz.mixins import active_fields_word, length_word, selector_word
from ssz.ssz_base import SSZModel, SSZType
from ssz.uint import BaseUint
from ssz.union import CompatibleUnion


def _pack_bytes(data: bytes) -> list[bytes]:
    """
    Right-pad serialized bytes to a chunk boundary and split into chunks.

    Layout for a 5-byte payload:

        bytes    :  01 02 03 04 05
        padded   :  01 02 03 04 05 00 00 ... 00     (zero-padded to 32 bytes)
        chunks   :  [ 01 02 03 04 05 00 ... 00 ]

    Only the trailing chunk is padded, so every chunk is exactly 32 bytes.
    They are plain bytes, nothing reading them but a hash.
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

    The delimiter and the length-mix are separate steps, left to the caller.
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

    Invariant: the width is the declared element type's, coerced on the way in.
    """
    if element_size == 1:
        return _pack_bytes(bytes(elements))
    # A list rather than a generator, so the join can size its result in one pass.
    return _pack_bytes(b"".join([int.to_bytes(e, element_size, "little") for e in elements]))


@dataclass(frozen=True, slots=True)
class PackedLeaves:
    """
    Leaves as data, where elements share a chunk with their neighbours.

    The chunk is the leaf, so nothing below it can be addressed.
    """

    chunks: tuple[bytes, ...]
    """The packed data, one 32-byte chunk per leaf."""

    def __len__(self) -> int:
        """Leaves held, one per chunk."""
        return len(self.chunks)


@dataclass(frozen=True, slots=True)
class NestedLeaves:
    """
    Leaves as values, one root each.

    A position carrying no value merkleizes as a zero leaf.
    """

    values: tuple[SSZType | None, ...]
    """The nested values, one per leaf, or None where the position carries none."""

    def __len__(self) -> int:
        """Leaves held, one per position, whether or not it carries a value."""
        return len(self.values)


type Leaves = PackedLeaves | NestedLeaves
"""What a shape puts under its tree: data sharing chunks, or values with roots of their own."""


@dataclass(frozen=True, slots=True)
class MerkleLayout:
    """
    The subtree one value merkleizes into, before any of it is hashed.

        shape                 leaves               tree                        mixed in
        Container             fields               bounded by the field count  -
        List                  elements or packing  bounded by the limit        count
        ProgressiveList       elements or packing  progressive spine           count
        ProgressiveContainer  layout positions     progressive spine           layout
        CompatibleUnion       the option it holds  bounded by one              selector

    Stating those steps rather than taking them lets a root and a proof share one rule.
    Leaves past the last are the zero padding the tree shape supplies.
    """

    leaves: Leaves
    """What the shape put under the tree, and which of the two ways it did it."""

    limit: int | None
    """Chunk capacity of the bounded tree over the leaves, or None for a progressive spine."""

    mixin: Chunk | None
    """Word the subtree root is hashed against, or None when the shape mixes nothing in."""

    @classmethod
    def packing(
        cls, chunks: Sequence[bytes], *, limit: int | None, mixin: Chunk | None = None
    ) -> MerkleLayout:
        """A layout whose leaves are packed data."""
        return cls(leaves=PackedLeaves(tuple(chunks)), limit=limit, mixin=mixin)

    @classmethod
    def nesting(
        cls, values: Iterable[SSZType | None], *, limit: int | None, mixin: Chunk | None = None
    ) -> MerkleLayout:
        """A layout whose leaves are the roots of nested values."""
        return cls(leaves=NestedLeaves(tuple(values)), limit=limit, mixin=mixin)

    @property
    def leaf_count(self) -> int:
        """Leaves the shape produced, before any zero padding."""
        # Either variant holds one entry per leaf, so neither has to be told apart to count.
        return len(self.leaves)


@singledispatch
def merkle_layout(value: object) -> MerkleLayout:
    """
    How one value merkleizes: its leaves, their tree shape, and the word mixed in.

    Raises:
        SSZTypeError: If the value's type has no registered handler.
    """
    raise SSZTypeError(TypeFault.NO_MERKLE_LAYOUT, type=type(value).__name__)


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
        limit=(type(value).declared_limit() + BYTES_PER_CHUNK - 1) // BYTES_PER_CHUNK,
        mixin=length_word(len(serialized_bytes)),
    )


@merkle_layout.register
def _layout_bitvector(value: BitVector) -> MerkleLayout:
    return MerkleLayout.packing(
        _pack_bits(value.data),
        limit=(type(value).declared_length() + BITS_PER_CHUNK - 1) // BITS_PER_CHUNK,
    )


@merkle_layout.register
def _layout_bitlist(value: BitList) -> MerkleLayout:
    return MerkleLayout.packing(
        _pack_bits(value.data),
        limit=(type(value).declared_limit() + BITS_PER_CHUNK - 1) // BITS_PER_CHUNK,
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
    element_type, length = cls.ELEMENT_TYPE, cls.declared_length()
    if issubclass(element_type, (BaseUint, Boolean)):
        # Basic elements pack their serialized bytes into a single byte stream before chunking.
        element_size = element_type.get_byte_length()
        return MerkleLayout.packing(
            _pack_basic_elements(value.data, element_size),
            limit=(length * element_size + BYTES_PER_CHUNK - 1) // BYTES_PER_CHUNK,
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
            limit=(limit * element_size + BYTES_PER_CHUNK - 1) // BYTES_PER_CHUNK,
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
    #
    # The leaf count is therefore the layout width, never the field count.
    #
    # Six positions holding three fields merkleize six leaves, where three would root differently.
    cls = type(value)
    # A layout is declared as bits and never coerced, so a list of them arrives as one.
    names, word = progressive_container_plan(tuple(cls.ACTIVE_FIELDS), field_names(cls))
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
    names = field_names(type(value))
    return MerkleLayout.nesting([getattr(value, name) for name in names], limit=len(names))


@cache
def progressive_container_plan(
    active_fields: tuple[int, ...], field_names: tuple[str, ...]
) -> tuple[tuple[str | None, ...], Chunk]:
    """
    Which field sits at each position of a progressive layout, and the word mixed in.

    One entry per position, naming the field that sits there, or None for a gap.
    Neither answer reads the value, so both are worked out once per layout.

    Keyed by the layout, never by the type, since a layout can be rewritten afterwards.
    A value that has already rooted keeps the root it took.

    Raises:
        SSZTypeError: A layout that does not pair with the fields one to one.
    """
    positions: list[str | None] = [None] * len(active_fields)
    active_positions = [position for position, bit in enumerate(active_fields) if bit]
    # The declaration checks this pairing too, and a reassigned layout arrives unchecked.
    # So the layout rides along, since the declared one is no longer the one in force.
    if len(active_positions) != len(field_names):
        raise SSZTypeError(
            TypeFault.LAYOUT_FIELD_COUNT,
            active=len(active_positions),
            declared=len(field_names),
            layout=active_fields,
        )
    # Fields follow the set bits: the n-th field belongs at the n-th set position.
    for position, name in zip(active_positions, field_names, strict=True):
        positions[position] = name
    return tuple(positions), active_fields_word(active_fields)


@cache
def field_names(cls: type[SSZModel]) -> tuple[str, ...]:
    """
    Every field name, in the declaration order that is the canonical SSZ field order.

    Cached because a layout wants them twice, and the model's mapping is a property.
    """
    return tuple(cls.model_fields)

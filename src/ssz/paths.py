"""Paths through an SSZ type, resolved to the generalized index of the node they select."""

import math
from typing import Final, NamedTuple

from ssz.bitfields import BitList, BitVector, ProgressiveBitList
from ssz.boolean import Boolean
from ssz.byte_arrays import ByteList, ByteVector
from ssz.collections import List, ProgressiveList, Vector
from ssz.container import Container, ProgressiveContainer
from ssz.exceptions import SSZTypeError, SSZValueError, TypeFault, ValueFault
from ssz.gindex import gindex_child, gindex_concat, progressive_chunk_gindex
from ssz.merkleization import (
    BITS_PER_CHUNK,
    BYTES_PER_CHUNK,
    _field_names,
    _next_pow2,
    _progressive_container_plan,
)
from ssz.ssz_base import SSZType
from ssz.uint import BaseUint, Uint8
from ssz.union import CompatibleUnion

LENGTH_KEY: Final = "__len__"
"""Path step addressing the element count mixed into a variable-size root."""

ACTIVE_FIELDS_KEY: Final = "__active_fields__"
"""Path step addressing the field layout mixed into a progressive container root."""

SELECTOR_KEY: Final = "__selector__"
"""Path step addressing the type selector mixed into a compatible union root."""

type PathStep = int | str
"""One step of a path: a field name, an element position, or a mixed-in word."""


_MIXED_IN_WORDS: Final[dict[PathStep, tuple[tuple[type[SSZType], ...], str]]] = {
    LENGTH_KEY: ((List, ByteList, BitList, ProgressiveList, ProgressiveBitList), "element count"),
    ACTIVE_FIELDS_KEY: ((ProgressiveContainer,), "field layout"),
    SELECTOR_KEY: ((CompatibleUnion,), "type selector"),
}
"""Each reserved step: the shapes that mix that word in, and what the word is called.

This is the whole set of words an SSZ root is hashed against.
An integer step misses the table, a position being no reserved word.
"""


class ChunkPosition(NamedTuple):
    """Where one element sits: the chunk that holds it, and its byte range inside that chunk."""

    chunk: int
    """Leaf the element lands in, which is what a generalized index names."""

    start: int
    """First byte of the element inside that chunk."""

    stop: int
    """One past the element's last byte, equal to the first where the element is a single bit."""


def item_length(ssz_type: type[SSZType]) -> int:
    """Bytes one element of this type occupies inside a chunk, or a whole chunk if composite."""
    if issubclass(ssz_type, (BaseUint, Boolean)):
        return ssz_type.get_byte_length()
    return BYTES_PER_CHUNK


def chunk_count(ssz_type: type[SSZType]) -> int:
    """
    Leaves this type merkleizes into, counting only its own level.

    A basic value is one leaf, and bits and basic elements pack several to a leaf.
    A composite element or a field takes one of its own.

    Raises:
        SSZTypeError: A shape with no bounded leaf count.
    """
    if issubclass(ssz_type, (BaseUint, Boolean)):
        return 1
    if issubclass(ssz_type, CompatibleUnion):
        # A union adds no leaf of its own: the option it holds is the whole tree below.
        return 1
    if issubclass(ssz_type, BitVector):
        return (ssz_type.declared_length() + BITS_PER_CHUNK - 1) // BITS_PER_CHUNK
    if issubclass(ssz_type, BitList):
        return (ssz_type.declared_limit() + BITS_PER_CHUNK - 1) // BITS_PER_CHUNK
    if issubclass(ssz_type, ByteVector):
        return (ssz_type.declared_length() + BYTES_PER_CHUNK - 1) // BYTES_PER_CHUNK
    if issubclass(ssz_type, ByteList):
        return (ssz_type.declared_limit() + BYTES_PER_CHUNK - 1) // BYTES_PER_CHUNK
    if issubclass(ssz_type, Vector):
        width = ssz_type.declared_length() * item_length(ssz_type.ELEMENT_TYPE)
        return (width + BYTES_PER_CHUNK - 1) // BYTES_PER_CHUNK
    if issubclass(ssz_type, List):
        width = ssz_type.declared_limit() * item_length(ssz_type.ELEMENT_TYPE)
        return (width + BYTES_PER_CHUNK - 1) // BYTES_PER_CHUNK
    if issubclass(ssz_type, Container):
        return len(_field_names(ssz_type))
    # A progressive shape grows without bound.
    # It therefore has no leaf count to report.
    raise SSZTypeError(TypeFault.NO_CHUNK_COUNT, type=ssz_type.__name__)


def element_type(ssz_type: type[SSZType], step: PathStep) -> type[SSZType]:
    """
    Type reached by one step of a path.

    Raises:
        SSZTypeError: A shape with nothing to step into.
        SSZValueError: An unknown field name.
    """
    if issubclass(ssz_type, (Container, ProgressiveContainer)):
        for name, field_type in ssz_type._FIELD_TYPES:
            if name == str(step):
                return field_type
        raise SSZValueError(ValueFault.NO_SUCH_FIELD, type=ssz_type.__name__, step=step)
    if issubclass(ssz_type, (BitVector, BitList, ProgressiveBitList)):
        return Boolean
    if issubclass(ssz_type, (ByteVector, ByteList)):
        # A byte array is a collection of single opaque bytes.
        return Uint8
    if issubclass(ssz_type, (Vector, List, ProgressiveList)):
        return ssz_type.ELEMENT_TYPE
    raise SSZTypeError(TypeFault.NOT_STEPPABLE, type=ssz_type.__name__)


def _position_count(ssz_type: type[SSZType]) -> float:
    """
    Positions the shape declares, or no bound for one that grows with its data.

    A declared position is addressable whether or not a value fills it.
    """
    if issubclass(ssz_type, (ProgressiveList, ProgressiveBitList)):
        return math.inf
    if issubclass(ssz_type, (Vector, ByteVector, BitVector)):
        return ssz_type.declared_length()
    if issubclass(ssz_type, (List, ByteList, BitList)):
        return ssz_type.declared_limit()
    raise SSZTypeError(TypeFault.NOT_STEPPABLE, type=ssz_type.__name__)


def _element_position(ssz_type: type[SSZType], step: PathStep) -> int:
    """
    The position one step selects, refused unless the shape declares it.

    Unchecked, the arithmetic runs on any integer and lands on a real node:

        element -1 of a list    ->  the mixed-in element count
        element -1 of a vector  ->  the root
    """
    # A boolean is an integer in Python and a nonsense position everywhere else.
    if not isinstance(step, int) or isinstance(step, bool):
        raise SSZValueError(ValueFault.NOT_A_POSITION, step=step)
    if not 0 <= step < _position_count(ssz_type):
        raise SSZValueError(ValueFault.NO_SUCH_POSITION, type=ssz_type.__name__, step=step)
    return step


def _field_layout_position(ssz_type: type[ProgressiveContainer], step: PathStep) -> int:
    """
    Layout position of one field of a progressive container.

    A field sits at the n-th set position rather than at its ordinal, skipping a vacancy:

        layout (1, 0, 1, 1) with fields p, q, r  ->  p at 0, q at 2, r at 3

    Raises:
        SSZValueError: An unknown field name.
        SSZTypeError: A layout that no longer pairs with its fields.
    """
    names = _field_names(ssz_type)
    if str(step) not in names:
        raise SSZValueError(ValueFault.NO_SUCH_FIELD, type=ssz_type.__name__, step=step)
    # A layout is declared as bits and never coerced, so a list of them arrives as one.
    positions, _ = _progressive_container_plan(tuple(ssz_type.ACTIVE_FIELDS), names)
    return positions.index(str(step))


def chunk_position(ssz_type: type[SSZType], step: PathStep) -> ChunkPosition:
    """
    Where one element sits: its chunk, and the byte range it occupies inside that chunk.

    A generalized index names a chunk, and packed elements share one, so a proof reaches
    all of them and the byte range says which was asked for:

        List[Uint64, 8], element 3  ->  chunk 0, bytes 24 to 32

    Raises:
        SSZTypeError: A shape with no positions to address.
        SSZValueError: An unknown field name, or a position the shape does not declare.
    """
    if issubclass(ssz_type, ProgressiveContainer):
        # A progressive container merkleizes a field at its layout position, not at its ordinal.
        return ChunkPosition(
            _field_layout_position(ssz_type, step), 0, item_length(element_type(ssz_type, step))
        )
    if issubclass(ssz_type, Container):
        names = _field_names(ssz_type)
        if str(step) not in names:
            raise SSZValueError(ValueFault.NO_SUCH_FIELD, type=ssz_type.__name__, step=step)
        return ChunkPosition(names.index(str(step)), 0, item_length(element_type(ssz_type, step)))
    position = _element_position(ssz_type, step)
    if issubclass(ssz_type, (BitVector, BitList, ProgressiveBitList)):
        # One bit occupies no whole byte.
        # A bit therefore reports a chunk with an empty range inside it.
        return ChunkPosition(position // BITS_PER_CHUNK, 0, 0)
    width = item_length(element_type(ssz_type, step))
    start = position * width
    return ChunkPosition(
        start // BYTES_PER_CHUNK, start % BYTES_PER_CHUNK, start % BYTES_PER_CHUNK + width
    )


def get_generalized_index(ssz_type: type[SSZType], *path: PathStep) -> int:
    """
    Position in a Merkle tree of the value a path selects.

    Steps are field names and element positions.
    A reserved word names the mixed-in word instead, and ends the path:

        get_generalized_index(BeaconState, "finalized_checkpoint", "root")
        get_generalized_index(Attestations, "__len__")

    That word is the right child, which puts the contents on the left.
    In a progressive container or a union it is also the only thing separating an absent
    field from one holding zero.

    Raises:
        SSZTypeError: A step the shape cannot take.
        SSZValueError: A name, selector or position the shape does not have.
    """
    index = 1
    current = ssz_type
    for position, step in enumerate(path):
        # A basic value is one leaf with nothing inside it.
        if issubclass(current, (BaseUint, Boolean)):
            raise SSZTypeError(TypeFault.NO_PARTS, type=current.__name__)

        # A mixed-in word is one leaf too, and it ends the path that names it.
        if (mixin := _MIXED_IN_WORDS.get(step)) is not None:
            shapes, word = mixin
            if not issubclass(current, shapes):
                raise SSZTypeError(TypeFault.NO_MIXIN, type=current.__name__, word=word)
            if position != len(path) - 1:
                raise SSZTypeError(TypeFault.NO_PARTS_MIXIN, type=current.__name__, word=word)
            return gindex_child(index, right_side=True)

        if issubclass(current, CompatibleUnion):
            if not isinstance(step, int) or isinstance(step, bool):
                raise SSZValueError(ValueFault.NOT_A_POSITION, step=step)
            option = current.OPTIONS.get(step)
            if option is None:
                raise SSZValueError(ValueFault.NO_SUCH_OPTION, type=current.__name__, step=step)
            # Every option shares the left child.
            # That is what keeps a field common to several options at one position.
            index = gindex_child(index, right_side=False)
            current = option
            continue

        if issubclass(current, (ProgressiveContainer, ProgressiveList, ProgressiveBitList)):
            # A progressive shape places its chunks on a spine rather than in a bounded tree.
            index = gindex_concat(
                index, progressive_chunk_gindex(chunk_position(current, step).chunk)
            )
            current = element_type(current, step)
            continue

        chunk = chunk_position(current, step).chunk
        # A mixed-in element count sits at the right child.
        # The contents therefore start one level down, on the left.
        if issubclass(current, (List, ByteList, BitList)):
            index = gindex_child(index, right_side=False)
        # In a bounded tree of a given width, chunk c is the node at width + c.
        index = gindex_concat(index, _next_pow2(chunk_count(current)) + chunk)
        current = element_type(current, step)

    return index

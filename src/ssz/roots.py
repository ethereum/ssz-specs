"""Rooting a value, and the witness that lets a root be reused."""

from __future__ import annotations

import os
from collections.abc import Callable
from functools import cache, singledispatch
from typing import Final

from ssz.bitfields import BitList, BitVector, ProgressiveBitList
from ssz.boolean import Boolean
from ssz.byte_arrays import ByteList, ByteVector
from ssz.chunks import BYTES_PER_CHUNK, ZERO_ROOT, Root
from ssz.collections import List, ProgressiveList, Vector
from ssz.container import Container, ProgressiveContainer
from ssz.exceptions import SSZValueError, ValueFault
from ssz.layout import MerkleLayout, merkle_layout
from ssz.mixins import mix_in
from ssz.ssz_base import SSZModel, SSZType
from ssz.trees import merkleize, merkleize_progressive
from ssz.uint import BaseUint
from ssz.union import CompatibleUnion

PARANOID_ROOTS: bool = os.environ.get("SSZ_PARANOID_ROOTS") == "1"
"""
Whether every remembered root is recomputed and checked against the memo.

A proof built from the same layout agrees with a stale root while both are wrong.
Recomputing is the only evidence against one.
Enable with SSZ_PARANOID_ROOTS=1.
"""


def layout_chunks(layout: MerkleLayout, start: int = 0, stop: int | None = None) -> list[bytes]:
    """
    The leaves in a half-open range, as chunks.

    A nested value is rooted here rather than when the layout is built.
    A proof therefore hashes only the part of the tree it walks into.

    Every leaf is 32 bytes: a packed one is plain bytes, a nested one its own root.
    """
    if layout.nested is None:
        return list(layout.packed[start:stop])
    values = layout.nested[start:stop]
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


_IMMUTABLE_LEAVES: Final = (BaseUint, Boolean, ByteVector)
"""The SSZ types that subclass an immutable builtin, whose roots cannot go stale."""


@cache
def _nested_field_names(cls: type[SSZModel]) -> tuple[str, ...]:
    """
    The fields of a struct that can hold a value with a root of its own.

    Leaf fields are dropped: reading eight of them on each of 64 validators would cost
    512 reads for nothing.
    A field with no single declared class is kept.
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

    A root is reused only while an equal witness is rebuilt.
    Three things decide one:

    - The type, fixed once declared.
    - Contents this value owns, whose mutation paths raise its version.
    - The nested values' own witnesses, one level down.

    An unregistered shape gets a token equal to nothing, so it is slow rather than wrong.
    """
    return object()


@cache
def _witness_rule(cls: type) -> Callable[..., object]:
    """
    The rule that witnesses one class, resolved from the registry above once per class.

    A rule follows from a class's bases alone, so it is resolved once per class.
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
    Every validated element is exactly the declared type, so one resolution serves all.

    Construction that skips validation can leave an element of another class.
    A packed element survives that, its rule reading a version and a count that suit any shape.
    A leaf-typed one does not, which a test pins as a known limitation.
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
    # Mapped rather than looped, because a comprehension would capture the rule in a cell.
    # Building that cell would cost every packed sequence above, which reads no rule at all.
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
    chunks = layout_chunks(
        layout,
    )
    # The two tree shapes are the only ones SSZ defines.
    # A layout names one of them.
    if layout.limit is None:
        root = merkleize_progressive(chunks)
    else:
        root = merkleize(chunks, layout.limit)
    # A shape that mixes a word in puts its contents on the left and the word on the right.
    return root if layout.mixin is None else mix_in(root, layout.mixin)


def hash_tree_root(value: object) -> Root:
    """
    Compute the SSZ Merkle root of a value.

    A value whose whole encoding fits one chunk is its own root, once padded.
    A value that can hold one reports the root it last computed, until a mutation
    invalidates its witness.

    Raises:
        SSZTypeError: If the value's type has no registered handler.
    """
    # A value of at most one chunk bounds its tree at one leaf.
    # A one-leaf tree has no parent to hash, leaving the padded encoding as the root.
    #
    # Invariant: the layout states this rule too, for the proof machinery to walk.
    # A test pins the two against each other for every type.
    #
    # The plain checks come first, a negative check against the abstract base being dearer.
    # It would cost more than the root it decides.
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
            # Raised rather than asserted: an interpreter run with assertions off would
            # otherwise pay the recomputation and check nothing, which is the one thing
            # this mode exists to do.
            if recomputed != memo[1]:
                raise SSZValueError(ValueFault.STALE_ROOT, type=type(value).__name__)
            return recomputed
        root = _root_from_layout(value)
        # A model declares no writable attributes, leaving the slot to be set directly.
        object.__setattr__(value, "_root_memo", (witness, root))
        return root

    return _root_from_layout(value)

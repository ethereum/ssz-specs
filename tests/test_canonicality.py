"""One encoding per value, and one value per accepted encoding."""

import io
from collections.abc import Sequence
from typing import Any

import pytest
from hypothesis import given, settings, strategies as st

from ssz import (
    BitList,
    BitVector,
    Boolean,
    Byte,
    ByteList,
    ByteVector,
    CompatibleUnion,
    Container,
    List,
    ProgressiveBitList,
    ProgressiveContainer,
    ProgressiveList,
    SSZError,
    SSZType,
    Uint8,
    Uint16,
    Uint32,
    Uint64,
    Uint128,
    Uint256,
    Vector,
)
from ssz.offsets import BYTES_PER_LENGTH_OFFSET
from ssz.roots import hash_tree_root
from ssz.ssz_base import SSZCollection
from ssz.uint import BaseUint


class Bytes4(ByteVector):
    """A four-byte fixed array."""

    LENGTH = 4


class ByteList8(ByteList):
    """A byte string of at most eight bytes."""

    LIMIT = 8


class BitVector12(BitVector):
    """A bit vector whose width leaves four padding bits in its final byte."""

    LENGTH = 12


class BitList13(BitList):
    """A bit list whose limit lets the delimiter spill into a second byte."""

    LIMIT = 13


class Uint16Vector3(Vector[Uint16]):
    """A vector of three fixed-size elements."""

    LENGTH = 3


class ByteList8Vector2(Vector[ByteList8]):
    """A vector of two variable-size elements, so it carries an offset table."""

    LENGTH = 2


class Uint16List5(List[Uint16]):
    """A list of at most five fixed-size elements."""

    LIMIT = 5


class ByteList8List3(List[ByteList8]):
    """A list of at most three variable-size elements."""

    LIMIT = 3


class Uint16ProgressiveList(ProgressiveList[Uint16]):
    """A progressive list of fixed-size elements."""


class ByteList8ProgressiveList(ProgressiveList[ByteList8]):
    """A progressive list of variable-size elements."""


class OneVar(Container):
    """A struct with one variable field, so its offset table holds a single entry."""

    head: Uint32
    tail: ByteList8


class Mixed(Container):
    """A struct interleaving fixed and variable fields."""

    a: Uint64
    b: Uint16List5
    c: Boolean
    d: ByteList8


class GappedProgressive(ProgressiveContainer):
    """A struct whose layout leaves three positions empty between its fields."""

    ACTIVE_FIELDS = (1, 0, 1, 0, 0, 1)

    head: Uint32
    body: ByteList8
    flags: BitList13


class Square(ProgressiveContainer):
    """A fixed-size union option, holding its colour at position two."""

    ACTIVE_FIELDS = (1, 0, 1)

    side: Uint16
    color: Uint8


class Circle(ProgressiveContainer):
    """The other fixed-size option, holding the same colour at the same position."""

    ACTIVE_FIELDS = (0, 1, 1)

    radius: Uint16
    color: Uint8


class Tagged(ProgressiveContainer):
    """A variable-size union option, its payload at position two."""

    ACTIVE_FIELDS = (1, 0, 1)

    tag: Uint8
    payload: ByteList8


class Labelled(ProgressiveContainer):
    """The other variable-size option, its payload at the same position."""

    ACTIVE_FIELDS = (0, 1, 1)

    label: Uint8
    payload: ByteList8


class Shape(CompatibleUnion):
    """A union over the two fixed-size options."""

    OPTIONS = {1: Square, 2: Circle}


class Payload(CompatibleUnion):
    """A union over the two variable-size options."""

    OPTIONS = {1: Tagged, 3: Labelled}


def _uints(uint_type: type[BaseUint]) -> st.SearchStrategy[BaseUint]:
    """Every value the width admits, the boundaries included."""
    return st.integers(min_value=0, max_value=2**uint_type.BITS - 1).map(uint_type)


def _bits(
    bitfield_type: type[SSZCollection[Boolean]], *, min_size: int = 0, max_size: int
) -> st.SearchStrategy[SSZType]:
    """Bit patterns of the widths this bitfield admits."""
    return st.lists(st.booleans(), min_size=min_size, max_size=max_size).map(
        lambda drawn: bitfield_type(data=[Boolean(bit) for bit in drawn])
    )


def _sequences(
    collection_type: type[SSZCollection[Any]],
    elements: st.SearchStrategy[SSZType],
    *,
    min_size: int = 0,
    max_size: int,
) -> st.SearchStrategy[SSZType]:
    """Element sequences of the counts this collection admits."""
    return st.lists(elements, min_size=min_size, max_size=max_size).map(
        lambda drawn: collection_type(data=drawn)
    )


_BYTE_STRINGS = st.binary(max_size=8).map(lambda raw: ByteList8(data=raw))

_UNIVERSE: dict[type[SSZType], st.SearchStrategy[SSZType]] = {
    Uint8: _uints(Uint8),
    Uint16: _uints(Uint16),
    Uint32: _uints(Uint32),
    Uint64: _uints(Uint64),
    Uint128: _uints(Uint128),
    Uint256: _uints(Uint256),
    Byte: _uints(Byte),
    Boolean: st.booleans().map(Boolean),
    Bytes4: st.binary(min_size=4, max_size=4).map(Bytes4),
    ByteList8: _BYTE_STRINGS,
    BitVector12: _bits(BitVector12, min_size=12, max_size=12),
    BitList13: _bits(BitList13, max_size=13),
    ProgressiveBitList: _bits(ProgressiveBitList, max_size=40),
    Uint16Vector3: _sequences(Uint16Vector3, _uints(Uint16), min_size=3, max_size=3),
    ByteList8Vector2: _sequences(ByteList8Vector2, _BYTE_STRINGS, min_size=2, max_size=2),
    Uint16List5: _sequences(Uint16List5, _uints(Uint16), max_size=5),
    ByteList8List3: _sequences(ByteList8List3, _BYTE_STRINGS, max_size=3),
    Uint16ProgressiveList: _sequences(Uint16ProgressiveList, _uints(Uint16), max_size=9),
    ByteList8ProgressiveList: _sequences(ByteList8ProgressiveList, _BYTE_STRINGS, max_size=4),
    OneVar: st.builds(OneVar, head=_uints(Uint32), tail=_BYTE_STRINGS),
    Mixed: st.builds(
        Mixed,
        a=_uints(Uint64),
        b=_sequences(Uint16List5, _uints(Uint16), max_size=5),
        c=st.booleans().map(Boolean),
        d=_BYTE_STRINGS,
    ),
    GappedProgressive: st.builds(
        GappedProgressive,
        head=_uints(Uint32),
        body=_BYTE_STRINGS,
        flags=_bits(BitList13, max_size=13),
    ),
    Shape: st.one_of(
        st.builds(
            Shape,
            selector=st.just(Uint8(1)),
            data=st.builds(Square, side=_uints(Uint16), color=_uints(Uint8)),
        ),
        st.builds(
            Shape,
            selector=st.just(Uint8(2)),
            data=st.builds(Circle, radius=_uints(Uint16), color=_uints(Uint8)),
        ),
    ),
    Payload: st.one_of(
        st.builds(
            Payload,
            selector=st.just(Uint8(1)),
            data=st.builds(Tagged, tag=_uints(Uint8), payload=_BYTE_STRINGS),
        ),
        st.builds(
            Payload,
            selector=st.just(Uint8(3)),
            data=st.builds(Labelled, label=_uints(Uint8), payload=_BYTE_STRINGS),
        ),
    ),
}

TYPE_UNIVERSE = [
    pytest.param(ssz_type, values, id=ssz_type.__name__) for ssz_type, values in _UNIVERSE.items()
]


def _shift_word(encoding: bytes, start: int, delta: int) -> bytes:
    """The encoding with the four-byte little-endian word at one position moved, as an offset."""
    end = start + BYTES_PER_LENGTH_OFFSET
    word = int.from_bytes(encoding[start:end], "little")
    moved = (word + delta) % (1 << (8 * BYTES_PER_LENGTH_OFFSET))
    return encoding[:start] + moved.to_bytes(BYTES_PER_LENGTH_OFFSET, "little") + encoding[end:]


def _pointers(encoding: bytes) -> tuple[int, ...]:
    """Every position within the encoding that some four-byte window of it names."""
    windows = range(len(encoding) - BYTES_PER_LENGTH_OFFSET + 1)
    return tuple(
        sorted(
            {
                word
                for start in windows
                if (
                    word := int.from_bytes(
                        encoding[start : start + BYTES_PER_LENGTH_OFFSET], "little"
                    )
                )
                <= len(encoding)
            }
        )
    )


def _resized(encoding: bytes, at: int, delta: int) -> bytes:
    """The encoding with bytes opened or closed at one position, every word past it moved along."""
    limit = 1 << (8 * BYTES_PER_LENGTH_OFFSET)
    if delta >= 0:
        resized = bytearray(encoding[:at] + bytes(delta) + encoding[at:])
    else:
        resized = bytearray(encoding[:at] + encoding[at - delta :])
    for start in range(len(encoding) - BYTES_PER_LENGTH_OFFSET + 1):
        end = start + BYTES_PER_LENGTH_OFFSET
        word = int.from_bytes(encoding[start:end], "little")
        if at <= word <= len(encoding):
            resized[start:end] = ((word + delta) % limit).to_bytes(
                BYTES_PER_LENGTH_OFFSET, "little"
            )
    return bytes(resized)


def _edited(encoding: bytes) -> st.SearchStrategy[bytes]:
    """One short edit: a splice, a cut, a byte swapped, or a four-byte word moved."""
    edits = [
        st.tuples(
            st.integers(min_value=0, max_value=len(encoding)),
            st.binary(min_size=1, max_size=4),
        ).map(lambda edit: encoding[: edit[0]] + edit[1] + encoding[edit[0] :]),
    ]
    if encoding:
        positions = st.integers(min_value=0, max_value=len(encoding) - 1)
        edits.append(
            st.tuples(positions, st.integers(min_value=1, max_value=4)).map(
                lambda edit: encoding[: edit[0]] + encoding[edit[0] + edit[1] :]
            )
        )
        edits.append(
            st.tuples(positions, st.integers(min_value=0, max_value=255)).map(
                lambda edit: encoding[: edit[0]] + bytes((edit[1],)) + encoding[edit[0] + 1 :]
            )
        )
        edits.append(
            st.tuples(positions, st.integers(min_value=0, max_value=7)).map(
                lambda edit: (
                    encoding[: edit[0]]
                    + bytes((encoding[edit[0]] ^ 1 << edit[1],))
                    + encoding[edit[0] + 1 :]
                )
            )
        )
    # An offset sits at whatever byte its own fixed part reaches, which is rarely a round one.
    if len(encoding) >= BYTES_PER_LENGTH_OFFSET:
        edits.append(
            st.tuples(
                st.integers(min_value=0, max_value=len(encoding) - BYTES_PER_LENGTH_OFFSET),
                st.integers(min_value=-4, max_value=4),
            ).map(lambda edit: _shift_word(encoding, *edit))
        )
    return st.one_of(edits)


def _near(encoding: bytes) -> st.SearchStrategy[bytes]:
    """Byte strings up to three short edits away from a valid one."""
    once = _edited(encoding)
    twice = once.flatmap(_edited)
    return st.one_of(once, twice, twice.flatmap(_edited))


def _regapped(encoding: bytes) -> st.SearchStrategy[bytes]:
    """A gap opened, or an overlap closed, at a position the encoding itself points to."""
    # An offset table is consistent as a whole, so a moved body is refused as a table, not a gap.
    boundaries = _pointers(encoding)
    if not boundaries:
        return st.just(encoding)
    return st.tuples(
        st.sampled_from(boundaries),
        st.integers(min_value=-4, max_value=4).filter(bool),
    ).map(lambda edit: _resized(encoding, *edit))


def _final_bit_set(encoding: bytes) -> st.SearchStrategy[bytes]:
    """The encoding with one more bit set in its final byte, where padding and a delimiter live."""
    if not encoding:
        return st.binary(max_size=1)
    return st.sampled_from(range(8)).map(
        lambda bit: encoding[:-1] + bytes((encoding[-1] | 1 << bit,))
    )


def _byte_strings(values: st.SearchStrategy[SSZType]) -> st.SearchStrategy[bytes]:
    """Candidate inputs: near a valid encoding, regapped, of a valid width, or unrelated."""
    encodings = values.map(lambda value: value.encode_bytes())
    return st.one_of(
        encodings.flatmap(_near),
        encodings.flatmap(_regapped),
        # A fixed-size shape admits inputs of one width alone, and every bit of one is fair game.
        encodings.flatmap(
            lambda encoding: st.binary(min_size=len(encoding), max_size=len(encoding))
        ),
        encodings.flatmap(_final_bit_set),
        st.binary(max_size=48),
    )


@pytest.mark.parametrize(("ssz_type", "values"), TYPE_UNIVERSE)
@given(data=st.data())
@settings(derandomize=True, max_examples=500)
def test_re_encoding_an_accepted_input_reproduces_it(
    ssz_type: type[SSZType], values: st.SearchStrategy[SSZType], data: st.DataObject
) -> None:
    """A value read within a budget spends every byte of it, and re-encodes to those bytes."""
    candidate = data.draw(_byte_strings(values))
    stream = io.BytesIO(candidate)
    try:
        # Anything a decoder refuses it refuses as an SSZ fault, so nothing wider is caught.
        decoded = ssz_type.deserialize(stream, len(candidate))
    except SSZError:
        return

    # A nested budget comes from an enclosing table, so leaving it part spent is a second spelling.
    assert stream.tell() == len(candidate)
    assert decoded.encode_bytes() == candidate


@pytest.mark.parametrize(("ssz_type", "values"), TYPE_UNIVERSE)
@given(data=st.data())
@settings(derandomize=True)
def test_values_and_encodings_stand_one_to_one(
    ssz_type: type[SSZType], values: st.SearchStrategy[SSZType], data: st.DataObject
) -> None:
    """Two values of one type share an encoding only by being the same value."""
    left = data.draw(values)
    right = data.draw(values)

    assert (left == right) == (left.encode_bytes() == right.encode_bytes())


@pytest.mark.parametrize(("ssz_type", "values"), TYPE_UNIVERSE)
@given(data=st.data())
@settings(derandomize=True)
def test_a_root_survives_an_encode_and_decode_round_trip(
    ssz_type: type[SSZType], values: st.SearchStrategy[SSZType], data: st.DataObject
) -> None:
    """A value rebuilt from its own bytes roots to what the value it came from rooted to."""
    value = data.draw(values)

    # Rooted before the encoding, so a remembered root is what the fresh value is checked against.
    root = hash_tree_root(value)

    assert hash_tree_root(ssz_type.decode_bytes(value.encode_bytes())) == root


def test_the_universe_covers_every_shape() -> None:
    """A shape absent from the universe is a shape these three properties never reach."""
    shapes: Sequence[type[SSZType]] = (
        BaseUint,
        Boolean,
        ByteVector,
        ByteList,
        BitVector,
        BitList,
        ProgressiveBitList,
        Vector,
        List,
        ProgressiveList,
        Container,
        ProgressiveContainer,
        CompatibleUnion,
    )
    covered = {shape for shape in shapes if any(issubclass(known, shape) for known in _UNIVERSE)}

    assert covered == set(shapes)

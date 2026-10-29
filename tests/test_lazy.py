"""Elements read from an encoding on first use, against the plain list they stand for."""

from __future__ import annotations

import copy
import io
import pickle
import random
from array import array
from typing import Any

import pytest

from ssz import ByteList, List, Uint64
from ssz.lazy import UNREAD, LazyElements


class Note(ByteList):
    """A short run of opaque bytes, so elements have bodies of varying width."""

    LIMIT = 6


class Notes(List[Note]):
    """Notes behind an offset table."""

    LIMIT = 256


class Words(List[Uint64]):
    """Integers, eight bytes apart."""

    LIMIT = 256


def _words(values: list[Uint64]) -> LazyElements:
    """Integers over their encoding, none decoded yet."""
    encoding = Words(data=values).encode_bytes()
    return LazyElements(
        encoding,
        0,
        len(encoding),
        len(values),
        8,
        None,
        lambda data, start, stop: Uint64.decode_bytes(data[start:stop]),
    )


def _notes(values: list[Note]) -> LazyElements:
    """Notes over their encoding, each between its offset and the next."""
    encoding = Notes(data=values).encode_bytes()
    bounds = array("Q", array("I", encoding[: 4 * len(values)]))
    bounds.append(len(encoding))
    return LazyElements(
        encoding,
        0,
        len(encoding),
        len(values),
        0,
        bounds,
        lambda data, start, stop: Note.decode_bytes(data[start:stop]),
    )


def _encoded(lazy: LazyElements, fixed: bool) -> bytes:
    """What the elements write, as the sequence holding them encodes them."""
    stream = io.BytesIO()
    assert lazy.serialize(stream, fixed) == len(stream.getvalue())
    return stream.getvalue()


@pytest.mark.parametrize("seed", range(20))
@pytest.mark.parametrize("fixed", [True, False], ids=["words", "notes"])
def test_every_edit_matches_a_plain_list(seed: int, fixed: bool) -> None:
    # One run of edits applied alike to the lazy elements and to the list they stand for.
    rng = random.Random(seed)

    def element() -> Any:
        """A fresh element of the kind under test."""
        if fixed:
            return Uint64(rng.randrange(2**64))
        return Note(data=rng.randbytes(rng.randrange(7)))

    plain = [element() for _ in range(rng.randrange(1, 12))]
    lazy = _words(list(plain)) if fixed else _notes(list(plain))
    for _ in range(40):
        size = len(plain)
        at = rng.randrange(-size, size) if size else 0
        match rng.randrange(9):
            case 0 if size:
                assert lazy[at] == plain[at]
            case 1 if size:
                value = element()
                lazy[at] = plain[at] = value
            case 2:
                start, stop = sorted(rng.sample(range(size + 2), 2))
                values = [element() for _ in range(rng.randrange(3))]
                lazy[start:stop] = plain[start:stop] = values
            case 3 if size:
                del lazy[at], plain[at]
            case 4:
                value = element()
                lazy.insert(at, value)
                plain.insert(at, value)
            case 5:
                value = element()
                lazy.append(value)
                plain.append(value)
            case 6 if size:
                assert lazy.pop(at) == plain.pop(at)
            case 7 if size:
                assert lazy.pop() == plain.pop()
            case _:
                start, stop = sorted(rng.sample(range(size + 2), 2))
                assert lazy[start:stop] == plain[start:stop]
        assert len(lazy) == len(plain)
        # The encoding mixes untouched bytes with written elements, and must still match.
        want = Words(data=plain) if fixed else Notes(data=plain)
        assert _encoded(lazy, fixed) == want.encode_bytes()
    assert lazy == plain
    assert list(lazy) == plain


def test_reads_decode_once_and_only_what_is_read() -> None:
    # A position holds nothing until it is read, and the element read is kept.
    values = [Uint64(n) for n in range(5)]
    lazy = _words(values)
    first = lazy[2]
    assert first == values[2]
    assert lazy.items[2] is first
    assert lazy[2] is first
    assert [position for position, item in enumerate(lazy.items) if item is UNREAD] == [0, 1, 3, 4]
    # An element handed out may be written in place, so its bytes no longer stand for it.
    assert not lazy.pristine()


def test_out_of_range_positions_are_refused_as_a_list_refuses_them() -> None:
    lazy = _words([Uint64(1)])
    with pytest.raises(IndexError, match=r"^list index out of range$"):
        lazy[1]
    with pytest.raises(IndexError, match=r"^list index out of range$"):
        lazy[-2]
    with pytest.raises(TypeError, match=r"^list indices must be integers or slices, not str$"):
        lazy["0"]  # ty: ignore[invalid-argument-type]
    # A position counted from the end reads the element it names.
    assert lazy[-1] == Uint64(1)
    lazy.pop()
    with pytest.raises(IndexError):
        lazy.pop()


def test_equality_compares_elements_whatever_holds_them() -> None:
    # Two untouched runs over equal bytes are equal without decoding a single element.
    values = [Uint64(n) for n in range(4)]
    one, other = _words(values), _words(values)
    assert one == other
    assert all(item is UNREAD for item in (*one.items, *other.items))
    # Untouched runs over different bytes are compared element by element.
    assert one != _words(values[::-1])
    # Once one is touched, the elements are compared instead.
    other[0] = Uint64(9)
    assert one != other
    assert one == values and one == tuple(values)
    # Anything that is not a sequence of elements is left to its own comparison.
    assert one.__eq__(5) is NotImplemented
    assert one != 5


def test_copies_and_pickles_are_plain_lists() -> None:
    # A copy or a pickle stands for the elements alone, readable without the encoding.
    values = [Note(data=b"ab"), Note(data=b""), Note(data=b"xyz")]
    lazy = _notes(values)
    assert repr(lazy) == repr(values)
    for twin in (copy.copy(lazy), copy.deepcopy(lazy), pickle.loads(pickle.dumps(lazy))):
        assert type(twin) is list
        assert twin == values
    # A deep copy shares no element with the original.
    deep = copy.deepcopy(lazy)
    assert all(a is not b for a, b in zip(deep, lazy, strict=True))

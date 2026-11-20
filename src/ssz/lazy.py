"""
Elements read from an encoding on first use, for the native backend's decoder.

A sequence decoded by the native backend keeps its encoding and builds no element up front.
An element is decoded the first time it is read, and kept from then on.
Until then its bytes in the encoding are its value, so they serve its encoding and its root.

The specification never builds one: decoding there builds every element at once.
"""

from __future__ import annotations

from array import array
from collections.abc import Callable, Iterable, Iterator, MutableSequence
from copy import deepcopy
from typing import IO, Any, Final, overload, override

from ssz.offsets import check_composite_size

UNREAD: Final = type("Unread", (), {"__slots__": (), "__repr__": lambda self: "UNREAD"})()
"""What a position holds until its element is decoded."""

read_hook: Callable[[Any, int, Any], None] | None = None
"""Told of each element decoded, with the value holding it and its position, by the backend."""


class LazyElements(MutableSequence[Any]):
    """
    A sequence whose elements are decoded from an encoding the first time each is read.

    The first elements map onto the encoding: one width apart, or between consecutive bounds.
    Positions past that count, and every position read or written, hold their element.
    A write that moves positions decodes every element first, and the encoding is then unused.
    """

    __slots__ = (
        "bounds",
        "decode",
        "encoded",
        "encoding",
        "items",
        "original",
        "owner",
        "start",
        "stop",
        "touched",
        "width",
    )

    def __init__(
        self,
        encoding: bytes,
        start: int,
        stop: int,
        count: int,
        width: int,
        bounds: array[int] | None,
        decode: Callable[[bytes, int, int], Any],
    ) -> None:
        """
        Elements over the encoding's range from start to stop, none decoded yet.

        Fixed-size elements sit one width apart from the start; the others between bounds.
        The bounds count from the start: each element's offset, then the range's size.
        """
        self.encoding, self.start, self.stop = encoding, start, stop
        self.width, self.bounds, self.decode = width, bounds, decode
        self.items: list[Any] = [UNREAD] * count
        self.encoded = count
        self.original = count
        self.touched: set[int] = set()
        self.owner: Any = None

    def span(self, position: int) -> tuple[int, int]:
        """Where an element still in the encoding starts and stops."""
        if self.bounds is None:
            start = self.start + position * self.width
            return start, start + self.width
        return self.start + self.bounds[position], self.start + self.bounds[position + 1]

    def read(self, position: int) -> Any:
        """The element at a position counted from zero, decoded now if it was not before."""
        element = self.items[position]
        if element is UNREAD:
            element = self.decode(self.encoding, *self.span(position))
            self.items[position] = element
            self.touched.add(position)
            if read_hook is not None and self.owner is not None:
                read_hook(self.owner, position, element)
        return element

    def pristine(self) -> bool:
        """Whether every element is still exactly what the encoding holds."""
        return not self.touched and self.original == len(self.items) == self.encoded

    def size_of_original(self) -> int:
        """Where the last element still mapping onto the encoding ends, counted from the start."""
        if self.bounds is None:
            return self.original * self.width
        return self.bounds[self.original]

    def held(self) -> Iterable[int]:
        """The positions holding a decoded or written element, in no particular order."""
        return (*self.touched, *range(self.original, len(self.items)))

    def read_all(self) -> None:
        """Decode every element, after which the encoding is never read again."""
        for position in range(self.original):
            self.read(position)
        self.original = 0
        self.touched.clear()

    def fixed_encoding(self) -> bytes:
        """The elements' encodings back to back, for elements of one fixed width."""
        if self.pristine():
            return self.encoding[self.start : self.stop]
        width, items, kept = self.width, self.items, self.original
        joined = bytearray(self.encoding[self.start : self.start + kept * width])
        # Only positions still mapping onto the encoding are ever touched.
        for position in self.touched:
            joined[position * width : position * width + width] = items[position].encode_bytes()
        joined += b"".join([element.encode_bytes() for element in items[kept:]])
        return bytes(joined)

    def serialize(self, stream: IO[bytes], fixed: bool) -> int:
        """
        Write the elements' encoding, as the sequence holding them encodes them.

        Untouched elements write their own bytes; a variable-size run is written whole or rebuilt.
        """
        if fixed:
            encoded = self.fixed_encoding()
        elif self.pristine():
            encoded = self.encoding[self.start : self.stop]
        else:
            # Each body with its offset in front of all of them, as the specification lays out.
            bodies = [
                self.encoding[slice(*self.span(position))]
                if element is UNREAD
                else element.encode_bytes()
                for position, element in enumerate(self.items)
            ]
            offset = 4 * len(bodies)
            check_composite_size(offset)
            table = bytearray()
            for body in bodies:
                table += offset.to_bytes(4, "little")
                offset += len(body)
                check_composite_size(offset)
            encoded = bytes(table) + b"".join(bodies)
            stream.write(encoded)
            return len(encoded)
        stream.write(encoded)
        check_composite_size(len(encoded))
        return len(encoded)

    def __len__(self) -> int:
        """How many elements, decoded or not."""
        return len(self.items)

    @overload
    def __getitem__(self, index: int) -> Any: ...
    @overload
    def __getitem__(self, index: slice) -> list[Any]: ...

    @override
    def __getitem__(self, index: int | slice) -> Any:
        """An element, or a list of the elements in a range, decoding each one read."""
        if isinstance(index, slice):
            return [self.read(position) for position in range(*index.indices(len(self.items)))]
        # The list checks the position, raising what a list raises.
        element = self.items[index]
        if element is not UNREAD:
            return element
        position = index.__index__()
        return self.read(position + len(self.items) if position < 0 else position)

    @override
    def __setitem__(self, index: int | slice, value: Any) -> None:
        """Write an element, or a range of them, which a list would accept."""
        if isinstance(index, slice):
            self.read_all()
            self.items[index] = value
            return
        position = index.__index__()
        self.items[position] = value
        if position < 0:
            position += len(self.items)
        if position < self.original:
            self.touched.add(position)

    @override
    def __delitem__(self, index: int | slice) -> None:
        """Remove an element or a range, which moves every later one."""
        self.read_all()
        del self.items[index]

    @override
    def insert(self, index: int, value: Any) -> None:
        """Insert an element, which moves every later one unless it lands at the end."""
        if index < len(self.items):
            self.read_all()
        self.items.insert(index, value)

    @override
    def append(self, value: Any) -> None:
        """Add an element at the end, moving nothing."""
        self.items.append(value)

    @override
    def pop(self, index: int = -1) -> Any:
        """Remove and return an element, the last one by default."""
        if not self.items:
            raise IndexError("pop from empty list")
        position = index + len(self.items) if index < 0 else index
        if position != len(self.items) - 1:
            self.read_all()
            return self.items.pop(index)
        element = self.read(position)
        self.items.pop()
        # The encoding now maps onto fewer positions, and the one gone is no longer written.
        if position < self.original:
            self.original = position
        self.touched.discard(position)
        return element

    @override
    def __iter__(self) -> Iterator[Any]:
        """Every element in order, decoding each one not read before."""
        read = self.read
        for position in range(len(self.items)):
            yield read(position)

    def __eq__(self, other: object) -> bool:
        """Equal to any sequence holding equal elements in the same order."""
        if isinstance(other, LazyElements) and self.pristine() and other.pristine():
            if self.encoding[self.start : self.stop] == other.encoding[other.start : other.stop]:
                return len(self) == len(other)
        if isinstance(other, (list, tuple, LazyElements)):
            return list(self) == list(other)
        return NotImplemented

    __hash__ = None  # type: ignore[assignment]

    def __repr__(self) -> str:
        """Show the elements, as the list they stand for."""
        return repr(list(self))

    def copy_for(self, owner: Any) -> LazyElements:
        """An independent copy, sharing the encoding and copying every decoded element."""
        twin = LazyElements.__new__(LazyElements)
        twin.encoding, twin.start, twin.stop = self.encoding, self.start, self.stop
        twin.width, twin.bounds, twin.decode = self.width, self.bounds, self.decode
        twin.encoded = self.encoded
        twin.items = list(self.items)
        for position in self.held():
            twin.items[position] = self.items[position].copy()
        twin.original, twin.touched, twin.owner = self.original, set(self.touched), owner
        return twin

    def __copy__(self) -> list[Any]:
        """A shallow copy, as the plain list of elements this stands for."""
        return list(self)

    def __deepcopy__(self, memo: dict[int, Any]) -> list[Any]:
        """A deep copy, as a plain list of copied elements."""
        return [deepcopy(element, memo) for element in self]

    def __reduce__(self) -> tuple[type[list[Any]], tuple[list[Any]]]:
        """Pickle as the plain list of elements, which any backend reads back."""
        return list, (list(self),)

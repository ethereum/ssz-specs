"""The JSON form of every SSZ type, as the consensus-specs mapping assigns it."""

from __future__ import annotations

import json
from typing import Any

import pytest

from ssz import (
    BitList,
    BitVector,
    Boolean,
    ByteList,
    ByteVector,
    Container,
    List,
    ProgressiveBitList,
    ProgressiveContainer,
    ProgressiveList,
    Uint16,
    Vector,
)
from ssz.base import json_writer
from ssz.ssz_base import SSZType
from ssz.uint import Byte


class Uint16Vector3(Vector[Uint16]):
    """Three numbers, each of which the mapping writes as decimal digits in a string."""

    LENGTH = 3


class Uint16List4(List[Uint16]):
    """Up to four numbers."""

    LIMIT = 4


class Uint16ProgressiveList(ProgressiveList[Uint16]):
    """Any number of numbers, per EIP-7916."""


class ByteVector4(ByteVector):
    """Four bytes of opaque data."""

    LENGTH = 4


class ByteList8(ByteList):
    """Up to eight bytes of opaque data."""

    LIMIT = 8


class ByteVector4Elementwise(Vector[Byte]):
    """The other spelling of a fixed byte array, an element type in place of a byte count."""

    LENGTH = 4


class ByteList4Elementwise(List[Byte]):
    """The other spelling of a bounded byte array."""

    LIMIT = 4


class ByteProgressiveList(ProgressiveList[Byte]):
    """The unbounded byte array, which only the elementwise spelling reaches."""


class BitVector5(BitVector):
    """Five bits, packed into the one byte they fit in."""

    LENGTH = 5


class BitList20(BitList):
    """Up to twenty bits, closed by a delimiter bit."""

    LIMIT = 20


class Point(Container):
    """Two numbers under names, which the mapping writes as an object."""

    x: Uint16
    y: Uint16


class Corner(ProgressiveContainer):
    """Two numbers holding positions 0 and 2, per EIP-7495."""

    ACTIVE_FIELDS = (1, 0, 1)

    x: Uint16
    y: Uint16


CASES: list[tuple[SSZType, Any]] = [
    (Boolean(True), True),
    (Byte(0xFF), "0xff"),
    (Uint16(0x1234), "4660"),
    (Uint16Vector3(data=[1, 2, 3]), ["1", "2", "3"]),
    (Uint16List4(data=[1, 2]), ["1", "2"]),
    (Uint16ProgressiveList(data=[1, 2]), ["1", "2"]),
    (ByteVector4(b"\x11\x22\x33\x44"), "0x11223344"),
    (ByteList8(data=b"\x11\x22"), "0x1122"),
    (ByteVector4Elementwise.of(0x11, 0x22, 0x33, 0x44), "0x11223344"),
    (ByteList4Elementwise.of(0x11, 0x22), "0x1122"),
    (ByteProgressiveList.of(0x11, 0x22), "0x1122"),
    (BitVector5(data=[1, 0, 1, 0, 1]), "0x15"),
    (BitList20(data=[1, 0, 1]), "0x0d"),
    (ProgressiveBitList(data=[1, 0, 1]), "0x0d"),
    (Point(x=Uint16(1), y=Uint16(2)), {"x": "1", "y": "2"}),
    (Corner(x=Uint16(1), y=Uint16(2)), {"x": "1", "y": "2"}),
]
"""One value of every kind the mapping names, against the JSON that mapping assigns it."""


@pytest.mark.parametrize("value,expected", CASES, ids=lambda case: type(case).__name__)
def test_the_mapping_writes_what_the_table_says(value: SSZType, expected: Any) -> None:
    """No collection is wrapped: the array or the hex string is the whole rendering."""
    assert json.loads(json_writer(type(value)).dump_json(value)) == expected


@pytest.mark.parametrize("value,expected", CASES, ids=lambda case: type(case).__name__)
def test_the_mapping_reads_back_what_it_wrote(value: SSZType, expected: Any) -> None:
    """Both doors rebuild the value: the JSON text, and the object a parser already built."""
    reader = json_writer(type(value))
    assert reader.validate_json(json.dumps(expected)) == value
    assert reader.validate_python(expected) == value


class EveryKind(Container):
    """One field of every collection kind, so a container's fields are checked in place."""

    vector: Uint16Vector3
    bounded_list: Uint16List4
    progressive_list: Uint16ProgressiveList
    byte_vector: ByteVector4
    byte_list: ByteList8
    byte_vector_elementwise: ByteVector4Elementwise
    byte_list_elementwise: ByteList4Elementwise
    byte_progressive_list: ByteProgressiveList
    bit_vector: BitVector5
    bit_list: BitList20
    progressive_bit_list: ProgressiveBitList


def test_a_container_writes_each_collection_field_bare() -> None:
    """A field is written exactly as the value would be on its own, at any nesting depth."""
    value = EveryKind(
        vector=Uint16Vector3(data=[1, 2, 3]),
        bounded_list=Uint16List4(data=[1, 2]),
        progressive_list=Uint16ProgressiveList(data=[1, 2]),
        byte_vector=ByteVector4(b"\x11\x22\x33\x44"),
        byte_list=ByteList8(data=b"\x11\x22"),
        byte_vector_elementwise=ByteVector4Elementwise.of(0x11, 0x22, 0x33, 0x44),
        byte_list_elementwise=ByteList4Elementwise.of(0x11, 0x22),
        byte_progressive_list=ByteProgressiveList.of(0x11, 0x22),
        bit_vector=BitVector5(data=[1, 0, 1, 0, 1]),
        bit_list=BitList20(data=[1, 0, 1]),
        progressive_bit_list=ProgressiveBitList(data=[1, 0, 1]),
    )
    written = value.model_dump_json()

    assert json.loads(written) == {
        "vector": ["1", "2", "3"],
        "bounded_list": ["1", "2"],
        "progressive_list": ["1", "2"],
        "byte_vector": "0x11223344",
        "byte_list": "0x1122",
        "byte_vector_elementwise": "0x11223344",
        "byte_list_elementwise": "0x1122",
        "byte_progressive_list": "0x1122",
        "bit_vector": "0x15",
        "bit_list": "0x0d",
        "progressive_bit_list": "0x0d",
    }
    assert EveryKind.model_validate_json(written) == value
    assert EveryKind.model_validate(json.loads(written)) == value


POINT = Point(x=Uint16(1), y=Uint16(2))
"""One container value, reused wherever a sequence needs a composite element."""


class ListOfLists(List[Uint16List4]):
    """A sequence whose elements are themselves sequences, so an array nests in an array."""

    LIMIT = 2


class VectorOfContainers(Vector[Point]):
    """A sequence of objects, an element being written as the element type writes it."""

    LENGTH = 2


class ListOfBitLists(List[BitList20]):
    """A sequence of hex strings, one bitfield per element."""

    LIMIT = 2


@pytest.mark.parametrize(
    "value,expected",
    [
        (ListOfLists(data=[Uint16List4(data=[1, 2]), Uint16List4(data=[])]), [["1", "2"], []]),
        (VectorOfContainers(data=[POINT] * 2), [{"x": "1", "y": "2"}] * 2),
        (ListOfBitLists(data=[BitList20(data=[1, 0, 1])]), ["0x0d"]),
    ],
    ids=["list_of_lists", "vector_of_containers", "list_of_bit_lists"],
)
def test_a_nested_collection_is_written_and_read_bare(value: SSZType, expected: Any) -> None:
    """An element carries no wrapper either, so the mapping is the same at every depth."""
    assert json.loads(json_writer(type(value)).dump_json(value)) == expected
    assert json_writer(type(value)).validate_python(expected) == value

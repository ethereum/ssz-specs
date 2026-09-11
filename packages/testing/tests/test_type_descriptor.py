"""A consumer holding only the emitted JSON rebuilds the type and reads the vector back."""

from typing import Any, Final

import pytest

from ssz import (
    BaseUint,
    BitList,
    BitVector,
    Boolean,
    ByteList,
    ByteVector,
    CompatibleUnion,
    Container,
    List,
    ProgressiveBitList,
    ProgressiveContainer,
    ProgressiveList,
    SSZType,
    Uint8,
    Uint16,
    Uint64,
    Vector,
    hash_tree_root,
)
from ssz_testing.hex_codec import from_hex, to_hex
from ssz_testing.serialization import SSZTest

BASES: Final[dict[str, type[SSZType]]] = {
    "Boolean": Boolean,
    "BitVector": BitVector,
    "BitList": BitList,
    "ProgressiveBitList": ProgressiveBitList,
    "ByteVector": ByteVector,
    "ByteList": ByteList,
    "Vector": Vector,
    "List": List,
    "ProgressiveList": ProgressiveList,
    "Container": Container,
    "ProgressiveContainer": ProgressiveContainer,
    "CompatibleUnion": CompatibleUnion,
}


def build_type(descriptor: dict[str, Any]) -> type[SSZType]:
    """Rebuild an SSZ type from one emitted descriptor, reading no declaration of this repo."""
    body: dict[str, Any] = {"__module__": "consumer"}
    if "bits" in descriptor:
        return type(descriptor["kind"], (BaseUint,), body | {"BITS": descriptor["bits"]})
    if "length" in descriptor:
        body["LENGTH"] = descriptor["length"]
    if "limit" in descriptor:
        body["LIMIT"] = descriptor["limit"]
    if "elementType" in descriptor:
        body["ELEMENT_TYPE"] = build_type(descriptor["elementType"])
    if "activeFields" in descriptor:
        body["ACTIVE_FIELDS"] = tuple(descriptor["activeFields"])
    if "options" in descriptor:
        body["OPTIONS"] = {
            option["selector"]: build_type(option["type"]) for option in descriptor["options"]
        }
    if "fields" in descriptor:
        body["__annotations__"] = {
            field["name"]: build_type(field["type"]) for field in descriptor["fields"]
        }
    return type(descriptor["kind"], (BASES[descriptor["kind"]],), body)


class Bytes4(ByteVector):
    LENGTH = 4


class SampleByteList8(ByteList):
    LIMIT = 8


class SampleBitVector9(BitVector):
    LENGTH = 9


class SampleBitList16(BitList):
    LIMIT = 16


class SampleBytes4Vector2(Vector[Bytes4]):
    LENGTH = 2


class SampleSquare(ProgressiveContainer):
    ACTIVE_FIELDS = (1, 0, 1)

    side: Uint16
    color: Uint8


class SampleCircle(ProgressiveContainer):
    ACTIVE_FIELDS = (0, 1, 1)

    radius: Uint16
    color: Uint8


class SampleSquareList4(List[SampleSquare]):
    LIMIT = 4


class SampleSquareProgressiveList(ProgressiveList[SampleSquare]):
    pass


class SampleShape(CompatibleUnion):
    OPTIONS = {1: SampleSquare, 2: SampleCircle}


class SampleNested(Container):
    count: Uint64
    digest: Bytes4
    shape: SampleShape
    squares: SampleSquareList4


SAMPLE_VALUES: Final = (
    Boolean(True),
    Uint64(2**63),
    Bytes4(b"abcd"),
    SampleByteList8(data=b"abc"),
    SampleBitVector9(data=[Boolean(bit) for bit in (1, 0, 1, 0, 1, 0, 1, 0, 1)]),
    SampleBitList16(data=[Boolean(bit) for bit in (1, 1, 0, 1, 1)]),
    ProgressiveBitList(data=[Boolean(bit) for bit in (1, 0, 1)]),
    SampleBytes4Vector2(data=[Bytes4(b"abcd"), Bytes4(b"efgh")]),
    SampleSquareList4(data=[SampleSquare(side=Uint16(3), color=Uint8(4))]),
    SampleSquareProgressiveList(data=[SampleSquare(side=Uint16(5), color=Uint8(6))] * 3),
    SampleShape(selector=Uint8(2), data=SampleCircle(radius=Uint16(7), color=Uint8(8))),
    SampleNested(
        count=Uint64(9),
        digest=Bytes4(b"wxyz"),
        shape=SampleShape(selector=Uint8(1), data=SampleSquare(side=Uint16(1), color=Uint8(2))),
        squares=SampleSquareList4(data=[SampleSquare(side=Uint16(3), color=Uint8(4))] * 2),
    ),
)


@pytest.mark.parametrize("value", SAMPLE_VALUES, ids=lambda value: type(value).__name__)
def test_a_consumer_rebuilds_the_type_from_the_descriptor_alone(value: SSZType) -> None:
    """The rebuilt type decodes the vector's bytes back to the same encoding and the same root."""
    emitted = SSZTest(type_name=type(value).__name__, value=value).generate().json_dict

    rebuilt = build_type(emitted["typeDescriptor"])
    decoded = rebuilt.decode_bytes(from_hex(emitted["serialized"]))

    assert to_hex(decoded.encode_bytes()) == emitted["serialized"]
    assert to_hex(hash_tree_root(decoded)) == emitted["root"]

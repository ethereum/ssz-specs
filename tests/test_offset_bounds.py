"""Composite byte-size bounds include fixed data, offset tables, and the final body."""

import io

import pytest

from ssz.byte_arrays import ByteList, ByteVector
from ssz.collections import List, ProgressiveList, Vector
from ssz.container import Container, ProgressiveContainer
from ssz.exceptions import SSZValueError, ValueFault
from ssz.offsets import check_composite_size
from ssz.ssz_base import SSZType
from ssz.uint import Uint8
from ssz.union import CompatibleUnion


class Bytes16(ByteVector):
    """One fixed payload filling the reduced test budget."""

    LENGTH = 16


class Bytes12(ByteList):
    """A variable payload filling the budget together with its four-byte offset."""

    LIMIT = 12


class FixedVector(Vector[Bytes16]):
    """One fixed element."""

    LENGTH = 1


class VariableVector(Vector[Bytes12]):
    """One variable element."""

    LENGTH = 1


class FixedList(List[Bytes16]):
    """A bounded sequence of fixed elements."""

    LIMIT = 4


class VariableList(List[Bytes12]):
    """A bounded sequence of variable elements."""

    LIMIT = 4


class FixedProgressiveList(ProgressiveList[Bytes16]):
    """An unbounded sequence of fixed elements."""


class VariableProgressiveList(ProgressiveList[Bytes12]):
    """An unbounded sequence of variable elements."""


class FixedContainer(Container):
    """One fixed field."""

    payload: Bytes16


class VariableContainer(Container):
    """One variable field, whose end has no offset of its own."""

    payload: Bytes12


class FixedProgressiveContainer(ProgressiveContainer):
    """One fixed field in a progressive layout."""

    ACTIVE_FIELDS = (1,)
    payload: Bytes16


class VariableProgressiveContainer(ProgressiveContainer):
    """One variable field in a progressive layout."""

    ACTIVE_FIELDS = (1,)
    payload: Bytes12


@pytest.mark.parametrize("size", [0, 2**32 - 1])
def test_composite_size_below_limit(size: int) -> None:
    # The four-byte range excludes its upper endpoint, while an empty composite fits.
    check_composite_size(size)


@pytest.mark.parametrize("size", [2**32, 2**32 + 1])
def test_composite_size_at_or_above_limit(size: int) -> None:
    # Exercise the actual protocol boundary directly, without allocating the payload.
    with pytest.raises(SSZValueError) as raised:
        check_composite_size(size)
    assert raised.value.fault is ValueFault.OFFSET_OVERFLOW
    assert raised.value.fields == {"size": size}


@pytest.mark.parametrize("limit", [15, 16, 17])
@pytest.mark.parametrize(
    "value",
    [
        FixedVector(data=[Bytes16()]),
        VariableVector(data=[Bytes12(data=bytes(12))]),
        FixedList(data=[Bytes16()]),
        VariableList(data=[Bytes12(data=bytes(12))]),
        FixedProgressiveList(data=[Bytes16()]),
        VariableProgressiveList(data=[Bytes12(data=bytes(12))]),
        FixedContainer(payload=Bytes16()),
        VariableContainer(payload=Bytes12(data=bytes(12))),
        FixedProgressiveContainer(payload=Bytes16()),
        VariableProgressiveContainer(payload=Bytes12(data=bytes(12))),
    ],
    ids=lambda value: type(value).__name__,
)
def test_composite_size_boundary(
    value: SSZType, limit: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    # Every fixture encodes to sixteen real bytes, including any four-byte offset.
    encoded = value.encode_bytes()
    assert len(encoded) == 16

    # Lower only the size ceiling; offset widths and all encoded bytes stay unchanged.
    monkeypatch.setattr("ssz.offsets._COMPOSITE_SIZE_LIMIT", limit)
    if limit > 16:
        assert value.encode_bytes() == encoded
        assert type(value).decode_bytes(encoded) == value
        return

    # Both writing and reading must reject the complete size, including the final body.
    with pytest.raises(SSZValueError) as written:
        value.encode_bytes()
    assert written.value.fault is ValueFault.OFFSET_OVERFLOW
    assert written.value.fields == {"size": 16}

    # An oversized scope is refused before consuming even its first field or offset.
    source = io.BytesIO(encoded)
    with pytest.raises(SSZValueError) as read:
        type(value).deserialize(source, len(encoded))
    assert read.value.fault is ValueFault.OFFSET_OVERFLOW
    assert read.value.fields == {"size": 16}
    assert source.tell() == 0


def test_offset_table_alone_reaches_limit(monkeypatch: pytest.MonkeyPatch) -> None:
    # Four empty variable bodies still require sixteen bytes of offset table.
    value = VariableList(data=[Bytes12()] * 4)
    monkeypatch.setattr("ssz.offsets._COMPOSITE_SIZE_LIMIT", 16)
    output = io.BytesIO()
    with pytest.raises(SSZValueError) as raised:
        value.serialize(output)
    assert raised.value.fault is ValueFault.OFFSET_OVERFLOW
    assert raised.value.fields == {"size": 16}
    assert output.tell() == 0


def test_primitive_bytes_have_no_composite_limit(monkeypatch: pytest.MonkeyPatch) -> None:
    # Raw byte arrays have no offset table and retain their own declared size rules.
    monkeypatch.setattr("ssz.offsets._COMPOSITE_SIZE_LIMIT", 12)
    for value in (Bytes16(), Bytes12(data=bytes(12))):
        encoded = value.encode_bytes()
        assert type(value).decode_bytes(encoded) == value


def test_union_selector_does_not_add_a_composite_limit(monkeypatch: pytest.MonkeyPatch) -> None:
    # The option fits in sixteen bytes, and its selector adds one byte outside that composite.
    class FixedUnion(CompatibleUnion):
        """One fixed composite option."""

        OPTIONS = {1: FixedContainer}

    value = FixedUnion(selector=Uint8(1), data=FixedContainer(payload=Bytes16()))
    monkeypatch.setattr("ssz.offsets._COMPOSITE_SIZE_LIMIT", 17)
    encoded = value.encode_bytes()
    assert len(encoded) == 17
    assert FixedUnion.decode_bytes(encoded) == value

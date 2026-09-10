"""A wrong byte count is one fault, whether the value is the whole input or an option."""

from typing import Final

import pytest

from ssz.bitfields import BitVector
from ssz.boolean import Bit, Boolean
from ssz.byte_arrays import ByteVector
from ssz.collections import Vector
from ssz.container import Container
from ssz.exceptions import SSZError, SSZValueError, ValueFault
from ssz.ssz_base import SSZType
from ssz.uint import Byte, Uint8, Uint16, Uint32, Uint64, Uint128, Uint256
from ssz.union import CompatibleUnion

_SELECTOR: Final = 1
"""The one selector every union below declares, so an option's budget is the rest of the input."""


class Bytes4(ByteVector):
    """A fixed byte array, whose width the constructor also pins."""

    LENGTH = 4


class BitVector8(BitVector):
    """A bit count filling its byte exactly."""

    LENGTH = 8


class BitVector12(BitVector):
    """A bit count leaving padding in its last byte, so the width is not the count."""

    LENGTH = 12


class Uint16Vector2(Vector[Uint16]):
    """A fixed-size vector, whose width is its element width times its count."""

    LENGTH = 2


class BoolVector3(Vector[Boolean]):
    """A fixed-size vector of one-byte elements."""

    LENGTH = 3


class FixedStruct(Container):
    """A fixed-size struct, which reads its fields out of the budget it was handed."""

    head: Uint16
    flag: Boolean


LEAF_TYPES: Final[tuple[type[SSZType], ...]] = (
    Uint8,
    Uint16,
    Uint32,
    Uint64,
    Uint128,
    Uint256,
    Boolean,
    Bytes4,
    BitVector8,
    BitVector12,
    Uint16Vector2,
    BoolVector3,
)
"""Every fixed-width type that measures a budget against its own width before reading."""

FIXED_WIDTH_TYPES: Final[tuple[type[SSZType], ...]] = (*LEAF_TYPES, FixedStruct)
"""Every fixed-width type, the struct included, which reads its fields before measuring."""


def _union_over(option: type[SSZType]) -> type[CompatibleUnion]:
    """A union of one option, so decoding puts that option one byte into the input."""
    return type(f"UnionOf{option.__name__}", (CompatibleUnion,), {"OPTIONS": {_SELECTOR: option}})


def _refusal(decode: type[SSZType], payload: bytes) -> SSZError:
    """Decode a payload this type does not admit, and hand back the refusal."""
    with pytest.raises(SSZValueError) as raised:
        decode.decode_bytes(payload)
    return raised.value


@pytest.mark.parametrize("surplus", [-1, 1], ids=["one_short", "one_over"])
@pytest.mark.parametrize("fixed_type", FIXED_WIDTH_TYPES, ids=lambda cls: cls.__name__)
def test_a_wrong_byte_count_reports_one_fault_wherever_the_value_sits(
    fixed_type: type[SSZType], surplus: int
) -> None:
    payload = bytes(fixed_type.get_byte_length() + surplus)

    top_level = _refusal(fixed_type, payload)
    nested = _refusal(_union_over(fixed_type), bytes([_SELECTOR]) + payload)

    # The path differs, since one value sits under a selector and the other is the input.
    # The fault and its sentence are what a vector publishes, and those must agree.
    assert nested.fault is top_level.fault
    assert nested.message == top_level.message


@pytest.mark.parametrize("surplus", [-1, 1], ids=["one_short", "one_over"])
@pytest.mark.parametrize("fixed_type", LEAF_TYPES, ids=lambda cls: cls.__name__)
def test_a_budget_that_is_not_the_width_is_reported_as_the_budget_it_is(
    fixed_type: type[SSZType], surplus: int
) -> None:
    name = fixed_type.__name__
    width = fixed_type.get_byte_length()
    count = width + surplus

    refusal = _refusal(fixed_type, bytes(count))

    assert refusal.fault is ValueFault.SCOPE
    assert refusal.message == f"{name} spans {width} bytes, and the budget is {count}"


def test_a_struct_reads_its_fields_before_it_can_measure_its_budget() -> None:
    over = _refusal(FixedStruct, bytes(4))
    assert over.fault is ValueFault.SCOPE
    assert str(over) == "FixedStruct spans 3 bytes, and the budget is 4"

    # A short budget surfaces as the field that ran out, not as the budget.
    short = _refusal(FixedStruct, bytes(2))
    assert short.fault is ValueFault.TRUNCATED
    assert str(short) == "flag: Boolean needs 1 bytes, the input holds 0"


def test_the_aliases_name_the_types_this_property_was_established_over() -> None:
    assert Bit is Boolean
    assert Byte is Uint8

"""SSZ conformance vectors for the byte-array alias, the last default rows, and two refusals."""

from typing import ClassVar, Final

import pytest

from ssz import (
    BitList,
    Byte,
    ByteList,
    List,
    ProgressiveBitList,
    ProgressiveContainer,
    Uint8,
    Uint64,
    Uint256,
)
from ssz_testing import (
    DeclaredField,
    ExpectedRejection,
    SSZTestFiller,
    TypeDescriptor,
    TypeFault,
    TypeRejectionFiller,
    ValueFault,
    describe_type,
)


class SampleAliasByteList8(ByteList):
    """Up to eight opaque bytes, the shorthand half of the pair against a list of byte elements."""

    LIMIT: ClassVar[int] = 8


class SampleAliasByteElementList8(List[Byte]):
    """Up to eight byte elements, the spelled-out half of that pair."""

    LIMIT: ClassVar[int] = 8
    ELEMENT_TYPE = Byte


class SampleBitList16(BitList):
    """Up to sixteen packed bits, a bounded bitfield whose default is empty."""

    LIMIT: ClassVar[int] = 16


class SampleDefaultedShape(ProgressiveContainer):
    """A fixed-size field and an unbounded one, laid out either side of a gap."""

    ACTIVE_FIELDS = (1, 0, 1)

    weight: Uint64
    flags: ProgressiveBitList


ALIAS_BYTES: Final = bytes.fromhex("deadbeef")
"""The four bytes both spellings of the bounded byte array are filled with."""

UINT8: Final = describe_type(Uint8)
"""A byte-wide integer, read off the real class, the field an illegal layout is counted against."""

ONE_FIELD: Final = (DeclaredField(name="amount", type=UINT8),)
"""A single named field, enough to give a progressive struct something to lay out."""


@pytest.mark.tags("alias")
def test_byte_list_alias_of_byte_element_list(ssz_test: SSZTestFiller) -> None:
    """
    A bounded byte array is the shorthand for a bounded list of byte elements.

    Given
    -----
    - the bytes 0xde, 0xad, 0xbe, 0xef held in a ByteList[8].

    When
    ----
    - the value is encoded, decoded, and rooted.

    Then
    ----
    - the encoding is the four bytes themselves, the count carried by the byte count.
    - the four packed bytes fill one chunk, the limit of eight bytes, and the length 4 mixes in.
    - both encoding and root equal those of the list of byte elements beside it.
    """
    ssz_test(
        case_id="alias/byte_list8/alias_of_byte_element_list",
        type_name="SampleAliasByteList8",
        value=SampleAliasByteList8(data=ALIAS_BYTES),
    )


@pytest.mark.tags("alias")
def test_byte_element_list_alias_of_byte_list(ssz_test: SSZTestFiller) -> None:
    """
    A bounded list of byte elements is the spelled-out form of a bounded byte array.

    Given
    -----
    - the bytes 0xde, 0xad, 0xbe, 0xef held in a List[Byte, 8].

    When
    ----
    - the value is encoded, decoded, and rooted.

    Then
    ----
    - the encoding is the four bytes themselves, one byte per element rather than one per index.
    - the elements pack into one chunk, the limit of eight bytes, and the length 4 mixes in.
    - both encoding and root equal those of the byte list beside it, and so does the JSON.
    """
    ssz_test(
        case_id="alias/byte_element_list8/alias_of_byte_list",
        type_name="SampleAliasByteElementList8",
        value=SampleAliasByteElementList8(data=[Byte(value) for value in ALIAS_BYTES]),
    )


@pytest.mark.tags("distinction")
def test_byte_at_its_upper_bound(ssz_test: SSZTestFiller) -> None:
    """
    A byte encodes and merkleizes as the one-byte uint, and parts from it only in the JSON.

    Given
    -----
    - the value 255 as a byte.

    When
    ----
    - the value is encoded, decoded, and rooted.

    Then
    ----
    - the encoding is the single byte 0xff.
    - that byte fills one chunk, so the root is 0xff followed by thirty-one zero bytes.
    - both match the one-byte uint at the same value.
    - only the descriptor kind and the JSON, "0xff" against "255", tell the two apart.
    """
    ssz_test(case_id="byte/max", type_name="Byte", value=Byte(2**8 - 1))


@pytest.mark.tags("default")
def test_default_bitlist(ssz_test: SSZTestFiller) -> None:
    """
    The default of a bitlist is empty, holding no bit at all.

    Given
    -----
    - the default value a bitlist of up to sixteen bits hands out.

    When
    ----
    - the value is encoded, decoded, and rooted.

    Then
    ----
    - the encoding is the single delimiter byte 0x01, which no bitfield encoding is ever without.
    - no leaf holds a bit, and the limit of one chunk gives the zero chunk.
    - the length 0 is mixed into that chunk.
    """
    ssz_test(
        case_id="default/bitlist16",
        type_name="SampleBitList16",
        value=SampleBitList16.default(),
    )


@pytest.mark.tags("default")
def test_default_progressive_bitlist(ssz_test: SSZTestFiller) -> None:
    """
    The default of a progressive bitlist is empty, the same as the bounded bitfield beside it.

    Given
    -----
    - the default value a progressive bitlist hands out.

    When
    ----
    - the value is encoded, decoded, and rooted.

    Then
    ----
    - the encoding is the single delimiter byte 0x01.
    - the spine holds no level, so the root is the zero terminator with the length 0 mixed in.
    """
    ssz_test(
        case_id="default/progressive_bitlist",
        type_name="ProgressiveBitList",
        value=ProgressiveBitList.default(),
    )


@pytest.mark.tags("default")
def test_default_progressive_container(ssz_test: SSZTestFiller) -> None:
    """
    The default of a progressive container is one field default per declared field.

    Given
    -----
    - the default value a progressive container of a uint and a progressive bitlist hands out.

    When
    ----
    - the value is encoded, decoded, and rooted.

    Then
    ----
    - the encoding is eight zero bytes, an offset of 12, and the bitfield's lone delimiter byte.
    - the gap in the layout costs no byte, the wire format following the declared fields alone.
    - the two fields sit at positions 0 and 2 of the spine, and the layout (1, 0, 1) mixes in.
    """
    ssz_test(
        case_id="default/progressive_container",
        type_name="SampleDefaultedShape",
        value=SampleDefaultedShape.default(),
    )


@pytest.mark.tags("illegal")
def test_a_progressive_container_layout_holding_a_two_is_refused(
    ssz_type_rejection: TypeRejectionFiller,
) -> None:
    """
    Declaring a progressive container whose layout holds a value other than 0 or 1 is refused.

    Given
    -----
    - a progressive container with one field, laid out as (1, 0, 2).

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, a layout holding one bit per position and nothing wider.
    - reading each entry for truth would take the 2 for a second field.
    """
    ssz_type_rejection(
        case_id="illegal/progressive_container/layout_not_bits",
        type_name="IllegalNonBitLayoutContainer",
        type_descriptor=TypeDescriptor(
            kind="ProgressiveContainer", active_fields=(1, 0, 2), fields=ONE_FIELD
        ),
        rejection_reason=TypeFault.LAYOUT_NOT_BITS,
        exact_message="a field layout holds only 0 and 1",
    )


@pytest.mark.tags("illegal")
def test_a_progressive_container_without_a_layout_is_refused(
    ssz_type_rejection: TypeRejectionFiller,
) -> None:
    """
    Declaring a progressive container that names fields but no layout is refused.

    Given
    -----
    - a progressive container declaring one field and no active fields at all.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, EIP-7495 placing a field only where the layout says it sits.
    - defaulting the layout to one set bit per field would merkleize this as a plain struct.
    """
    ssz_type_rejection(
        case_id="illegal/progressive_container/no_layout",
        type_name="IllegalLayoutlessContainer",
        type_descriptor=TypeDescriptor(kind="ProgressiveContainer", fields=ONE_FIELD),
        rejection_reason=TypeFault.UNDECLARED,
        exact_message="IllegalLayoutlessContainer must declare ACTIVE_FIELDS",
    )


@pytest.mark.tags("boundary")
def test_uint8_one_byte_long(ssz_test: SSZTestFiller) -> None:
    """
    A one-byte unsigned integer given two bytes is rejected.

    Given
    -----
    - the type Uint8, which spans one byte.
    - the input bytes 0x0102, one byte past that.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the type's width and the budget disagree.
    - the trailing byte is not discarded, and the leading one is not read as the value.
    """
    ssz_test(
        case_id="uint8/invalid/one_byte_long",
        type_name="Uint8",
        value=Uint8(0),
        raw_bytes="0x0102",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            message_substring="spans 1 bytes, and the budget is 2",
        ),
    )


@pytest.mark.tags("boundary")
def test_uint256_one_byte_short(ssz_test: SSZTestFiller) -> None:
    """
    A thirty-two-byte unsigned integer given thirty-one bytes is rejected.

    Given
    -----
    - the type Uint256, which spans thirty-two bytes.
    - thirty-one bytes of 0x11, one byte short of that.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the type's width and the budget disagree.
    - through a big-number path of its own the short input reads as a smaller number.
    """
    ssz_test(
        case_id="uint256/invalid/one_byte_short",
        type_name="Uint256",
        value=Uint256(0),
        raw_bytes="0x" + "11" * 31,
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            message_substring="spans 32 bytes, and the budget is 31",
        ),
    )


@pytest.mark.tags("boundary")
def test_uint256_one_byte_long(ssz_test: SSZTestFiller) -> None:
    """
    A thirty-two-byte unsigned integer given thirty-three bytes is rejected.

    Given
    -----
    - the type Uint256, which spans thirty-two bytes.
    - thirty-three bytes of 0x11, one byte past that.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the type's width and the budget disagree.
    - the extra byte is not discarded, and its bits do not overflow into a wider number.
    """
    ssz_test(
        case_id="uint256/invalid/one_byte_long",
        type_name="Uint256",
        value=Uint256(0),
        raw_bytes="0x" + "11" * 33,
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            message_substring="spans 32 bytes, and the budget is 33",
        ),
    )

"""SSZ conformance vectors for offsets whose value does not fit the one byte a small case uses."""

from typing import ClassVar

import pytest

from ssz import BitVector, Boolean, ByteList, Container, List
from ssz_testing import ExpectedRejection, SSZTestFiller, ValueFault

pytestmark = pytest.mark.tags("offsets", "boundary")


def counting_bytes(count: int, start: int) -> bytes:
    """Bytes counting up from the given value, so a body shifted by a byte reads differently."""
    return bytes((start + index) % 256 for index in range(count))


def every_third_bit(count: int) -> list[Boolean]:
    """Bits with every third one set, a pattern whose period divides no chunk width."""
    return [Boolean(index % 3 == 0) for index in range(count)]


class WideByteList512(ByteList):
    """Byte list of up to 512 bytes, wide enough for a body that pushes the offset after it."""

    LIMIT: ClassVar[int] = 512


class WideOffsetPair(Container):
    """Struct of two byte lists, whose second offset is wherever the first body ends."""

    head: WideByteList512
    tail: WideByteList512


class WideBits256(BitVector):
    """Bit vector of exactly one chunk."""

    LENGTH: ClassVar[int] = 256


class WideBits257(BitVector):
    """Bit vector one bit past a chunk, so its 33 bytes leave the next offset slot unaligned."""

    LENGTH: ClassVar[int] = 257


class WideBits1280(BitVector):
    """Bit vector of exactly five chunks."""

    LENGTH: ClassVar[int] = 1280


class WideBits1281(BitVector):
    """Bit vector one bit past five chunks."""

    LENGTH: ClassVar[int] = 1281


class WideSpacedOffsets(Container):
    """Struct alternating byte lists with bit vectors, so bitfields stand between the offsets."""

    first: WideByteList512
    flags_256: WideBits256
    second: WideByteList512
    flags_257: WideBits257
    third: WideByteList512
    flags_1280: WideBits1280
    fourth: WideByteList512
    flags_1281: WideBits1281


class WideTableByteList8(ByteList):
    """Byte list of up to 8 bytes, the smallest thing a long offset table can point at."""

    LIMIT: ClassVar[int] = 8


class WideTableList64(List[WideTableByteList8]):
    """List of up to 64 of them, whose full table is 256 bytes and opens past one byte's reach."""

    LIMIT: ClassVar[int] = 64
    ELEMENT_TYPE = WideTableByteList8


OFFSET_PAIR_DECODER = WideOffsetPair(head=WideByteList512(), tail=WideByteList512())
"""One value of that shape, present only to name the decoder the struct rejections run."""

TABLE_LIST_DECODER = WideTableList64(data=[WideTableByteList8()])
"""The same for the shape whose table is read off its own first offset."""


def test_struct_second_offset_above_one_byte(ssz_test: SSZTestFiller) -> None:
    """
    A struct whose first body pushes the second offset past 255 round-trips.

    Given
    -----
    - a struct of two byte lists, whose table of two offsets spans eight bytes.
    - a first body of 300 bytes, so the offsets are 8 and 308.
    - the second offset therefore needs two bytes, and reads 0x34 0x01 rather than 0x34.

    When
    ----
    - the value is encoded and decoded again.

    Then
    ----
    - the value survives the round trip, and the root is the one pinned here.
    - a decoder reading an offset as a single byte takes the second one for 52.
    - that is a legal table over these bytes, so it hands back a different pair of bodies.
    """
    ssz_test(
        case_id="wide_offset/pair/second_offset_above_one_byte",
        type_name="WideOffsetPair",
        value=WideOffsetPair(
            head=WideByteList512(data=counting_bytes(300, 0xA0)),
            tail=WideByteList512(data=counting_bytes(4, 0x10)),
        ),
        expected_root="0xd6d0e8c5e709d55d2adb24c82e912ea27b5cb5564aa36d668e95f55b5ad80269",
    )


def test_struct_offsets_spaced_by_wide_fixed_fields(ssz_test: SSZTestFiller) -> None:
    """
    A struct whose offset slots are separated by bitfields wider than a chunk round-trips.

    Given
    -----
    - a struct alternating four byte lists with bit vectors of 256, 257, 1280 and 1281 bits.
    - a fixed part of 402 bytes, of which the four offsets occupy sixteen.
    - offset slots at byte 0, 36, 73 and 237, so no two are within one chunk of each other.
    - a slot at byte 73, which no multiple of four lands on either.
    - offsets of 402, 406, 414 and 426, every one of them past what a single byte holds.

    When
    ----
    - the value is encoded and decoded again.

    Then
    ----
    - the value survives the round trip, and the root is the one pinned here.
    - a decoder that strides the fixed part by chunks, or by fours, reads the wrong slots.
    """
    ssz_test(
        case_id="wide_offset/spaced_struct/offsets_across_a_wide_fixed_part",
        type_name="WideSpacedOffsets",
        value=WideSpacedOffsets(
            first=WideByteList512(data=counting_bytes(4, 0x10)),
            flags_256=WideBits256(data=every_third_bit(WideBits256.LENGTH)),
            second=WideByteList512(data=counting_bytes(8, 0x20)),
            flags_257=WideBits257(data=every_third_bit(WideBits257.LENGTH)),
            third=WideByteList512(data=counting_bytes(12, 0x30)),
            flags_1280=WideBits1280(data=every_third_bit(WideBits1280.LENGTH)),
            fourth=WideByteList512(data=counting_bytes(16, 0x40)),
            flags_1281=WideBits1281(data=every_third_bit(WideBits1281.LENGTH)),
        ),
        expected_root="0xeda5971a89368b676a90a74f255c88aa37b190171ee03631ce77ed06edb2a71a",
    )


def test_list_table_wholly_above_one_byte(ssz_test: SSZTestFiller) -> None:
    """
    A list filled to a limit whose whole offset table stands past 255 round-trips.

    Given
    -----
    - a list of up to 64 byte lists, filled to its limit, so its table spans 256 bytes.
    - a one-byte body per element, giving offsets 256 through 319.
    - every entry of the table, the first included, therefore needs two bytes.

    When
    ----
    - the value is encoded and decoded again.

    Then
    ----
    - the value survives the round trip, and the root is the one pinned here.
    - a decoder reading an offset as a single byte takes the first one for zero.
    - the count a list reads off that first offset is wrong by the same stroke.
    """
    ssz_test(
        case_id="wide_offset/bytelist8_list64/table_above_one_byte",
        type_name="WideTableList64",
        value=WideTableList64(
            data=[
                WideTableByteList8(data=bytes([byte]))
                for byte in counting_bytes(WideTableList64.LIMIT, 0xA0)
            ]
        ),
        expected_root="0xc7305e1f4dd66cf1ddf6076c80121237047c1c26a0525043567b3e3b047343d3",
    )


def test_struct_first_offset_high_bytes_read(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a struct whose first offset is legal only in its low two bytes is rejected.

    Given
    -----
    - a struct of two byte lists, whose fixed part of two offsets ends at eight.
    - a first offset of 0x00010008, which is 65544 and reads 08 00 01 00 on the wire.
    - a second offset of eight, and a budget of eight, which is the whole fixed part.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the first offset must end the fixed part exactly.
    - the refusal names 65544, so all four bytes of the offset were read.
    - a decoder reading one or two bytes sees a first offset of eight and two empty bodies.
    - it accepts these bytes as a well-formed value, which is the failure this case catches.
    """
    ssz_test(
        case_id="wide_offset/pair/invalid/first_offset_high_bytes_ignored",
        type_name="WideOffsetPair",
        value=OFFSET_PAIR_DECODER,
        raw_bytes="0x0800010008000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.FIRST_OFFSET,
            exact_message="the first offset is 65544, and the fixed part ends at 8",
        ),
    )


def test_list_first_offset_at_the_aligned_maximum(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a list whose first offset is the largest aligned four-byte word is rejected.

    Given
    -----
    - a list of byte lists, in a budget of eight bytes.
    - a first offset of 0xFFFFFFF0, the highest multiple of four a four-byte offset can carry.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the first offset runs past the budget, before any count is derived.
    - the budget is settled against the offset, so no allocation follows from the value 4294967280.
    - the refusal names that value, so all four bytes were read.
    - the twin ending 0xFF is refused for being unaligned instead, one rule earlier.
    """
    ssz_test(
        case_id="wide_offset/bytelist8_list64/invalid/first_offset_at_aligned_maximum",
        type_name="WideTableList64",
        value=TABLE_LIST_DECODER,
        raw_bytes="0xf0ffffffdeadbeef",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.OFFSET_PAST_SCOPE,
            exact_message="offset 4294967280 runs past the budget of 8",
        ),
    )

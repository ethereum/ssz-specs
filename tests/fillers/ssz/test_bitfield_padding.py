"""SSZ conformance test vectors for every padding bit a bitfield's final byte has to leave clear."""

from typing import ClassVar

import pytest

from ssz import BitList, BitVector, Boolean, Container, List, Uint8
from ssz_testing import ExpectedRejection, SSZTestFiller, ValueFault


class PaddingBitVector4(BitVector):
    """Four-bit vector, the width a beacon state gives its justification bits."""

    LENGTH: ClassVar[int] = 4


class PaddingBitVector7(BitVector):
    """Seven-bit vector, the narrowest padding there is: one bit, and it is the byte's highest."""

    LENGTH: ClassVar[int] = 7


class PaddingBitVector9(BitVector):
    """Nine-bit vector, the widest padding there is: seven bits above a single data bit."""

    LENGTH: ClassVar[int] = 9


class PaddingBitVector12(BitVector):
    """Twelve-bit vector, whose second byte splits evenly into four data bits and four padding."""

    LENGTH: ClassVar[int] = 12


class PaddingBitList1(BitList):
    """Bitlist capped at one bit, so its delimiter sits at bit zero or bit one of a single byte."""

    LIMIT: ClassVar[int] = 1


class PaddingBitVector12List4(List[PaddingBitVector12]):
    """Bounded list of twelve-bit vectors, which puts an element's final byte mid-input."""

    LIMIT: ClassVar[int] = 4


class PaddingTaggedBits(Container):
    """A fixed field ahead of a list of bit vectors, so the bits are reached through an offset."""

    tag: Uint8
    bits: PaddingBitVector12List4


TAGGED_BITS = PaddingTaggedBits(
    tag=Uint8(0xAA),
    bits=PaddingBitVector12List4(
        data=[
            PaddingBitVector12(data=[Boolean(True)] * 12),
            PaddingBitVector12(data=[Boolean(True)] * 12),
        ]
    ),
)
"""One value of that shape, present only to name the decoder the container case runs."""


@pytest.mark.tags("malleability")
def test_bitvector4_highest_padding_bit(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a four-bit vector that sets the highest bit of its byte is rejected.

    Given
    -----
    - a bitvector of four bits, whose byte holds four data bits and four padding bits.
    - the input byte 0x80, which sets padding bit seven and leaves the three below it clear.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the final byte sets a padding bit.
    - bit seven is where a mask built to the wrong width stops covering the padding.
    - it is also where a byte read as a signed value changes sign.
    """
    ssz_test(
        case_id="padding/bitvector4/invalid/highest_padding_bit",
        type_name="PaddingBitVector4",
        value=PaddingBitVector4(),
        raw_bytes="0x80",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.PADDING_BITS,
            exact_message="the final byte 0x80 sets a padding bit",
        ),
    )


@pytest.mark.tags("malleability")
def test_bitvector4_all_padding_bits(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a four-bit vector whose whole padding is set is rejected.

    Given
    -----
    - a bitvector of four bits, whose byte holds four data bits and four padding bits.
    - the input byte 0xf0, which sets all four padding bits and no data bit.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the final byte sets a padding bit.
    - the four bits this would decode to are the all-clear vector, which encodes as 0x00.
    """
    ssz_test(
        case_id="padding/bitvector4/invalid/all_padding_bits",
        type_name="PaddingBitVector4",
        value=PaddingBitVector4(),
        raw_bytes="0xf0",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.PADDING_BITS,
            exact_message="the final byte 0xf0 sets a padding bit",
        ),
    )


@pytest.mark.tags("malleability", "boundary")
def test_bitvector7_only_padding_bit(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a seven-bit vector that sets its single padding bit is rejected.

    Given
    -----
    - a bitvector of seven bits, one short of filling its byte.
    - the input byte 0x80, which sets the one padding bit that byte has.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the final byte sets a padding bit.
    - a length one below a multiple of eight leaves the padding a single bit.
    - the lowest padding bit and the highest are then the same bit.
    """
    ssz_test(
        case_id="padding/bitvector7/invalid/only_padding_bit",
        type_name="PaddingBitVector7",
        value=PaddingBitVector7(),
        raw_bytes="0x80",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.PADDING_BITS,
            exact_message="the final byte 0x80 sets a padding bit",
        ),
    )


@pytest.mark.tags("malleability")
def test_bitvector9_highest_padding_bit(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a nine-bit vector that sets the highest bit of its second byte is rejected.

    Given
    -----
    - a bitvector of nine bits, whose second byte holds one data bit and seven padding bits.
    - the input bytes 0xff80, whose final byte sets padding bit seven and nothing below it.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the final byte sets a padding bit.
    - the padding fills the byte bar one bit, the widest the gap to the lowest bit gets.
    """
    ssz_test(
        case_id="padding/bitvector9/invalid/highest_padding_bit",
        type_name="PaddingBitVector9",
        value=PaddingBitVector9(),
        raw_bytes="0xff80",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.PADDING_BITS,
            exact_message="the final byte 0x80 sets a padding bit",
        ),
    )


@pytest.mark.tags("malleability")
def test_bitvector9_all_padding_bits(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a nine-bit vector whose whole padding is set is rejected.

    Given
    -----
    - a bitvector of nine bits, whose second byte holds one data bit and seven padding bits.
    - the input bytes 0x00fe, which set all seven padding bits and no data bit.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the final byte sets a padding bit.
    - the nine bits this would decode to are the all-clear vector, which encodes as 0x0000.
    """
    ssz_test(
        case_id="padding/bitvector9/invalid/all_padding_bits",
        type_name="PaddingBitVector9",
        value=PaddingBitVector9(),
        raw_bytes="0x00fe",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.PADDING_BITS,
            exact_message="the final byte 0xfe sets a padding bit",
        ),
    )


@pytest.mark.tags("malleability")
def test_bitvector12_all_padding_bits(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a twelve-bit vector whose whole padding is set is rejected.

    Given
    -----
    - a bitvector of twelve bits, whose second byte splits four data bits and four padding.
    - the input bytes 0x00f0, which set all four padding bits and no data bit.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the final byte sets a padding bit.
    - the twelve bits this would decode to are the all-clear vector, which encodes as 0x0000.
    """
    ssz_test(
        case_id="padding/bitvector12/invalid/all_padding_bits",
        type_name="PaddingBitVector12",
        value=PaddingBitVector12(),
        raw_bytes="0x00f0",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.PADDING_BITS,
            exact_message="the final byte 0xf0 sets a padding bit",
        ),
    )


@pytest.mark.tags("malleability", "offsets")
def test_container_element_highest_padding_bit(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a container whose first listed bit vector sets the highest bit of its byte is rejected.

    Given
    -----
    - a container holding a one-byte tag and a list of twelve-bit vectors behind an offset.
    - the input bytes 0xaa05000000ff80ff0f, whose list opens at offset five and holds two.
    - the first element sets padding bit seven of its second byte.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is the bit vector's padding rule, reported at the element that broke it.
    - the offending byte is the seventh of nine, not the last of the input.
    - a decoder reading the rule as being about the last input byte accepts this.
    """
    ssz_test(
        case_id="padding/tagged_bits/invalid/element_highest_padding_bit",
        type_name="PaddingTaggedBits",
        value=TAGGED_BITS,
        raw_bytes="0xaa05000000ff80ff0f",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.PADDING_BITS,
            exact_message="bits[0]: the final byte 0x80 sets a padding bit",
        ),
    )


@pytest.mark.tags("empty", "boundary")
def test_bitlist1_empty(ssz_test: SSZTestFiller) -> None:
    """
    A bitlist capped at one bit holding no bit encodes to its delimiter alone.

    Given
    -----
    - a bitlist capped at one bit.
    - no data bits at all.

    When
    ----
    - the value is encoded, decoded and merkleized.

    Then
    ----
    - the encoding is the single byte 0x01, the delimiter sitting at bit zero.
    - the seven bits above it are padding and stay clear.
    """
    ssz_test(
        case_id="padding/bitlist1/empty",
        type_name="PaddingBitList1",
        value=PaddingBitList1(),
    )


@pytest.mark.tags("boundary", "limit")
def test_bitlist1_at_limit(ssz_test: SSZTestFiller) -> None:
    """
    A bitlist capped at one bit holding that bit puts its delimiter at bit one.

    Given
    -----
    - a bitlist capped at one bit.
    - one data bit, set.

    When
    ----
    - the value is encoded, decoded and merkleized.

    Then
    ----
    - the encoding is 0x03, the data bit at position zero and the delimiter at one.
    - a cap of one is the smallest a bitlist can carry.
    - it is the only cap whose full list still keeps its delimiter inside the first byte.
    """
    ssz_test(
        case_id="padding/bitlist1/at_limit",
        type_name="PaddingBitList1",
        value=PaddingBitList1(data=[Boolean(True)]),
    )


@pytest.mark.tags("limit", "boundary")
def test_bitlist1_over_limit(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a bitlist capped at one bit from a byte delimiting two is rejected.

    Given
    -----
    - a bitlist capped at one bit.
    - the input byte 0x07, whose delimiter sits at bit two and so implies two data bits.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the implied bit-length exceeds the limit.
    - one bit fewer, 0x03, is the one-bit encoding the type does admit.
    - the whole boundary of this type lives in adjacent bits of a single byte.
    """
    ssz_test(
        case_id="padding/bitlist1/invalid/over_limit",
        type_name="PaddingBitList1",
        value=PaddingBitList1(),
        raw_bytes="0x07",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.LIMIT,
            exact_message="PaddingBitList1 holds at most 1 bits, got 2",
        ),
    )

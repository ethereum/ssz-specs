"""SSZ conformance test vectors for every padding bit a bitfield's final byte has to leave clear."""

from typing import ClassVar

import pytest

from ssz import BitList, BitVector, Boolean, CompatibleUnion, Container, List, Uint8
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


class PaddingBitVector4Union(CompatibleUnion):
    """Union over a four-bit vector, which reaches the padded byte through a selector."""

    OPTIONS = {1: PaddingBitVector4, 2: PaddingBitVector4}


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
def test_bitvector4_second_padding_bit(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a four-bit vector that sets its second padding bit and not its first is rejected.

    Given
    -----
    - a bitvector of four bits, whose byte holds four data bits and four padding bits.
    - the input byte 0x20, which sets padding bit five and leaves padding bit four clear.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the final byte sets a padding bit.
    - the rule names every bit above the declared length, not the first of them: a decoder
      testing only the lowest padding bit refuses 0x10 and accepts this.
    """
    ssz_test(
        case_id="padding/bitvector4/invalid/second_padding_bit",
        type_name="PaddingBitVector4",
        value=PaddingBitVector4(),
        raw_bytes="0x20",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.PADDING_BITS,
            exact_message="the final byte 0x20 sets a padding bit",
        ),
    )


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
    - bit seven is where a mask built to the wrong width stops covering the padding, and
      where a byte read as a signed value changes sign.
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
    - a length one below a multiple of eight is where the padding is a single bit, so the
      lowest padding bit and the highest are the same bit and the check has no room to be
      off by one in either direction.
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
def test_bitvector9_second_padding_bit(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a nine-bit vector that sets its second padding bit and not its first is rejected.

    Given
    -----
    - a bitvector of nine bits, whose second byte holds one data bit and seven padding bits.
    - the input bytes 0xff04, whose final byte sets padding bit two and leaves bit one clear.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the final byte sets a padding bit.
    - a decoder testing only the lowest padding bit accepts this, and the bytes before the
      final one say nothing about it either way.
    """
    ssz_test(
        case_id="padding/bitvector9/invalid/second_padding_bit",
        type_name="PaddingBitVector9",
        value=PaddingBitVector9(),
        raw_bytes="0xff04",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.PADDING_BITS,
            exact_message="the final byte 0x04 sets a padding bit",
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
    - the padding here runs the full width of the byte bar one bit, so the distance between
      the bit that is set and the bit a lazy check looks at is the widest it gets.
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
def test_bitvector12_highest_padding_bit(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a twelve-bit vector that sets the highest bit of its second byte is rejected.

    Given
    -----
    - a bitvector of twelve bits, whose second byte splits four data bits and four padding.
    - the input bytes 0xff80, whose final byte sets padding bit seven and nothing below it.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the final byte sets a padding bit.
    - the same width already pins its lowest padding bit through 0xff10, and the two
      together say the rule is about the whole padding rather than its first bit.
    """
    ssz_test(
        case_id="padding/bitvector12/invalid/highest_padding_bit",
        type_name="PaddingBitVector12",
        value=PaddingBitVector12(),
        raw_bytes="0xff80",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.PADDING_BITS,
            exact_message="the final byte 0x80 sets a padding bit",
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


@pytest.mark.tags("malleability", "union")
def test_union_option_highest_padding_bit(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a union whose bit-vector option sets the highest bit of its byte is rejected.

    Given
    -----
    - a union over a four-bit vector, whose byte holds four padding bits.
    - the input bytes 0x0280, whose payload sets padding bit seven and nothing below it.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is the bit vector's padding rule, reported under the selector.
    - the union already pins the lowest padding bit through 0x0210, and a decoder that
      unpacks an option through a path of its own can check only that one there too.
    """
    ssz_test(
        case_id="padding/compatible_union/invalid/option_highest_padding_bit",
        type_name="PaddingBitVector4Union",
        value=PaddingBitVector4Union(
            selector=Uint8(2), data=PaddingBitVector4(data=[Boolean(True)] * 4)
        ),
        raw_bytes="0x0280",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.PADDING_BITS,
            exact_message="[2]: the final byte 0x80 sets a padding bit",
        ),
    )


@pytest.mark.tags("malleability", "offsets")
def test_container_element_highest_padding_bit(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a container whose first listed bit vector sets the highest bit of its byte is rejected.

    Given
    -----
    - a container holding a one-byte tag and a list of twelve-bit vectors behind an offset.
    - the input bytes 0xaa05000000ff80ff0f, whose list opens at offset five and holds two
      elements, the first of them setting padding bit seven of its second byte.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is the bit vector's padding rule, reported at the element that broke it.
    - the offending byte is the seventh of nine, so a decoder that reads the padding rule
      as being about the last byte of its input rather than the last byte of the bit
      vector accepts this.
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
    - the encoding is the single byte 0x03, the data bit at position zero and the
      delimiter at position one.
    - a cap of one is the smallest a bitlist can carry, and it is the only cap under which
      a full list still leaves its delimiter inside the first byte.
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
    - one bit fewer, 0x03, is the one-bit encoding the type does admit, so the whole
      accept-or-refuse boundary of this type lives in adjacent bits of a single byte.
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

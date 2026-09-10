"""SSZ conformance test vectors for the byte strings the three bitfield shapes refuse."""

from typing import ClassVar

import pytest

from ssz import BitList, BitVector, ProgressiveBitList
from ssz_testing import ExpectedRejection, SSZTestFiller, ValueFault


class SampleBitVector4(BitVector):
    """4-bit bitvector. Half of its single byte is padding that has to stay clear."""

    LENGTH: ClassVar[int] = 4


class SampleBitVector8(BitVector):
    """8-bit bitvector. Fits exactly in one byte of SSZ encoding, so it has no padding bits."""

    LENGTH: ClassVar[int] = 8


class SampleBitVector12(BitVector):
    """12-bit bitvector. Spans two bytes, the upper half of the second one padding."""

    LENGTH: ClassVar[int] = 12


class SampleBitList16(BitList):
    """BitList allowing up to 16 bits. Exercises the length-delimiting sentinel bit."""

    LIMIT: ClassVar[int] = 16


@pytest.mark.tags("malleability")
def test_bitvector4_padding_bit_set(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a bit vector whose padding sets a bit above its declared length is rejected.

    Given
    -----
    - a bitvector of four bits, packed into one byte.
    - the input byte 0x10, which sets bit four, the lowest bit above the declared four.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the final byte sets a padding bit.
    - accepting it would give the four-bit value 0x0f decodes to a second encoding.
    """
    ssz_test(
        case_id="bitvector4/invalid/padding_bit_set",
        type_name="SampleBitVector4",
        value=SampleBitVector4(),
        raw_bytes="0x10",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.PADDING_BITS,
            message_substring="the final byte 0x10 sets a padding bit",
        ),
    )


@pytest.mark.tags("malleability")
def test_bitvector12_padding_bit_set(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a two-byte bit vector whose second byte pads above the declared length is rejected.

    Given
    -----
    - a bitvector of twelve bits, packed into two bytes.
    - the input bytes 0xff10, whose final byte sets bit twelve, four bits into the padding.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the final byte sets a padding bit.
    - the padding rule applies to the final byte alone, whatever the bytes before it hold.
    """
    ssz_test(
        case_id="bitvector12/invalid/padding_bit_set",
        type_name="SampleBitVector12",
        value=SampleBitVector12(),
        raw_bytes="0xff10",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.PADDING_BITS,
            message_substring="the final byte 0x10 sets a padding bit",
        ),
    )


@pytest.mark.tags("boundary")
def test_bitvector8_empty_input(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a bit vector from no bytes at all is rejected.

    Given
    -----
    - a bitvector of eight bits, which packs into exactly one byte.
    - an empty input.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the input spans fewer bytes than the type does.
    """
    ssz_test(
        case_id="bitvector8/invalid/empty_input",
        type_name="SampleBitVector8",
        value=SampleBitVector8(),
        raw_bytes="0x",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            message_substring="SampleBitVector8 spans 1 bytes, and the budget is 0",
        ),
    )


@pytest.mark.tags("boundary")
def test_bitvector8_bit_above_length_needs_a_second_byte(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a bit vector handed a byte past the ones its bits pack into is rejected.

    Given
    -----
    - a bitvector of eight bits, a length that fills its single byte exactly.
    - the input bytes 0x0001, which set bit eight, the first bit above the declared eight.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the input spans more bytes than the type does.
    - a length that is a multiple of eight has no padding bits, so the byte count alone
      is what refuses a bit set above it.
    """
    ssz_test(
        case_id="bitvector8/invalid/bit_above_length",
        type_name="SampleBitVector8",
        value=SampleBitVector8(),
        raw_bytes="0x0001",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            message_substring="SampleBitVector8 spans 1 bytes, and the budget is 2",
        ),
    )


@pytest.mark.tags("boundary")
def test_bitvector12_missing_byte(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a bit vector from one byte fewer than its bits need is rejected.

    Given
    -----
    - a bitvector of twelve bits, which packs into two bytes.
    - the single input byte 0xff.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the input spans fewer bytes than the type does.
    """
    ssz_test(
        case_id="bitvector12/invalid/missing_byte",
        type_name="SampleBitVector12",
        value=SampleBitVector12(),
        raw_bytes="0xff",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            message_substring="SampleBitVector12 spans 2 bytes, and the budget is 1",
        ),
    )


@pytest.mark.tags("boundary")
def test_bitlist16_empty_input(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a bitlist from no bytes at all is rejected.

    Given
    -----
    - a bitlist capped at sixteen bits.
    - an empty input.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that an empty input encodes no value.
    - the empty bitlist is not spelled this way: it still carries its delimiter, as 0x01.
    """
    ssz_test(
        case_id="bitlist16/invalid/empty_input",
        type_name="SampleBitList16",
        value=SampleBitList16(),
        raw_bytes="0x",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.EMPTY_ENCODING,
            message_substring="an empty input encodes no value",
        ),
    )


@pytest.mark.tags("malleability")
def test_bitlist16_no_delimiter(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a bitlist whose bytes set no bit anywhere is rejected.

    Given
    -----
    - a bitlist capped at sixteen bits.
    - the input bytes 0x0000, which set no bit at all and so carry no delimiter.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the encoding sets no delimiter bit.
    - this pairs with the trailing-zeros case, which is the same two bytes with a
      delimiter present but sitting below the final byte.
    """
    ssz_test(
        case_id="bitlist16/invalid/no_delimiter",
        type_name="SampleBitList16",
        value=SampleBitList16(),
        raw_bytes="0x0000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.NO_DELIMITER,
            message_substring="the encoding sets no delimiter bit",
        ),
    )


@pytest.mark.tags("malleability")
def test_bitlist16_trailing_zero_byte(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a bitlist carrying one zero byte past its delimiter is rejected.

    Given
    -----
    - a bitlist capped at sixteen bits.
    - the input bytes 0x0d00, whose delimiter sits at bit three of the first byte.
    - a second byte of zeros past that delimiter.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that zero bytes past the delimiter give one value a second encoding.
    - the three bits this would decode to already encode canonically as 0x0d.
    """
    ssz_test(
        case_id="bitlist16/invalid/trailing_zero_byte",
        type_name="SampleBitList16",
        value=SampleBitList16(),
        raw_bytes="0x0d00",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.TRAILING_ZEROS,
            message_substring="zero bytes past the delimiter give one value a second encoding",
        ),
    )


@pytest.mark.tags("malleability")
def test_bitlist16_two_trailing_zero_bytes(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a bitlist carrying two zero bytes past its delimiter is rejected.

    Given
    -----
    - a bitlist capped at sixteen bits.
    - the input bytes 0x0d0000, whose delimiter sits at bit three of the first byte.
    - two further bytes of zeros past that delimiter.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that zero bytes past the delimiter give one value a second encoding.
    - the rule counts no run of padding as short enough, so a decoder that trims trailing
      zero bytes before hunting the delimiter accepts an unbounded family of encodings.
    """
    ssz_test(
        case_id="bitlist16/invalid/two_trailing_zero_bytes",
        type_name="SampleBitList16",
        value=SampleBitList16(),
        raw_bytes="0x0d0000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.TRAILING_ZEROS,
            message_substring="zero bytes past the delimiter give one value a second encoding",
        ),
    )


@pytest.mark.tags("limit")
def test_bitlist16_over_limit(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a bitlist whose delimiter implies more bits than the limit allows is rejected.

    Given
    -----
    - a bitlist capped at sixteen bits.
    - the input bytes 0xffff02, whose delimiter sits at bit seventeen.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the implied bit-length exceeds the limit.
    - one bit fewer, 0xffff01, is the sixteen-bit encoding the type does admit.
    """
    ssz_test(
        case_id="bitlist16/invalid/over_limit",
        type_name="SampleBitList16",
        value=SampleBitList16(),
        raw_bytes="0xffff02",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.LIMIT,
            message_substring="SampleBitList16 holds at most 16 elements, got 17",
        ),
    )


@pytest.mark.tags("boundary")
def test_progressive_bitlist_empty_input(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a progressive bitlist from no bytes at all is rejected.

    Given
    -----
    - a progressive bitlist, which caps its bit count at nothing.
    - an empty input.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that an empty input encodes no value.
    - holding no bits is not holding no bytes: the empty value still encodes as 0x01.
    """
    ssz_test(
        case_id="progressive_bitlist/invalid/empty_input",
        type_name="ProgressiveBitList",
        value=ProgressiveBitList(),
        raw_bytes="0x",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.EMPTY_ENCODING,
            message_substring="an empty input encodes no value",
        ),
    )


@pytest.mark.tags("malleability")
def test_progressive_bitlist_no_delimiter(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a progressive bitlist whose byte sets no bit is rejected.

    Given
    -----
    - a progressive bitlist, which caps its bit count at nothing.
    - the single input byte 0x00, which sets no bit and so carries no delimiter.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the encoding sets no delimiter bit.
    - a bound is what a progressive bitlist drops, not the delimiter rule.
    """
    ssz_test(
        case_id="progressive_bitlist/invalid/no_delimiter",
        type_name="ProgressiveBitList",
        value=ProgressiveBitList(),
        raw_bytes="0x00",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.NO_DELIMITER,
            message_substring="the encoding sets no delimiter bit",
        ),
    )


@pytest.mark.tags("malleability")
def test_progressive_bitlist_trailing_zero_byte(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a progressive bitlist carrying a zero byte past its delimiter is rejected.

    Given
    -----
    - a progressive bitlist, which caps its bit count at nothing.
    - the input bytes 0x2b00, whose delimiter sits at bit five of the first byte.
    - a second byte of zeros past that delimiter.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that zero bytes past the delimiter give one value a second encoding.
    - the five bits this would decode to already encode canonically as 0x2b.
    """
    ssz_test(
        case_id="progressive_bitlist/invalid/trailing_zero_byte",
        type_name="ProgressiveBitList",
        value=ProgressiveBitList(),
        raw_bytes="0x2b00",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.TRAILING_ZEROS,
            message_substring="zero bytes past the delimiter give one value a second encoding",
        ),
    )

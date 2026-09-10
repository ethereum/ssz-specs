"""SSZ conformance test vectors for the inputs an EIP-8016 compatible union refuses."""

from typing import ClassVar

import pytest

from ssz import (
    BitList,
    BitVector,
    Boolean,
    ByteList,
    CompatibleUnion,
    Container,
    Uint8,
    Uint32,
)
from ssz_testing import ExpectedRejection, SSZTestFiller, ValueFault

pytestmark = pytest.mark.tags("union")


class ChosenBitList8(BitList):
    """Bitlist capped at eight bits, whose delimiter rules a union option must still obey."""

    LIMIT: ClassVar[int] = 8


class ChosenBitVector4(BitVector):
    """Four-bit bitvector, whose four padding bits a union option must still leave clear."""

    LENGTH: ClassVar[int] = 4


class ChosenByteList4(ByteList):
    """Byte list capped at four bytes, whose limit a union option must still respect."""

    LIMIT: ClassVar[int] = 4


class BooleanChoice(CompatibleUnion):
    """Union over one boolean, under two selectors."""

    OPTIONS = {1: Boolean, 2: Boolean}


class Uint32Choice(CompatibleUnion):
    """Union over a four-byte integer, the simplest fixed-width option."""

    OPTIONS = {1: Uint32, 2: Uint32}


class BitList8Choice(CompatibleUnion):
    """Union over a bounded bitlist."""

    OPTIONS = {1: ChosenBitList8, 2: ChosenBitList8}


class BitVector4Choice(CompatibleUnion):
    """Union over a fixed-length bitvector."""

    OPTIONS = {1: ChosenBitVector4, 2: ChosenBitVector4}


class ByteList4Choice(CompatibleUnion):
    """Union over a bounded byte list."""

    OPTIONS = {1: ChosenByteList4, 2: ChosenByteList4}


class TaggedChoice(Container):
    """Container reaching a union through an offset, so the union's budget is the container's."""

    tag: Uint32
    body: BooleanChoice


def test_union_decode_failure_first_reserved_selector(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a union whose selector is the first reserved value is rejected.

    Given
    -----
    - a union declaring selectors 1 and 2, the legal range ending at 127.
    - the input bytes 0x8001, whose selector 128 is the first value with the high bit set.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected before the payload byte is read.
    - the reason is that the selector names no option, the same reason an in-range
      undeclared selector gives.
    """
    ssz_test(
        case_id="compatible_union/invalid/reserved_selector_128",
        type_name="BooleanChoice",
        value=BooleanChoice(selector=Uint8(1), data=Boolean(True)),
        raw_bytes="0x8001",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.UNKNOWN_SELECTOR,
            exact_message="selector 128 names no option of BooleanChoice",
        ),
    )


def test_union_decode_failure_top_of_byte_selector(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a union whose selector is the top of a byte is rejected.

    Given
    -----
    - the same union, and the input bytes 0xff01.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the selector names no option.
    - a decoder that reads the selector as a signed byte, or that checks only the low
      seven bits, would accept this input as selector 1.
    """
    ssz_test(
        case_id="compatible_union/invalid/reserved_selector_255",
        type_name="BooleanChoice",
        value=BooleanChoice(selector=Uint8(1), data=Boolean(True)),
        raw_bytes="0xff01",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.UNKNOWN_SELECTOR,
            exact_message="selector 255 names no option of BooleanChoice",
        ),
    )


@pytest.mark.tags("empty")
def test_union_decode_failure_no_selector_in_container(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a container whose union field gets no bytes at all is rejected.

    Given
    -----
    - a container holding a four-byte tag and a union.
    - the input bytes 0x0700000008000000, whose offset leaves the union an empty budget.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the budget holds no selector, the field naming where it ran out.
    - the offset itself is well formed, so only the union's own minimum width refuses it.
    """
    ssz_test(
        case_id="compatible_union/invalid/no_selector_in_container",
        type_name="TaggedChoice",
        value=TaggedChoice(
            tag=Uint32(7), body=BooleanChoice(selector=Uint8(1), data=Boolean(True))
        ),
        raw_bytes="0x0700000008000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.NO_SELECTOR,
            exact_message="body: a budget of 0 holds no selector",
        ),
    )


def test_union_decode_failure_boolean_option_not_a_bit(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a union whose boolean option holds a byte that is not a bit is rejected.

    Given
    -----
    - a union over a boolean.
    - the input bytes 0x0102, whose selector is declared and whose payload byte is 2.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is the boolean's own, since the payload is read as the named option.
    - the message opens with the selector as a path step, which is what shows the option
      and not the union refused it.
    """
    ssz_test(
        case_id="compatible_union/invalid/option_not_a_bit",
        type_name="BooleanChoice",
        value=BooleanChoice(selector=Uint8(1), data=Boolean(True)),
        raw_bytes="0x0102",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.NOT_A_BIT,
            exact_message="[1]: a boolean is 0 or 1, got 0x02",
        ),
    )


def test_union_decode_failure_fixed_option_too_few_bytes(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a union whose fixed-width option is one byte short is rejected.

    Given
    -----
    - a union over a four-byte integer.
    - the input bytes 0x01010203, which leave the option three bytes.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is a budget mismatch, reported by the option against its own width.
    - the path step is the selector the option was read under.
    """
    ssz_test(
        case_id="compatible_union/invalid/option_budget_too_small",
        type_name="Uint32Choice",
        value=Uint32Choice(selector=Uint8(1), data=Uint32(0x04030201)),
        raw_bytes="0x01010203",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            exact_message="[1]: Uint32 spans 4 bytes, and the budget is 3",
        ),
    )


def test_union_decode_failure_fixed_option_too_many_bytes(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a union whose fixed-width option is one byte long is rejected.

    Given
    -----
    - the same union, and the input bytes 0x020102030405 under the other selector.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected, a surplus byte being as much of a mismatch as a missing one.
    - the reason is the same budget mismatch, so both directions read alike.
    - the path step is 2, the selector this payload was read under.
    """
    ssz_test(
        case_id="compatible_union/invalid/option_budget_too_large",
        type_name="Uint32Choice",
        value=Uint32Choice(selector=Uint8(2), data=Uint32(0x04030201)),
        raw_bytes="0x020102030405",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            exact_message="[2]: Uint32 spans 4 bytes, and the budget is 5",
        ),
    )


def test_union_decode_failure_bitlist_option_trailing_zeros(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a union whose bitlist option carries a zero byte past its delimiter is rejected.

    Given
    -----
    - a union over a bitlist capped at eight bits.
    - the input bytes 0x020300, whose 0x03 already delimits a one-bit list.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is the bitlist's canonicality rule, not the union's.
    - a union option is bound by every rule its own type states, so the second encoding
      of a one-bit list is no more admissible inside a union than outside one.
    """
    ssz_test(
        case_id="compatible_union/invalid/option_trailing_zeros",
        type_name="BitList8Choice",
        value=BitList8Choice(selector=Uint8(2), data=ChosenBitList8(data=[Boolean(True)])),
        raw_bytes="0x020300",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.TRAILING_ZEROS,
            exact_message=("[2]: zero bytes past the delimiter give one value a second encoding"),
        ),
    )


def test_union_decode_failure_bitvector_option_padding_bit(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a union whose bitvector option sets a padding bit is rejected.

    Given
    -----
    - a union over a four-bit bitvector, whose byte has four padding bits.
    - the input bytes 0x0210, which set bit four.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is the bitvector's padding rule, reported under the selector.
    - the payload is one byte wide either way, so nothing but the option's own rule
      separates this input from a valid one.
    """
    ssz_test(
        case_id="compatible_union/invalid/option_padding_bit",
        type_name="BitVector4Choice",
        value=BitVector4Choice(selector=Uint8(2), data=ChosenBitVector4(data=[Boolean(True)] * 4)),
        raw_bytes="0x0210",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.PADDING_BITS,
            exact_message="[2]: the final byte 0x10 sets a padding bit",
        ),
    )


@pytest.mark.tags("limit")
def test_union_decode_failure_byte_list_option_over_limit(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a union whose byte-list option runs past its limit is rejected.

    Given
    -----
    - a union over a byte list capped at four bytes.
    - the input bytes 0x02aabbccddee, whose payload is five bytes.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is the list's limit, counted over the budget the selector left.
    - the selector byte is not part of that count, so the payload alone is measured.
    """
    ssz_test(
        case_id="compatible_union/invalid/option_over_limit",
        type_name="ByteList4Choice",
        value=ByteList4Choice(selector=Uint8(2), data=ChosenByteList4(data=b"\xaa\xbb\xcc\xdd")),
        raw_bytes="0x02aabbccddee",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.LIMIT,
            exact_message="[2]: ChosenByteList4 holds at most 4 bytes, got 5",
        ),
    )

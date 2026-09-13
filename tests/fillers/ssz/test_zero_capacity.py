"""SSZ conformance test vectors for the collections a capacity of zero leaves legal."""

from typing import ClassVar, Final

import pytest

from ssz import BitList, ByteList, List, Uint64
from ssz_testing import ExpectedRejection, SSZTestFiller, ValueFault

pytestmark = pytest.mark.tags("boundary", "limit")

EMPTY_COLLECTION_ROOT: Final = "0xf5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b"
"""One zero leaf under a mixed-in count of zero, the root a capacity of zero always reaches."""


class ZeroCapacityUint64List(List[Uint64]):
    """List of eight-byte integers bounded at zero, holding the empty value and no other."""

    LIMIT: ClassVar[int] = 0


class ZeroCapacityBitList(BitList):
    """Bitlist bounded at zero bits, whose one value still writes a delimiter byte."""

    LIMIT: ClassVar[int] = 0


class ZeroCapacityByteList(ByteList):
    """Byte list bounded at zero bytes, the byte-flavoured shape the same rule leaves legal."""

    LIMIT: ClassVar[int] = 0


@pytest.mark.tags("empty")
def test_list_bounded_at_zero_elements(ssz_test: SSZTestFiller) -> None:
    """
    A list bounded at zero elements holds the empty value.

    Given
    -----
    - a list of eight-byte integers bounded at zero elements.
    - the empty value, the only one that bound admits.

    When
    ----
    - the value is encoded and merkleized.

    Then
    ----
    - the declaration stands, the illegal-types list naming only the vector.
    - it encodes to no bytes.
    - the bound gives it no data chunk, and the capacity rounds up to one leaf.
    - the root is that leaf under a mixed-in count of zero.
    """
    ssz_test(
        case_id="zero_capacity/uint64_list0/empty",
        type_name="ZeroCapacityUint64List",
        value=ZeroCapacityUint64List(),
        expected_root=EMPTY_COLLECTION_ROOT,
    )


@pytest.mark.tags("empty")
def test_bitlist_bounded_at_zero_bits(ssz_test: SSZTestFiller) -> None:
    """
    A bitlist bounded at zero bits holds the empty value, and encodes to one byte.

    Given
    -----
    - a bitlist bounded at zero bits.
    - the empty value, the only one that bound admits.

    When
    ----
    - the value is encoded and merkleized.

    Then
    ----
    - the declaration stands, the illegal-types list naming only the bitvector.
    - it encodes to 0x01, the delimiter sitting at position zero.
    - that byte is why a bitvector of zero bits is illegal and this shape is not.
    - the root is one zero leaf under a mixed-in count of zero.
    """
    ssz_test(
        case_id="zero_capacity/bitlist0/delimiter_only",
        type_name="ZeroCapacityBitList",
        value=ZeroCapacityBitList(),
        expected_root=EMPTY_COLLECTION_ROOT,
    )


@pytest.mark.tags("empty")
def test_byte_list_bounded_at_zero_bytes(ssz_test: SSZTestFiller) -> None:
    """
    A byte list bounded at zero bytes holds the empty value.

    Given
    -----
    - a byte list bounded at zero bytes.
    - the empty value, the only one that bound admits.

    When
    ----
    - the value is encoded and merkleized.

    Then
    ----
    - the declaration stands, the alias reading like the list beside it.
    - an implementation keying its refusal on the kind would refuse this one.
    - it encodes to no bytes, and roots as the list does.
    """
    ssz_test(
        case_id="zero_capacity/bytelist0/empty",
        type_name="ZeroCapacityByteList",
        value=ZeroCapacityByteList(),
        expected_root=EMPTY_COLLECTION_ROOT,
    )


def test_bitlist_bounded_at_zero_given_one_bit(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a bitlist bounded at zero bits from an input carrying one bit is rejected.

    Given
    -----
    - a bitlist bounded at zero bits.
    - the input byte 0x02, its delimiter at position one, leaving one bit.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the recovered bit count exceeds the limit, so a bound of zero bounds.
    - it spans the same byte the accepted encoding does, so a width check admits it.
    - the bit it leaves is clear, so a bit-set check admits it too.
    """
    ssz_test(
        case_id="zero_capacity/bitlist0/invalid/one_bit",
        type_name="ZeroCapacityBitList",
        value=ZeroCapacityBitList(),
        raw_bytes="0x02",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.LIMIT,
            exact_message="ZeroCapacityBitList holds at most 0 bits, got 1",
        ),
    )

"""SSZ conformance test vectors for the option kinds an EIP-8016 compatible union admits."""

from typing import ClassVar

import pytest

from ssz import (
    BitList,
    BitVector,
    Boolean,
    ByteList,
    ByteVector,
    CompatibleUnion,
    Container,
    Uint8,
    Uint16,
    Uint32,
    Uint64,
    Vector,
)
from ssz_testing import SSZTestFiller

pytestmark = pytest.mark.tags("union")


class OptionBytes4(ByteVector):
    """Four-byte string, a fixed-size byte array standing as a union option."""

    LENGTH: ClassVar[int] = 4


class OptionByteList8(ByteList):
    """Byte string capped at eight bytes, a variable-size byte array standing as a union option."""

    LIMIT: ClassVar[int] = 8


class OptionBitVector8(BitVector):
    """Eight-bit bitvector, one packed byte, standing as a union option."""

    LENGTH: ClassVar[int] = 8


class OptionBitList16(BitList):
    """Bitlist capped at sixteen bits, delimiter and all, standing as a union option."""

    LIMIT: ClassVar[int] = 16


class OptionUint16Vector3(Vector[Uint16]):
    """Three two-byte elements, a fixed-size vector standing as a union option."""

    LENGTH: ClassVar[int] = 3


class OptionPoint(Container):
    """Plain container of two four-byte fields, not a progressive one."""

    x: Uint32
    y: Uint32


class OptionUint64Union(CompatibleUnion):
    """Union over a basic type, the same uint under a low selector and a mid-range one."""

    OPTIONS = {1: Uint64, 64: Uint64}


class OptionBytes4Union(CompatibleUnion):
    """Union over a fixed-size byte array."""

    OPTIONS = {1: OptionBytes4, 2: OptionBytes4}


class OptionByteList8Union(CompatibleUnion):
    """Union over a bounded byte string."""

    OPTIONS = {1: OptionByteList8, 2: OptionByteList8}


class OptionBitVector8Union(CompatibleUnion):
    """Union over a fixed-length bitvector."""

    OPTIONS = {1: OptionBitVector8, 2: OptionBitVector8}


class OptionBitList16Union(CompatibleUnion):
    """Union over a bounded bitlist."""

    OPTIONS = {1: OptionBitList16, 2: OptionBitList16}


class OptionUint16Vector3Union(CompatibleUnion):
    """Union over a fixed-size vector of a basic element."""

    OPTIONS = {1: OptionUint16Vector3, 2: OptionUint16Vector3}


class OptionPointUnion(CompatibleUnion):
    """Union over a plain container."""

    OPTIONS = {1: OptionPoint, 2: OptionPoint}


class OptionByteAlone(CompatibleUnion):
    """Single-option union over one byte, the smallest union EIP-8016 admits."""

    OPTIONS = {42: Uint8}


def test_union_over_a_uint_at_a_low_selector(ssz_test: SSZTestFiller) -> None:
    """
    A union holding a basic uint option under selector 1 round-trips unchanged.

    Given
    -----
    - a union declaring an eight-byte uint under selectors 1 and 64.
    - a value holding that uint under selector 1.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is the selector byte followed by the uint's eight little-endian bytes.
    - the payload roots to one packed chunk, with the selector mixed in above it.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="union_option/uint64/selector_1",
        type_name="OptionUint64Union",
        value=OptionUint64Union(selector=Uint8(1), data=Uint64(0x1234567890ABCDEF)),
    )


def test_union_over_a_uint_at_a_mid_range_selector(ssz_test: SSZTestFiller) -> None:
    """
    The same uint payload under selector 64 round-trips unchanged and roots differently.

    Given
    -----
    - the same union, and the same uint value, under selector 64.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the payload bytes match the selector-1 case exactly, only the leading byte differing.
    - the root differs, because the selector is mixed in above an identical subtree.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="union_option/uint64/selector_64",
        type_name="OptionUint64Union",
        value=OptionUint64Union(selector=Uint8(64), data=Uint64(0x1234567890ABCDEF)),
    )


def test_union_over_a_byte_vector(ssz_test: SSZTestFiller) -> None:
    """
    A union holding a fixed-size byte array round-trips unchanged.

    Given
    -----
    - a union over a four-byte string.
    - a value holding four nonzero bytes.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is the selector byte followed by the four bytes, with no offset.
    - the payload roots to one chunk, the four bytes right-padded with zeros.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="union_option/byte_vector",
        type_name="OptionBytes4Union",
        value=OptionBytes4Union(selector=Uint8(1), data=OptionBytes4(b"\xde\xad\xbe\xef")),
    )


def test_union_over_a_byte_list(ssz_test: SSZTestFiller) -> None:
    """
    A union holding a bounded byte string round-trips unchanged.

    Given
    -----
    - a union over a byte string capped at eight bytes.
    - a value holding three of them.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the bytes follow the selector directly, their count carried by the scope alone.
    - the payload mixes its length in above one packed chunk, and the selector above that.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="union_option/byte_list",
        type_name="OptionByteList8Union",
        value=OptionByteList8Union(selector=Uint8(2), data=OptionByteList8(data=b"\x01\x02\x03")),
    )


def test_union_over_a_bitvector(ssz_test: SSZTestFiller) -> None:
    """
    A union holding a fixed-length bitvector round-trips unchanged.

    Given
    -----
    - a union over an eight-bit bitvector.
    - a value whose set bits pack into a single byte.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is the selector byte followed by that one packed byte.
    - no length is mixed in below the selector, the capacity being fixed.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="union_option/bitvector",
        type_name="OptionBitVector8Union",
        value=OptionBitVector8Union(
            selector=Uint8(1),
            data=OptionBitVector8(
                data=[
                    Boolean(True),
                    Boolean(False),
                    Boolean(True),
                    Boolean(True),
                    Boolean(False),
                    Boolean(False),
                    Boolean(False),
                    Boolean(True),
                ]
            ),
        ),
    )


def test_union_over_a_bitlist(ssz_test: SSZTestFiller) -> None:
    """
    A union holding a bounded bitlist round-trips unchanged.

    Given
    -----
    - a union over a bitlist capped at sixteen bits.
    - a value holding five bits.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the payload byte carries the five bits and the delimiter bit above them.
    - the bit count is mixed in below the selector, the delimiter never reaching the tree.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="union_option/bitlist",
        type_name="OptionBitList16Union",
        value=OptionBitList16Union(
            selector=Uint8(2),
            data=OptionBitList16(
                data=[Boolean(True), Boolean(True), Boolean(False), Boolean(False), Boolean(True)]
            ),
        ),
    )


def test_union_over_a_fixed_size_vector(ssz_test: SSZTestFiller) -> None:
    """
    A union holding a fixed-size vector round-trips unchanged.

    Given
    -----
    - a union over three two-byte elements.
    - a value holding all three.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the six element bytes follow the selector, with no offset and no length.
    - the payload packs into one chunk, and the selector is mixed in above it.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="union_option/vector",
        type_name="OptionUint16Vector3Union",
        value=OptionUint16Vector3Union(
            selector=Uint8(1),
            data=OptionUint16Vector3(data=[Uint16(0x1111), Uint16(0x2222), Uint16(0x3333)]),
        ),
    )


def test_union_over_a_plain_container(ssz_test: SSZTestFiller) -> None:
    """
    A union holding a plain container round-trips unchanged.

    Given
    -----
    - a union over a container of two four-byte fields, with no progressive layout.
    - a value holding both fields.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the eight fixed bytes follow the selector, the container being fixed-size.
    - the payload roots to one field chunk per field, with no layout word mixed in.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="union_option/container",
        type_name="OptionPointUnion",
        value=OptionPointUnion(
            selector=Uint8(2), data=OptionPoint(x=Uint32(0x0A0B0C0D), y=Uint32(0x01020304))
        ),
    )


def test_single_option_union_rooted_on_its_own(ssz_test: SSZTestFiller) -> None:
    """
    A union declaring one option round-trips unchanged as a top-level value.

    Given
    -----
    - a union declaring one byte under selector 42, and nothing else.
    - a value holding that byte, rooted on its own rather than nested in another type.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is two bytes, the selector and the payload.
    - the root still mixes the selector in, a lone option earning no exemption.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="union_option/single_option",
        type_name="OptionByteAlone",
        value=OptionByteAlone(selector=Uint8(42), data=Uint8(0xAB)),
    )

"""SSZ: how many elements a chunk holds at each basic width, and the container shapes around it."""

from typing import ClassVar

import pytest

from ssz import (
    BitList,
    BitVector,
    Boolean,
    Container,
    ProgressiveList,
    Uint8,
    Uint16,
    Uint32,
    Uint64,
    Uint128,
    Uint256,
    Vector,
)
from ssz_testing import ExpectedRejection, SSZTestFiller, ValueFault


class DensityUint16Vector16(Vector[Uint16]):
    """Sixteen two-byte elements, the count that fills one chunk at that width."""

    LENGTH: ClassVar[int] = 16


class DensityUint32Vector8(Vector[Uint32]):
    """Eight four-byte elements, the count that fills one chunk at that width."""

    LENGTH: ClassVar[int] = 8


class DensityUint128Vector2(Vector[Uint128]):
    """Two sixteen-byte elements, the count that fills one chunk at that width."""

    LENGTH: ClassVar[int] = 2


class DensityUint128Vector3(Vector[Uint128]):
    """Three sixteen-byte elements, so the second chunk is half data and half padding."""

    LENGTH: ClassVar[int] = 3


class DensityUint128ProgressiveList(ProgressiveList[Uint128]):
    """Sixteen-byte elements under a spine, where no declared capacity bounds the chunk count."""


class DensityWidthContainer(Container):
    """One field per unsigned integer width, so no two of its leaves pad out alike."""

    tiny: Uint8
    small: Uint16
    medium: Uint32
    large: Uint64
    huge: Uint128
    full: Uint256


class BitsList5(BitList):
    """Five bits at most, the first variable field of the bitfield-only struct."""

    LIMIT: ClassVar[int] = 5


class BitsVector2(BitVector):
    """Two bits, which occupy one whole byte of the fixed part."""

    LENGTH: ClassVar[int] = 2


class BitsVector1(BitVector):
    """One bit, which occupies one whole byte of the fixed part."""

    LENGTH: ClassVar[int] = 1


class BitsList6(BitList):
    """Six bits at most, the second variable field of the bitfield-only struct."""

    LIMIT: ClassVar[int] = 6


class BitsVector8(BitVector):
    """Eight bits, the only field of the struct whose bit count is already a byte."""

    LENGTH: ClassVar[int] = 8


class BitsStruct(Container):
    """Bitfields alone, two sub-byte bit vectors adjacent between the two bitlist offsets."""

    head_bits: BitsList5
    pair: BitsVector2
    single: BitsVector1
    tail_bits: BitsList6
    octet: BitsVector8


UINT16_ASCENDING = [
    Uint16(0x0201),
    Uint16(0x0403),
    Uint16(0x0605),
    Uint16(0x0807),
    Uint16(0x0A09),
    Uint16(0x0C0B),
    Uint16(0x0E0D),
    Uint16(0x100F),
    Uint16(0x1211),
    Uint16(0x1413),
    Uint16(0x1615),
    Uint16(0x1817),
    Uint16(0x1A19),
    Uint16(0x1C1B),
    Uint16(0x1E1D),
    Uint16(0x201F),
]
"""Sixteen two-byte elements whose little-endian bytes run 1 through 32."""


UINT32_ASCENDING = [
    Uint32(0x04030201),
    Uint32(0x08070605),
    Uint32(0x0C0B0A09),
    Uint32(0x100F0E0D),
    Uint32(0x14131211),
    Uint32(0x18171615),
    Uint32(0x1C1B1A19),
    Uint32(0x201F1E1D),
]
"""Eight four-byte elements whose little-endian bytes run 1 through 32."""


UINT128_ASCENDING = [
    Uint128(0x100F0E0D0C0B0A090807060504030201),
    Uint128(0x201F1E1D1C1B1A191817161514131211),
    Uint128(0x302F2E2D2C2B2A292827262524232221),
]
"""Three sixteen-byte elements whose little-endian bytes run 1 through 48."""


@pytest.mark.tags("boundary")
def test_uint16_vector_filling_one_chunk(ssz_test: SSZTestFiller) -> None:
    """
    A 16-element uint16 vector merkleizes to a stable root.

    Given
    -----
    - a uint16 vector of 16 distinct elements, sixteen to a chunk at two bytes each.
    - elements chosen so the packed chunk is the ascending bytes 1 through 32.

    When
    ----
    - the value is encoded, merkleized and then decoded.

    Then
    ----
    - the encoding fills exactly one chunk, with no padding byte.
    - the root is that chunk unhashed, the same one a 32-element uint8 vector of those bytes packs.
    - a packer writing the elements big-endian roots to something else.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="density/uint16_vector16/one_chunk",
        type_name="DensityUint16Vector16",
        value=DensityUint16Vector16(data=UINT16_ASCENDING),
        expected_root="0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20",
    )


@pytest.mark.tags("boundary")
def test_uint32_vector_filling_one_chunk(ssz_test: SSZTestFiller) -> None:
    """
    An 8-element uint32 vector merkleizes to a stable root.

    Given
    -----
    - a uint32 vector of 8 distinct elements, eight to a chunk at four bytes each.
    - elements chosen so the packed chunk is the ascending bytes 1 through 32.

    When
    ----
    - the value is encoded, merkleized and then decoded.

    Then
    ----
    - the encoding fills exactly one chunk, with no padding byte.
    - the root is that chunk unhashed, and equals the 16-element uint16 vector's above.
    - a packer writing the elements big-endian roots to something else.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="density/uint32_vector8/one_chunk",
        type_name="DensityUint32Vector8",
        value=DensityUint32Vector8(data=UINT32_ASCENDING),
        expected_root="0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20",
    )


@pytest.mark.tags("boundary")
def test_uint128_vector_filling_one_chunk(ssz_test: SSZTestFiller) -> None:
    """
    A 2-element uint128 vector merkleizes to a stable root.

    Given
    -----
    - a uint128 vector of 2 distinct elements, two to a chunk at sixteen bytes each.
    - elements chosen so the packed chunk is the ascending bytes 1 through 32.

    When
    ----
    - the value is encoded, merkleized and then decoded.

    Then
    ----
    - the encoding fills exactly one chunk, with no padding byte.
    - the root is that chunk unhashed, the same one the two vectors above root to.
    - two elements to a chunk is a density no other vector in the suite reaches.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="density/uint128_vector2/one_chunk",
        type_name="DensityUint128Vector2",
        value=DensityUint128Vector2(data=UINT128_ASCENDING[:2]),
        expected_root="0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20",
    )


@pytest.mark.tags("boundary")
def test_uint128_vector_spilling_into_half_a_chunk(ssz_test: SSZTestFiller) -> None:
    """
    A 3-element uint128 vector merkleizes to a stable root.

    Given
    -----
    - a uint128 vector of 3 distinct elements, 48 bytes at sixteen bytes each.
    - a second chunk holding one element and sixteen bytes of zero padding.

    When
    ----
    - the value is encoded, merkleized and then decoded.

    Then
    ----
    - the encoding is the 48 packed bytes.
    - the capacity is two chunks, so the root joins the two leaves with no padding leaf.
    - the sixteen trailing zero bytes sit inside the second leaf, not in a leaf of their own.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="density/uint128_vector3/partial_chunk",
        type_name="DensityUint128Vector3",
        value=DensityUint128Vector3(data=UINT128_ASCENDING),
        expected_root="0xc2eeebe3698f978911d8e7fee3d1cada347475930ae1b59ce2b2490a957dce79",
    )


@pytest.mark.tags("boundary")
def test_uint128_progressive_list_spilling_into_half_a_chunk(ssz_test: SSZTestFiller) -> None:
    """
    A 3-element uint128 progressive list merkleizes to a stable root.

    Given
    -----
    - a progressive list of 3 sixteen-byte elements, the same 48 bytes the vector above holds.
    - two packed chunks, so the spine opens a first level of one and a second level of four.

    When
    ----
    - the value is encoded, merkleized and then decoded.

    Then
    ----
    - the encoding is the 48 packed bytes.
    - the second level holds one chunk against three zero leaves.
    - the word mixed in is the element count 3, not the chunk count 2.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="density/uint128_progressive_list/partial_chunk",
        type_name="DensityUint128ProgressiveList",
        value=DensityUint128ProgressiveList(data=UINT128_ASCENDING),
        expected_root="0x46147cf3dc3d14ea3602f0ce40bc7a38edf336170d3c37cf44da087ee31d0181",
    )


@pytest.mark.tags("default")
def test_container_of_every_width_all_zero(ssz_test: SSZTestFiller) -> None:
    """
    A container whose six fields are all zero merkleizes to a stable root.

    Given
    -----
    - a container of one field per unsigned integer width, every one of them zero.
    - six leaves that are each the zero chunk, under a tree padded to eight.

    When
    ----
    - the value is encoded, merkleized and then decoded.

    Then
    ----
    - the encoding is 63 zero bytes, the sum of the six declared widths.
    - the root is the all-zero perfect tree of eight leaves, data and padding alike.
    - a container is the only shape whose leaves are field roots.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="density/container/all_zero",
        type_name="DensityWidthContainer",
        value=DensityWidthContainer.default(),
        expected_root="0xc78009fdf07fc56a11f122370658a353aaa542ed63e44c4bc15ff4cd105ab33c",
    )


def test_container_of_every_width_all_max(ssz_test: SSZTestFiller) -> None:
    """
    A container whose six fields are each at their type maximum merkleizes to a stable root.

    Given
    -----
    - a container of one field per unsigned integer width, every one of them at its maximum.
    - six leaves that differ only in how many leading bytes are set before the zero padding.

    When
    ----
    - the value is encoded, merkleized and then decoded.

    Then
    ----
    - the encoding is 63 bytes of 0xff.
    - the one-byte field's leaf holds one 0xff and 31 zeros, and the widest field's holds 32.
    - a field padded on the wrong side, or to the wrong width, roots to something else.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="density/container/all_max",
        type_name="DensityWidthContainer",
        value=DensityWidthContainer(
            tiny=Uint8(2**8 - 1),
            small=Uint16(2**16 - 1),
            medium=Uint32(2**32 - 1),
            large=Uint64(2**64 - 1),
            huge=Uint128(2**128 - 1),
            full=Uint256(2**256 - 1),
        ),
        expected_root="0xcb96f7919dbf0e496d8bad47e89b9c1722b4cc37b7ff980ec72a5fd8a2d95f3b",
    )


@pytest.mark.tags("offsets")
def test_bitfield_only_struct(ssz_test: SSZTestFiller) -> None:
    """
    A container of bitfields alone round-trips unchanged and merkleizes to a stable root.

    Given
    -----
    - a container of 5- and 6-bit bitlists and 2-, 1- and 8-bit bit vectors.
    - each bit vector taking one whole byte of the fixed part, whatever its bit count.

    When
    ----
    - the value is encoded, merkleized and then decoded.

    Then
    ----
    - the fixed part spans eleven bytes: two offsets of four, and three bit vectors of one.
    - the first offset is eleven and the second is twelve, the first bitlist spanning one byte.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="bit_struct/filled",
        type_name="BitsStruct",
        value=BitsStruct(
            head_bits=BitsList5(data=[Boolean(True), Boolean(False), Boolean(True)]),
            pair=BitsVector2(data=[Boolean(True), Boolean(False)]),
            single=BitsVector1(data=[Boolean(True)]),
            tail_bits=BitsList6(
                data=[
                    Boolean(False),
                    Boolean(True),
                    Boolean(True),
                    Boolean(False),
                    Boolean(True),
                    Boolean(True),
                ]
            ),
            octet=BitsVector8(data=[Boolean(index % 2 == 0) for index in range(8)]),
        ),
    )


@pytest.mark.tags("offsets")
def test_bitfield_only_struct_first_offset_below_fixed_part(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a bitfield-only struct whose first offset stops short of its fixed part is rejected.

    Given
    -----
    - the encoding above, whose fixed part ends at eleven.
    - a first offset of nine, what rounding each bit vector's bit count down to bytes gives.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the first offset must be the fixed part's width exactly.
    - a decoder measuring the two sub-byte bit vectors as nothing reads the payload early.
    """
    ssz_test(
        case_id="bit_struct/invalid/first_offset_below_fixed_part",
        type_name="BitsStruct",
        value=BitsStruct.default(),
        raw_bytes="0x0900000001010c000000550d76",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.FIRST_OFFSET,
            exact_message="the first offset is 9, and the fixed part ends at 11",
        ),
    )


@pytest.mark.tags("offsets")
def test_bitfield_only_struct_first_offset_above_fixed_part(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a bitfield-only struct whose first offset overshoots its fixed part is rejected.

    Given
    -----
    - the encoding above, whose fixed part ends at eleven.
    - a first offset of nineteen, what counting a byte per bit of each bit vector gives.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the first offset must be the fixed part's width exactly.
    - the offset is settled before the table closes over the budget.
    """
    ssz_test(
        case_id="bit_struct/invalid/first_offset_above_fixed_part",
        type_name="BitsStruct",
        value=BitsStruct.default(),
        raw_bytes="0x1300000001010c000000550d76",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.FIRST_OFFSET,
            exact_message="the first offset is 19, and the fixed part ends at 11",
        ),
    )

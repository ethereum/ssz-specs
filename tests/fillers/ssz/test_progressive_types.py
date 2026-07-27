"""SSZ conformance test vectors for the EIP-7916 progressive types."""

from ssz import (
    Boolean,
    Bytes,
    Container,
    ProgressiveBitlist,
    ProgressiveList,
    Uint8,
    Uint16,
    Uint64,
)
from ssz_testing import SSZTestFiller


class Bytes32(Bytes):
    LENGTH = 32


class SampleUint64ProgressiveList(ProgressiveList[Uint64]):
    """
    Progressive list of eight-byte elements, with no capacity.

    Four elements fill one 32-byte Merkle chunk, so the element counts below walk
    the spine's level boundaries at 1, 5, 21, and 85 chunks.
    """

    ELEMENT_TYPE = Uint64


class SampleBytes32ProgressiveList(ProgressiveList[Bytes32]):
    """Progressive list of composite 32-byte elements, one Merkle leaf each."""

    ELEMENT_TYPE = Bytes32


class SampleUint16ProgressiveList(ProgressiveList[Uint16]):
    """Progressive list of two-byte elements, used standalone and as a nested element."""

    ELEMENT_TYPE = Uint16


class SampleNestedProgressiveList(ProgressiveList[SampleUint16ProgressiveList]):
    """Progressive list of variable-size elements, encoded behind an offset table."""

    ELEMENT_TYPE = SampleUint16ProgressiveList


class SampleContainerWithProgressiveList(Container):
    """Container embedding a progressive list between two fixed-size fields."""

    a: Uint16
    b: SampleUint64ProgressiveList
    c: Uint8


PROGRESSIVE_BITLIST_LEVEL_BITS = 257
"""Bit count that spills one bit past the first Merkle chunk, opening the second level."""


def test_progressive_list_empty(ssz_test: SSZTestFiller) -> None:
    """
    An empty progressive list round-trips unchanged.

    Given
    -----
    - a progressive list of eight-byte elements with no entries.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is empty.
    - the root is the zero terminator with a zero count mixed in.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleUint64ProgressiveList",
        value=SampleUint64ProgressiveList(data=[]),
    )


def test_progressive_list_single_element(ssz_test: SSZTestFiller) -> None:
    """
    A progressive list holding one element round-trips unchanged.

    Given
    -----
    - a progressive list with a single eight-byte element.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the root hashes one chunk against the terminator.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleUint64ProgressiveList",
        value=SampleUint64ProgressiveList(data=[Uint64(1)]),
    )


def test_progressive_list_fills_first_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive list whose data fills the first level exactly round-trips unchanged.

    Given
    -----
    - a progressive list of four eight-byte elements.
    - data occupying exactly one 32-byte chunk, the full width of level one.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the root leaves every level past the first as the terminator.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleUint64ProgressiveList",
        value=SampleUint64ProgressiveList(data=[Uint64(value) for value in range(4)]),
    )


def test_progressive_list_opens_second_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive list one element past the first chunk round-trips unchanged.

    Given
    -----
    - a progressive list of five eight-byte elements.
    - data occupying two chunks, so the four-wide second level opens.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the root pads the second level's lone chunk out to width four.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleUint64ProgressiveList",
        value=SampleUint64ProgressiveList(data=[Uint64(value) for value in range(5)]),
    )


def test_progressive_list_fills_second_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive list whose data fills two levels exactly round-trips unchanged.

    Given
    -----
    - a progressive list of twenty eight-byte elements.
    - data occupying five chunks, the cumulative capacity of levels one and two.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the root needs no padding in either occupied level.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleUint64ProgressiveList",
        value=SampleUint64ProgressiveList(data=[Uint64(value) for value in range(20)]),
    )


def test_progressive_list_opens_third_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive list one element past the second level round-trips unchanged.

    Given
    -----
    - a progressive list of twenty-one eight-byte elements.
    - data occupying six chunks, so the sixteen-wide third level opens.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the root pads the third level's lone chunk out to width sixteen.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleUint64ProgressiveList",
        value=SampleUint64ProgressiveList(data=[Uint64(value) for value in range(21)]),
    )


def test_progressive_list_fills_third_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive list whose data fills three levels exactly round-trips unchanged.

    Given
    -----
    - a progressive list of eighty-four eight-byte elements.
    - data occupying twenty-one chunks, the cumulative capacity of levels one to three.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the root needs no padding in any occupied level.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleUint64ProgressiveList",
        value=SampleUint64ProgressiveList(data=[Uint64(value) for value in range(84)]),
    )


def test_progressive_list_opens_fourth_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive list one element past the third level round-trips unchanged.

    Given
    -----
    - a progressive list of eighty-five eight-byte elements.
    - data occupying twenty-two chunks, so the sixty-four-wide fourth level opens.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the root pads the fourth level's lone chunk out to width sixty-four.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleUint64ProgressiveList",
        value=SampleUint64ProgressiveList(data=[Uint64(value) for value in range(85)]),
    )


def test_progressive_list_of_composites_empty(ssz_test: SSZTestFiller) -> None:
    """
    An empty progressive list of composite elements round-trips unchanged.

    Given
    -----
    - a progressive list of 32-byte elements with no entries.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is empty.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleBytes32ProgressiveList",
        value=SampleBytes32ProgressiveList(data=[]),
    )


def test_progressive_list_of_composites_single(ssz_test: SSZTestFiller) -> None:
    """
    A progressive list holding one composite element round-trips unchanged.

    Given
    -----
    - a progressive list with a single 32-byte element.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the element's own root is the only leaf of the first level.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleBytes32ProgressiveList",
        value=SampleBytes32ProgressiveList(data=[Bytes32(b"\xaa" * 32)]),
    )


def test_progressive_list_of_composites_crosses_a_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive list of six composite elements round-trips unchanged.

    Given
    -----
    - a progressive list of six 32-byte elements.
    - one leaf per element, so six leaves reach into the third level.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the root places each element root at a stable position on the spine.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleBytes32ProgressiveList",
        value=SampleBytes32ProgressiveList(
            data=[Bytes32(bytes([value]) * 32) for value in range(1, 7)]
        ),
    )


def test_progressive_list_of_variable_size_elements(ssz_test: SSZTestFiller) -> None:
    """
    A progressive list of variable-size elements round-trips unchanged.

    Given
    -----
    - a progressive list whose elements are themselves progressive lists.
    - inner lists of differing widths, including an empty one.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding carries an offset table sized for the runtime element count.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleNestedProgressiveList",
        value=SampleNestedProgressiveList(
            data=[
                SampleUint16ProgressiveList(data=[Uint16(1), Uint16(2)]),
                SampleUint16ProgressiveList(data=[]),
                SampleUint16ProgressiveList(data=[Uint16(3), Uint16(4), Uint16(5)]),
            ]
        ),
    )


def test_progressive_bitlist_empty(ssz_test: SSZTestFiller) -> None:
    """
    An empty progressive bitlist round-trips unchanged.

    Given
    -----
    - a progressive bitlist with no data bits.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is the single delimiter byte 0x01.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="ProgressiveBitlist",
        value=ProgressiveBitlist(data=[]),
    )


def test_progressive_bitlist_small(ssz_test: SSZTestFiller) -> None:
    """
    A short progressive bitlist round-trips unchanged.

    Given
    -----
    - a progressive bitlist of three data bits.
    - a delimiter bit immediately above them in the same byte.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the root hashes one chunk against the terminator and mixes in the bit count.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="ProgressiveBitlist",
        value=ProgressiveBitlist(data=[Boolean(True), Boolean(False), Boolean(True)]),
    )


def test_progressive_bitlist_fills_one_chunk(ssz_test: SSZTestFiller) -> None:
    """
    A progressive bitlist filling exactly one chunk round-trips unchanged.

    Given
    -----
    - a progressive bitlist of 256 data bits, all set.
    - a delimiter bit that spills into a fresh byte.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the packed data occupies one chunk, so only the first level is occupied.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="ProgressiveBitlist",
        value=ProgressiveBitlist(data=[Boolean(True)] * 256),
    )


def test_progressive_bitlist_opens_second_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive bitlist one bit past a chunk round-trips unchanged.

    Given
    -----
    - a progressive bitlist of 257 data bits, all set.
    - one bit spilling into a second chunk of packed data.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the second level opens and pads its lone chunk out to width four.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="ProgressiveBitlist",
        value=ProgressiveBitlist(data=[Boolean(True)] * PROGRESSIVE_BITLIST_LEVEL_BITS),
    )


def test_container_with_progressive_list_field(ssz_test: SSZTestFiller) -> None:
    """
    A container embedding a progressive list round-trips unchanged.

    Given
    -----
    - a container with a fixed-size field, a progressive list, and another fixed field.
    - a populated progressive list in the middle position.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the container writes one offset for the variable-size field.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleContainerWithProgressiveList",
        value=SampleContainerWithProgressiveList(
            a=Uint16(0xABCD),
            b=SampleUint64ProgressiveList(data=[Uint64(1), Uint64(2), Uint64(3)]),
            c=Uint8(0xFF),
        ),
    )


def test_container_with_empty_progressive_list_field(ssz_test: SSZTestFiller) -> None:
    """
    A container embedding an empty progressive list round-trips unchanged.

    Given
    -----
    - a container whose progressive list field holds no elements.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the offset points past the end of the fixed part, with no body following it.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleContainerWithProgressiveList",
        value=SampleContainerWithProgressiveList(
            a=Uint16(0xABCD),
            b=SampleUint64ProgressiveList(data=[]),
            c=Uint8(0xFF),
        ),
    )

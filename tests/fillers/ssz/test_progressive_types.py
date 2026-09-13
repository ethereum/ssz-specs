"""SSZ conformance test vectors for the EIP-7916 progressive types."""

import pytest

from ssz import (
    Boolean,
    ByteVector,
    Container,
    ProgressiveBitList,
    ProgressiveList,
    Uint8,
    Uint16,
    Uint64,
)
from ssz_testing import SSZTestFiller


class Bytes32(ByteVector):
    LENGTH = 32


class SampleUint64ProgressiveList(ProgressiveList[Uint64]):
    """Progressive list of eight-byte elements, four to a 32-byte chunk, with no capacity."""

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
        case_id="progressive_list/single_element",
        type_name="SampleUint64ProgressiveList",
        value=SampleUint64ProgressiveList(data=[Uint64(1)]),
        expected_root="0x905efb51c2764c2c7a4efb0548e372569df06db82115c3b1896c186632f3fe5b",
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
        case_id="progressive_list/fills_first_level",
        type_name="SampleUint64ProgressiveList",
        value=SampleUint64ProgressiveList(data=[Uint64(value) for value in range(4)]),
        expected_root="0xfb119bdda96d8ebf59b511db66fc19a40f4f1543a5aa87d8d9b4519655a8eda9",
    )


@pytest.mark.tags("multi-level")
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
        case_id="progressive_list/opens_second_level",
        type_name="SampleUint64ProgressiveList",
        value=SampleUint64ProgressiveList(data=[Uint64(value) for value in range(5)]),
        expected_root="0xb52da986d8c44ac58d43d54d5a6f27363363ad09e1249d211c38c21c5221e5f4",
    )


@pytest.mark.tags("multi-level")
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
        case_id="progressive_list/fills_second_level",
        type_name="SampleUint64ProgressiveList",
        value=SampleUint64ProgressiveList(data=[Uint64(value) for value in range(20)]),
        expected_root="0x1957d11b2bce3ef0c72872fca6fa4cffacc27e601c91b88ab8e6b28eebc6525c",
    )


@pytest.mark.tags("multi-level")
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
        case_id="progressive_list/opens_third_level",
        type_name="SampleUint64ProgressiveList",
        value=SampleUint64ProgressiveList(data=[Uint64(value) for value in range(21)]),
        expected_root="0x86a8ce9749021379ba7af31ac5d6f3b33e0e0791a5c9bb2e00580fe8d6aeb117",
    )


@pytest.mark.tags("multi-level")
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
        case_id="progressive_list/fills_third_level",
        type_name="SampleUint64ProgressiveList",
        value=SampleUint64ProgressiveList(data=[Uint64(value) for value in range(84)]),
        expected_root="0x765cd3f85263382f72bcf782dd80038ec9184206fdde9e0872f5ec4025ed992f",
    )


@pytest.mark.tags("multi-level")
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
        case_id="progressive_list/opens_fourth_level",
        type_name="SampleUint64ProgressiveList",
        value=SampleUint64ProgressiveList(data=[Uint64(value) for value in range(85)]),
        expected_root="0x44149f84b9899187d206378ab59b88e7e59ebd3ed84fd95b4b2ba58b08f98024",
    )


@pytest.mark.tags("empty")
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
        case_id="progressive_list/composites/empty",
        type_name="SampleBytes32ProgressiveList",
        value=SampleBytes32ProgressiveList(data=[]),
        expected_root="0xf5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b",
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
        case_id="progressive_list/composites/single_element",
        type_name="SampleBytes32ProgressiveList",
        value=SampleBytes32ProgressiveList(data=[Bytes32(b"\xaa" * 32)]),
        expected_root="0xbb93b54e640d8bb22570653bf0423df16e94fb3a1652e9ee7b218e5fa8eaaf5c",
    )


@pytest.mark.tags("multi-level")
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
        case_id="progressive_list/composites/crosses_level",
        type_name="SampleBytes32ProgressiveList",
        value=SampleBytes32ProgressiveList(
            data=[Bytes32(bytes([value]) * 32) for value in range(1, 7)]
        ),
        expected_root="0x690beb7f075e2dc91699aa3ee9354687772923889ce755458cb405ae95e34055",
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
        case_id="progressive_list/variable_size_elements",
        type_name="SampleNestedProgressiveList",
        value=SampleNestedProgressiveList(
            data=[
                SampleUint16ProgressiveList(data=[Uint16(1), Uint16(2)]),
                SampleUint16ProgressiveList(data=[]),
                SampleUint16ProgressiveList(data=[Uint16(3), Uint16(4), Uint16(5)]),
            ]
        ),
        expected_root="0xd0df6fea8320f394b0d6673861125069302ab339bbd80979dc41d998581d3a83",
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
        case_id="progressive_bitlist/three_bits",
        type_name="ProgressiveBitList",
        value=ProgressiveBitList(data=[Boolean(True), Boolean(False), Boolean(True)]),
        expected_root="0x45192380e83a4b9ee939ac3836a6dccc51d3451db8886d53668264ea2e2cb877",
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
        case_id="progressive_bitlist/fills_one_chunk",
        type_name="ProgressiveBitList",
        value=ProgressiveBitList(data=[Boolean(True)] * 256),
        expected_root="0xb3327406854ffab96af59832dfa3f690f72c4f898e2ffd4ef3e90cc2fb876b43",
    )


@pytest.mark.tags("multi-level")
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
        case_id="progressive_bitlist/opens_second_level",
        type_name="ProgressiveBitList",
        value=ProgressiveBitList(data=[Boolean(True)] * PROGRESSIVE_BITLIST_LEVEL_BITS),
        expected_root="0xbe707c375a49431fdb06c00f7a4dcc9200d5613ea02999dc5e081913171bb8d0",
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
        case_id="progressive_list/in_container/populated",
        type_name="SampleContainerWithProgressiveList",
        value=SampleContainerWithProgressiveList(
            a=Uint16(0xABCD),
            b=SampleUint64ProgressiveList(data=[Uint64(1), Uint64(2), Uint64(3)]),
            c=Uint8(0xFF),
        ),
        expected_root="0x74672f25a9fafa50effa21ab09753b79597c3c84c1d4604aee9d31b3452f7343",
    )


@pytest.mark.tags("empty")
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
        case_id="progressive_list/in_container/empty",
        type_name="SampleContainerWithProgressiveList",
        value=SampleContainerWithProgressiveList(
            a=Uint16(0xABCD),
            b=SampleUint64ProgressiveList(data=[]),
            c=Uint8(0xFF),
        ),
        expected_root="0xc889b4be0e0bca1fe0ffdd0235b1f6b4df7f356f1aa19a2743338a271843057e",
    )

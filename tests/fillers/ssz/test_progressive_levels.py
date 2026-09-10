"""SSZ conformance test vectors for the deeper levels of the EIP-7916 progressive spine."""

from itertools import accumulate
from typing import ClassVar

import pytest

from ssz import (
    BITS_PER_CHUNK,
    Boolean,
    ByteVector,
    ProgressiveBitList,
    ProgressiveContainer,
    ProgressiveList,
    Uint8,
    Uint16,
    Uint64,
    active_fields,
)
from ssz_testing import SSZTestFiller

pytestmark = pytest.mark.tags("multi-level", "boundary")

SPINE_LEVELS = 5
"""Spine levels these vectors reach, the fifth being 256 chunks wide."""

SPINE_CAPACITY = tuple(accumulate(4**level for level in range(SPINE_LEVELS)))
"""Chunks the spine holds once each level is full: 1, 5, 21, 85, 341."""

UINT64S_PER_CHUNK = BITS_PER_CHUNK // Uint64.BITS
"""Eight-byte elements packed into one 32-byte chunk."""

BEACON_STATE_WIDTH = 46
"""Positions in the post-EIP-8015 beacon state layout, the wide shape the helper documents."""

BEACON_STATE_GAPS = (8, 9, 10, 28)
"""Positions that layout leaves empty, holding every later field where it already sits."""


class Bytes32(ByteVector):
    """Composite element of one Merkle leaf, so a leaf count is an element count."""

    LENGTH: ClassVar[int] = 32


class SampleUint64ProgressiveList(ProgressiveList[Uint64]):
    """Progressive list of eight-byte elements, four to a chunk."""

    ELEMENT_TYPE = Uint64


class SampleBytes32ProgressiveList(ProgressiveList[Bytes32]):
    """Progressive list of composite 32-byte elements, one Merkle leaf each."""

    ELEMENT_TYPE = Bytes32


class SampleThirdLevelExact(ProgressiveContainer):
    """Twenty-one positions, the cumulative capacity of the spine's first three levels."""

    ACTIVE_FIELDS = active_fields(
        width=SPINE_CAPACITY[2], gaps=tuple(range(1, SPINE_CAPACITY[2] - 1))
    )

    first: Uint16
    last: Uint8


class SampleFourthLevelExact(ProgressiveContainer):
    """Eighty-five positions, the cumulative capacity of the spine's first four levels."""

    ACTIVE_FIELDS = active_fields(
        width=SPINE_CAPACITY[3], gaps=tuple(range(1, SPINE_CAPACITY[3] - 1))
    )

    first: Uint16
    last: Uint8


class SampleFifthLevelOpened(ProgressiveContainer):
    """One position past that, so the width-256 fifth level opens with a single occupant."""

    ACTIVE_FIELDS = active_fields(
        width=SPINE_CAPACITY[3] + 1, gaps=tuple(range(1, SPINE_CAPACITY[3]))
    )

    first: Uint16
    last: Uint8


class SampleBeaconStateShape(ProgressiveContainer):
    """The post-EIP-8015 beacon state layout: 46 positions with gaps at 8, 9, 10 and 28."""

    ACTIVE_FIELDS = active_fields(width=BEACON_STATE_WIDTH, gaps=BEACON_STATE_GAPS)

    p00: Uint64
    p01: Uint64
    p02: Uint64
    p03: Uint64
    p04: Uint64
    p05: Uint64
    p06: Uint64
    p07: Uint64
    p11: Uint64
    p12: Uint64
    p13: Uint64
    p14: Uint64
    p15: Uint64
    p16: Uint64
    p17: Uint64
    p18: Uint64
    p19: Uint64
    p20: Uint64
    p21: Uint64
    p22: Uint64
    p23: Uint64
    p24: Uint64
    p25: Uint64
    p26: Uint64
    p27: Uint64
    p29: Uint64
    p30: Uint64
    p31: Uint64
    p32: Uint64
    p33: Uint64
    p34: Uint64
    p35: Uint64
    p36: Uint64
    p37: Uint64
    p38: Uint64
    p39: Uint64
    p40: Uint64
    p41: Uint64
    p42: Uint64
    p43: Uint64
    p44: Uint64
    p45: Uint64


def spine_bits(count: int) -> list[Boolean]:
    """Two bits set for every one clear, so no level of packed chunks is uniform."""
    return [Boolean(index % 3 != 2) for index in range(count)]


def spine_elements(count: int) -> list[Bytes32]:
    """Composite elements that differ from one another, each filling one leaf."""
    return [Bytes32(bytes([index]) * 32) for index in range(1, count + 1)]


def test_progressive_bitlist_fills_second_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive bitlist filling the second spine level exactly round-trips unchanged.

    Given
    -----
    - a progressive bitlist of 1280 data bits.
    - five packed chunks, the cumulative capacity of levels one and two.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the root needs no padding in either occupied level, and every level past them is the
      terminator.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="spine/progressive_bitlist/fills_second_level",
        type_name="ProgressiveBitList",
        value=ProgressiveBitList(data=spine_bits(SPINE_CAPACITY[1] * BITS_PER_CHUNK)),
    )


def test_progressive_bitlist_opens_third_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive bitlist one bit past the second spine level round-trips unchanged.

    Given
    -----
    - a progressive bitlist of 1281 data bits.
    - six packed chunks, one past the cumulative capacity of levels one and two.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the sixteen-wide third level opens and pads its lone chunk out to that width.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="spine/progressive_bitlist/opens_third_level",
        type_name="ProgressiveBitList",
        value=ProgressiveBitList(data=spine_bits(SPINE_CAPACITY[1] * BITS_PER_CHUNK + 1)),
    )


def test_progressive_bitlist_fills_third_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive bitlist filling the third spine level exactly round-trips unchanged.

    Given
    -----
    - a progressive bitlist of 5376 data bits.
    - twenty-one packed chunks, the cumulative capacity of levels one to three.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the root needs no padding in any occupied level.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="spine/progressive_bitlist/fills_third_level",
        type_name="ProgressiveBitList",
        value=ProgressiveBitList(data=spine_bits(SPINE_CAPACITY[2] * BITS_PER_CHUNK)),
    )


def test_progressive_bitlist_opens_fourth_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive bitlist one bit past the third spine level round-trips unchanged.

    Given
    -----
    - a progressive bitlist of 5377 data bits.
    - twenty-two packed chunks, one past the cumulative capacity of levels one to three.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the sixty-four-wide fourth level opens and pads its lone chunk out to that width.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="spine/progressive_bitlist/opens_fourth_level",
        type_name="ProgressiveBitList",
        value=ProgressiveBitList(data=spine_bits(SPINE_CAPACITY[2] * BITS_PER_CHUNK + 1)),
    )


def test_progressive_list_of_composites_fills_second_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive list of five composite elements round-trips unchanged.

    Given
    -----
    - a progressive list of five 32-byte elements.
    - one leaf per element, so five leaves fill levels one and two exactly.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the four-wide second level is full, and no level past it opens.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="spine/progressive_list/composites/fills_second_level",
        type_name="SampleBytes32ProgressiveList",
        value=SampleBytes32ProgressiveList(data=spine_elements(SPINE_CAPACITY[1])),
    )


def test_progressive_list_of_composites_fills_third_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive list of twenty-one composite elements round-trips unchanged.

    Given
    -----
    - a progressive list of twenty-one 32-byte elements.
    - one leaf per element, so twenty-one leaves fill levels one to three exactly.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the sixteen-wide third level is full, and no level past it opens.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="spine/progressive_list/composites/fills_third_level",
        type_name="SampleBytes32ProgressiveList",
        value=SampleBytes32ProgressiveList(data=spine_elements(SPINE_CAPACITY[2])),
    )


def test_progressive_list_of_composites_opens_fourth_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive list of twenty-two composite elements round-trips unchanged.

    Given
    -----
    - a progressive list of twenty-two 32-byte elements.
    - one leaf past the cumulative capacity of levels one to three.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the sixty-four-wide fourth level opens and pads its lone leaf out to that width.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="spine/progressive_list/composites/opens_fourth_level",
        type_name="SampleBytes32ProgressiveList",
        value=SampleBytes32ProgressiveList(data=spine_elements(SPINE_CAPACITY[2] + 1)),
    )


def test_progressive_list_fills_fourth_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive list filling the fourth spine level exactly round-trips unchanged.

    Given
    -----
    - a progressive list of 340 eight-byte elements.
    - eighty-five packed chunks, the cumulative capacity of levels one to four.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the sixty-four-wide fourth level is full, and no level past it opens.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="spine/progressive_list/fills_fourth_level",
        type_name="SampleUint64ProgressiveList",
        value=SampleUint64ProgressiveList(
            data=[Uint64(value) for value in range(SPINE_CAPACITY[3] * UINT64S_PER_CHUNK)]
        ),
    )


def test_progressive_list_opens_fifth_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive list one element past the fourth spine level round-trips unchanged.

    Given
    -----
    - a progressive list of 341 eight-byte elements.
    - eighty-six packed chunks, one past the cumulative capacity of levels one to four.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the 256-wide fifth level opens and pads its lone chunk out to that width.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="spine/progressive_list/opens_fifth_level",
        type_name="SampleUint64ProgressiveList",
        value=SampleUint64ProgressiveList(
            data=[Uint64(value) for value in range(SPINE_CAPACITY[3] * UINT64S_PER_CHUNK + 1)]
        ),
    )


def test_progressive_container_fills_third_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive container whose positions fill the third spine level round-trips unchanged.

    Given
    -----
    - a layout of twenty-one positions, the first and the last occupied.
    - one leaf per position, gap or not, so twenty-one leaves fill levels one to three exactly.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is the two fields back to back, the nineteen gaps costing nothing.
    - the sixteen-wide third level is full, and no level past it opens.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="spine/progressive_container/fills_third_level",
        type_name="SampleThirdLevelExact",
        value=SampleThirdLevelExact(first=Uint16(0x1234), last=Uint8(0x56)),
    )


def test_progressive_container_fills_fourth_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive container whose positions fill the fourth spine level round-trips unchanged.

    Given
    -----
    - a layout of eighty-five positions, the first and the last occupied.
    - eighty-five leaves, the cumulative capacity of levels one to four.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the sixty-four-wide fourth level is full, and no level past it opens.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="spine/progressive_container/fills_fourth_level",
        type_name="SampleFourthLevelExact",
        value=SampleFourthLevelExact(first=Uint16(0x1234), last=Uint8(0x56)),
    )


def test_progressive_container_opens_fifth_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive container one position past the fourth spine level round-trips unchanged.

    Given
    -----
    - a layout of eighty-six positions, the first and the last occupied.
    - one leaf past the cumulative capacity of levels one to four.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the 256-wide fifth level opens, holding the last field beside 255 zero leaves.
    - the encoding matches the eighty-five-position shape byte for byte, the roots differing
      only in the layout mixed in and the leaf the wider spine adds.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="spine/progressive_container/opens_fifth_level",
        type_name="SampleFifthLevelOpened",
        value=SampleFifthLevelOpened(first=Uint16(0x1234), last=Uint8(0x56)),
    )


def test_progressive_container_beacon_state_layout(ssz_test: SSZTestFiller) -> None:
    """
    A progressive container in the post-EIP-8015 beacon state layout round-trips unchanged.

    Given
    -----
    - a layout of forty-six positions with gaps at 8, 9, 10 and 28, built by the public helper.
    - forty-two eight-byte fields, each holding the position it sits at.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is the forty-two fields back to back, the four gaps costing nothing.
    - the forty-six leaves reach into the sixty-four-wide fourth level without filling it.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="spine/progressive_container/beacon_state_layout",
        type_name="SampleBeaconStateShape",
        value=SampleBeaconStateShape(
            p00=Uint64(0),
            p01=Uint64(1),
            p02=Uint64(2),
            p03=Uint64(3),
            p04=Uint64(4),
            p05=Uint64(5),
            p06=Uint64(6),
            p07=Uint64(7),
            p11=Uint64(11),
            p12=Uint64(12),
            p13=Uint64(13),
            p14=Uint64(14),
            p15=Uint64(15),
            p16=Uint64(16),
            p17=Uint64(17),
            p18=Uint64(18),
            p19=Uint64(19),
            p20=Uint64(20),
            p21=Uint64(21),
            p22=Uint64(22),
            p23=Uint64(23),
            p24=Uint64(24),
            p25=Uint64(25),
            p26=Uint64(26),
            p27=Uint64(27),
            p29=Uint64(29),
            p30=Uint64(30),
            p31=Uint64(31),
            p32=Uint64(32),
            p33=Uint64(33),
            p34=Uint64(34),
            p35=Uint64(35),
            p36=Uint64(36),
            p37=Uint64(37),
            p38=Uint64(38),
            p39=Uint64(39),
            p40=Uint64(40),
            p41=Uint64(41),
            p42=Uint64(42),
            p43=Uint64(43),
            p44=Uint64(44),
            p45=Uint64(45),
        ),
    )

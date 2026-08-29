"""SSZ conformance test vectors for the EIP-7495 progressive container."""

from ssz import (
    Boolean,
    Container,
    List,
    ProgressiveBitList,
    ProgressiveContainer,
    ProgressiveList,
    Uint8,
    Uint16,
    Uint32,
    Uint64,
)
from ssz_testing import ExpectedRejection, RejectionReason, SSZTestFiller


class SampleUint16List4(List[Uint16]):
    """Bounded list of two-byte elements, used as a variable-size field."""

    LIMIT = 4
    ELEMENT_TYPE = Uint16


class SampleUint64ProgressiveList(ProgressiveList[Uint64]):
    """Progressive list of eight-byte elements, used as a variable-size field."""

    ELEMENT_TYPE = Uint64


class SampleSquare(ProgressiveContainer):
    """
    EIP-7495's own example: a field at position 0, a gap, then a field at position 2.

    The cleared bit leaves a zero leaf where no field sits, which is what keeps the
    field at position 2 in place across versions of the shape.
    """

    ACTIVE_FIELDS = (1, 0, 1)

    side: Uint16
    color: Uint8


class SampleCircle(ProgressiveContainer):
    """
    The other half of that example: a leading gap, then fields at positions 1 and 2.

    It shares position 2 with SampleSquare and encodes to the very same bytes, so the
    two are told apart only by the layout mixed into the root.
    """

    ACTIVE_FIELDS = (0, 1, 1)

    radius: Uint16
    color: Uint8


class SampleOneField(ProgressiveContainer):
    """Narrowest legal layout: one position, occupied."""

    ACTIVE_FIELDS = (1,)

    a: Uint16


class SampleLeadingGaps(ProgressiveContainer):
    """Two leading gaps, so the sole field is merkleized at position two."""

    ACTIVE_FIELDS = (0, 0, 1)

    c: Uint32


class SampleMultipleGaps(ProgressiveContainer):
    """Three fields separated by gaps of differing widths."""

    ACTIVE_FIELDS = (1, 0, 0, 1, 0, 1)

    a: Uint8
    b: Uint16
    c: Uint32


class SampleWidestLayout(ProgressiveContainer):
    """
    Widest legal layout: 256 positions, the capacity of the mixed-in word.

    Only the last position is occupied, so 255 zero leaves precede the single field.
    """

    ACTIVE_FIELDS = (*([0] * 255), 1)

    tail: Uint8


class SampleLevelBoundary(ProgressiveContainer):
    """
    Twenty-two positions, so the leaves open the width-64 level of the spine.

    Every position is a leaf, gap or not, which is what puts the leaf count one past
    the cumulative capacity of the first three levels.
    """

    ACTIVE_FIELDS = (1, *([0] * 20), 1)

    first: Uint16
    last: Uint8


class SampleBoundedListField(ProgressiveContainer):
    """Fixed field, a gap, then a bounded list, so the shape needs one offset."""

    ACTIVE_FIELDS = (1, 0, 1)

    head: Uint64
    body: SampleUint16List4


class SampleProgressiveFields(ProgressiveContainer):
    """Fixed field followed by both EIP-7916 shapes, so two offsets follow it."""

    ACTIVE_FIELDS = (1, 1, 1)

    head: Uint64
    numbers: SampleUint64ProgressiveList
    flags: ProgressiveBitList


class SampleInnerShape(ProgressiveContainer):
    """Fixed-size progressive container nested inside another one."""

    ACTIVE_FIELDS = (1, 0, 1)

    x: Uint16
    y: Uint8


class SampleOuterShape(ProgressiveContainer):
    """Progressive container holding a progressive container as a field."""

    ACTIVE_FIELDS = (1, 0, 1)

    head: Uint8
    inner: SampleInnerShape


class SampleSquareProgressiveList(ProgressiveList[SampleSquare]):
    """Progressive list whose elements are progressive containers."""

    ELEMENT_TYPE = SampleSquare


class SampleShapeContainer(Container):
    """Ordinary container holding a progressive container as its second field."""

    tag: Uint8
    shape: SampleSquare


def test_progressive_container_square(ssz_test: SSZTestFiller) -> None:
    """
    A progressive container with an interior gap round-trips unchanged.

    Given
    -----
    - a layout of three positions with the middle one cleared.
    - a two-byte field at position 0 and a one-byte field at position 2.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is three bytes, the gap costing nothing.
    - the root places the field roots at positions 0 and 2 and mixes the layout in.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleSquare",
        value=SampleSquare(side=Uint16(0x1234), color=Uint8(0x56)),
    )


def test_progressive_container_circle(ssz_test: SSZTestFiller) -> None:
    """
    A progressive container with a leading gap round-trips unchanged.

    Given
    -----
    - a layout of three positions with the first one cleared.
    - the same field widths as the interior-gap shape, in positions 1 and 2.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding matches the interior-gap shape byte for byte.
    - the root differs from it, because the mixed-in layout differs.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleCircle",
        value=SampleCircle(radius=Uint16(0x1234), color=Uint8(0x56)),
    )


def test_progressive_container_single_field(ssz_test: SSZTestFiller) -> None:
    """
    A progressive container occupying its only position round-trips unchanged.

    Given
    -----
    - a layout of one position, occupied.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the single leaf fills the width-one level and meets the terminator.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleOneField",
        value=SampleOneField(a=Uint16(0xBEEF)),
    )


def test_progressive_container_leading_gaps(ssz_test: SSZTestFiller) -> None:
    """
    A progressive container behind two leading gaps round-trips unchanged.

    Given
    -----
    - a layout whose first two positions are cleared.
    - a four-byte field at position 2.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is the field alone, since gaps take no bytes.
    - the first two leaves of the tree are zero chunks.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleLeadingGaps",
        value=SampleLeadingGaps(c=Uint32(0x11223344)),
    )


def test_progressive_container_multiple_gaps(ssz_test: SSZTestFiller) -> None:
    """
    A progressive container with gaps of differing widths round-trips unchanged.

    Given
    -----
    - a layout of six positions, three of them occupied.
    - fields of one, two and four bytes at positions 0, 3 and 5.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is the three fields back to back.
    - the tree holds six leaves, three of which are zero chunks.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleMultipleGaps",
        value=SampleMultipleGaps(a=Uint8(1), b=Uint16(0x0203), c=Uint32(0x04050607)),
    )


def test_progressive_container_widest_layout(ssz_test: SSZTestFiller) -> None:
    """
    A progressive container with the widest legal layout round-trips unchanged.

    Given
    -----
    - a layout of 256 positions, the capacity of the mixed-in word.
    - a single one-byte field at the last position.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is one byte.
    - the mixed-in word has only its highest bit set.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleWidestLayout",
        value=SampleWidestLayout(tail=Uint8(0xAB)),
    )


def test_progressive_container_opens_the_fourth_level(ssz_test: SSZTestFiller) -> None:
    """
    A progressive container whose leaves cross a spine level round-trips unchanged.

    Given
    -----
    - a layout of twenty-two positions, two of them occupied.
    - twenty-two leaves, one past the cumulative capacity of the first three levels.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the width-64 level opens with a single occupant.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleLevelBoundary",
        value=SampleLevelBoundary(first=Uint16(0x1234), last=Uint8(0x56)),
    )


def test_progressive_container_with_bounded_list_field(ssz_test: SSZTestFiller) -> None:
    """
    A progressive container holding a bounded list round-trips unchanged.

    Given
    -----
    - a fixed-size field, a gap, and a bounded list of two-byte elements.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - one offset follows the fixed part, pointing at the list body.
    - the list contributes its own length-mixed root as the leaf at position 2.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleBoundedListField",
        value=SampleBoundedListField(
            head=Uint64(7),
            body=SampleUint16List4(data=[Uint16(1), Uint16(2)]),
        ),
    )


def test_progressive_container_with_empty_variable_field(ssz_test: SSZTestFiller) -> None:
    """
    A progressive container whose list field is empty round-trips unchanged.

    Given
    -----
    - the same shape as above with no list elements at all.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the offset points past the end of the fixed part, with no body following it.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleBoundedListField",
        value=SampleBoundedListField(head=Uint64(7), body=SampleUint16List4(data=[])),
    )


def test_progressive_container_with_progressive_fields(ssz_test: SSZTestFiller) -> None:
    """
    A progressive container holding both EIP-7916 shapes round-trips unchanged.

    Given
    -----
    - a fixed-size field followed by a progressive list and a progressive bitlist.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - two offsets follow the fixed part, in field order.
    - each field contributes its own length-mixed root as one leaf.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleProgressiveFields",
        value=SampleProgressiveFields(
            head=Uint64(7),
            numbers=SampleUint64ProgressiveList(data=[Uint64(1), Uint64(2), Uint64(3)]),
            flags=ProgressiveBitList(data=[Boolean(True), Boolean(False), Boolean(True)]),
        ),
    )


def test_nested_progressive_containers(ssz_test: SSZTestFiller) -> None:
    """
    A progressive container holding another one round-trips unchanged.

    Given
    -----
    - an outer layout with a gap, whose second field is a fixed-size progressive container.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the inner shape inlines, since it is fixed-size.
    - the inner shape's own layout-mixed root is the outer leaf at position 2.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleOuterShape",
        value=SampleOuterShape(
            head=Uint8(1),
            inner=SampleInnerShape(x=Uint16(0x0203), y=Uint8(4)),
        ),
    )


def test_progressive_list_of_progressive_containers(ssz_test: SSZTestFiller) -> None:
    """
    A progressive list of progressive containers round-trips unchanged.

    Given
    -----
    - a progressive list whose elements are three-byte progressive containers.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the fixed-size element bodies sit back to back with no offset table.
    - each element root is one leaf of the list's spine.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleSquareProgressiveList",
        value=SampleSquareProgressiveList(
            data=[
                SampleSquare(side=Uint16(1), color=Uint8(2)),
                SampleSquare(side=Uint16(3), color=Uint8(4)),
            ]
        ),
    )


def test_container_holding_a_progressive_container(ssz_test: SSZTestFiller) -> None:
    """
    An ordinary container holding a progressive container round-trips unchanged.

    Given
    -----
    - a container with a one-byte tag and a fixed-size progressive container field.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the progressive field inlines, so the container stays fixed-size.
    - the container merkleizes the field's layout-mixed root as an ordinary leaf.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleShapeContainer",
        value=SampleShapeContainer(
            tag=Uint8(0xFF),
            shape=SampleSquare(side=Uint16(0x1234), color=Uint8(0x56)),
        ),
    )


def test_progressive_container_decode_failure_trailing_byte(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a fixed-size progressive container with a spare byte is rejected.

    Given
    -----
    - a three-byte fixed-size shape.
    - the input bytes 0x34125600, one byte longer than the canonical encoding.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that a shape of fixed-size fields spans exactly its own width.
    """
    ssz_test(
        type_name="SampleSquare",
        value=SampleSquare(side=Uint16(0x1234), color=Uint8(0x56)),
        raw_bytes="0x34125600",
        expected_rejection=ExpectedRejection(
            reason=RejectionReason.DECODE_ERROR,
            exact_message="SampleSquare spans 3 bytes, and the budget is 4",
        ),
    )


def test_progressive_container_decode_failure_first_offset(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a progressive container whose first offset skips a byte is rejected.

    Given
    -----
    - a shape whose fixed part is twelve bytes: an eight-byte field and one offset.
    - an offset of thirteen, which leaves a byte belonging to no field.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the first offset must end the fixed part exactly.
    """
    ssz_test(
        type_name="SampleBoundedListField",
        value=SampleBoundedListField(head=Uint64(7), body=SampleUint16List4(data=[])),
        raw_bytes="0x07000000000000000d000000",
        expected_rejection=ExpectedRejection(
            reason=RejectionReason.DECODE_ERROR,
            exact_message="the first offset is 13, and the fixed part ends at 12",
        ),
    )

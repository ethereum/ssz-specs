"""SSZ conformance test vectors for a progressive container handed another layout's payload."""

from typing import ClassVar

from ssz import (
    Boolean,
    List,
    ProgressiveContainer,
    SSZType,
    Uint8,
    Uint16,
    Uint64,
    hash_tree_root,
)
from ssz_testing import ExpectedRejection, SSZTestFiller, ValueFault


def payload_from(value: SSZType, expected: str) -> str:
    """
    The bytes one layout writes, checked against the literal a vector hands to another type.

    Raises:
        AssertionError: When the source layout no longer writes the authored bytes.
    """
    encoded = f"0x{value.encode_bytes().hex()}"
    if encoded != expected:
        raise AssertionError(
            f"{type(value).__name__} now encodes to {encoded}, and the vector says {expected}"
        )
    return expected


def assert_collision(first: SSZType, second: SSZType) -> None:
    """
    Check that two layouts encode alike and root apart, which is all that keeps them distinct.

    Raises:
        AssertionError: When the encodings differ, or when the roots agree.
    """
    if first.encode_bytes() != second.encode_bytes():
        raise AssertionError(
            f"{type(first).__name__} and {type(second).__name__} no longer encode alike: "
            f"0x{first.encode_bytes().hex()} against 0x{second.encode_bytes().hex()}"
        )
    if hash_tree_root(first) == hash_tree_root(second):
        raise AssertionError(
            f"{type(first).__name__} and {type(second).__name__} merkleize alike, "
            f"so nothing tells the two layouts apart"
        )


class LayoutUint16List4(List[Uint16]):
    """Bounded list of two-byte elements, used as a variable-size field."""

    LIMIT: ClassVar[int] = 4
    ELEMENT_TYPE = Uint16


class LayoutShapeV1(ProgressiveContainer):
    """Two fields on a gapless layout, the shape one fork ships."""

    ACTIVE_FIELDS = (1, 1)

    slot: Uint64
    slashed: Boolean


class LayoutShapeV2(ProgressiveContainer):
    """The next fork's shape, which appends a field on a trailing set bit."""

    ACTIVE_FIELDS = (1, 1, 1)

    slot: Uint64
    slashed: Boolean
    index: Uint64


class LayoutShapeV3(ProgressiveContainer):
    """A later fork's shape, which drops the middle field by clearing its bit."""

    ACTIVE_FIELDS = (1, 0, 1)

    slot: Uint64
    index: Uint64


class LayoutHeadFirst(ProgressiveContainer):
    """A fixed-size field ahead of a bounded list, so the list's offset follows it."""

    ACTIVE_FIELDS = (1, 1)

    head: Uint64
    tail: LayoutUint16List4


class LayoutHeadLast(ProgressiveContainer):
    """The same two fields with the fixed-size one moved past the list, so the offset leads."""

    ACTIVE_FIELDS = (0, 1, 1)

    tail: LayoutUint16List4
    head: Uint64


class LayoutGapAtOne(ProgressiveContainer):
    """Four positions with the second vacant, holding an eight-byte field at position two."""

    ACTIVE_FIELDS = (1, 0, 1, 1)

    slot: Uint64
    index: Uint64
    tail: Uint8


class LayoutGapAtTwo(ProgressiveContainer):
    """The same width with the third position vacant, holding a one-byte field at position one."""

    ACTIVE_FIELDS = (1, 1, 0, 1)

    slot: Uint64
    slashed: Boolean
    tail: Uint8


class LayoutTwoTails(ProgressiveContainer):
    """A fixed-size field and two bounded lists, so two offsets follow the fixed part."""

    ACTIVE_FIELDS = (1, 0, 1, 1)

    head: Uint64
    first: LayoutUint16List4
    second: LayoutUint16List4


class LayoutNarrowCollision(ProgressiveContainer):
    """Three positions with the second vacant, over a one-byte field and a bounded list."""

    ACTIVE_FIELDS = (1, 0, 1)

    tag: Uint8
    values: LayoutUint16List4


class LayoutWideCollision(ProgressiveContainer):
    """Four positions with the first and third vacant, over those same two field types."""

    ACTIVE_FIELDS = (0, 1, 0, 1)

    tag: Uint8
    values: LayoutUint16List4


NARROW_COLLIDING_VALUE = LayoutNarrowCollision(
    tag=Uint8(7), values=LayoutUint16List4(data=[Uint16(1), Uint16(2)])
)
"""The three-position half of the colliding pair, filled so the list contributes a body."""

WIDE_COLLIDING_VALUE = LayoutWideCollision(
    tag=Uint8(7), values=LayoutUint16List4(data=[Uint16(1), Uint16(2)])
)
"""The four-position half, carrying the very same field values."""


def test_field_added_at_an_interior_position(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a shape that inserted a field mid-layout from the payload without it is rejected.

    Given
    -----
    - a shape of three set positions, whose middle field is a one-byte boolean.
    - the payload of the shape that lacks that field, sixteen bytes of two eight-byte fields.

    When
    ----
    - the input is decoded into the shape that has the extra field.

    Then
    ----
    - decoding is rejected.
    - the reason is that the inserted field widens the shape to seventeen bytes, one past
      the sixteen the payload carries.
    - EIP-7495 gives a progressive container the serialization of an ordinary container, so
      nothing on the wire announces which layout wrote these bytes.
    """
    ssz_test(
        case_id="layout/invalid/field_added_at_an_interior_position",
        type_name="LayoutShapeV2",
        value=LayoutShapeV2(slot=Uint64(1), slashed=Boolean(True), index=Uint64(2)),
        raw_bytes=payload_from(
            LayoutShapeV3(slot=Uint64(1), index=Uint64(1)),
            "0x01000000000000000100000000000000",
        ),
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            exact_message="LayoutShapeV2 spans 17 bytes, and the budget is 16",
        ),
    )


def test_field_dropped_from_the_middle(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a shape that cleared a middle bit from the payload that still carries it is rejected.

    Given
    -----
    - a shape whose middle position was vacated, spanning sixteen bytes.
    - the payload of the shape that still holds a one-byte field there, seventeen bytes.

    When
    ----
    - the input is decoded into the shape with the vacated position.

    Then
    ----
    - decoding is rejected.
    - the reason is that the spare byte belongs to no field of this shape.
    """
    ssz_test(
        case_id="layout/invalid/field_dropped_from_the_middle",
        type_name="LayoutShapeV3",
        value=LayoutShapeV3(slot=Uint64(1), index=Uint64(2)),
        raw_bytes=payload_from(
            LayoutShapeV2(slot=Uint64(1), slashed=Boolean(True), index=Uint64(2)),
            "0x0100000000000000010200000000000000",
        ),
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            exact_message="LayoutShapeV3 spans 16 bytes, and the budget is 17",
        ),
    )


def test_field_moved_past_a_later_one(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a shape whose fixed field moved behind its list from the earlier payload is rejected.

    Given
    -----
    - a shape declaring a bounded list first and an eight-byte field after it.
    - the payload of the shape that ordered those two the other way round.

    When
    ----
    - the input is decoded into the shape with the moved field.

    Then
    ----
    - decoding is rejected.
    - the reason is that the leading four bytes read as an offset that does not end the fixed part.
    - moving a field past another is the one layout edit the wire can catch, since it is the only
      one that changes the order the fields are written in.
    """
    ssz_test(
        case_id="layout/invalid/field_moved_past_a_later_one",
        type_name="LayoutHeadLast",
        value=LayoutHeadLast(tail=LayoutUint16List4(data=[]), head=Uint64(7)),
        raw_bytes=payload_from(
            LayoutHeadFirst(head=Uint64(7), tail=LayoutUint16List4(data=[Uint16(1), Uint16(2)])),
            "0x07000000000000000c00000001000200",
        ),
        expected_rejection=ExpectedRejection(
            reason=ValueFault.FIRST_OFFSET,
            exact_message="the first offset is 7, and the fixed part ends at 12",
        ),
    )


def test_wider_shape_into_a_narrower_type(ssz_test: SSZTestFiller) -> None:
    """
    Decoding the older shape from a payload written after a field was appended is rejected.

    Given
    -----
    - the shape one fork ships, spanning nine bytes.
    - the payload of the next fork's shape, which appended an eight-byte field.

    When
    ----
    - the input is decoded into the older shape.

    Then
    ----
    - decoding is rejected.
    - the reason is that eight bytes belong to no field the older shape declares.
    """
    ssz_test(
        case_id="layout/invalid/wider_shape_into_a_narrower_type",
        type_name="LayoutShapeV1",
        value=LayoutShapeV1(slot=Uint64(1), slashed=Boolean(True)),
        raw_bytes=payload_from(
            LayoutShapeV2(slot=Uint64(1), slashed=Boolean(True), index=Uint64(2)),
            "0x0100000000000000010200000000000000",
        ),
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            exact_message="LayoutShapeV1 spans 9 bytes, and the budget is 17",
        ),
    )


def test_narrower_shape_into_a_wider_type(ssz_test: SSZTestFiller) -> None:
    """
    Decoding the shape with an appended field from the older payload is rejected.

    Given
    -----
    - the next fork's shape, spanning seventeen bytes.
    - the payload of the shape it grew from, nine bytes.

    When
    ----
    - the input is decoded into the newer shape.

    Then
    ----
    - decoding is rejected.
    - the reason is that the shape spans seventeen bytes and the older payload carries nine.
    """
    ssz_test(
        case_id="layout/invalid/narrower_shape_into_a_wider_type",
        type_name="LayoutShapeV2",
        value=LayoutShapeV2(slot=Uint64(1), slashed=Boolean(True), index=Uint64(2)),
        raw_bytes=payload_from(
            LayoutShapeV1(slot=Uint64(1), slashed=Boolean(True)),
            "0x010000000000000001",
        ),
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            exact_message="LayoutShapeV2 spans 17 bytes, and the budget is 9",
        ),
    )


def test_same_width_other_gap_positions(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a four-position shape from the payload of another four-position shape is rejected.

    Given
    -----
    - a layout of four positions whose third is vacant, spanning ten bytes.
    - the payload of a layout of the same four positions whose second is vacant, seventeen bytes.

    When
    ----
    - the input is decoded into the first of those two.

    Then
    ----
    - decoding is rejected.
    - the reason is that the two shapes span different widths, the fields either side of the
      moved gap being of different types.
    - a gap that moves without disturbing the field types is refused by nothing at all, since
      the encodings then match byte for byte.
    """
    ssz_test(
        case_id="layout/invalid/same_width_other_gap_positions",
        type_name="LayoutGapAtTwo",
        value=LayoutGapAtTwo(slot=Uint64(1), slashed=Boolean(True), tail=Uint8(9)),
        raw_bytes=payload_from(
            LayoutGapAtOne(slot=Uint64(1), index=Uint64(1), tail=Uint8(9)),
            "0x0100000000000000010000000000000009",
        ),
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            exact_message="LayoutGapAtTwo spans 10 bytes, and the budget is 17",
        ),
    )


def test_progressive_container_offsets_out_of_order(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a progressive container whose two offsets descend is rejected.

    Given
    -----
    - a shape whose fixed part is sixteen bytes: an eight-byte field and two offsets.
    - a first offset of sixteen, which ends that fixed part exactly.
    - a second offset of twelve, which sits below the offset before it.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected before any body is read.
    - the reason is that an offset is above the one after it, at the first list.
    """
    ssz_test(
        case_id="layout/invalid/offsets_out_of_order",
        type_name="LayoutTwoTails",
        value=LayoutTwoTails(
            head=Uint64(7),
            first=LayoutUint16List4(data=[]),
            second=LayoutUint16List4(data=[]),
        ),
        raw_bytes="0x0700000000000000100000000c0000000100",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.OFFSET_UNORDERED,
            exact_message="first: offset 16 is above the offset after it, 12",
        ),
    )


def test_progressive_container_offset_past_budget(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a progressive container whose last offset overruns the input is rejected.

    Given
    -----
    - the same sixteen-byte fixed part of an eight-byte field and two offsets.
    - a second offset of twenty, in an input of eighteen bytes.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected before any body is read.
    - the reason is that an offset runs past the budget, at the second list.
    """
    ssz_test(
        case_id="layout/invalid/offset_past_budget",
        type_name="LayoutTwoTails",
        value=LayoutTwoTails(
            head=Uint64(7),
            first=LayoutUint16List4(data=[]),
            second=LayoutUint16List4(data=[]),
        ),
        raw_bytes="0x070000000000000010000000140000000100",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.OFFSET_PAST_SCOPE,
            exact_message="second: offset 20 runs past the budget of 18",
        ),
    )


def test_collision_three_position_layout(ssz_test: SSZTestFiller) -> None:
    """
    Three positions over a one-byte field and a bounded list, against four positions holding both.

    Given
    -----
    - a layout of three positions whose second is vacant.
    - a one-byte field of 7 and a list of the two-byte elements 1 and 2.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is the nine bytes 0x070500000001000200.
    - the four-position shape beside this one encodes to those very same nine bytes, and each
      decodes the other's payload without complaint.
    - only the root separates the two, the layout being all that is mixed in.
    """
    assert_collision(NARROW_COLLIDING_VALUE, WIDE_COLLIDING_VALUE)
    ssz_test(
        case_id="layout/collision/three_position_layout",
        type_name="LayoutNarrowCollision",
        value=NARROW_COLLIDING_VALUE,
    )


def test_collision_four_position_layout(ssz_test: SSZTestFiller) -> None:
    """
    Four positions over those same two field types, against the three-position shape.

    Given
    -----
    - a layout of four positions whose first and third are vacant.
    - the same one-byte field of 7 and the same list of 1 and 2.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is the same nine bytes 0x070500000001000200 the narrower shape writes.
    - the root differs from the narrower shape's, which is the whole of EIP-7495's guarantee:
      a verifier told these apart by nothing but the mixed-in layout.
    """
    assert_collision(NARROW_COLLIDING_VALUE, WIDE_COLLIDING_VALUE)
    ssz_test(
        case_id="layout/collision/four_position_layout",
        type_name="LayoutWideCollision",
        value=WIDE_COLLIDING_VALUE,
    )

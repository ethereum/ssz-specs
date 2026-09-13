"""SSZ conformance test vectors telling a field that is absent from one that is zero."""

from typing import ClassVar

import pytest

from ssz import (
    SELECTOR_KEY,
    CompatibleUnion,
    Container,
    List,
    ProgressiveContainer,
    ProgressiveList,
    SSZType,
    Uint8,
    Uint16,
    Uint64,
    ValueFault,
    get_generalized_index,
    node_root,
)
from ssz_testing import ExpectedRejection, ProofTestFiller

pytestmark = pytest.mark.tags("proofs", "absence")


def last_node(value: SSZType, position: int) -> int:
    """The index of one position, required here to be a node of this value's own tree."""
    index = get_generalized_index(type(value), position)
    node_root(value, index)
    return index


class AbsenceSquare(ProgressiveContainer):
    """Union option standing its own field at layout position 0 and the shared one at 2."""

    ACTIVE_FIELDS = (1, 0, 1)

    side: Uint16
    color: Uint8


class AbsenceCircle(ProgressiveContainer):
    """The compatible option, standing its own field at layout position 1 instead."""

    ACTIVE_FIELDS = (0, 1, 1)

    radius: Uint16
    color: Uint8


class AbsenceShape(CompatibleUnion):
    """Union over the two layouts, every option rooted at the shared left child."""

    OPTIONS = {1: AbsenceSquare, 2: AbsenceCircle}


class AbsenceDetail(Container):
    """Two-field struct, standing wherever a leaf has to have an interior to descend into."""

    lo: Uint16
    hi: Uint16


class AbsenceDetailed(ProgressiveContainer):
    """Union option standing a composite at layout position 0 and the shared field at 2."""

    ACTIVE_FIELDS = (1, 0, 1)

    detail: AbsenceDetail
    color: Uint8


class AbsenceOutline(CompatibleUnion):
    """Union pairing the composite-bearing layout with the one that leaves its position vacant."""

    OPTIONS = {1: AbsenceDetailed, 2: AbsenceCircle}


class AbsenceDetailList8(List[AbsenceDetail]):
    """Eight composite elements at most, each taking a leaf of its own."""

    LIMIT: ClassVar[int] = 8
    ELEMENT_TYPE = AbsenceDetail


class AbsenceUint64ProgressiveList(ProgressiveList[Uint64]):
    """Progressive list of eight-byte elements, four to a chunk along the spine."""

    ELEMENT_TYPE = Uint64


CIRCLE = AbsenceShape(
    selector=Uint8(2),
    data=AbsenceCircle(radius=Uint16(0x1234), color=Uint8(0x42)),
)
"""A union holding its second option, whose layout leaves position 0 vacant."""

DETAILED = AbsenceOutline(
    selector=Uint8(1),
    data=AbsenceDetailed(
        detail=AbsenceDetail(lo=Uint16(0x1234), hi=Uint16(0x5678)), color=Uint8(0x42)
    ),
)
"""A union holding the option that declares a composite at position 0."""

VACANT = AbsenceOutline(
    selector=Uint8(2),
    data=AbsenceCircle(radius=Uint16(0x1234), color=Uint8(0x42)),
)
"""The same union holding the option that leaves that position vacant."""

TWO_DETAILS = AbsenceDetailList8(
    data=[AbsenceDetail(lo=Uint16(1), hi=Uint16(2)), AbsenceDetail(lo=Uint16(3), hi=Uint16(4))]
)
"""Two of the eight elements filled, the other six being the tree's zero padding."""

TWO = AbsenceUint64ProgressiveList(data=[Uint64(value) for value in range(2)])
"""Two elements, so the spine closes after its one-chunk first level."""

FIVE = AbsenceUint64ProgressiveList(data=[Uint64(value) for value in range(5)])
"""Five elements, so the spine closes after its four-chunk second level."""

TWENTY_ONE = AbsenceUint64ProgressiveList(data=[Uint64(value) for value in range(21)])
"""Twenty-one elements, so the spine closes after its sixteen-chunk third level."""


def test_a_field_of_another_option_reads_as_zero(proof_test: ProofTestFiller) -> None:
    """
    A field the option held declares nowhere is proved to be zero, and the branch verifies.

    Given
    -----
    - a union of two compatible layouts, holding the second.
    - the first option's own field, which that option stands at layout position 0.
    - the second option leaves position 0 vacant, so no value of it ever writes there.

    When
    ----
    - the path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 8, under the left child every option shares.
    - the leaf is 32 zero bytes, that position holding nothing under this option.
    - the branch rebuilds the value's root, so a verifier accepts the proof.
    - the zero is the absence of a field, not a field whose value is zero.
    - EIP-8016 fixes one index per field, putting a vacancy and a zero at the same place.
    - the selector tells the two apart, as absence/compatible_union/selector_mixin proves.
    """
    proof_test(
        case_id="absence/compatible_union/vacant_position_reads_zero",
        type_name="AbsenceShape",
        value=CIRCLE,
        path=(1, "side"),
        expected_index=8,
    )


def test_a_shared_field_carries_what_the_option_holds(proof_test: ProofTestFiller) -> None:
    """
    A field both options declare is proved at one index, and carries what the value holds.

    Given
    -----
    - a union of two compatible layouts, holding the second.
    - the field both options stand at layout position 2, named through the first option.

    When
    ----
    - the path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 73, the index the second option gives it too.
    - the leaf carries 0x42, which is the value the second option actually holds.
    - the branch rebuilds the value's root.
    - a shared position reads the held option's data where a vacant one reads zero.
    - the leaf alone does not say which of the two a verifier is looking at.
    """
    assert get_generalized_index(AbsenceShape, 2, "color") == 73
    proof_test(
        case_id="absence/compatible_union/shared_position_holds_the_value",
        type_name="AbsenceShape",
        value=CIRCLE,
        path=(1, "color"),
        expected_index=73,
    )


def test_the_selector_is_what_distinguishes_the_options(proof_test: ProofTestFiller) -> None:
    """
    The selector mixed into a union's root is a provable leaf, and is what names the option.

    Given
    -----
    - a union of two compatible layouts, holding the second.
    - the reserved step naming the mixed-in type selector.

    When
    ----
    - the path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 3, the right child of the root.
    - the leaf is the selector as a little-endian 32-byte word, so it reads 2.
    - the one-node branch is the root of the option's own tree, and rebuilds the value's root.
    - reading a zero leaf as a field whose value is zero takes this selector first.
    """
    proof_test(
        case_id="absence/compatible_union/selector_mixin",
        type_name="AbsenceShape",
        value=CIRCLE,
        path=(SELECTOR_KEY,),
        expected_index=3,
    )


def test_a_composite_the_option_declares_can_be_descended_into(proof_test: ProofTestFiller) -> None:
    """
    A field of a struct held at a union position is proved one level below that position.

    Given
    -----
    - a union of two compatible layouts, holding the first.
    - that option's own field at layout position 0, which is a two-field struct.
    - the first field of that struct.

    When
    ----
    - the path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 16, the left child of the position's own index 8.
    - the leaf carries 0x1234 little-endian, which is what the struct holds there.
    - the branch rebuilds the value's root.
    - index 16 is a node only because the position holds a value.
    """
    proof_test(
        case_id="absence/compatible_union/declared_composite_has_an_interior",
        type_name="AbsenceOutline",
        value=DETAILED,
        path=(1, "detail", "lo"),
        expected_index=16,
    )


def test_a_vacant_position_has_no_interior(proof_test: ProofTestFiller) -> None:
    """
    A vacant position is a zero leaf and not a zero subtree, so nothing below it is provable.

    Given
    -----
    - the same union, holding the second option, whose layout leaves position 0 vacant.
    - the same path one level below that position.

    When
    ----
    - the path is resolved and the node at that index looked for.

    Then
    ----
    - the path resolves to generalized index 16 again, path resolution reading the type alone.
    - index 8 is still a node, and still reads as 32 zero bytes.
    - index 16 is refused for PATH_INTO_GAP, the vacancy merkleizing to a leaf.
    - a zero subtree would have let one prove a field of a struct that is not there.
    """
    assert bytes(node_root(VACANT, 8)) == bytes(32)
    proof_test(
        case_id="absence/compatible_union/invalid/vacant_position_has_no_interior",
        type_name="AbsenceOutline",
        value=VACANT,
        path=(1, "detail", "lo"),
        expected_index=16,
        expected_rejection=ExpectedRejection(
            reason=ValueFault.PATH_INTO_GAP,
            exact_message="the path descends into an empty position of AbsenceCircle",
        ),
    )


def test_a_padded_element_of_a_bounded_list_reads_as_zero(proof_test: ProofTestFiller) -> None:
    """
    A position a bounded list pads out to is a node, and is proved to hold nothing.

    Given
    -----
    - a list of at most eight composite elements, two of them filled.
    - position 5, which is padding under this value and a held element under a longer one.

    When
    ----
    - the path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 21, the contents sitting under the left child.
    - the leaf is 32 zero bytes, the tree padding out to its declared capacity of eight.
    - the branch ends on the mixed-in element count at index 3.
    - that count puts the position past the end rather than at a default element.
    - absence is provable here, where a progressive shape has no padded slot to point at.
    """
    proof_test(
        case_id="absence/list/padded_element_reads_zero",
        type_name="AbsenceDetailList8",
        value=TWO_DETAILS,
        path=(5,),
        expected_index=21,
    )


def test_a_padded_element_of_a_bounded_list_has_no_interior(proof_test: ProofTestFiller) -> None:
    """
    That padding is one leaf and not a subtree, so a field of a padded element is refused.

    Given
    -----
    - the same list of at most eight composite elements, two of them filled.
    - the first field of the element at position 5.

    When
    ----
    - the path is resolved and the node at that index looked for.

    Then
    ----
    - the path resolves to generalized index 42, the left child of the element's own index 21.
    - index 42 is refused for PATH_INTO_GAP, though index 21 is a node this value proves zero.
    - a bounded tree pads with a zero leaf, not with a default element.
    - a default element would have an interior, and its fields would be provable one by one.
    """
    proof_test(
        case_id="absence/list/invalid/into_a_padded_element",
        type_name="AbsenceDetailList8",
        value=TWO_DETAILS,
        path=(5, "lo"),
        expected_index=42,
        expected_rejection=ExpectedRejection(
            reason=ValueFault.PATH_INTO_GAP,
            exact_message="the path descends into an empty position of AbsenceDetailList8",
        ),
    )


def test_a_position_past_a_one_chunk_spine_has_no_node(proof_test: ProofTestFiller) -> None:
    """
    A position past the end of a progressive spine is refused rather than read as zero.

    Given
    -----
    - a progressive list of two eight-byte elements, four to a chunk.
    - the spine therefore closes after its first level, whose one chunk holds positions 0 to 3.
    - position 4, the first of the four-chunk second level that this value never reaches.

    When
    ----
    - the path is resolved and the node at that index looked for.

    Then
    ----
    - the path resolves to generalized index 40, path resolution reading the type alone.
    - position 3 is a node of this tree at index 4, sharing chunk 0 with positions 0 to 2.
    - position 4 is refused for PATH_PAST_SPINE, the spine closing on a zero node.
    - there is no leaf and no branch.
    - a bounded shape would have padded to its capacity and proved that padding as a leaf.
    """
    assert last_node(TWO, 3) == 4
    proof_test(
        case_id="absence/progressive_list/invalid/past_a_one_chunk_spine",
        type_name="AbsenceUint64ProgressiveList",
        value=TWO,
        path=(4,),
        expected_index=40,
        expected_rejection=ExpectedRejection(
            reason=ValueFault.PATH_PAST_SPINE,
            exact_message=(
                "the path lies past the end of the progressive spine "
                "of AbsenceUint64ProgressiveList"
            ),
        ),
    )


def test_a_position_past_a_five_chunk_spine_has_no_node(proof_test: ProofTestFiller) -> None:
    """
    Growing the list onto the second spine level moves the boundary and no further.

    Given
    -----
    - a progressive list of five eight-byte elements, opening the four-chunk second level.
    - the two levels together hold positions 0 to 19.
    - position 20, the first of the sixteen-chunk third level that this value never reaches.

    When
    ----
    - the path is resolved and the node at that index looked for.

    Then
    ----
    - the path resolves to generalized index 352.
    - position 19 is a node at index 43, the second level padding out to its four chunks.
    - position 20 is refused for PATH_PAST_SPINE.
    - a level the value opens is padded to its full width.
    - a level it never opens is not there at all.
    """
    assert last_node(FIVE, 19) == 43
    proof_test(
        case_id="absence/progressive_list/invalid/past_a_five_chunk_spine",
        type_name="AbsenceUint64ProgressiveList",
        value=FIVE,
        path=(20,),
        expected_index=352,
        expected_rejection=ExpectedRejection(
            reason=ValueFault.PATH_PAST_SPINE,
            exact_message=(
                "the path lies past the end of the progressive spine "
                "of AbsenceUint64ProgressiveList"
            ),
        ),
    )


def test_a_position_past_a_twenty_one_chunk_spine_has_no_node(proof_test: ProofTestFiller) -> None:
    """
    One more level of growth moves the boundary again, by the factor of four the spine scales by.

    Given
    -----
    - a progressive list of twenty-one eight-byte elements, opening the third level.
    - the three levels together hold positions 0 to 83.
    - position 84, the first of the sixty-four-chunk fourth level.

    When
    ----
    - the path is resolved and the node at that index looked for.

    Then
    ----
    - the path resolves to generalized index 2944.
    - position 83 is a node at index 367, the third level padding out to its sixteen chunks.
    - position 84 is refused for PATH_PAST_SPINE.
    - the boundaries 4, 20 and 84 are 1, 1 + 4 and 1 + 4 + 16 chunks of four elements each.
    - how far the spine runs fixes what is provable, the type leaving positions unbounded.
    """
    assert last_node(TWENTY_ONE, 83) == 367
    proof_test(
        case_id="absence/progressive_list/invalid/past_a_twenty_one_chunk_spine",
        type_name="AbsenceUint64ProgressiveList",
        value=TWENTY_ONE,
        path=(84,),
        expected_index=2944,
        expected_rejection=ExpectedRejection(
            reason=ValueFault.PATH_PAST_SPINE,
            exact_message=(
                "the path lies past the end of the progressive spine "
                "of AbsenceUint64ProgressiveList"
            ),
        ),
    )

"""SSZ conformance test vectors for the indices a progressive shape holds still."""

from typing import Any, cast

import pytest

from ssz import (
    ByteVector,
    CompatibleUnion,
    ProgressiveContainer,
    ProgressiveList,
    SSZType,
    Uint8,
    Uint16,
    Uint64,
    active_fields,
    get_generalized_index,
    hash_tree_root,
)
from ssz_testing import GindexTestFiller, ProofTestFiller

pytestmark = pytest.mark.tags("gindex", "proofs", "stability")

STATE_WIDTH = 46
"""Positions the post-EIP-8015 beacon state layout declares."""

STATE_GAPS = (8, 9, 10, 28)
"""Positions that layout leaves vacant."""

DROPPED_POSITION = 31
"""Position a later fork vacates, which sits ahead of the field these vectors follow."""


def distinct_roots(*values: SSZType) -> None:
    """Check that these values merkleize to roots of their own."""
    roots = [hash_tree_root(value).hex() for value in values]
    if len(set(roots)) != len(roots):
        raise AssertionError(f"two of these values merkleize alike: {roots}")


def shared_index(field: str, *layouts: type[ProgressiveContainer]) -> int:
    """The generalized index every one of these layouts puts that field at."""
    indices = {layout.__name__: get_generalized_index(layout, field) for layout in layouts}
    if len(set(indices.values())) != 1:
        raise AssertionError(f"the field moves between these layouts: {indices}")
    distinct_roots(*(layout() for layout in layouts))
    return next(iter(indices.values()))


def shared_option_index(union: type[CompatibleUnion], field: str) -> int:
    """The generalized index every option of this union puts that field at."""
    indices = {
        selector: get_generalized_index(union, selector, field) for selector in union.OPTIONS
    }
    if len(set(indices.values())) != 1:
        raise AssertionError(f"the field moves between these options: {indices}")
    return next(iter(indices.values()))


class StabilityRoot(ByteVector):
    """Fixed 32-byte array, standing in for a block or state root."""

    LENGTH = 32


class StabilityHeaderV1(ProgressiveContainer):
    """Three fields on a gapless layout, the header shape one fork ships."""

    ACTIVE_FIELDS = (1, 1, 1)

    slot: Uint64
    proposer_index: Uint64
    body_root: StabilityRoot


class StabilityHeaderSibling(ProgressiveContainer):
    """The same width with position 0 vacant and another field standing at position 1."""

    ACTIVE_FIELDS = (0, 1, 1)

    builder_index: Uint64
    body_root: StabilityRoot


class StabilityHeaderV2(ProgressiveContainer):
    """The first header shape with a fourth field appended past its last set position."""

    ACTIVE_FIELDS = (1, 1, 1, 1)

    slot: Uint64
    proposer_index: Uint64
    body_root: StabilityRoot
    payload_root: StabilityRoot


HEADER_LAYOUTS = (StabilityHeaderV1, StabilityHeaderSibling, StabilityHeaderV2)
"""The three header shapes, which all carry a body root at layout position 2."""


class StabilityReceiptV1(ProgressiveContainer):
    """Four positions with the second vacant, the shape a fork leaves when it drops a field."""

    ACTIVE_FIELDS = (1, 0, 1, 1)

    amount: Uint64
    tag: Uint64
    receipt_root: StabilityRoot


class StabilityReceiptSibling(ProgressiveContainer):
    """The same four positions with the first vacated as well, so two gaps precede the last."""

    ACTIVE_FIELDS = (0, 0, 1, 1)

    tag: Uint64
    receipt_root: StabilityRoot


class StabilityReceiptV2(ProgressiveContainer):
    """The gapped shape with a fifth position appended past its last set one."""

    ACTIVE_FIELDS = (1, 0, 1, 1, 1)

    amount: Uint64
    tag: Uint64
    receipt_root: StabilityRoot
    gas_used: Uint64


RECEIPT_LAYOUTS = (StabilityReceiptV1, StabilityReceiptSibling, StabilityReceiptV2)
"""The three receipt shapes, which all carry a receipt root at layout position 3, past a gap."""


def wide_state(name: str, gaps: tuple[int, ...]) -> type[ProgressiveContainer]:
    """A beacon-state-shaped layout of 46 positions, one eight-byte field at each it sets."""
    annotations: dict[str, Any] = {
        f"f{position}": Uint64 for position in range(STATE_WIDTH) if position not in gaps
    }
    return cast(
        "type[ProgressiveContainer]",
        type(
            name,
            (ProgressiveContainer,),
            {
                "ACTIVE_FIELDS": active_fields(width=STATE_WIDTH, gaps=gaps),
                "__annotations__": annotations,
            },
        ),
    )


StabilityWideState = wide_state("StabilityWideState", STATE_GAPS)
"""The realistic wide layout, whose 46 positions run onto the fourth spine level."""

StabilityWideStateDropped = wide_state("StabilityWideStateDropped", (*STATE_GAPS, DROPPED_POSITION))
"""The same layout after a fork drops the field at position 31, widening the gaps by one."""

WIDE_LAYOUTS = (StabilityWideState, StabilityWideStateDropped)
"""The wide layout before and after that drop, both carrying a field at position 45."""


class StabilityRootProgressiveList(ProgressiveList[StabilityRoot]):
    """Unbounded sequence of 32-byte elements, one element to a chunk."""

    ELEMENT_TYPE = StabilityRoot


def root_list(length: int) -> StabilityRootProgressiveList:
    """A progressive list of the given length, each element distinguishable from its neighbours."""
    return StabilityRootProgressiveList(
        data=[StabilityRoot(bytes([(position * 7 + 1) % 256]) * 32) for position in range(length)]
    )


SHORT_ROOT_LIST = root_list(6)
"""Six elements, whose chunks reach the third spine level."""

MEDIUM_ROOT_LIST = root_list(30)
"""Thirty elements, whose chunks reach the fourth spine level."""

LONG_ROOT_LIST = root_list(100)
"""A hundred elements, whose chunks reach the fifth spine level."""


class StabilityDeposit(ProgressiveContainer):
    """Union option holding its own field at position 0 and the shared one at position 3."""

    ACTIVE_FIELDS = (1, 0, 0, 1)

    amount: Uint16
    tag: Uint8


class StabilityWithdrawal(ProgressiveContainer):
    """The compatible option, holding its own field at position 1 and the shared one at 3."""

    ACTIVE_FIELDS = (0, 1, 0, 1)

    validator_index: Uint16
    tag: Uint8


class StabilityRequest(CompatibleUnion):
    """Two options that merkleize alike, differing only in the field each declares alone."""

    OPTIONS = {1: StabilityDeposit, 2: StabilityWithdrawal}


def test_a_field_of_the_base_layout(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A progressive container puts a field at the index its layout position gives it.

    Given
    -----
    - a header of three fields on a gapless layout, its body root at position 2.
    - a path naming that field.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 41, position 2 on the second spine level.
    - the two vectors beside this one resolve the same path, against a variant layout, to 41 again.
    """
    assert shared_index("body_root", *HEADER_LAYOUTS) == 41
    ssz_gindex_test(
        case_id="stability/progressive_container/body_root_in_the_base_layout",
        type_name="StabilityHeaderV1",
        ssz_type=StabilityHeaderV1,
        path=("body_root",),
        gindex=41,
    )


def test_a_field_of_a_sibling_layout(ssz_gindex_test: GindexTestFiller) -> None:
    """
    Vacating an earlier position moves nothing that comes after it.

    Given
    -----
    - a header whose layout leaves position 0 vacant and stands another field at position 1.
    - a path naming the body root, which sits at position 2 here as well.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 41, the answer the base layout gives.
    - the layout word differs, so this shape roots differently from the base while agreeing here.
    """
    assert shared_index("body_root", *HEADER_LAYOUTS) == 41
    ssz_gindex_test(
        case_id="stability/progressive_container/body_root_in_a_sibling_layout",
        type_name="StabilityHeaderSibling",
        ssz_type=StabilityHeaderSibling,
        path=("body_root",),
        gindex=41,
    )


def test_a_field_when_a_later_field_is_appended(ssz_gindex_test: GindexTestFiller) -> None:
    """
    Appending a field past the last set position leaves every earlier field where it was.

    Given
    -----
    - the base header with a fourth field at position 3.
    - a path naming the body root at position 2.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 41, unmoved by the field appended after it.
    - a bounded struct pads its fields to a power of two, so the append that crosses the next
      one drops every leaf a level and renumbers it, which is the breakage EIP-7495 avoids.
    """
    assert shared_index("body_root", *HEADER_LAYOUTS) == 41
    ssz_gindex_test(
        case_id="stability/progressive_container/body_root_when_a_field_is_appended",
        type_name="StabilityHeaderV2",
        ssz_type=StabilityHeaderV2,
        path=("body_root",),
        gindex=41,
    )


def test_a_field_after_a_gap(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A field past a vacancy sits at its layout position, not at its ordinal among the fields.

    Given
    -----
    - a receipt of three fields whose layout leaves position 1 vacant.
    - a path naming the receipt root, the third field, standing at position 3.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 42, position 3 on the second spine level.
    - counting fields rather than positions would answer 41, the position before it.
    """
    assert shared_index("receipt_root", *RECEIPT_LAYOUTS) == 42
    ssz_gindex_test(
        case_id="stability/progressive_container/receipt_root_after_a_gap",
        type_name="StabilityReceiptV1",
        ssz_type=StabilityReceiptV1,
        path=("receipt_root",),
        gindex=42,
    )


def test_a_field_after_a_second_gap(ssz_gindex_test: GindexTestFiller) -> None:
    """
    Widening the vacancy ahead of a field still leaves the field where it was.

    Given
    -----
    - the same receipt with position 0 vacated too, so two positions precede the pair of fields.
    - a path naming the receipt root at position 3.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 42, the answer the one-gap layout gives.
    - the field is now the second declared rather than the third, and the index does not follow.
    """
    assert shared_index("receipt_root", *RECEIPT_LAYOUTS) == 42
    ssz_gindex_test(
        case_id="stability/progressive_container/receipt_root_after_a_second_gap",
        type_name="StabilityReceiptSibling",
        ssz_type=StabilityReceiptSibling,
        path=("receipt_root",),
        gindex=42,
    )


def test_a_field_after_a_gap_when_a_later_field_is_appended(
    ssz_gindex_test: GindexTestFiller,
) -> None:
    """
    A gap and an append together leave a field at one index.

    Given
    -----
    - the one-gap receipt with a fifth position appended past its last set one.
    - a path naming the receipt root at position 3.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 42, the answer both other receipt layouts give.
    """
    assert shared_index("receipt_root", *RECEIPT_LAYOUTS) == 42
    ssz_gindex_test(
        case_id="stability/progressive_container/receipt_root_after_a_gap_and_an_append",
        type_name="StabilityReceiptV2",
        ssz_type=StabilityReceiptV2,
        path=("receipt_root",),
        gindex=42,
    )


def test_a_high_field_of_a_wide_layout(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A realistic beacon state layout puts its last field deep on the spine.

    Given
    -----
    - a layout of 46 positions with four of them vacant, the shape a beacon state declares.
    - a path naming the field at position 45.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 2968, position 45 on the 64-wide fourth spine level.
    """
    assert shared_index("f45", *WIDE_LAYOUTS) == 2968
    ssz_gindex_test(
        case_id="stability/progressive_container/wide_layout_last_field",
        type_name="StabilityWideState",
        ssz_type=StabilityWideState,
        path=("f45",),
        gindex=2968,
    )


def test_a_high_field_of_a_wide_layout_after_a_drop(ssz_gindex_test: GindexTestFiller) -> None:
    """
    Dropping a field from the middle of a wide layout leaves the fields above it in place.

    Given
    -----
    - the same 46-position layout with position 31 vacated as well.
    - a path naming the field at position 45, fourteen positions above the one dropped.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 2968, the answer the layout gave before the drop.
    - a bounded struct renumbers every field that follows a removal.
    - the vacancy left in the layout is what holds the place here.
    """
    assert shared_index("f45", *WIDE_LAYOUTS) == 2968
    ssz_gindex_test(
        case_id="stability/progressive_container/wide_layout_last_field_after_a_drop",
        type_name="StabilityWideStateDropped",
        ssz_type=StabilityWideStateDropped,
        path=("f45",),
        gindex=2968,
    )


def test_an_element_of_a_short_progressive_list(proof_test: ProofTestFiller) -> None:
    """
    An element of a progressive list is proved at the index its position gives it.

    Given
    -----
    - a progressive list of six 32-byte elements, whose chunks reach the third spine level.
    - the element at position 5, the first chunk of that level.

    When
    ----
    - the path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 352.
    - the branch rebuilds the value's root.
    - the two longer lists beside this one carry the same index against a different root.
    """
    distinct_roots(SHORT_ROOT_LIST, MEDIUM_ROOT_LIST, LONG_ROOT_LIST)
    proof_test(
        case_id="stability/progressive_list/element_five_of_six",
        type_name="StabilityRootProgressiveList",
        value=SHORT_ROOT_LIST,
        path=(5,),
        expected_index=352,
    )


def test_an_element_of_a_longer_progressive_list(proof_test: ProofTestFiller) -> None:
    """
    Growing the list onto a further spine level leaves the earlier elements where they were.

    Given
    -----
    - the same list holding thirty elements, whose chunks reach the fourth spine level.
    - the element at position 5.

    When
    ----
    - the path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 352, the answer the six-element list gives.
    - the root differs from the shorter list's, so this is a different tree and not the same
      one filled twice.
    - the branch holds eight nodes here as it does there, the index alone fixing its length.
    """
    distinct_roots(SHORT_ROOT_LIST, MEDIUM_ROOT_LIST, LONG_ROOT_LIST)
    proof_test(
        case_id="stability/progressive_list/element_five_of_thirty",
        type_name="StabilityRootProgressiveList",
        value=MEDIUM_ROOT_LIST,
        path=(5,),
        expected_index=352,
    )


def test_an_element_of_a_long_progressive_list(proof_test: ProofTestFiller) -> None:
    """
    Two more spine levels of growth still leave an element at the index it started at.

    Given
    -----
    - the same list holding a hundred elements, whose chunks reach the fifth spine level.
    - the element at position 5.

    When
    ----
    - the path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 352 across all three lengths, which is what
      EIP-7916 promises a verifier that hard-codes it.
    - a bounded list of the same elements moves that index whenever its capacity is redeclared.
    """
    distinct_roots(SHORT_ROOT_LIST, MEDIUM_ROOT_LIST, LONG_ROOT_LIST)
    proof_test(
        case_id="stability/progressive_list/element_five_of_one_hundred",
        type_name="StabilityRootProgressiveList",
        value=LONG_ROOT_LIST,
        path=(5,),
        expected_index=352,
    )


def test_a_shared_field_under_the_first_option(ssz_gindex_test: GindexTestFiller) -> None:
    """
    Every option of a compatible union shares the left child, so a shared field has one index.

    Given
    -----
    - a union whose options both set layout position 3 and stand the same field there.
    - a path naming the first option and then that field.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 74.
    """
    assert shared_option_index(StabilityRequest, "tag") == 74
    ssz_gindex_test(
        case_id="stability/compatible_union/tag_under_the_first_option",
        type_name="StabilityRequest",
        ssz_type=StabilityRequest,
        path=(1, "tag"),
        gindex=74,
    )


def test_a_shared_field_under_the_second_option(ssz_gindex_test: GindexTestFiller) -> None:
    """
    The same field under the other option resolves to the same node.

    Given
    -----
    - the same union, whose options differ in the field each declares alone.
    - a path naming the second option and then the shared field.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 74 again, so one proof serves whichever option a value turns out to hold.
    - the two options root differently, the layout word and the selector both telling them apart.
    """
    assert shared_option_index(StabilityRequest, "tag") == 74
    ssz_gindex_test(
        case_id="stability/compatible_union/tag_under_the_second_option",
        type_name="StabilityRequest",
        ssz_type=StabilityRequest,
        path=(2, "tag"),
        gindex=74,
    )

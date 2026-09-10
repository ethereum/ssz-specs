"""SSZ: hash_tree_root vectors for the tree shapes merkleize folds, pads and shortcuts."""

from typing import ClassVar

import pytest

from ssz import (
    BYTES_PER_CHUNK,
    Boolean,
    ByteVector,
    Container,
    List,
    Uint8,
    Uint16,
    Uint32,
    Uint64,
    Vector,
    hash_tree_root,
)
from ssz_testing import SSZTestFiller

pytestmark = pytest.mark.tags("boundary", "multi-level")


class TreeShapeBytes32(ByteVector):
    """One chunk wide, so a sequence of these has one leaf per element."""

    LENGTH: ClassVar[int] = BYTES_PER_CHUNK


class TreeShapeVector3(Vector[TreeShapeBytes32]):
    """Three leaves in a four-leaf tree: a chunk count that is not a power of two."""

    LENGTH: ClassVar[int] = 3


class TreeShapeVector6(Vector[TreeShapeBytes32]):
    """Six leaves in an eight-leaf tree: an even leaf level over an odd level above it."""

    LENGTH: ClassVar[int] = 6


class TreeShapeVector8(Vector[TreeShapeBytes32]):
    """Eight leaves, a perfect tree, so every level is folded whole."""

    LENGTH: ClassVar[int] = 8


class TreeShapeBytes32List300(List[TreeShapeBytes32]):
    """A 300-element cap, so the tree is 512 leaves wide however few elements it holds."""

    LIMIT: ClassVar[int] = 300
    ELEMENT_TYPE = TreeShapeBytes32


class TreeShapePair(Container):
    """Two fixed fields, the composite element a list of composites is built from."""

    a: Uint64
    b: Uint32


class TreeShapePairList5(List[TreeShapePair]):
    """A five-element cap, a limit that is not a power of two, over composite elements."""

    LIMIT: ClassVar[int] = 5
    ELEMENT_TYPE = TreeShapePair


class TreeShapeFiveFields(Container):
    """Five fields, so the field tree pads five leaves out to eight."""

    a: Uint8
    b: Uint16
    c: Uint32
    d: Uint64
    e: Boolean


class TreeShapeSevenFields(Container):
    """Seven fields, so the field tree pads seven leaves out to eight."""

    a: Uint8
    b: Uint16
    c: Uint32
    d: Uint64
    e: Boolean
    f: Uint8
    g: Uint32


class TreeShapeInner(Container):
    """The nested value that the expansion holds whole and the summary holds rooted."""

    epoch: Uint64
    root: TreeShapeBytes32


class TreeShapeExpansion(Container):
    """Three fields, the middle one a nested container held whole."""

    slot: Uint64
    body: TreeShapeInner
    flag: Boolean


class TreeShapeSummary(Container):
    """The same three fields, the middle one replaced by that container's hash_tree_root."""

    slot: Uint64
    body: TreeShapeBytes32
    flag: Boolean


def marker(byte: int) -> TreeShapeBytes32:
    """A chunk-wide leaf of one repeated byte, distinct per byte and never all-zero."""
    return TreeShapeBytes32(bytes([byte]) * BYTES_PER_CHUNK)


SUMMARIZED_BODY = TreeShapeInner(epoch=Uint64(9), root=marker(0xAB))
"""The nested value both halves of the summary-and-expansion pair are built around."""


def test_vector_of_three_chunks_pads_to_four_leaves(ssz_test: SSZTestFiller) -> None:
    """
    A three-leaf vector merkleizes to a stable root.

    Given
    -----
    - a vector of three chunk-wide elements, each holding a distinct byte.
    - a chunk count of three, padded out to a four-leaf tree.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root matches the expected layout.
    - the odd leaf level is closed by a zero leaf before the first fold.
    """
    ssz_test(
        case_id="tree_shape/vector3/padded_to_four_leaves",
        type_name="TreeShapeVector3",
        value=TreeShapeVector3(data=[marker(0x11), marker(0x22), marker(0x33)]),
    )


def test_vector_of_six_chunks_folds_an_odd_level_above_the_leaves(
    ssz_test: SSZTestFiller,
) -> None:
    """
    A six-leaf vector merkleizes to a stable root.

    Given
    -----
    - a vector of six chunk-wide elements, each holding a distinct byte.
    - a chunk count of six, padded out to an eight-leaf tree.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root matches the expected layout.
    - the leaf level folds whole, and the three-node level above it is closed by a zero
      subtree spanning two leaves.
    """
    ssz_test(
        case_id="tree_shape/vector6/odd_level_above_leaves",
        type_name="TreeShapeVector6",
        value=TreeShapeVector6(
            data=[
                marker(0x11),
                marker(0x22),
                marker(0x33),
                marker(0x44),
                marker(0x55),
                marker(0x66),
            ]
        ),
    )


def test_vector_of_identical_chunks_takes_the_uniform_level_shortcut(
    ssz_test: SSZTestFiller,
) -> None:
    """
    An eight-leaf vector whose leaves are all equal merkleizes to a stable root.

    Given
    -----
    - a vector of eight chunk-wide elements holding the same non-zero byte.
    - a leaf level that spans its data tree and holds one repeated value.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root matches the expected layout.
    - the uniform level is not paired off, but folded against itself once per height.
    """
    ssz_test(
        case_id="tree_shape/vector8/uniform_leaves",
        type_name="TreeShapeVector8",
        value=TreeShapeVector8(data=[marker(0x77)] * 8),
    )


def test_vector_zero_except_the_last_chunk_is_not_a_zero_tree(ssz_test: SSZTestFiller) -> None:
    """
    An eight-leaf vector whose only data sits in the last leaf merkleizes to a stable root.

    Given
    -----
    - a vector of eight chunk-wide elements, the first seven all-zero.
    - a last element holding a non-zero byte.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root matches the expected layout.
    - the all-zero shortcut does not fire, so the root is not the eight-leaf zero tree.
    """
    ssz_test(
        case_id="tree_shape/vector8/only_last_leaf_set",
        type_name="TreeShapeVector8",
        value=TreeShapeVector8(data=[TreeShapeBytes32.zero()] * 7 + [marker(0x01)]),
    )


@pytest.mark.tags("limit")
def test_list_of_four_chunks_under_a_512_leaf_tree(ssz_test: SSZTestFiller) -> None:
    """
    A list holding four elements under a 300-element cap merkleizes to a stable root.

    Given
    -----
    - a list of chunk-wide elements capped at 300, so its tree is 512 leaves wide.
    - four elements, each holding a distinct byte.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root matches the expected layout.
    - the data folds into a four-leaf subtree, which is then hashed against an all-zero
      subtree once per height up to the full width.
    """
    ssz_test(
        case_id="tree_shape/list300/four_of_512_leaves",
        type_name="TreeShapeBytes32List300",
        value=TreeShapeBytes32List300(
            data=[marker(0x11), marker(0x22), marker(0x33), marker(0x44)]
        ),
    )


@pytest.mark.tags("limit")
def test_list_of_composites_below_a_non_power_of_two_limit(ssz_test: SSZTestFiller) -> None:
    """
    A list holding three containers under a five-element cap merkleizes to a stable root.

    Given
    -----
    - a list of two-field containers capped at five, so its tree is eight leaves wide.
    - three elements, each leaf being the root of its own container.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root matches the expected layout.
    - the odd leaf level is closed by a zero leaf, and the four-leaf subtree above it is
      hashed against an all-zero subtree to reach the full width.
    """
    ssz_test(
        case_id="tree_shape/list5/three_composite_elements",
        type_name="TreeShapePairList5",
        value=TreeShapePairList5(
            data=[
                TreeShapePair(a=Uint64(1), b=Uint32(2)),
                TreeShapePair(a=Uint64(3), b=Uint32(4)),
                TreeShapePair(a=Uint64(5), b=Uint32(6)),
            ]
        ),
    )


def test_container_with_five_fields(ssz_test: SSZTestFiller) -> None:
    """
    A five-field container merkleizes to a stable root.

    Given
    -----
    - a container of five fixed-size fields, each holding a distinct value.
    - a field count of five, padded out to an eight-leaf tree.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root matches the expected layout.
    - a zero subtree closes the odd level at two successive heights.
    """
    ssz_test(
        case_id="tree_shape/container5/five_fields",
        type_name="TreeShapeFiveFields",
        value=TreeShapeFiveFields(
            a=Uint8(0x11),
            b=Uint16(0x2222),
            c=Uint32(0x33333333),
            d=Uint64(0x4444444444444444),
            e=Boolean(True),
        ),
    )


def test_container_with_seven_fields(ssz_test: SSZTestFiller) -> None:
    """
    A seven-field container merkleizes to a stable root.

    Given
    -----
    - a container of seven fixed-size fields, each holding a distinct value.
    - a field count of seven, padded out to an eight-leaf tree.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root matches the expected layout.
    - a single zero leaf closes the odd leaf level, and every level above it folds whole.
    """
    ssz_test(
        case_id="tree_shape/container7/seven_fields",
        type_name="TreeShapeSevenFields",
        value=TreeShapeSevenFields(
            a=Uint8(0x11),
            b=Uint16(0x2222),
            c=Uint32(0x33333333),
            d=Uint64(0x4444444444444444),
            e=Boolean(True),
            f=Uint8(0x55),
            g=Uint32(0x66666666),
        ),
    )


@pytest.mark.tags("summary")
def test_expansion_holding_the_nested_container_whole(ssz_test: SSZTestFiller) -> None:
    """
    A container holding a nested container merkleizes to a stable root.

    Given
    -----
    - a three-field container whose middle field is a two-field container.
    - a field count of three, padded out to a four-leaf tree.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root matches the expected layout.
    - the middle leaf is the nested container's own root.
    - the root equals the root of the summary that holds that root in the field's place.
    """
    ssz_test(
        case_id="tree_shape/expansion/nested_container_held_whole",
        type_name="TreeShapeExpansion",
        value=TreeShapeExpansion(slot=Uint64(64), body=SUMMARIZED_BODY, flag=Boolean(True)),
    )


@pytest.mark.tags("summary")
def test_summary_holding_the_nested_root_in_its_place(ssz_test: SSZTestFiller) -> None:
    """
    A container holding a nested container's root merkleizes to a stable root.

    Given
    -----
    - a three-field container whose middle field is a 32-byte vector.
    - that field holding the hash_tree_root of the container the expansion holds whole.

    When
    ----
    - the value is merkleized.

    Then
    ----
    - the root matches the expected layout.
    - the root equals the expansion's root, the summary property the specification states.
    """
    summary = TreeShapeSummary(
        slot=Uint64(64),
        body=TreeShapeBytes32(hash_tree_root(SUMMARIZED_BODY)),
        flag=Boolean(True),
    )
    expansion = TreeShapeExpansion(slot=Uint64(64), body=SUMMARIZED_BODY, flag=Boolean(True))
    assert hash_tree_root(summary) == hash_tree_root(expansion)
    ssz_test(
        case_id="tree_shape/summary/nested_root_in_place",
        type_name="TreeShapeSummary",
        value=summary,
    )

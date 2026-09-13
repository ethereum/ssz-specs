"""SSZ conformance test vectors for paths reaching below a leaf of a progressive shape."""

import pytest

from ssz import (
    Boolean,
    ByteVector,
    Container,
    ProgressiveBitList,
    ProgressiveContainer,
    ProgressiveList,
    Uint64,
)
from ssz.paths import ACTIVE_FIELDS_KEY, LENGTH_KEY
from ssz_testing import ProofTestFiller

pytestmark = pytest.mark.tags("gindex", "proofs")


class DeepPathRoot(ByteVector):
    """Fixed 32-byte array, standing in for a block or state root."""

    LENGTH = 32


class DeepPathEntry(Container):
    """Two-field struct, taking one leaf of the spine and holding two of its own."""

    epoch: Uint64
    root: DeepPathRoot


class DeepPathEntryList(ProgressiveList[DeepPathEntry]):
    """Progressive list of composite elements, one chunk each along the spine."""


class DeepPathGapped(ProgressiveContainer):
    """Two fields with position 1 vacant, so the composite field stands at position 2."""

    ACTIVE_FIELDS = (1, 0, 1)

    tag: Uint64
    entry: DeepPathEntry


class DeepPathBits(ProgressiveBitList):
    """Unbounded bit sequence, 256 bits to a chunk along the spine."""


ENTRIES = DeepPathEntryList(
    data=[
        DeepPathEntry(epoch=Uint64(index), root=DeepPathRoot(bytes([index]) * 32))
        for index in range(6)
    ]
)
"""Six composite elements, filling chunks 0 to 5 and so reaching the third spine level."""

GAPPED = DeepPathGapped(
    tag=Uint64(0xFEED),
    entry=DeepPathEntry(epoch=Uint64(4_294_967_297), root=DeepPathRoot(b"\xb7" * 32)),
)
"""A progressive container whose second field is a struct, the vacancy ahead of it unfilled."""

BITS = DeepPathBits(data=[Boolean(index % 4 == 0) for index in range(300)])
"""Three hundred bits, so chunk 0 is full and chunk 1 opens the second spine level."""


def test_a_field_of_an_element_on_the_second_spine_level(proof_test: ProofTestFiller) -> None:
    """
    A path descends below a progressive leaf, the element root being no stopping point.

    Given
    -----
    - a progressive list of six two-field structs, one chunk each.
    - element 1, which is chunk 1, the first of the four-wide second spine level.
    - the second field of that element.

    When
    ----
    - the two-step path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 81, the element's own index 3 spliced onto 40.
    - the leaf is the element's root field, not the element root that index 40 names.
    - the branch holds six nodes: the sibling field, then the spine above it.
    - the branch rebuilds the value's root, element count and all.
    """
    proof_test(
        case_id="progressive_path/progressive_list/element_field_on_the_second_level",
        type_name="DeepPathEntryList",
        value=ENTRIES,
        path=(1, "root"),
        expected_index=81,
    )


def test_a_field_of_an_element_on_the_third_spine_level(proof_test: ProofTestFiller) -> None:
    """
    Descending below a leaf of a deeper spine level splices onto a longer index.

    Given
    -----
    - the same list of six elements.
    - element 5, which is chunk 5, the first of the sixteen-wide third spine level.
    - the second field of that element.

    When
    ----
    - the two-step path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 705, the element's own index 3 spliced onto 352.
    - the element's own level hangs below the four of the level's subtree, not beside them.
    - the branch holds nine nodes, one of them inside the element and eight above it.
    - the branch rebuilds the value's root.
    """
    proof_test(
        case_id="progressive_path/progressive_list/element_field_on_the_third_level",
        type_name="DeepPathEntryList",
        value=ENTRIES,
        path=(5, "root"),
        expected_index=705,
    )


def test_a_field_of_a_field_standing_after_a_layout_gap(proof_test: ProofTestFiller) -> None:
    """
    A path reaches below a progressive container field that a vacancy moved.

    Given
    -----
    - a progressive container of two fields on a layout of (1, 0, 1).
    - the second field, a struct standing at layout position 2 rather than at position 1.
    - the second field of that struct.

    When
    ----
    - the two-step path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 83, index 3 spliced onto the position's 41.
    - reading the field at its ordinal would answer 81, the vacancy at position 1.
    - the branch ends on the mixed-in field layout, which is what tells absent from zero.
    - the branch rebuilds the value's root.
    """
    proof_test(
        case_id="progressive_path/progressive_container/field_of_a_field_after_a_gap",
        type_name="DeepPathGapped",
        value=GAPPED,
        path=("entry", "root"),
        expected_index=83,
    )


def test_the_field_layout_of_a_progressive_container(proof_test: ProofTestFiller) -> None:
    """
    The field layout mixed into a progressive container's root is a provable leaf.

    Given
    -----
    - the same progressive container, whose layout of (1, 0, 1) leaves position 1 vacant.
    - the reserved step naming the mixed-in field layout.

    When
    ----
    - the path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 3, the right child of the root.
    - the leaf is the layout bits little-endian in a 32-byte word, so it reads 0x05.
    - the one-node branch is the root of the spine, and rebuilds the value's root.
    """
    proof_test(
        case_id="progressive_path/progressive_container/field_layout",
        type_name="DeepPathGapped",
        value=GAPPED,
        path=(ACTIVE_FIELDS_KEY,),
        expected_index=3,
    )


def test_the_first_bit_of_a_progressive_bitlist(proof_test: ProofTestFiller) -> None:
    """
    A bit of a progressive bitlist is proved by the spine chunk that packs it.

    Given
    -----
    - a progressive bitlist holding 300 bits, every fourth one set.
    - bit 0, which sits in chunk 0, alone on the first spine level.

    When
    ----
    - the path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 4, the same index element 0 of any spine gets.
    - the leaf holds bits 0 to 255, so packing eight bits to a chunk would answer elsewhere.
    - the branch rebuilds the value's root.
    """
    proof_test(
        case_id="progressive_path/progressive_bit_list/first_bit",
        type_name="DeepPathBits",
        value=BITS,
        path=(0,),
        expected_index=4,
    )


def test_the_first_bit_of_the_second_spine_level(proof_test: ProofTestFiller) -> None:
    """
    Bit 256 opens the second chunk, which is the first of the second spine level.

    Given
    -----
    - the same bitlist of 300 bits, so chunk 1 holds 44 of them.
    - bit 256, the first bit past the chunk boundary.

    When
    ----
    - the path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 40, one right turn down the spine.
    - a bounded bitlist of two chunks would place chunk 1 at index 5, its capacity fixing that.
    - the branch rebuilds the value's root.
    """
    proof_test(
        case_id="progressive_path/progressive_bit_list/first_bit_of_the_second_level",
        type_name="DeepPathBits",
        value=BITS,
        path=(256,),
        expected_index=40,
    )


def test_the_bit_count_of_a_progressive_bitlist(proof_test: ProofTestFiller) -> None:
    """
    The bit count mixed into a progressive bitlist's root is a provable leaf.

    Given
    -----
    - the same bitlist of 300 bits.
    - the reserved step naming the mixed-in element count.

    When
    ----
    - the path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 3, the right child of the root.
    - the leaf is 300 as a little-endian 32-byte word, the bit count and not the chunk count.
    - the one-node branch is the root of the spine, and rebuilds the value's root.
    """
    proof_test(
        case_id="progressive_path/progressive_bit_list/element_count",
        type_name="DeepPathBits",
        value=BITS,
        path=(LENGTH_KEY,),
        expected_index=3,
    )

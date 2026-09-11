"""SSZ conformance test vectors for a single Merkle branch against one generalized index."""

from typing import ClassVar

import pytest

from ssz import (
    BitList,
    Boolean,
    ByteVector,
    CompatibleUnion,
    Container,
    List,
    ProgressiveContainer,
    ProgressiveList,
    Uint8,
    Uint16,
    Uint64,
    ValueFault,
)
from ssz.paths import LENGTH_KEY
from ssz_testing import ExpectedRejection, ProofMutation, ProofTestFiller

pytestmark = pytest.mark.tags("proofs")

ROOT_IS_ADMITTED = (
    "merkle-proofs.md rebuilds index 1 from an empty branch and returns the leaf unchanged"
)
"""What the specification does with the one index this suite refuses to call a branch."""

ANY_NODE_WIDTH_IS_ADMITTED = (
    "merkle-proofs.md hashes a proof node of any width, never checking it against 32 bytes"
)
"""What the specification does with a node whose width would move the hashing boundary."""


class SampleBranchBytes32(ByteVector):
    """Composite field of exactly one Merkle leaf."""

    LENGTH: ClassVar[int] = 32


class SampleBranchCheckpoint(Container):
    """Two-field struct, standing as the nested value a path descends into."""

    epoch: Uint64
    root: SampleBranchBytes32


class SampleBranchBlock(Container):
    """Four-field struct, whose fields are the four leaves of a two-level tree."""

    slot: Uint64
    proposer: Uint64
    graffiti: SampleBranchBytes32
    accepted: Boolean


class SampleBranchState(Container):
    """Four-field struct whose third field is a struct of its own."""

    slot: Uint64
    parent: SampleBranchBytes32
    checkpoint: SampleBranchCheckpoint
    extra: Uint64


class SampleBranchCheckpointList4(List[SampleBranchCheckpoint]):
    """List of four composite elements, each taking a leaf of its own."""

    LIMIT: ClassVar[int] = 4
    ELEMENT_TYPE = SampleBranchCheckpoint


class SampleBranchUint64List8(List[Uint64]):
    """List of eight eight-byte elements, four of them packed into each of two leaves."""

    LIMIT: ClassVar[int] = 8
    ELEMENT_TYPE = Uint64


class SampleBranchBitList1024(BitList):
    """Bitlist of at most 1024 bits, packed 256 to a leaf across four of them."""

    LIMIT: ClassVar[int] = 1024


class SampleBranchProgressiveList(ProgressiveList[Uint64]):
    """Progressive list of eight-byte elements, four to a chunk along the spine."""

    ELEMENT_TYPE = Uint64


class SampleBranchSquare(ProgressiveContainer):
    """Union option holding its own field at position 0 and the shared one at position 2."""

    ACTIVE_FIELDS = (1, 0, 1)

    side: Uint16
    color: Uint8


class SampleBranchCircle(ProgressiveContainer):
    """The compatible option, sharing the position of the second field."""

    ACTIVE_FIELDS = (0, 1, 1)

    radius: Uint16
    color: Uint8


class SampleBranchShape(CompatibleUnion):
    """Union over the two layouts, every option rooted at the left child."""

    OPTIONS = {1: SampleBranchSquare, 2: SampleBranchCircle}


BLOCK = SampleBranchBlock(
    slot=Uint64(3_141_592),
    proposer=Uint64(65_537),
    graffiti=SampleBranchBytes32(bytes(range(32))),
    accepted=Boolean(True),
)
"""The flat struct every branch over a flat container is read against."""

STATE = SampleBranchState(
    slot=Uint64(8_675_309),
    parent=SampleBranchBytes32(b"\xa1" * 32),
    checkpoint=SampleBranchCheckpoint(
        epoch=Uint64(4_294_967_297),
        root=SampleBranchBytes32(b"\xc0" * 32),
    ),
    extra=Uint64(255),
)
"""The nested struct the two-step path is read against."""

CHECKPOINT_LIST = SampleBranchCheckpointList4(
    data=[
        SampleBranchCheckpoint(epoch=Uint64(index), root=SampleBranchBytes32(bytes([index]) * 32))
        for index in (1, 2, 3)
    ]
)
"""Three of four declared positions filled, so the fourth leaf is the zero padding."""

PACKED_LIST = SampleBranchUint64List8(
    data=[Uint64(value) for value in (11, 22, 33, 44, 55)],
)
"""Five of eight declared positions filled, four of them sharing the first leaf."""

BIT_LIST = SampleBranchBitList1024(data=[Boolean(index % 3 == 0) for index in range(400)])
"""Four hundred bits, so bit 300 sits in the second of four declared leaves."""

PROGRESSIVE_LIST = SampleBranchProgressiveList(data=[Uint64(value) for value in range(30)])
"""Thirty elements, so chunk 6 sits on the third level of the spine."""

SHAPE = SampleBranchShape(
    selector=Uint8(1),
    data=SampleBranchSquare(side=Uint16(0x1234), color=Uint8(0x42)),
)
"""A union holding its first option, whose fields sit under the left child."""


def test_a_field_of_a_flat_container(proof_test: ProofTestFiller) -> None:
    """
    A field of a flat struct is proved by the two siblings above it.

    Given
    -----
    - a four-field struct, whose fields are the four leaves of the tree.
    - the third field, which is one composite leaf of its own.

    When
    ----
    - the path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 6.
    - the branch holds the fourth field and the pair of the first two, in that order.
    - the branch rebuilds the value's root.
    """
    proof_test(
        case_id="proof/container/flat_field",
        type_name="SampleBranchBlock",
        value=BLOCK,
        path=("graffiti",),
        expected_index=6,
    )


def test_a_field_of_a_nested_container(proof_test: ProofTestFiller) -> None:
    """
    A field of a nested struct is proved by a branch spanning both trees.

    Given
    -----
    - a four-field struct whose third field is a two-field struct.
    - the second field of that inner struct.

    When
    ----
    - the two-step path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 13, the inner index spliced onto the outer one.
    - the branch holds three nodes: one from the inner tree, two from the outer one.
    - the branch rebuilds the value's root.
    """
    proof_test(
        case_id="proof/container/nested_field",
        type_name="SampleBranchState",
        value=STATE,
        path=("checkpoint", "root"),
        expected_index=13,
    )


def test_a_composite_element_of_a_list(proof_test: ProofTestFiller) -> None:
    """
    An element of a list of structs is proved against the root the length is mixed into.

    Given
    -----
    - a list of at most four composite elements, three of them filled.
    - the third element, which takes a leaf of its own.

    When
    ----
    - the path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 10, the contents sitting under the left child.
    - the branch ends on the mixed-in element count at index 3.
    - the branch rebuilds the value's root.
    """
    proof_test(
        case_id="proof/list/composite_element",
        type_name="SampleBranchCheckpointList4",
        value=CHECKPOINT_LIST,
        path=(2,),
        expected_index=10,
    )


def test_a_packed_element_of_a_list(proof_test: ProofTestFiller) -> None:
    """
    A packed basic element is proved by the leaf it shares with its neighbours.

    Given
    -----
    - a list of at most eight eight-byte elements, five of them filled.
    - the fourth element, which is the last of the four packed into the first leaf.

    When
    ----
    - the path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 4, the leaf holding elements 0 to 3 together.
    - the leaf is the four elements little-endian, back to back.
    - the branch rebuilds the value's root.
    """
    proof_test(
        case_id="proof/list/packed_element",
        type_name="SampleBranchUint64List8",
        value=PACKED_LIST,
        path=(3,),
        expected_index=4,
    )


def test_the_element_count_of_a_list(proof_test: ProofTestFiller) -> None:
    """
    The element count mixed into a list's root is a provable leaf like any other.

    Given
    -----
    - a list of at most eight eight-byte elements, five of them filled.
    - the reserved step naming the mixed-in element count.

    When
    ----
    - the path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 3, the right child of the root.
    - the leaf is the count as a little-endian 32-byte word.
    - the one-node branch is the root of the contents, and rebuilds the value's root.
    """
    proof_test(
        case_id="proof/list/length_mixin",
        type_name="SampleBranchUint64List8",
        value=PACKED_LIST,
        path=(LENGTH_KEY,),
        expected_index=3,
    )


def test_a_bit_of_a_bitlist(proof_test: ProofTestFiller) -> None:
    """
    A bit of a bitlist is proved by the leaf that packs it.

    Given
    -----
    - a bitlist of at most 1024 bits, holding 400 of them.
    - bit 300, which sits in the second of the four declared leaves.

    When
    ----
    - the path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 9.
    - the leaf holds bits 256 to 511, of which only the first 144 are data.
    - the branch rebuilds the value's root.
    """
    proof_test(
        case_id="proof/bit_list/packed_bit",
        type_name="SampleBranchBitList1024",
        value=BIT_LIST,
        path=(300,),
        expected_index=9,
    )


def test_an_element_deep_on_a_progressive_spine(proof_test: ProofTestFiller) -> None:
    """
    An element on the third level of a progressive spine is proved by an eight-node branch.

    Given
    -----
    - a progressive list of thirty eight-byte elements, four to a chunk.
    - element 24, which sits in chunk 6, on the sixteen-wide third level of the spine.

    When
    ----
    - the path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 353.
    - the branch holds eight nodes: four inside the level's subtree, then the spine above it.
    - the branch rebuilds the value's root, element count and all.
    """
    proof_test(
        case_id="proof/progressive_list/deep_element",
        type_name="SampleBranchProgressiveList",
        value=PROGRESSIVE_LIST,
        path=(24,),
        expected_index=353,
    )


def test_a_field_of_a_union_option(proof_test: ProofTestFiller) -> None:
    """
    A field of the option a union holds is proved under the shared left child.

    Given
    -----
    - a union of two compatible layouts, holding the first.
    - the field both options place at layout position 2.

    When
    ----
    - the path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 73, under the left child every option shares.
    - the branch ends on the mixed-in selector, which is what tells the options apart.
    - the branch rebuilds the value's root.
    """
    proof_test(
        case_id="proof/compatible_union/option_field",
        type_name="SampleBranchShape",
        value=SHAPE,
        path=(1, "color"),
        expected_index=73,
    )


def test_a_tampered_leaf_does_not_rebuild_the_root(proof_test: ProofTestFiller) -> None:
    """
    A leaf with one bit turned over no longer rebuilds the root.

    Given
    -----
    - the branch for the third field of the flat struct.
    - the same branch, with the lowest bit of the leaf turned over.

    When
    ----
    - the leaf and the branch are hashed up to a root.

    Then
    ----
    - the rebuilt root differs from the one the vector states.
    - the proof must be refused, and nothing about it is malformed.
    """
    proof_test(
        case_id="proof/container/invalid/tampered_leaf",
        type_name="SampleBranchBlock",
        value=BLOCK,
        path=("graffiti",),
        expected_index=6,
        mutation=ProofMutation.TAMPERED_LEAF,
    )


def test_a_reversed_branch_does_not_rebuild_the_root(proof_test: ProofTestFiller) -> None:
    """
    A branch given top-down no longer rebuilds the root.

    Given
    -----
    - the branch for the third field of the flat struct, which holds two nodes.
    - the same two nodes in the other order.

    When
    ----
    - the leaf and the branch are hashed up to a root.

    Then
    ----
    - the rebuilt root differs from the one the vector states.
    - a verifier reading the branch top-down passes this case and must not.
    """
    proof_test(
        case_id="proof/container/invalid/reversed_branch",
        type_name="SampleBranchBlock",
        value=BLOCK,
        path=("graffiti",),
        expected_index=6,
        mutation=ProofMutation.REVERSED_BRANCH,
    )


def test_a_branch_missing_its_top_node_is_refused(proof_test: ProofTestFiller) -> None:
    """
    A branch one node short of the index's depth is refused before it is hashed.

    Given
    -----
    - the branch for the third field of the flat struct, which holds two nodes.
    - the same branch with its top node dropped.

    When
    ----
    - the leaf and the branch are handed to the verifier.

    Then
    ----
    - the depth of index 6 asks for two nodes and one arrived.
    - the proof is refused for BRANCH_LENGTH.
    """
    proof_test(
        case_id="proof/container/invalid/short_branch",
        type_name="SampleBranchBlock",
        value=BLOCK,
        path=("graffiti",),
        expected_index=6,
        mutation=ProofMutation.DROPPED_NODE,
        expected_rejection=ExpectedRejection(
            reason=ValueFault.BRANCH_LENGTH,
            exact_message="a branch for index 6 holds 2 nodes, got 1",
        ),
    )


def test_a_branch_carrying_one_node_too_many_is_refused(proof_test: ProofTestFiller) -> None:
    """
    A branch longer than the index's depth is refused before it is hashed.

    Given
    -----
    - the branch for the third field of the flat struct, which holds two nodes.
    - the same branch with a zero node appended.

    When
    ----
    - the leaf and the branch are handed to the verifier.

    Then
    ----
    - the depth of index 6 asks for two nodes and three arrived.
    - the proof is refused for BRANCH_LENGTH, rather than the extra node being ignored.
    """
    proof_test(
        case_id="proof/container/invalid/long_branch",
        type_name="SampleBranchBlock",
        value=BLOCK,
        path=("graffiti",),
        expected_index=6,
        mutation=ProofMutation.EXTRA_NODE,
        expected_rejection=ExpectedRejection(
            reason=ValueFault.BRANCH_LENGTH,
            exact_message="a branch for index 6 holds 2 nodes, got 3",
        ),
    )


def test_a_node_narrower_than_a_chunk_is_refused(proof_test: ProofTestFiller) -> None:
    """
    A proof node of 31 bytes is refused rather than hashed at a moved boundary.

    Given
    -----
    - the branch for the third field of the flat struct.
    - the same branch with its first node one byte short.

    When
    ----
    - the leaf and the branch are handed to the verifier.

    Then
    ----
    - the node is refused for COUNT, a 31 and 33 split hashing like a different pair.
    - this suite is stricter than the specification here, and the vector says so.
    """
    proof_test(
        case_id="proof/container/invalid/truncated_node",
        type_name="SampleBranchBlock",
        value=BLOCK,
        path=("graffiti",),
        expected_index=6,
        mutation=ProofMutation.TRUNCATED_NODE,
        stricter_than_spec=ANY_NODE_WIDTH_IS_ADMITTED,
        expected_rejection=ExpectedRejection(
            reason=ValueFault.COUNT,
            exact_message="Chunk holds exactly 32 bytes, got 31",
        ),
    )


def test_the_root_is_no_branch_of_its_own(proof_test: ProofTestFiller) -> None:
    """
    Index 1 with an empty branch is refused, the root proving nothing about itself.

    Given
    -----
    - the empty path, which names the root.
    - a leaf equal to that root, and a branch holding nothing.

    When
    ----
    - the leaf and the empty branch are handed to the verifier.

    Then
    ----
    - the proof is refused for ROOT_HAS_NO_BRANCH.
    - this suite is stricter than the specification here, and the vector says so.
    """
    proof_test(
        case_id="proof/container/invalid/root_index_empty_branch",
        type_name="SampleBranchBlock",
        value=BLOCK,
        path=(),
        expected_index=1,
        stricter_than_spec=ROOT_IS_ADMITTED,
        expected_rejection=ExpectedRejection(
            reason=ValueFault.ROOT_HAS_NO_BRANCH,
            exact_message="the root has no proof branch of its own",
        ),
    )

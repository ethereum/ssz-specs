"""SSZ conformance test vectors for several generalized indices authenticated at once."""

from typing import ClassVar

import pytest

from ssz import ByteVector, Container, List, Uint64, ValueFault
from ssz.paths import LENGTH_KEY
from ssz_testing import ExpectedRejection, MultiproofMutation, MultiproofTestFiller

pytestmark = pytest.mark.tags("multiproofs")

REPEAT_IS_ADMITTED = (
    "merkle-proofs.md admits a repeated index, keeping the last leaf given for it and "
    "dropping the other without a word"
)
"""What the specification does with a claim it holds two values for."""

NESTING_IS_ADMITTED = (
    "merkle-proofs.md admits an index below another and rebuilds the higher one from its own "
    "children, so the lower claim is never checked"
)
"""What the specification does with a claim that sits under another claim."""

EMPTY_IS_UNSTATED = (
    "merkle-proofs.md states no refusal for an empty request: calculate_multi_merkle_root "
    "reaches the end with no node at index 1 to return"
)
"""What the specification does with a request that claims nothing."""


class SampleMultiproofBytes32(ByteVector):
    """Composite field of exactly one Merkle leaf."""

    LENGTH: ClassVar[int] = 32


class SampleMultiproofCheckpoint(Container):
    """Two-field struct, standing as the nested value one claim descends into."""

    epoch: Uint64
    root: SampleMultiproofBytes32


class SampleMultiproofOctet(Container):
    """Eight-field struct, whose fields are the eight leaves of a three-level tree."""

    f0: Uint64
    f1: Uint64
    f2: Uint64
    f3: Uint64
    f4: Uint64
    f5: Uint64
    f6: Uint64
    f7: Uint64


class SampleMultiproofRecord(Container):
    """Four-field struct, whose fields are the four leaves of a two-level tree."""

    alpha: Uint64
    beta: Uint64
    gamma: Uint64
    delta: Uint64


class SampleMultiproofState(Container):
    """Four-field struct whose third field is a struct of its own."""

    slot: Uint64
    parent: SampleMultiproofBytes32
    checkpoint: SampleMultiproofCheckpoint
    extra: Uint64


class SampleMultiproofUint64List8(List[Uint64]):
    """List of eight eight-byte elements, four of them packed into each of two leaves."""

    LIMIT: ClassVar[int] = 8
    ELEMENT_TYPE = Uint64


OCTET = SampleMultiproofOctet(
    f0=Uint64(100),
    f1=Uint64(101),
    f2=Uint64(102),
    f3=Uint64(103),
    f4=Uint64(104),
    f5=Uint64(105),
    f6=Uint64(106),
    f7=Uint64(107),
)
"""The eight-leaf tree the specification's own worked example is drawn on."""

RECORD = SampleMultiproofRecord(
    alpha=Uint64(1),
    beta=Uint64(2),
    gamma=Uint64(3),
    delta=Uint64(4),
)
"""The four-leaf tree the two-claim requests are read against."""

STATE = SampleMultiproofState(
    slot=Uint64(8_675_309),
    parent=SampleMultiproofBytes32(b"\xa1" * 32),
    checkpoint=SampleMultiproofCheckpoint(
        epoch=Uint64(4_294_967_297),
        root=SampleMultiproofBytes32(b"\xc0" * 32),
    ),
    extra=Uint64(255),
)
"""The nested struct a claim and one of its descendants are read against."""

PACKED_LIST = SampleMultiproofUint64List8(data=[Uint64(value) for value in (11, 22, 33, 44, 55)])
"""Five of eight declared positions filled, four of them sharing the first leaf."""


def test_the_worked_example_of_the_specification(multiproof_test: MultiproofTestFiller) -> None:
    """
    The three claims merkle-proofs.md draws are proved by the three nodes it draws.

    Given
    -----
    - an eight-field struct, one field per leaf of a three-level tree.
    - positions 0, 1 and 6 of that tree, which are generalized indices 8, 9 and 14.

    When
    ----
    - the shared nodes the request needs are worked out and read off the tree.

    Then
    ----
    - the request needs exactly three nodes, 15, 6 and 5, in that descending order.
    - node 4 is not asked for, the verifier rebuilding it from the first two claims.
    - the three leaves and those three nodes rebuild the value's root.
    """
    multiproof_test(
        case_id="multiproof/container/spec_worked_example",
        type_name="SampleMultiproofOctet",
        value=OCTET,
        paths=(("f0",), ("f1",), ("f6",)),
        expected_indices=(8, 9, 14),
        expected_helper_indices=(15, 6, 5),
    )


def test_two_claims_over_one_container(multiproof_test: MultiproofTestFiller) -> None:
    """
    Two fields of a four-leaf struct are proved by the two leaves they do not hold.

    Given
    -----
    - a four-field struct, one field per leaf.
    - the first and third fields, which are generalized indices 4 and 6.

    When
    ----
    - the shared nodes the request needs are worked out and read off the tree.

    Then
    ----
    - the request needs nodes 7 and 5, in that descending order.
    - nodes 2 and 3 are not asked for, the verifier rebuilding both on the way up.
    - the two leaves and those two nodes rebuild the value's root.
    """
    multiproof_test(
        case_id="multiproof/container/two_fields",
        type_name="SampleMultiproofRecord",
        value=RECORD,
        paths=(("alpha",), ("gamma",)),
        expected_indices=(4, 6),
        expected_helper_indices=(7, 5),
    )


def test_one_claim_is_exactly_a_branch(multiproof_test: MultiproofTestFiller) -> None:
    """
    A request for one index asks for exactly that index's branch, in the same order.

    Given
    -----
    - a four-field struct, one field per leaf.
    - the third field alone, which is generalized index 6.

    When
    ----
    - the shared nodes the request needs are worked out and read off the tree.

    Then
    ----
    - the request needs nodes 7 and 2, which is the branch of index 6 node for node.
    - the descending order is what makes the two agree, and this case pins it.
    - the leaf and those two nodes rebuild the value's root.
    """
    multiproof_test(
        case_id="multiproof/container/one_index_is_a_branch",
        type_name="SampleMultiproofRecord",
        value=RECORD,
        paths=(("gamma",),),
        expected_indices=(6,),
        expected_helper_indices=(7, 2),
    )


def test_an_element_beside_the_element_count(multiproof_test: MultiproofTestFiller) -> None:
    """
    A packed element and the count mixed in beside it are proved by one shared node.

    Given
    -----
    - a list of at most eight eight-byte elements, five of them filled.
    - the first element, and the reserved step naming the mixed-in element count.

    When
    ----
    - the shared nodes the request needs are worked out and read off the tree.

    Then
    ----
    - the two claims are generalized indices 4 and 3, one on each side of the root.
    - the request needs one node, 5, the second leaf of the contents.
    - claiming the count leaves nothing to carry for the right half of the tree.
    """
    multiproof_test(
        case_id="multiproof/list/element_and_length",
        type_name="SampleMultiproofUint64List8",
        value=PACKED_LIST,
        paths=((0,), (LENGTH_KEY,)),
        expected_indices=(4, 3),
        expected_helper_indices=(5,),
    )


def test_a_tampered_leaf_does_not_rebuild_the_root(multiproof_test: MultiproofTestFiller) -> None:
    """
    A leaf with one bit turned over no longer rebuilds the root.

    Given
    -----
    - the two-claim request over the four-field struct.
    - the same request, with the lowest bit of the first leaf turned over.

    When
    ----
    - the leaves and the shared nodes are hashed up to a root.

    Then
    ----
    - the rebuilt root differs from the one the vector states.
    - the request must be refused, and nothing about its shape is malformed.
    """
    multiproof_test(
        case_id="multiproof/container/invalid/tampered_leaf",
        type_name="SampleMultiproofRecord",
        value=RECORD,
        paths=(("alpha",), ("gamma",)),
        expected_indices=(4, 6),
        expected_helper_indices=(7, 5),
        mutation=MultiproofMutation.TAMPERED_LEAF,
    )


def test_a_repeated_index_is_refused(multiproof_test: MultiproofTestFiller) -> None:
    """
    One index claimed twice is refused rather than one of its two leaves being dropped.

    Given
    -----
    - a four-field struct, one field per leaf.
    - the first field claimed twice, so generalized index 4 arrives twice.

    When
    ----
    - the shared nodes the request needs are worked out.

    Then
    ----
    - the request is refused for REPEATED_INDEX, and carries no nodes.
    - this suite is stricter than the specification here, and the vector says so.
    """
    multiproof_test(
        case_id="multiproof/container/invalid/repeated_index",
        type_name="SampleMultiproofRecord",
        value=RECORD,
        paths=(("alpha",), ("alpha",)),
        expected_indices=(4, 4),
        stricter_than_spec=REPEAT_IS_ADMITTED,
        expected_rejection=ExpectedRejection(
            reason=ValueFault.REPEATED_INDEX,
            exact_message="a generalized index is repeated",
        ),
    )


def test_an_index_below_another_is_refused(multiproof_test: MultiproofTestFiller) -> None:
    """
    A claim sitting under another claim is refused rather than left unchecked.

    Given
    -----
    - a four-field struct whose third field is a two-field struct.
    - that field and one of its own fields, which are generalized indices 6 and 13.

    When
    ----
    - the shared nodes the request needs are worked out.

    Then
    ----
    - the request is refused for NESTED_INDEX, naming the lower of the two.
    - the higher claim would be rebuilt from its children, so the lower one proves nothing.
    - this suite is stricter than the specification here, and the vector says so.
    """
    multiproof_test(
        case_id="multiproof/container/invalid/nested_index",
        type_name="SampleMultiproofState",
        value=STATE,
        paths=(("checkpoint",), ("checkpoint", "root")),
        expected_indices=(6, 13),
        stricter_than_spec=NESTING_IS_ADMITTED,
        expected_rejection=ExpectedRejection(
            reason=ValueFault.NESTED_INDEX,
            exact_message="13 lies below another index in the same request",
        ),
    )


def test_a_request_claiming_nothing_is_refused(multiproof_test: MultiproofTestFiller) -> None:
    """
    A request holding no index is refused rather than proving nothing successfully.

    Given
    -----
    - a four-field struct, one field per leaf.
    - no claims at all, so no leaves and no nodes.

    When
    ----
    - the shared nodes the request needs are worked out.

    Then
    ----
    - the request is refused for EMPTY_REQUEST.
    - this suite is stricter than the specification here, and the vector says so.
    """
    multiproof_test(
        case_id="multiproof/container/invalid/empty_request",
        type_name="SampleMultiproofRecord",
        value=RECORD,
        paths=(),
        expected_indices=(),
        expected_rejection=ExpectedRejection(
            reason=ValueFault.EMPTY_REQUEST,
            exact_message="a request holds at least one index",
        ),
        stricter_than_spec=EMPTY_IS_UNSTATED,
    )


def test_a_leaf_per_index_is_required(multiproof_test: MultiproofTestFiller) -> None:
    """
    Two indices with one leaf between them are refused before anything is hashed.

    Given
    -----
    - the two-claim request over the four-field struct.
    - the same request with its second leaf dropped.

    When
    ----
    - the leaves and the shared nodes are handed to the verifier.

    Then
    ----
    - the request is refused for LEAF_COUNT.
    - the leaves are matched to the indices by position, so a short list mismatches them all.
    """
    multiproof_test(
        case_id="multiproof/container/invalid/leaf_count",
        type_name="SampleMultiproofRecord",
        value=RECORD,
        paths=(("alpha",), ("gamma",)),
        expected_indices=(4, 6),
        expected_helper_indices=(7, 5),
        mutation=MultiproofMutation.DROPPED_LEAF,
        expected_rejection=ExpectedRejection(
            reason=ValueFault.LEAF_COUNT,
            exact_message="2 indices need as many leaves, got 1",
        ),
    )


def test_a_node_the_request_did_not_ask_for_is_refused(
    multiproof_test: MultiproofTestFiller,
) -> None:
    """
    A proof holding one node too many is refused rather than the extra being ignored.

    Given
    -----
    - the two-claim request over the four-field struct, which needs two nodes.
    - the same request with a zero node appended to the proof.

    When
    ----
    - the leaves and the shared nodes are handed to the verifier.

    Then
    ----
    - the request is refused for PROOF_LENGTH.
    - a proof is matched to the helper indices by position, so a third node has no index.
    """
    multiproof_test(
        case_id="multiproof/container/invalid/proof_length",
        type_name="SampleMultiproofRecord",
        value=RECORD,
        paths=(("alpha",), ("gamma",)),
        expected_indices=(4, 6),
        expected_helper_indices=(7, 5),
        mutation=MultiproofMutation.EXTRA_NODE,
        expected_rejection=ExpectedRejection(
            reason=ValueFault.PROOF_LENGTH,
            exact_message="this request needs 2 proof nodes, got 3",
        ),
    )

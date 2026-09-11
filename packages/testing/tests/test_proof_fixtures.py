"""What the proof formats emit, and what they refuse to call a passing test."""

from hashlib import sha256
from typing import Any

import pytest

from ssz import Container, List, Uint64, ValueFault
from ssz.paths import LENGTH_KEY
from ssz_testing.fixtures import ExpectedRejection
from ssz_testing.hex_codec import to_hex
from ssz_testing.proof_fixtures import (
    MultiproofMutation,
    MultiproofTest,
    ProofMutation,
    ProofPathStep,
    ProofTest,
)


class Quad(Container):
    """Four one-leaf fields, so the tree is two levels of four leaves."""

    a: Uint64
    b: Uint64
    c: Uint64
    d: Uint64


class Pair(Container):
    """Two one-leaf fields, so a branch holds a single node."""

    first: Uint64
    second: Uint64


class Numbers(List[Uint64]):
    """Four eight-byte elements at most, all four packed into one leaf."""

    LIMIT = 4
    ELEMENT_TYPE = Uint64


QUAD = Quad(a=Uint64(1), b=Uint64(2), c=Uint64(3), d=Uint64(4))
PAIR = Pair(first=Uint64(5), second=Uint64(6))
NUMBERS = Numbers(data=[Uint64(7), Uint64(8)])


def leaf(value: int) -> bytes:
    """The chunk one eight-byte element sits in, alone."""
    return value.to_bytes(8, "little") + bytes(24)


def node(left: bytes, right: bytes) -> bytes:
    """The parent of two nodes, hashed here rather than by the code under test."""
    return sha256(left + right).digest()


QUAD_ROOT = node(node(leaf(1), leaf(2)), node(leaf(3), leaf(4)))


def test_a_branch_vector_carries_everything_a_consumer_checks() -> None:
    """The value, its root, the path, the index it resolves to, the leaf and the branch."""
    vector = ProofTest(type_name="Quad", value=QUAD, path=("c",), expected_index=6).generate()

    emitted = {name: field for name, field in vector.json_dict.items() if name != "typeDescriptor"}
    assert emitted == {
        "typeName": "Quad",
        "value": {"a": "1", "b": "2", "c": "3", "d": "4"},
        "serialized": to_hex(QUAD.encode_bytes()),
        "root": to_hex(QUAD_ROOT),
        "path": [{"field": "c"}],
        "index": "6",
        "leaf": to_hex(leaf(3)),
        "branch": [to_hex(leaf(4)), to_hex(node(leaf(1), leaf(2)))],
        "branchIndices": ["7", "2"],
        "valid": True,
    }
    assert vector.json_dict["typeDescriptor"]["kind"] == "Container"


def test_a_branch_vector_is_filed_under_the_kind_it_is_about() -> None:
    """The directory and the index row come from the declaration, not from the format."""
    vector = ProofTest(type_name="Numbers", value=NUMBERS, path=(1,)).generate()

    assert vector.case_type_name() == "Numbers"
    assert vector.case_kind() == "list"
    assert vector.declared_types()["Numbers"].kind == "List"


@pytest.mark.parametrize(
    ("step", "written"),
    [
        pytest.param("c", {"field": "c"}, id="field"),
        pytest.param(1, {"position": "1"}, id="position"),
        pytest.param(LENGTH_KEY, {"mixin": LENGTH_KEY}, id="mixin"),
    ],
)
def test_a_path_step_is_written_as_the_one_shape_it_is(step: Any, written: dict[str, str]) -> None:
    """A name, a position and a reserved word are told apart rather than all being strings."""
    assert ProofPathStep.read(step).to_json(exclude_none=True) == written


def test_a_position_and_a_reserved_word_reach_the_vector() -> None:
    """A packed element and the count mixed in beside it are both provable nodes."""
    element = ProofTest(type_name="Numbers", value=NUMBERS, path=(1,), expected_index=2).generate()
    count = ProofTest(
        type_name="Numbers", value=NUMBERS, path=(LENGTH_KEY,), expected_index=3
    ).generate()

    assert element.json_dict["path"] == [{"position": "1"}]
    assert element.json_dict["leaf"] == to_hex(leaf(7)[:8] + leaf(8)[:8] + bytes(16))
    assert count.json_dict["path"] == [{"mixin": LENGTH_KEY}]
    assert count.json_dict["leaf"] == to_hex(leaf(2))


def test_the_root_carries_no_branch_of_its_own() -> None:
    """The empty path names the root, which this suite refuses to accept a proof of."""
    vector = ProofTest(
        type_name="Quad",
        value=QUAD,
        path=(),
        expected_index=1,
        stricter_than_spec="merkle-proofs.md returns the leaf unchanged",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.ROOT_HAS_NO_BRANCH,
            exact_message="the root has no proof branch of its own",
        ),
    ).generate()

    assert vector.json_dict["index"] == "1"
    assert vector.json_dict["leaf"] == to_hex(QUAD_ROOT)
    assert vector.json_dict["branch"] == []
    assert vector.json_dict["branchIndices"] == []
    assert vector.json_dict["rejectionReason"] == "ROOT_HAS_NO_BRANCH"
    assert vector.json_dict["stricterThanSpec"] == "merkle-proofs.md returns the leaf unchanged"
    assert vector.valid is False


def test_a_path_resolving_elsewhere_fails_the_fill() -> None:
    """A pinned index holds the arithmetic to what the author wrote out."""
    with pytest.raises(AssertionError, match=r"Expected index: 7\n\s+Actual index: 6"):
        ProofTest(type_name="Quad", value=QUAD, path=("c",), expected_index=7).generate()


@pytest.mark.parametrize(
    ("mutation", "rejection"),
    [
        pytest.param(ProofMutation.TAMPERED_LEAF, None, id="tampered_leaf"),
        pytest.param(ProofMutation.REVERSED_BRANCH, None, id="reversed_branch"),
        pytest.param(
            ProofMutation.DROPPED_NODE,
            ExpectedRejection(
                reason=ValueFault.BRANCH_LENGTH,
                exact_message="a branch for index 6 holds 2 nodes, got 1",
            ),
            id="dropped_node",
        ),
        pytest.param(
            ProofMutation.EXTRA_NODE,
            ExpectedRejection(
                reason=ValueFault.BRANCH_LENGTH,
                exact_message="a branch for index 6 holds 2 nodes, got 3",
            ),
            id="extra_node",
        ),
        pytest.param(
            ProofMutation.TRUNCATED_NODE,
            ExpectedRejection(
                reason=ValueFault.COUNT,
                exact_message="Chunk holds exactly 32 bytes, got 31",
            ),
            id="truncated_node",
        ),
    ],
)
def test_every_mutation_breaks_the_branch_it_was_built_from(
    mutation: ProofMutation, rejection: ExpectedRejection | None
) -> None:
    """No negative vector is emitted that a verifier would accept."""
    vector = ProofTest(
        type_name="Quad",
        value=QUAD,
        path=("c",),
        mutation=mutation,
        expected_rejection=rejection,
    ).generate()

    assert vector.valid is False
    assert vector.json_dict["root"] == to_hex(QUAD_ROOT)


def test_a_mutation_that_changes_nothing_fails_the_fill() -> None:
    """Reversing a one-node branch leaves it as it was, and a negative that verifies is no test."""
    with pytest.raises(AssertionError, match="a mutated proof still rebuilt the root"):
        ProofTest(
            type_name="Pair",
            value=PAIR,
            path=("second",),
            mutation=ProofMutation.REVERSED_BRANCH,
        ).generate()


def test_a_refusal_for_another_reason_fails_the_fill() -> None:
    """A vector states which refusal fires, not merely that one did."""
    wrong_reason = r"Expected fault: LEAF_COUNT\n\s+Actual fault: BRANCH_LENGTH"
    with pytest.raises(AssertionError, match=wrong_reason):
        ProofTest(
            type_name="Quad",
            value=QUAD,
            path=("c",),
            mutation=ProofMutation.DROPPED_NODE,
            expected_rejection=ExpectedRejection(reason=ValueFault.LEAF_COUNT),
        ).generate()


def test_a_multiproof_vector_carries_the_nodes_the_request_needs() -> None:
    """Two claims, the two leaves they do not hold, and the order the request reports them in."""
    vector = MultiproofTest(
        type_name="Quad",
        value=QUAD,
        paths=(("a",), ("c",)),
        expected_indices=(4, 6),
        expected_helper_indices=(7, 5),
    ).generate()

    emitted = {name: field for name, field in vector.json_dict.items() if name != "typeDescriptor"}
    assert emitted == {
        "typeName": "Quad",
        "value": {"a": "1", "b": "2", "c": "3", "d": "4"},
        "serialized": to_hex(QUAD.encode_bytes()),
        "root": to_hex(QUAD_ROOT),
        "paths": [[{"field": "a"}], [{"field": "c"}]],
        "indices": ["4", "6"],
        "leaves": [to_hex(leaf(1)), to_hex(leaf(3))],
        "helperIndices": ["7", "5"],
        "proof": [to_hex(leaf(4)), to_hex(leaf(2))],
        "valid": True,
    }
    assert vector.case_kind() == "container"


@pytest.mark.parametrize(
    ("expected_indices", "expected_helpers", "message"),
    [
        pytest.param((4, 7), None, "wrong indices", id="indices"),
        pytest.param(None, (5, 7), "wrong helper indices", id="helper_indices"),
    ],
)
def test_a_request_reporting_something_else_fails_the_fill(
    expected_indices: tuple[int, ...] | None,
    expected_helpers: tuple[int, ...] | None,
    message: str,
) -> None:
    """Both the resolved indices and the nodes they need are held to what the author wrote."""
    with pytest.raises(AssertionError, match=message):
        MultiproofTest(
            type_name="Quad",
            value=QUAD,
            paths=(("a",), ("c",)),
            expected_indices=expected_indices,
            expected_helper_indices=expected_helpers,
        ).generate()


def test_a_request_the_helper_walk_refuses_carries_no_nodes() -> None:
    """A repeated index is refused before any node is read, so the vector holds none."""
    vector = MultiproofTest(
        type_name="Quad",
        value=QUAD,
        paths=(("a",), ("a",)),
        expected_indices=(4, 4),
        stricter_than_spec="merkle-proofs.md keeps the last leaf given for it",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.REPEATED_INDEX,
            exact_message="a generalized index is repeated",
        ),
    ).generate()

    assert vector.json_dict["indices"] == ["4", "4"]
    assert vector.json_dict["leaves"] == [to_hex(leaf(1)), to_hex(leaf(1))]
    assert vector.json_dict["helperIndices"] == []
    assert vector.json_dict["proof"] == []
    assert vector.json_dict["rejectionReason"] == "REPEATED_INDEX"
    assert vector.valid is False


@pytest.mark.parametrize(
    ("mutation", "rejection"),
    [
        pytest.param(MultiproofMutation.TAMPERED_LEAF, None, id="tampered_leaf"),
        pytest.param(
            MultiproofMutation.DROPPED_LEAF,
            ExpectedRejection(
                reason=ValueFault.LEAF_COUNT,
                exact_message="2 indices need as many leaves, got 1",
            ),
            id="dropped_leaf",
        ),
        pytest.param(
            MultiproofMutation.EXTRA_NODE,
            ExpectedRejection(
                reason=ValueFault.PROOF_LENGTH,
                exact_message="this request needs 2 proof nodes, got 3",
            ),
            id="extra_node",
        ),
    ],
)
def test_every_mutation_breaks_the_request_it_was_built_from(
    mutation: MultiproofMutation, rejection: ExpectedRejection | None
) -> None:
    """No negative vector is emitted that a verifier would accept."""
    vector = MultiproofTest(
        type_name="Quad",
        value=QUAD,
        paths=(("a",), ("c",)),
        mutation=mutation,
        expected_rejection=rejection,
    ).generate()

    assert vector.valid is False
    assert vector.json_dict["root"] == to_hex(QUAD_ROOT)


def test_a_branch_the_vector_states_rebuilds_the_root_it_states() -> None:
    """The emitted hex, hashed here rather than by the code under test, reaches the same root."""
    vector = ProofTest(type_name="Quad", value=QUAD, path=("b",)).generate()

    index = int(vector.json_dict["index"])
    rebuilt = bytes.fromhex(vector.json_dict["leaf"].removeprefix("0x"))
    for level, sibling in enumerate(vector.json_dict["branch"]):
        step = bytes.fromhex(sibling.removeprefix("0x"))
        rebuilt = node(step, rebuilt) if index >> level & 1 else node(rebuilt, step)

    assert to_hex(rebuilt) == vector.json_dict["root"] == to_hex(QUAD_ROOT)

"""Fixture formats for Merkle proof conformance: one branch, and one multiproof."""

from collections.abc import Callable, Mapping, Sequence
from enum import Enum
from typing import Any, ClassVar, Final, Self

from pydantic import Field, computed_field, field_serializer

from ssz.base import json_writer
from ssz.exceptions import SSZError, SSZValueError, ValueFault
from ssz.gindex import get_branch_indices, get_helper_indices
from ssz.paths import (
    ACTIVE_FIELDS_KEY,
    LENGTH_KEY,
    SELECTOR_KEY,
    PathStep,
    get_generalized_index,
)
from ssz.proofs import build_multiproof, build_proof, node_root
from ssz.roots import hash_tree_root
from ssz.ssz_base import SSZType
from ssz.verification import verify_merkle_multiproof, verify_merkle_proof
from ssz_testing.fixtures import (
    BaseConsensusFixture,
    BaseTestSpec,
    CamelModel,
    TypeDescriptor,
    describe_type,
)
from ssz_testing.hex_codec import to_hex

MIXED_IN_WORDS: Final = frozenset({ACTIVE_FIELDS_KEY, LENGTH_KEY, SELECTOR_KEY})
"""The reserved path steps, each naming a word a root is hashed against rather than a field."""

ZERO_NODE: Final = bytes(32)
"""The node a negative vector appends, its content being what such a case is never about."""


def _flipped(node: bytes) -> bytes:
    """The same node with its first bit turned over, which is the smallest tamper there is."""
    return bytes([node[0] ^ 1]) + node[1:]


def _outcome(verify: Callable[[], bool]) -> tuple[SSZError[Any] | None, bool]:
    """Run one verification, telling a refusal apart from a verdict of false."""
    try:
        return None, verify()
    # Only an SSZ refusal is a vector; anything else is a bug, and crashes the fill.
    except SSZError as raised:
        return raised, False


class ProofMutation(Enum):
    """How a negative single-proof vector departs from the honest branch it was built from."""

    TAMPERED_LEAF = "tampered_leaf"
    REVERSED_BRANCH = "reversed_branch"
    DROPPED_NODE = "dropped_node"
    EXTRA_NODE = "extra_node"
    TRUNCATED_NODE = "truncated_node"


class MultiproofMutation(Enum):
    """How a negative multiproof vector departs from the honest request it was built from."""

    TAMPERED_LEAF = "tampered_leaf"
    DROPPED_LEAF = "dropped_leaf"
    EXTRA_NODE = "extra_node"


def _mutated_proof(
    mutation: ProofMutation | None, leaf: bytes, branch: tuple[bytes, ...]
) -> tuple[bytes, tuple[bytes, ...]]:
    """The leaf and branch a negative vector carries, departing from the honest pair one way."""
    match mutation:
        case ProofMutation.TAMPERED_LEAF:
            leaf = _flipped(leaf)
        case ProofMutation.REVERSED_BRANCH:
            branch = branch[::-1]
        case ProofMutation.DROPPED_NODE:
            branch = branch[:-1]
        case ProofMutation.EXTRA_NODE:
            branch = (*branch, ZERO_NODE)
        case ProofMutation.TRUNCATED_NODE:
            branch = (branch[0][:-1], *branch[1:])
    return leaf, branch


def _mutated_multiproof(
    mutation: MultiproofMutation | None, leaves: tuple[bytes, ...], proof: tuple[bytes, ...]
) -> tuple[tuple[bytes, ...], tuple[bytes, ...]]:
    """The leaves and nodes a negative vector carries, departing from the honest ones one way."""
    match mutation:
        case MultiproofMutation.TAMPERED_LEAF:
            leaves = (_flipped(leaves[0]), *leaves[1:])
        case MultiproofMutation.DROPPED_LEAF:
            leaves = leaves[:-1]
        case MultiproofMutation.EXTRA_NODE:
            proof = (*proof, ZERO_NODE)
    return leaves, proof


def _pinned(subject: str, actual: tuple[int, ...], expected: tuple[int, ...] | None) -> None:
    """Hold a resolved index list to the one the author wrote out, where they wrote one."""
    if expected is not None and actual != expected:
        raise AssertionError(
            f"The request reports the wrong {subject}.\n"
            f"  Expected: {list(expected)}\n"
            f"  Actual: {list(actual)}"
        )


class ProofPathStep(CamelModel):
    """One step of a path: a field name, an element position, or a mixed-in word."""

    model_config = CamelModel.model_config | {"extra": "forbid", "frozen": True}

    field: str | None = None
    """Name of the container field this step selects."""

    position: str | None = None
    """Decimal position of the element this step selects."""

    mixin: str | None = None
    """Reserved word naming the mixed-in leaf this step ends on."""

    @classmethod
    def read(cls, step: PathStep) -> Self:
        """Read one authored step as the single shape it is."""
        if isinstance(step, str):
            return cls(mixin=step) if step in MIXED_IN_WORDS else cls(field=step)
        return cls(position=str(step))


def _written_path(path: Sequence[PathStep]) -> tuple[ProofPathStep, ...]:
    """One authored path as the vector writes it."""
    return tuple(ProofPathStep.read(step) for step in path)


class ProofSubject(BaseConsensusFixture):
    """The value a proof is read against: its encoding, its declaration and its root."""

    type_name: str
    """SSZ type class name."""

    value: SSZType
    """The value whose Merkle tree the proof is read against."""

    serialized: str
    """Hex encoding of that value, so the subject can be rebuilt without the JSON mapping."""

    root: str
    """Hex tree root of that value, which every proof here has to rebuild."""

    stricter_than_spec: str | None = None
    """What merkle-proofs.md does here, present only where this suite refuses more than it does."""

    verified: bool = Field(exclude=True)
    """Whether the emitted proof rebuilt that root when the vector was filled."""

    @computed_field
    @property
    def valid(self) -> bool:
        """Whether a verifier must accept: a refusal denies this as surely as a wrong root."""
        return self.verified

    @field_serializer("value")
    def serialize_value(self, ssz_value: SSZType) -> Any:
        """Render the value as the SSZ JSON mapping of its own type spells it."""
        return json_writer(type(ssz_value)).dump_python(ssz_value, mode="json")

    @computed_field
    @property
    def type_descriptor(self) -> TypeDescriptor:
        """The declaration of that type, read off the class so no vector can misstate it."""
        return describe_type(type(self.value))

    def declared_types(self) -> Mapping[str, TypeDescriptor]:
        """The one name this vector emits, against the declaration it was filled from."""
        return {self.type_name: self.type_descriptor}

    def case_type_name(self) -> str:
        """The declared type name this vector is about."""
        return self.type_name

    def case_kind(self) -> str:
        """The kind the declaration already states, spelled as a directory can hold it."""
        return self.type_descriptor.directory_name


class ProofFixture(ProofSubject):
    """Emitted vector for one Merkle branch against one generalized index."""

    format_name: ClassVar[str] = "proof_test"

    path: tuple[ProofPathStep, ...]
    """Steps from the value's root down to the node the branch is about."""

    index: str
    """Decimal generalized index those steps resolve to."""

    leaf: str
    """Hex node the vector claims sits at that index."""

    branch: tuple[str, ...]
    """Hex sibling nodes from the leaf upward, in the order a verifier consumes them."""

    branch_indices: tuple[str, ...]
    """Decimal index of each of those nodes, which the index alone already fixes."""


class MultiproofFixture(ProofSubject):
    """Emitted vector for several generalized indices authenticated at once."""

    format_name: ClassVar[str] = "multiproof_test"

    paths: tuple[tuple[ProofPathStep, ...], ...]
    """Steps down to each claimed node, in the order the indices are given."""

    indices: tuple[str, ...]
    """Decimal generalized index each of those paths resolves to."""

    leaves: tuple[str, ...]
    """Hex node the vector claims at each index, one per index."""

    helper_indices: tuple[str, ...]
    """Decimal index of every node the request needs, descending, empty where none was reached."""

    proof: tuple[str, ...]
    """Hex node for each of those helper indices, in that same order."""


class BaseProofTest(BaseTestSpec):
    """Shared checking for the proof formats: one verification, against what was authored."""

    stricter_than_spec: str | None = None
    """What merkle-proofs.md does here, authored where this suite refuses more than it does."""

    def confirmed_fault(
        self, raised: SSZError[Any] | None, verified: bool, honest: bool
    ) -> ValueFault | None:
        """The fault the vector emits, the outcome having been checked against the authored one."""
        self.assert_expected_outcome(raised)
        if self.expected_rejection is None:
            if honest:
                assert verified, "an honest proof failed to rebuild the root"
            else:
                assert not verified, "a mutated proof still rebuilt the root"
            return None

        # A refusal was authored, and the check above already required one to have fired.
        assert raised is not None
        expected = self.expected_rejection.reason
        if raised.fault is not expected:
            raise AssertionError(
                f"The verifier refused for the wrong reason.\n"
                f"  Expected fault: {expected.name}\n"
                f"  Actual fault: {raised.fault.name}"
            )
        return expected


class ProofTest(BaseProofTest):
    """Spec for one Merkle branch: build it, verify it, and emit what a consumer checks."""

    format_name: ClassVar[str] = "proof_test"
    description: ClassVar[str] = "Tests a Merkle branch against one generalized index"

    type_name: str
    """SSZ type class name."""

    value: SSZType
    """The value the branch is read against."""

    path: tuple[PathStep, ...] = ()
    """Steps down to the node being proved, the empty path naming the root itself."""

    expected_index: int | None = None
    """Generalized index the path must resolve to, written out where a vector pins it."""

    mutation: ProofMutation | None = None
    """How this vector departs from the honest branch, absent on a vector that verifies."""

    def generate(self) -> ProofFixture:
        """Build the branch, confirm the outcome the author named, and emit the vector."""
        root = hash_tree_root(self.value)
        index = get_generalized_index(type(self.value), *self.path)
        if self.expected_index is not None and index != self.expected_index:
            raise AssertionError(
                f"The path resolves to the wrong index.\n"
                f"  Expected index: {self.expected_index}\n"
                f"  Actual index: {index}"
            )

        leaf = bytes(node_root(self.value, index))
        branch_indices: tuple[int, ...] = ()
        branch: tuple[bytes, ...] = ()
        # The root sits on no branch of its own, so a vector about index one carries none.
        if index > 1:
            branch_indices = tuple(get_branch_indices(index))
            branch = tuple(bytes(node) for node in build_proof(self.value, index))

        leaf, branch = _mutated_proof(self.mutation, leaf, branch)
        # Plain bytes, the way a consumer reads them off the vector: a node the width check
        # refuses is one of the cases, and it is no Chunk to begin with.
        raised, verified = _outcome(
            lambda: verify_merkle_proof(leaf, branch, index, root)  # ty: ignore[invalid-argument-type]
        )

        return ProofFixture(
            type_name=self.type_name,
            value=self.value,
            serialized=to_hex(self.value.encode_bytes()),
            root=to_hex(root),
            path=_written_path(self.path),
            index=str(index),
            leaf=to_hex(leaf),
            branch=tuple(to_hex(node) for node in branch),
            branch_indices=tuple(str(sibling) for sibling in branch_indices),
            verified=verified,
            stricter_than_spec=self.stricter_than_spec,
            rejection_reason=self.confirmed_fault(raised, verified, self.mutation is None),
        )


class MultiproofTest(BaseProofTest):
    """Spec for one multiproof: build the shared nodes, verify them, and emit the vector."""

    format_name: ClassVar[str] = "multiproof_test"
    description: ClassVar[str] = "Tests the nodes several generalized indices are proved by"

    type_name: str
    """SSZ type class name."""

    value: SSZType
    """The value the request is read against."""

    paths: tuple[tuple[PathStep, ...], ...]
    """Steps down to each claimed node, one path per index."""

    expected_indices: tuple[int, ...] | None = None
    """Generalized indices those paths must resolve to, in order."""

    expected_helper_indices: tuple[int, ...] | None = None
    """Nodes the request must ask for, in the order it must report them."""

    mutation: MultiproofMutation | None = None
    """How this vector departs from the honest request, absent on a vector that verifies."""

    def generate(self) -> MultiproofFixture:
        """Build the shared nodes, confirm the outcome the author named, and emit the vector."""
        root = hash_tree_root(self.value)
        indices = tuple(get_generalized_index(type(self.value), *path) for path in self.paths)
        _pinned("indices", indices, self.expected_indices)

        leaves = tuple(bytes(node_root(self.value, index)) for index in indices)
        helper_indices: tuple[int, ...] = ()
        proof: tuple[bytes, ...] = ()
        # A refused request reaches no node, and the verification below raises what refused it.
        try:
            helper_indices = tuple(get_helper_indices(indices))
            proof = tuple(bytes(node) for node in build_multiproof(self.value, indices))
        except SSZValueError:
            pass
        _pinned("helper indices", helper_indices, self.expected_helper_indices)

        leaves, proof = _mutated_multiproof(self.mutation, leaves, proof)
        # Plain bytes, the way a consumer reads them off the vector.
        raised, verified = _outcome(
            lambda: verify_merkle_multiproof(leaves, proof, indices, root)  # ty: ignore[invalid-argument-type]
        )

        return MultiproofFixture(
            type_name=self.type_name,
            value=self.value,
            serialized=to_hex(self.value.encode_bytes()),
            root=to_hex(root),
            paths=tuple(_written_path(path) for path in self.paths),
            indices=tuple(str(index) for index in indices),
            leaves=tuple(to_hex(leaf) for leaf in leaves),
            helper_indices=tuple(str(helper) for helper in helper_indices),
            proof=tuple(to_hex(node) for node in proof),
            verified=verified,
            stricter_than_spec=self.stricter_than_spec,
            rejection_reason=self.confirmed_fault(raised, verified, self.mutation is None),
        )

"""Tests for the root a value remembers between mutations.

Every mutation is checked against a second opinion rather than a pinned constant: the
same value serialized, decoded into a fresh tree, then rooted from cold.
"""

from typing import IO, Self, cast

import pytest

from ssz import merkleization
from ssz.bitfields import BitList
from ssz.boolean import Boolean
from ssz.byte_arrays import ByteList, ByteVector
from ssz.collections import List, ProgressiveList, Vector
from ssz.container import Container, ProgressiveContainer
from ssz.exceptions import SSZTypeError
from ssz.merkleization import _root_witness, hash_tree_root
from ssz.proofs import build_proof, get_generalized_index, node_root, verify_merkle_proof
from ssz.ssz_base import SSZModel
from ssz.uint import Uint8, Uint64
from ssz.union import CompatibleUnion

memo_in_force = pytest.mark.skipif(
    merkleization.PARANOID_ROOTS,
    reason="PARANOID_ROOTS recomputes every remembered root, which is the behaviour "
    "these tests observe the absence of",
)
"""Marks a test that observes the memo being reused, which paranoid mode suspends."""


class Bytes32(ByteVector):
    LENGTH = 32


class Bytes48(ByteVector):
    LENGTH = 48


class Validator(Container):
    pubkey: Bytes48
    effective_balance: Uint64
    slashed: Boolean


class Validators(List[Validator]):
    LIMIT = 8


class Balances(List[Uint64]):
    LIMIT = 8


class BlockRoots(Vector[Bytes32]):
    LENGTH = 4


class Flags(BitList):
    LIMIT = 8


class Blob(ByteList):
    LIMIT = 8


class Votes(ProgressiveList[Uint64]):
    pass


class Header(Container):
    slot: Uint64
    state_root: Bytes32


class Summary(ProgressiveContainer):
    ACTIVE_FIELDS = [1, 0, 1]
    epoch: Uint64
    root: Bytes32


class MiniState(Container):
    """One field per shape that carries a witness of its own, plus leaves around them."""

    slot: Uint64
    header: Header
    validators: Validators
    balances: Balances
    block_roots: BlockRoots
    flags: Flags
    blob: Blob
    votes: Votes
    summary: Summary


class Square(Container):
    side: Uint64


class Circle(Container):
    side: Uint64


class Shape(CompatibleUnion):
    OPTIONS = {1: Square, 2: Circle}


class Measure(CompatibleUnion):
    OPTIONS = {1: Uint64, 2: Uint64}


class Unmerkleizable(SSZModel):
    """A well-formed SSZ type that no merkleization rule knows about."""

    x: Uint64

    @classmethod
    def is_fixed_size(cls) -> bool:
        return True

    @classmethod
    def get_byte_length(cls) -> int:
        return 8

    def serialize(self, stream: IO[bytes]) -> int:
        return stream.write(self.x.encode_bytes())

    @classmethod
    def deserialize(cls, stream: IO[bytes], scope: int) -> Self:
        return cls(x=Uint64.deserialize(stream, scope))


def round_trip_root(value: SSZModel) -> object:
    """Root an equal value decoded from the bytes, so no memo is shared with the original."""
    rebuilt = type(value).decode_bytes(value.encode_bytes())
    assert rebuilt == value
    return hash_tree_root(rebuilt)


def a_state() -> MiniState:
    """A state with something in every shape, so no witness is exercised empty."""
    return MiniState(
        slot=Uint64(7),
        header=Header(slot=Uint64(7), state_root=Bytes32(b"\x01" * 32)),
        validators=Validators.of(
            Validator(pubkey=Bytes48(b"\x02" * 48)),  # ty: ignore[missing-argument]
        ),
        balances=Balances.of(Uint64(32)),
        block_roots=BlockRoots.of(*(Bytes32(bytes([i]) * 32) for i in range(4))),
        flags=Flags.of(1, 0, 1),
        blob=Blob(data=b"\xde\xad"),
        votes=Votes.of(Uint64(1), Uint64(2)),
        summary=Summary(epoch=Uint64(3), root=Bytes32(b"\x03" * 32)),
    )


MUTATIONS: list[tuple[str, object]] = [
    # A leaf field of the outermost value.
    ("slot", lambda s: setattr(s, "slot", Uint64(8))),
    # A leaf field one level down, reached through the field that holds it.
    ("nested leaf", lambda s: setattr(s.header, "slot", Uint64(8))),
    # The trap: a validator mutated in place.
    # Neither the element identities nor the list's own version change.
    # A witness that stopped at the first level would report the state as it was.
    ("nested in place", lambda s: setattr(s.validators[0], "effective_balance", Uint64(31))),
    ("nested in place again", lambda s: setattr(s.validators[0], "slashed", Boolean(1))),
    # The spec's own write-through pattern: borrow each element and assign to it.
    (
        "write through iteration",
        lambda s: [setattr(v, "slashed", Boolean(0)) for v in s.validators],
    ),
    (
        "list append",
        lambda s: s.validators.append(
            Validator(pubkey=Bytes48(b"\x04" * 48))  # ty: ignore[missing-argument]
        ),
    ),
    ("packed list append", lambda s: s.balances.append(Uint64(64))),
    ("packed element", lambda s: s.balances.__setitem__(0, Uint64(33))),
    ("vector element", lambda s: s.block_roots.__setitem__(2, Bytes32(b"\x11" * 32))),
    ("bitlist append", lambda s: s.flags.append(Boolean(1))),
    ("bit", lambda s: s.flags.__setitem__(0, Boolean(0))),
    ("bitlist pop", lambda s: s.flags.pop()),
    ("byte list append", lambda s: s.blob.append(0xAB)),
    ("byte", lambda s: s.blob.__setitem__(0, 0xCD)),
    ("byte list pop", lambda s: s.blob.pop()),
    ("progressive list append", lambda s: s.votes.append(Uint64(3))),
    ("progressive container field", lambda s: setattr(s.summary, "epoch", Uint64(4))),
    ("list pop", lambda s: s.validators.pop()),
    # Whole-field replacement, which changes the child object rather than its contents.
    (
        "field replaced",
        lambda s: setattr(s, "header", Header(slot=Uint64(9))),  # ty: ignore[missing-argument]
    ),
    (
        "collection replaced",
        lambda s: setattr(
            s,
            "validators",
            Validators.of(Validator(pubkey=Bytes48(b"\x05" * 48))),  # ty: ignore[missing-argument]
        ),
    ),
    ("slice assigned", lambda s: s.block_roots.__setitem__(slice(0, 2), [Bytes32.zero()] * 2)),
]
"""A cumulative mutation sequence, one entry per way this library can change a value."""


def test_every_mutation_reports_a_root_computed_from_cold() -> None:
    """
    Check the remembered root after every step of a mutation sequence.

    - It equals the root of the same value rebuilt from its bytes.
    - It differs from the step before, since every step changes the value.
    """
    state = a_state()
    previous = hash_tree_root(state)
    assert previous == round_trip_root(state)

    for name, mutate in MUTATIONS:
        mutate(state)  # ty: ignore[call-non-callable]
        root = hash_tree_root(state)
        assert root == round_trip_root(state), f"stale root after {name}"
        assert root != previous, f"root did not move for {name}"
        previous = root


@memo_in_force
def test_a_root_is_reused_until_the_value_changes() -> None:
    """The memo is live: an unchanged value hands back the very object it handed back."""
    state = a_state()
    first = state.hash_tree_root()
    assert state.hash_tree_root() is first

    state.validators[0].effective_balance = Uint64(31)
    second = state.hash_tree_root()
    assert second is not first
    assert state.hash_tree_root() is second


def test_a_value_mutated_back_reports_the_root_it_had_before() -> None:
    """A root follows contents, not history: the same bytes root the same way."""
    balances = Balances.of(Uint64(1), Uint64(2))
    before = balances.hash_tree_root()
    balances[0] = Uint64(99)
    assert balances.hash_tree_root() != before
    balances[0] = Uint64(1)
    assert balances.hash_tree_root() == before


def test_two_holders_of_one_child_both_see_it_change() -> None:
    """
    A child with two holders invalidates for both.

    The witness is read from the child rather than recorded by the holder.
    """
    shared = Validators.of(
        Validator(pubkey=Bytes48(b"\x06" * 48))  # ty: ignore[missing-argument]
    )
    left = MiniState(validators=shared)  # ty: ignore[missing-argument]
    right = MiniState(validators=shared)  # ty: ignore[missing-argument]
    assert left.hash_tree_root() == right.hash_tree_root()

    left_before = left.hash_tree_root()
    right.validators[0].slashed = Boolean(1)
    assert left.hash_tree_root() != left_before
    assert left.hash_tree_root() == round_trip_root(left)
    assert right.hash_tree_root() == round_trip_root(right)


def test_a_copy_carries_no_memo_of_the_value_it_came_from() -> None:
    """
    A copy starts cold, because no copying route carries a slot.

    Reading a copied version alongside diverged contents is how a stale root is served.
    """
    import copy
    import pickle

    state = a_state()
    original = state.hash_tree_root()

    for clone in (
        copy.deepcopy(state),
        state.model_copy(deep=True),
        pickle.loads(pickle.dumps(state)),
    ):
        assert clone.hash_tree_root() == original
        clone.validators[0].slashed = Boolean(1)
        assert clone.hash_tree_root() != original
        assert clone.hash_tree_root() == round_trip_root(clone)

    assert state.hash_tree_root() == original


@memo_in_force
def test_an_immutable_type_remembers_its_root_and_never_retires_it() -> None:
    """A frozen shape has one version forever, which is the cheapest memo there is."""

    class Frozen(Container):
        MUTABLE = False

        slot: Uint64

    frozen = Frozen(slot=Uint64(5))
    assert frozen.hash_tree_root() is frozen.hash_tree_root()
    with pytest.raises(SSZTypeError, match="Frozen is immutable"):
        frozen.slot = Uint64(6)


def test_a_union_holding_a_leaf_is_witnessed_through_the_leaf_constant() -> None:
    """A union declares its payload broadly, so the payload is read every time."""
    measure = Measure(selector=Uint8(1), data=Uint64(9))
    assert measure.hash_tree_root() == round_trip_root(measure)
    assert _root_witness(measure) == (0, (None,))

    shape = Shape(selector=Uint8(1), data=Square(side=Uint64(2)))
    before = shape.hash_tree_root()
    shape.data.side = Uint64(3)  # ty: ignore[unresolved-attribute]
    assert shape.hash_tree_root() != before
    assert shape.hash_tree_root() == round_trip_root(shape)


def test_a_shape_with_no_merkleization_rule_is_refused_rather_than_remembered() -> None:
    """An unknown shape gets a witness that never matches, so no root of it is reused."""
    value = Unmerkleizable(x=Uint64(1))
    assert _root_witness(value) != _root_witness(value)
    with pytest.raises(SSZTypeError, match="unsupported value type Unmerkleizable"):
        value.hash_tree_root()


def test_a_proof_and_the_root_it_verifies_against_agree_after_a_mutation() -> None:
    """
    Proofs read the same layout roots do, so the two have to move together.

    A stale memo would be self-consistent: a proof would verify against a wrong root.
    """
    state = a_state()
    index = get_generalized_index(MiniState, "validators", 0, "effective_balance")
    state.hash_tree_root()

    state.validators[0].effective_balance = Uint64(31)
    leaf = node_root(state, index)
    assert verify_merkle_proof(leaf, build_proof(state, index), index, state.hash_tree_root())
    assert state.hash_tree_root() == round_trip_root(state)


class TestParanoidRoots:
    """The mode that recomputes every remembered root and checks it."""

    def test_it_agrees_with_every_memo_across_the_whole_sequence(
        self, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """The same mutation sequence, with every hit checked against a recomputation."""
        monkeypatch.setattr(merkleization, "PARANOID_ROOTS", True)
        state = a_state()
        assert hash_tree_root(state) == round_trip_root(state)
        for name, mutate in MUTATIONS:
            mutate(state)  # ty: ignore[call-non-callable]
            assert hash_tree_root(state) == round_trip_root(state), f"stale root after {name}"

    def test_it_catches_a_root_gone_stale(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """
        The one failure no internal check can see, made visible.

        Writing straight to the contents raises no version and changes no count, so the
        witness still matches. Recomputing is what catches it.
        """
        balances = Balances.of(Uint64(1), Uint64(2))
        balances.hash_tree_root()
        # A cast, because the declared contents are a read-only sequence. Reaching past
        # that is the point of this test: it is the write no mutator sees.
        cast("list[Uint64]", balances.data)[0] = Uint64(99)

        monkeypatch.setattr(merkleization, "PARANOID_ROOTS", True)
        with pytest.raises(AssertionError, match="stale remembered root for Balances"):
            balances.hash_tree_root()


@memo_in_force
def test_writing_straight_to_data_can_leave_a_stale_root() -> None:
    """
    The residual risk, pinned rather than hidden.

    Public contents can be written without passing a mutator, which already defeats the
    element and capacity checks. The memo adds a stale root to that.

    A length change is caught by the element count in the witness.
    An element replaced in place is not.
    Paranoid mode catches both.
    """
    balances = Balances.of(Uint64(1), Uint64(2))
    remembered = balances.hash_tree_root()

    # Replaced in place: the count is the same, so the witness is the same. Stale.
    cast("list[Uint64]", balances.data)[0] = Uint64(99)
    assert balances.hash_tree_root() == remembered
    assert balances.hash_tree_root() != round_trip_root(balances)

    # Appended: the count moved, so the witness moved with it. Caught.
    cast("list[Uint64]", balances.data).append(Uint64(3))
    assert balances.hash_tree_root() != remembered
    assert balances.hash_tree_root() == round_trip_root(balances)

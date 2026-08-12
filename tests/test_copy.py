"""Tests for the copy method every SSZ type carries."""

import copy as copy_module

import pytest
from hypothesis import given, strategies as st
from pydantic import BaseModel

from ssz import (
    BitList,
    BitVector,
    Boolean,
    ByteList,
    ByteVector,
    Chunk,
    CompatibleUnion,
    Container,
    List,
    ProgressiveBitList,
    ProgressiveContainer,
    ProgressiveList,
    Root,
    SSZType,
    SSZTypeError,
    Uint8,
    Uint16,
    Uint64,
    Uint256,
    Vector,
)
from ssz.ssz_base import SSZCollection, SSZModel


class Bytes32(ByteVector):
    """A 32-byte array, the withdrawal credential and root shape."""

    LENGTH = 32


class Bytes48(ByteVector):
    """A 48-byte array, the BLS public key shape."""

    LENGTH = 48


class Validator(Container):
    """The consensus validator record: eight fields, every one of them an immutable leaf."""

    pubkey: Bytes48
    withdrawal_credentials: Bytes32
    effective_balance: Uint64
    slashed: Boolean
    activation_eligibility_epoch: Uint64
    activation_epoch: Uint64
    exit_epoch: Uint64
    withdrawable_epoch: Uint64


class ValidatorList(List[Validator]):
    """A registry of validator records, bounded well past what any test fills."""

    LIMIT = 1024


class ValidatorVector2(Vector[Validator]):
    """Two validator records, so a composite vector is covered as well as a list."""

    LENGTH = 2


class ValidatorProgressiveList(ProgressiveList[Validator]):
    """Validator records on a progressive spine, bounded by nothing."""


class Balances(List[Uint64]):
    """A list of basic elements, where every element is already its own duplicate."""

    LIMIT = 1024


class Roots(Vector[Bytes32]):
    """A run of byte arrays, so elements subclassing bytes are covered as well as ints."""

    LENGTH = 4


class TaggedBalances(Balances):
    """A list declaring a field beyond its contents, which a duplicate has to carry too."""

    tag: Uint64 = Uint64(0)


class Ledger(Container):
    """Two fields able to hold one and the same list, so a duplicate has sharing to resolve."""

    current: Balances
    previous: Balances


class Graffiti(ByteList):
    """A byte list, whose contents are bytes rather than a list of values."""

    LIMIT = 32


class Flags(BitList):
    """A bounded bitfield, whose contents are booleans in a list."""

    LIMIT = 16


class FixedFlags(BitVector):
    """A fixed bitfield, which accepts element writes but no length change."""

    LENGTH = 8


class Gapped(ProgressiveContainer):
    """A progressive layout with a cleared middle position."""

    ACTIVE_FIELDS = (1, 0, 1)

    side: Uint16
    color: Uint8


class LeadingGap(ProgressiveContainer):
    """The other layout, sharing only position 2, so the two are union-compatible."""

    ACTIVE_FIELDS = (0, 1, 1)

    radius: Uint16
    color: Uint8


class Shape(CompatibleUnion):
    """A union whose options are composites, so its payload is a model to duplicate."""

    OPTIONS = {1: Gapped, 2: LeadingGap}


class Word(Uint16):
    """A named 16-bit uint, compatible with Uint16 because it is the same width."""


class Number(CompatibleUnion):
    """A union whose options are basic types, so its payload is an immutable leaf."""

    OPTIONS = {1: Uint16, 2: Word}


class State(Container):
    """A state-shaped struct holding composites, basic elements and raw bytes."""

    slot: Uint64
    genesis_validators_root: Bytes32
    validators: ValidatorList
    balances: Balances
    graffiti: Graffiti
    flags: Flags


class FrozenList(List[Uint64]):
    """A list that refuses mutation, to pin that a duplicate of one is frozen too."""

    LIMIT = 4
    MUTABLE = False


class FrozenValidator(Validator):
    """An immutable struct, whose duplicate must be built without any field assignment."""

    MUTABLE = False


def make_validator(index: int) -> Validator:
    """One validator record, with every field distinct so a swapped leaf is visible."""
    return Validator(
        pubkey=Bytes48(bytes([index % 256]) * 48),
        withdrawal_credentials=Bytes32(bytes([(index + 1) % 256]) * 32),
        effective_balance=Uint64(32 * 10**9 + index),
        slashed=Boolean(index % 2 == 0),
        activation_eligibility_epoch=Uint64(index),
        activation_epoch=Uint64(index + 1),
        exit_epoch=Uint64(2**64 - 1),
        withdrawable_epoch=Uint64(2**64 - 2),
    )


def make_state(count: int = 8) -> State:
    """A populated state, deep enough that a shared nested list would be observable."""
    return State(
        slot=Uint64(1_000_000),
        genesis_validators_root=Bytes32(b"\x11" * 32),
        validators=ValidatorList(data=[make_validator(index) for index in range(count)]),
        balances=Balances(data=[Uint64(32 * 10**9) for _ in range(count)]),
        graffiti=Graffiti(data=b"eth-ssz-specs"),
        flags=Flags(data=[Boolean(True), Boolean(False), Boolean(True)]),
    )


IMMUTABLE_VALUES = [
    pytest.param(Uint8(0), id="uint8_zero"),
    pytest.param(Uint8(2**8 - 1), id="uint8_max"),
    pytest.param(Uint16(0x1234), id="uint16"),
    pytest.param(Uint64(2**64 - 1), id="uint64_max"),
    pytest.param(Uint256(2**256 - 1), id="uint256_max"),
    pytest.param(Word(7), id="named_uint_subtype"),
    pytest.param(Boolean(False), id="boolean_false"),
    pytest.param(Boolean(True), id="boolean_true"),
    pytest.param(Bytes32(bytes(range(32))), id="byte_vector_32"),
    pytest.param(Bytes48(bytes(range(48))), id="byte_vector_48"),
    pytest.param(Chunk(bytes(range(32))), id="chunk"),
    pytest.param(Root(bytes(range(32))), id="root"),
]
"""Every shape whose values cannot change, so each is already its own duplicate."""

MODEL_VALUES = [
    pytest.param(Validator.default(), id="container_default"),
    pytest.param(make_validator(3), id="container_populated"),
    pytest.param(ValidatorList(data=[]), id="list_of_composites_empty"),
    pytest.param(ValidatorList(data=[make_validator(1), make_validator(2)]), id="list_composites"),
    pytest.param(ValidatorVector2(data=[make_validator(1), make_validator(2)]), id="vector"),
    pytest.param(
        ValidatorProgressiveList(data=[make_validator(index) for index in range(5)]),
        id="progressive_list",
    ),
    pytest.param(Balances(data=[Uint64(1), Uint64(2)]), id="list_of_basics"),
    pytest.param(Graffiti(data=b""), id="byte_list_empty"),
    pytest.param(Graffiti(data=b"deadbeef"), id="byte_list_populated"),
    pytest.param(Flags(data=[Boolean(True), Boolean(False)]), id="bit_list"),
    pytest.param(FixedFlags(data=[Boolean(True)] + [Boolean(False)] * 7), id="bit_vector"),
    pytest.param(ProgressiveBitList(data=[Boolean(True)] * 257), id="progressive_bit_list"),
    pytest.param(Gapped(side=Uint16(0x1234), color=Uint8(0x42)), id="progressive_container"),
    pytest.param(
        Shape(selector=Uint8(1), data=Gapped(side=Uint16(9), color=Uint8(3))),
        id="union_over_composites",
    ),
    pytest.param(Number(selector=Uint8(2), data=Word(9)), id="union_over_basics"),
    pytest.param(make_state(), id="state"),
    pytest.param(FrozenValidator.default(), id="immutable_container"),
    pytest.param(FrozenList(data=[Uint64(1)]), id="immutable_list"),
]
"""Every Pydantic-backed shape, each of which owns something a duplicate must not share."""


@pytest.mark.parametrize("value", IMMUTABLE_VALUES + MODEL_VALUES)
def test_a_duplicate_holds_the_same_value(value: SSZType) -> None:
    """A duplicate holds the same value: it compares equal and roots identically."""
    duplicate = value.copy()

    assert duplicate == value
    assert duplicate.hash_tree_root() == value.hash_tree_root()
    assert duplicate.encode_bytes() == value.encode_bytes()
    assert type(duplicate) is type(value)


@pytest.mark.parametrize("value", IMMUTABLE_VALUES)
def test_an_immutable_value_is_its_own_duplicate(value: SSZType) -> None:
    """A value that cannot change hands itself back."""
    assert value.copy() is value
    assert isinstance(value, int | bytes)
    with pytest.raises(TypeError):
        value[0] = 1  # ty: ignore[invalid-assignment]


@pytest.mark.parametrize("value", MODEL_VALUES)
def test_a_model_duplicates_into_a_distinct_object(value: SSZModel) -> None:
    """A model owns writable state, so its duplicate is a second object."""
    duplicate = value.copy()

    assert duplicate is not value
    assert duplicate.__dict__ is not value.__dict__


@pytest.mark.parametrize("value", MODEL_VALUES)
def test_no_writable_object_is_shared_with_the_duplicate(value: SSZModel) -> None:
    """Structural independence, before any mutation: rebuilt lists, new models, shared leaves."""
    duplicate = value.copy()

    for name in type(value).model_fields:
        original_field = getattr(value, name)
        duplicate_field = getattr(duplicate, name)
        if isinstance(original_field, SSZModel | list):
            assert duplicate_field is not original_field
        else:
            # A uint, a boolean, a fixed byte array, or the bytes a byte list stores.
            assert duplicate_field is original_field


def test_the_leaves_of_a_validator_are_shared_rather_than_rebuilt() -> None:
    """A validator duplicates without building a single new leaf."""
    validator = make_validator(3)
    duplicate = validator.copy()

    for name in Validator.model_fields:
        assert getattr(duplicate, name) is getattr(validator, name)


def test_the_bytes_a_byte_list_holds_are_shared() -> None:
    """A byte list stores bytes, the one collection whose contents need no rebuilding."""
    graffiti = Graffiti(data=b"deadbeef")
    duplicate = graffiti.copy()

    assert duplicate.data is graffiti.data
    duplicate.append(0x21)
    assert graffiti.data == b"deadbeef"


def test_a_nested_write_to_the_duplicate_leaves_the_original_root_unchanged() -> None:
    """A write two levels down does not reach the original."""
    state = make_state()
    before = state.hash_tree_root()
    duplicate = state.copy()

    duplicate.validators[3].effective_balance = Uint64(0)

    assert state.hash_tree_root() == before
    assert state.validators[3].effective_balance == Uint64(32 * 10**9 + 3)
    assert duplicate.hash_tree_root() != before
    assert duplicate != state


def test_a_nested_write_to_the_original_leaves_the_duplicate_unchanged() -> None:
    """The converse: a write to the original does not reach the duplicate."""
    state = make_state()
    duplicate = state.copy()
    before = duplicate.hash_tree_root()

    state.validators[3].effective_balance = Uint64(0)
    state.validators.append(make_validator(99))
    state.slot = Uint64(0)

    assert duplicate.hash_tree_root() == before
    assert duplicate.validators[3].effective_balance == Uint64(32 * 10**9 + 3)
    assert len(duplicate.validators) == 8


def test_a_length_change_on_either_side_stays_on_that_side() -> None:
    """Appending and popping change the list object, so each value needs its own."""
    original = ValidatorList(data=[make_validator(1), make_validator(2)])
    duplicate = original.copy()

    duplicate.append(make_validator(3))
    original.pop()

    assert len(duplicate) == 3
    assert len(original) == 1
    assert duplicate.hash_tree_root() != original.hash_tree_root()


NESTED_WRITES = [
    pytest.param(
        make_state(),
        lambda state: state.validators[0].__setattr__("exit_epoch", Uint64(1)),
        id="container_holding_a_list_of_composites",
    ),
    pytest.param(
        make_state(),
        lambda state: state.balances.__setitem__(0, Uint64(7)),
        id="container_holding_a_list_of_basics",
    ),
    pytest.param(
        make_state(),
        lambda state: state.flags.append(Boolean(True)),
        id="container_holding_a_bitlist",
    ),
    pytest.param(
        make_state(),
        lambda state: state.graffiti.append(0x21),
        id="container_holding_a_byte_list",
    ),
    pytest.param(
        ValidatorList(data=[make_validator(1)]),
        lambda registry: registry[0].__setattr__("slashed", Boolean(True)),
        id="list_element",
    ),
    pytest.param(
        ValidatorVector2(data=[make_validator(1), make_validator(2)]),
        lambda pair: pair[1].__setattr__("slashed", Boolean(False)),
        id="vector_element",
    ),
    pytest.param(
        ValidatorProgressiveList(data=[make_validator(index) for index in range(5)]),
        lambda spine: spine[4].__setattr__("activation_epoch", Uint64(0)),
        id="progressive_list_element",
    ),
    pytest.param(
        Gapped(side=Uint16(0x1234), color=Uint8(0x42)),
        lambda gapped: gapped.__setattr__("color", Uint8(0)),
        id="progressive_container_field",
    ),
    pytest.param(
        Shape(selector=Uint8(1), data=Gapped(side=Uint16(9), color=Uint8(3))),
        lambda union: union.data.__setattr__("color", Uint8(0)),
        id="union_payload_field",
    ),
    pytest.param(
        Flags(data=[Boolean(True), Boolean(False)]),
        lambda flags: flags.__setitem__(1, Boolean(True)),
        id="bitlist_bit",
    ),
    pytest.param(
        FixedFlags(data=[Boolean(True)] + [Boolean(False)] * 7),
        lambda flags: flags.__setitem__(7, Boolean(True)),
        id="bitvector_bit",
    ),
]
"""One shape per composite family, paired with a write that must not cross the copy."""


@pytest.mark.parametrize("value, write", NESTED_WRITES)
def test_a_write_crosses_neither_way_for_any_composite_shape(
    value: SSZModel, write: object
) -> None:
    """Every composite family isolates a write, in both directions."""
    duplicate = value.copy()
    original_root = value.hash_tree_root()
    duplicate_root = duplicate.hash_tree_root()
    assert original_root == duplicate_root

    write(duplicate)  # ty: ignore[call-non-callable]
    assert value.hash_tree_root() == original_root
    assert duplicate.hash_tree_root() != duplicate_root

    second = value.copy()
    write(value)  # ty: ignore[call-non-callable]
    assert second.hash_tree_root() == original_root


def test_a_duplicate_is_independent_at_three_levels_of_nesting() -> None:
    """The recursion reaches every level, not only the top two."""
    state = make_state()
    duplicate = state.copy()

    assert duplicate.validators is not state.validators
    assert duplicate.validators.data is not state.validators.data
    assert duplicate.validators[0] is not state.validators[0]
    assert duplicate.validators[0].pubkey is state.validators[0].pubkey


def test_an_immutable_type_duplicates_and_its_duplicate_is_immutable_too() -> None:
    """A frozen value copies and stays frozen."""
    frozen = FrozenValidator.default()
    duplicate = frozen.copy()

    assert duplicate == frozen
    assert duplicate is not frozen
    with pytest.raises(SSZTypeError, match="FrozenValidator is immutable"):
        duplicate.exit_epoch = Uint64(1)

    frozen_list = FrozenList(data=[Uint64(1)])
    frozen_list_duplicate = frozen_list.copy()
    assert frozen_list_duplicate.data is not frozen_list.data
    with pytest.raises(SSZTypeError, match="FrozenList is immutable"):
        frozen_list_duplicate[0] = Uint64(2)


def test_a_duplicate_keeps_the_fields_that_were_explicitly_passed() -> None:
    """Which fields were passed and which defaulted travels with the duplicate."""
    validator = Validator(effective_balance=Uint64(7))  # ty: ignore[missing-argument]
    duplicate = validator.copy()

    assert duplicate.model_fields_set == {"effective_balance"}
    assert duplicate.model_dump(exclude_unset=True).keys() == {"effective_balance"}


@pytest.mark.parametrize("value", IMMUTABLE_VALUES)
def test_the_copy_module_hands_back_an_immutable_value_itself(value: SSZType) -> None:
    """A leaf answers the copy module with itself, where the stdlib would rebuild it."""
    assert copy_module.copy(value) is value
    assert copy_module.deepcopy(value) is value


def test_the_copy_module_keeps_its_own_semantics_for_a_model() -> None:
    """A model keeps Pydantic's copies, so the copy module answers as a reader expects."""
    assert State.__mro__.index(BaseModel) < State.__mro__.index(SSZType)

    state = make_state()

    shallow = copy_module.copy(state)
    assert shallow.validators is state.validators

    deep = copy_module.deepcopy(state)
    assert deep.validators[0] is not state.validators[0]
    assert deep.hash_tree_root() == state.hash_tree_root()
    deep.validators[0].exit_epoch = Uint64(1)
    assert state.validators[0].exit_epoch == Uint64(2**64 - 1)


def test_two_fields_holding_one_value_duplicate_into_two() -> None:
    """A duplicate resolves sharing inside the original rather than reproducing it."""
    shared = make_validator(1)
    registry = ValidatorList(data=[shared, shared])
    assert registry[0] is registry[1]

    duplicate = registry.copy()
    assert duplicate[0] is not duplicate[1]
    assert duplicate.hash_tree_root() == registry.hash_tree_root()

    duplicate[0].exit_epoch = Uint64(1)
    assert duplicate[1].exit_epoch == Uint64(2**64 - 1)

    memo_honest = copy_module.deepcopy(registry)
    assert memo_honest[0] is memo_honest[1]
    assert memo_honest[0] is not shared


DEEP_COPIED_SEQUENCES = [
    pytest.param(
        Balances(data=[Uint64(32 * 10**9 + index) for index in range(4)]),
        lambda balances: balances.append(Uint64(1)),
        id="list_of_uints",
    ),
    pytest.param(
        Roots(data=[Bytes32(bytes([index + 1]) * 32) for index in range(4)]),
        lambda roots: roots.__setitem__(0, Bytes32(bytes(32))),
        id="vector_of_byte_arrays",
    ),
]


@pytest.mark.parametrize("value, write", DEEP_COPIED_SEQUENCES)
def test_a_deep_copy_rebuilds_the_sequence_around_the_elements_it_already_holds(
    value: SSZCollection[SSZType], write: object
) -> None:
    duplicate = copy_module.deepcopy(value)
    before = value.hash_tree_root()

    assert duplicate == value
    assert type(duplicate) is type(value)
    assert duplicate.encode_bytes() == value.encode_bytes()
    assert duplicate.data is not value.data
    for original_element, duplicate_element in zip(value.data, duplicate.data, strict=True):
        assert duplicate_element is original_element

    write(duplicate)  # ty: ignore[call-non-callable]
    assert value.hash_tree_root() == before
    assert duplicate.hash_tree_root() != before


def test_a_list_reachable_twice_deep_copies_into_one_object() -> None:
    shared = Balances(data=[Uint64(1), Uint64(2)])
    ledger = Ledger(current=shared, previous=shared)
    assert ledger.current is ledger.previous

    duplicate = copy_module.deepcopy(ledger)

    assert duplicate.current is duplicate.previous
    assert duplicate.current is not shared
    duplicate.current.append(Uint64(3))
    assert len(duplicate.previous) == 3
    assert len(shared) == 2


def test_a_sequence_declaring_more_than_its_contents_deep_copies_every_field() -> None:
    """The extra field travels with the duplicate instead of reverting to its default."""
    tagged = TaggedBalances(data=[Uint64(1), Uint64(2)], tag=Uint64(7))

    duplicate = copy_module.deepcopy(tagged)

    assert duplicate.tag == Uint64(7)
    assert duplicate.data is not tagged.data
    duplicate.append(Uint64(3))
    assert len(tagged) == 2


def test_a_deep_copy_carries_its_own_record_of_which_fields_were_passed() -> None:
    empty = Balances()

    duplicate = copy_module.deepcopy(empty)

    assert duplicate.model_fields_set == set()
    assert duplicate.model_dump(exclude_unset=True) == {}

    duplicate.data = [Uint64(1)]
    assert duplicate.model_fields_set == {"data"}
    assert empty.model_fields_set == set()


MODEL_COPIED_SEQUENCES = [
    pytest.param(Balances(data=[Uint64(1), Uint64(2)]), id="list_of_uints"),
    pytest.param(
        Roots(data=[Bytes32(bytes([index + 1]) * 32) for index in range(4)]),
        id="vector_of_byte_arrays",
    ),
    pytest.param(
        ValidatorList(data=[make_validator(1), make_validator(2)]), id="list_of_composites"
    ),
]
"""Every sequence shape Pydantic's deep copy has to answer, fast path or not."""


@pytest.mark.parametrize("value", MODEL_COPIED_SEQUENCES)
def test_pydantics_deep_model_copy_answers_a_sequence_with_an_independent_one(
    value: SSZCollection[SSZType],
) -> None:
    """Pydantic asks for a deep copy with no memo."""
    duplicate = value.model_copy(deep=True)

    assert duplicate == value
    assert type(duplicate) is type(value)
    assert duplicate.data is not value.data
    for original_element, duplicate_element in zip(value.data, duplicate.data, strict=True):
        if isinstance(original_element, SSZModel):
            assert duplicate_element is not original_element
        else:
            assert duplicate_element is original_element


@given(counts=st.lists(st.integers(min_value=0, max_value=22), min_size=1, max_size=3))
def test_a_registry_of_any_length_duplicates_independently(counts: list[int]) -> None:
    """Independence holds at every element count, across two progressive spine levels."""
    for count in counts:
        registry = ValidatorProgressiveList(data=[make_validator(index) for index in range(count)])
        before = registry.hash_tree_root()
        duplicate = registry.copy()

        duplicate.append(make_validator(count))

        assert registry.hash_tree_root() == before
        assert len(registry) == count
        assert len(duplicate) == count + 1

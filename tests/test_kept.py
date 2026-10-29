"""Roots the native backend keeps current, against the specification's, mutation by mutation."""

from __future__ import annotations

import random
from collections.abc import Callable, Generator
from contextlib import contextmanager
from typing import Any

import pytest

from ssz import (
    BitList,
    Boolean,
    ByteList,
    ByteVector,
    CompatibleUnion,
    Container,
    List,
    ProgressiveContainer,
    ProgressiveList,
    Uint8,
    Uint16,
    Uint32,
    Uint64,
    Uint128,
    Vector,
    hash_tree_root,
    native,
)
from ssz.lazy import UNREAD, LazyElements

pytestmark = pytest.mark.skipif(
    not native.available(), reason="the native routines do not run here"
)


class Bytes32(ByteVector):
    """Thirty-two opaque bytes."""

    LENGTH = 32


class Bytes48(ByteVector):
    """Forty-eight opaque bytes, wider than one chunk."""

    LENGTH = 48


class Flags(BitList):
    """A few flags."""

    LIMIT = 12


class Item(Container):
    """A record with a wide key and a bitfield inside."""

    amount: Uint64
    key: Bytes48
    flags: Flags
    live: Boolean


class Items(List[Item]):
    """Records, under a bound that a long run reaches."""

    LIMIT = 40


class Numbers(List[Uint64]):
    """Integers, four to a chunk."""

    LIMIT = 300


class Small(List[Uint8]):
    """Bytes as integers, thirty-two to a chunk."""

    LIMIT = 70


class Switches(List[Boolean]):
    """Booleans, a byte each."""

    LIMIT = 70


class Scores(Vector[Uint32]):
    """A fixed run of integers, eight to a chunk."""

    LENGTH = 9


class Roots(Vector[Bytes32]):
    """A fixed run of roots."""

    LENGTH = 5


class Grid(Vector[Item]):
    """A fixed run of records."""

    LENGTH = 3


class Note(ByteList):
    """A short note."""

    LIMIT = 50


class Growing(ProgressiveList[Uint16]):
    """Integers under a spine that grows."""


class Sparse(ProgressiveContainer):
    """A struct with a gap in its layout."""

    ACTIVE_FIELDS = (1, 0, 1)

    first: Uint64
    item: Item


class Either(CompatibleUnion):
    """A record behind a selector."""

    OPTIONS = {1: Item}


class State(Container):
    """Every shape the backend keeps a root for, nested."""

    slot: Uint64
    items: Items
    numbers: Numbers
    small: Small
    switches: Switches
    scores: Scores
    roots: Roots
    grid: Grid
    inner: Item
    note: Note
    growing: Growing
    sparse: Sparse
    either: Either


@contextmanager
def backend_on(on: bool) -> Generator[None]:
    """Run a block with the native backend on or off, restoring what was there before."""
    was = native.enabled()
    native.enable() if on else native.disable()
    try:
        yield
    finally:
        native.enable() if was else native.disable()


def _item(rng: random.Random) -> Item:
    """A random record."""
    return Item(
        amount=Uint64(rng.randrange(2**64)),
        key=Bytes48(rng.randbytes(48)),
        flags=Flags(data=[rng.random() < 0.5 for _ in range(rng.randrange(13))]),
        live=Boolean(rng.random() < 0.5),
    )


def _state(rng: random.Random) -> State:
    """A random state."""
    return State(
        slot=Uint64(rng.randrange(2**64)),
        items=Items(data=[_item(rng) for _ in range(rng.randrange(6))]),
        numbers=Numbers(data=[Uint64(rng.randrange(2**64)) for _ in range(rng.randrange(30))]),
        small=Small(data=[Uint8(rng.randrange(256)) for _ in range(rng.randrange(40))]),
        switches=Switches(data=[Boolean(rng.random() < 0.5) for _ in range(rng.randrange(40))]),
        scores=Scores(data=[Uint32(rng.randrange(2**32)) for _ in range(9)]),
        roots=Roots(data=[Bytes32(rng.randbytes(32)) for _ in range(5)]),
        grid=Grid(data=[_item(rng) for _ in range(3)]),
        inner=_item(rng),
        note=Note(data=rng.randbytes(rng.randrange(51))),
        growing=Growing(data=[Uint16(rng.randrange(2**16)) for _ in range(rng.randrange(30))]),
        sparse=Sparse(first=Uint64(rng.randrange(9)), item=_item(rng)),
        either=Either(selector=Uint8(1), data=_item(rng)),
    )


type Step = Callable[[State], Any]


def _steps(rng: random.Random) -> list[Step]:
    """
    Mutations drawn once, each applied alike to two values.

    A position may be out of range and a value past its bound, so refusals are drawn too.
    """
    item, other = _item(rng), _item(rng)
    i, j = rng.randrange(-2, 8), rng.randrange(8)
    word = rng.randrange(2**64 + 2)
    raw = rng.randbytes(48)
    count = rng.randrange(1, 90)
    steps: list[Step] = [
        lambda s: setattr(s, "slot", Uint64(word % 2**64)),
        lambda s: s.items.append(item.copy()),
        lambda s: s.items.pop(),
        lambda s: s.items.__setitem__(i, other.copy()),
        lambda s: setattr(s.items[i], "amount", Uint64(word % 2**64)),
        lambda s: setattr(s.items[i], "key", Bytes48(raw)),
        lambda s: s.items[i].flags.append(Boolean(word & 1)),
        lambda s: s.items[i].flags.pop(),
        # One record at two positions, then written through one of them.
        lambda s: s.items.__setitem__(j, s.items[i]),
        lambda s: setattr(s, "inner", s.items[i]),
        lambda s: setattr(s.inner, "amount", Uint64(word % 2**64)),
        lambda s: setattr(s.grid[i % 3], "live", Boolean(word & 1)),
        lambda s: s.grid.__setitem__(i % 3, s.inner),
        lambda s: s.numbers.append(Uint64(word)),
        lambda s: s.numbers.pop(),
        lambda s: s.numbers.__setitem__(i, Uint64(word)),
        lambda s: s.numbers.__setitem__(slice(i % 5, j), [Uint64(n) for n in range(count % 7)]),
        lambda s: [s.numbers.append(Uint64(n)) for n in range(count)],
        lambda s: [s.small.append(Uint8(n % 256)) for n in range(count % 40)],
        lambda s: s.small.__setitem__(i, Uint8(word % 256)),
        lambda s: s.small.__setitem__(slice(j, i, -1), [Uint8(n) for n in range(count % 4)]),
        lambda s: s.switches.append(Boolean(word & 1)),
        lambda s: s.switches.pop(),
        lambda s: s.switches.__setitem__(i, Boolean(word & 1)),
        lambda s: s.scores.__setitem__(i, Uint32(word % 2**32)),
        lambda s: s.scores.__setitem__(i, s.scores[j % 9] + 1),
        lambda s: s.roots.__setitem__(i, Bytes32(raw[:32])),
        lambda s: setattr(s.note, "data", raw[: count % 51]),
        lambda s: s.note.append(word % 256),
        lambda s: s.growing.append(Uint16(word % 2**16)),
        lambda s: setattr(s.sparse.item, "amount", Uint64(word % 2**64)),
        lambda s: setattr(s.sparse, "item", s.items[i]),
        lambda s: setattr(s, "either", Either(selector=Uint8(1), data=other.copy())),
        lambda s: setattr(s.either.data, "amount", Uint64(word % 2**64)),
        lambda s: setattr(s, "items", Items(data=[item.copy() for _ in range(count % 9)])),
        lambda s: setattr(s, "items", s.items.copy()),
    ]
    return steps


def _apply(step: Step, state: State) -> str | None:
    """Apply a step, answering with the refusal it raised, if any, by type and message."""
    try:
        step(state)
    except Exception as refusal:  # noqa: BLE001 - every refusal is compared, whatever it is
        return f"{type(refusal).__name__}: {refusal}"
    return None


def _observe(state: State, on: bool) -> tuple[object, ...]:
    """The roots of the state and of its parts, and its encoding, from one backend."""
    with backend_on(on):
        parts = (
            *(state, state.items, state.numbers, state.inner, state.grid, state.sparse),
            *(state.small, state.switches, state.scores),
        )
        return (*(bytes(hash_tree_root(part)) for part in parts), state.encode_bytes())


@pytest.mark.parametrize("decoded", [False, True], ids=["built", "decoded"])
@pytest.mark.parametrize("seed", range(12))
def test_kept_roots_follow_every_mutation(
    seed: int, decoded: bool, monkeypatch: pytest.MonkeyPatch
) -> None:
    # Two equal states, one rooted by the native backend and one by the specification.
    # Decoded, the native one holds every sequence lazily over its encoding.
    # The module is named, not imported, since it loads the routines on import.
    monkeypatch.setattr("ssz.stored.LAZY_ELEMENTS", 1)
    rng = random.Random(seed)
    built = _state(rng)
    if decoded:
        encoding = built.encode_bytes()
        with backend_on(True):
            kept = State.decode_bytes(encoding)
        with backend_on(False):
            specified = State.decode_bytes(encoding)
        # Integers and booleans are built at once, and anything else is read on first use.
        assert type(kept.numbers.data) is list and type(kept.scores.data) is list
        assert type(kept.items.data) is LazyElements or not kept.items
    else:
        kept, specified = built.copy(), built.copy()
    for _ in range(150):
        steps = _steps(rng)
        step = steps[rng.randrange(len(steps))]
        assert _apply(step, kept) == _apply(step, specified)
        # A copy taken now must stay apart from the value it came from.
        if rng.random() < 0.1:
            kept, specified = kept.copy(), specified.copy()
        if rng.random() < 0.6:
            assert _observe(kept, True) == _observe(specified, False)
        # Equality reads the elements, whichever way each value holds them.
        if rng.random() < 0.1:
            assert kept == specified
    assert _observe(kept, True) == _observe(specified, False)


def test_a_child_held_by_two_parents_tells_both() -> None:
    # One record in two lists, rooted through both, then written once.
    rng = random.Random(99)
    shared = _item(rng)
    first, second = Items(data=[shared]), Items(data=[_item(rng), shared])
    with backend_on(True):
        before = (bytes(hash_tree_root(first)), bytes(hash_tree_root(second)))
        shared.amount = Uint64(7)
        after = (bytes(hash_tree_root(first)), bytes(hash_tree_root(second)))
    with backend_on(False):
        want = (bytes(hash_tree_root(first)), bytes(hash_tree_root(second)))
    assert after == want
    assert before[0] != after[0] and before[1] != after[1]


def test_a_mutation_with_the_backend_off_still_reaches_a_kept_root() -> None:
    # A root kept, the backend turned off for one write, then on again.
    rng = random.Random(5)
    state = _state(rng)
    with backend_on(True):
        hash_tree_root(state)
    with backend_on(False):
        state.inner.amount = Uint64(12345)
        want = bytes(hash_tree_root(state))
    with backend_on(True):
        assert bytes(hash_tree_root(state)) == want


def test_many_structs_rooted_together_root_as_the_specification_does() -> None:
    # Enough records to be rooted a field at a time, some holding what their fields do not declare.
    rng = random.Random(17)
    records = [_item(rng) for _ in range(35)]
    records[3] = Item.model_construct(
        amount=Uint16(5), key=Bytes32(rng.randbytes(32)), flags=Flags(), live=Boolean(True)
    )
    records[9] = Item.model_construct(
        amount=Uint64(1), key=bytes(70), flags=_item(rng), live=Boolean(False)
    )
    with backend_on(False):
        want = [bytes(hash_tree_root(Items.model_construct(data=records[:n]))) for n in (16, 35)]
    with backend_on(True):
        got = [bytes(hash_tree_root(Items.model_construct(data=records[:n]))) for n in (16, 35)]
        # Each record keeps its root, and hears of a write through the struct that holds it.
        whole = Items.model_construct(data=records)
        hash_tree_root(whole)
        records[20].flags.append(Boolean(True))
        records[9].flags.amount = Uint64(3)  # ty: ignore[unresolved-attribute]
        changed = bytes(hash_tree_root(whole))
    with backend_on(False):
        assert changed == bytes(hash_tree_root(Items.model_construct(data=records)))
    assert got == want


def test_a_copy_hears_of_writes_to_its_own_parts_and_not_the_original() -> None:
    # A state rooted, copied, then written at every depth through the copy alone.
    rng = random.Random(23)
    original = _state(rng)
    for _ in range(20):
        original.items.append(_item(rng))
    with backend_on(True):
        before = bytes(hash_tree_root(original))
        duplicate = original.copy()
        assert bytes(hash_tree_root(duplicate)) == before
        duplicate.items[17].amount = Uint64(1)
        duplicate.grid[1].flags.append(Boolean(True))
        duplicate.inner.live = Boolean(not duplicate.inner.live)
        duplicate.numbers.append(Uint64(2))
        duplicate.sparse.item.amount = Uint64(3)
        got = bytes(hash_tree_root(duplicate))
        assert bytes(hash_tree_root(original)) == before
    with backend_on(False):
        assert got == bytes(hash_tree_root(duplicate))
        assert before == bytes(hash_tree_root(original))


def test_many_changed_structs_are_rooted_together_as_the_specification_roots_them() -> None:
    # A rooted list of records, then enough of them replaced to be rooted again together.
    rng = random.Random(29)
    records = Items(data=[_item(rng) for _ in range(40)])
    replaced = rng.sample(range(40), 25)
    with backend_on(True):
        hash_tree_root(records)
        for position in replaced:
            records[position] = _item(rng)
        changed = bytes(hash_tree_root(records))
        kept_roots = [bytes(hash_tree_root(record)) for record in records]
        # A record rooted together with the rest still tells the list of a later write.
        records[replaced[0]].live = Boolean(not records[replaced[0]].live)
        again = bytes(hash_tree_root(records))
    with backend_on(False):
        want = bytes(hash_tree_root(records))
        records[replaced[0]].live = Boolean(not records[replaced[0]].live)
        assert changed == bytes(hash_tree_root(records))
        assert kept_roots == [bytes(hash_tree_root(record)) for record in records]
    assert again == want


def _rooted(make: Callable[[], Any], on: bool) -> str | bytes:
    """A fresh value's root from one backend, or the refusal it raised, by type and message."""
    with backend_on(on):
        try:
            return bytes(hash_tree_root(make()))
        except Exception as refusal:  # noqa: BLE001 - every refusal is compared, whatever it is
            return f"{type(refusal).__name__}: {refusal}"


class Header(Container):
    """A record of a word and a root, with no composite inside."""

    slot: Uint64
    root: Bytes32


class Headers(List[Header]):
    """Records of root-wide fields, enough of them to be rooted a field at a time."""

    LIMIT = 64


class Keys(List[Bytes48]):
    """Values wider than a chunk, each its own small tree."""

    LIMIT = 64


def _header(rng: random.Random) -> Header:
    """A random record."""
    return Header(slot=Uint64(rng.randrange(2**64)), root=Bytes32(rng.randbytes(32)))


class Endless(Vector[Uint64]):
    """A vector whose tree is deeper than the routines' own depths."""

    LENGTH = 2**70


def test_values_built_past_validation_root_or_refuse_as_the_specification_does() -> None:
    # Short vectors, a list one past its bound, and a struct holding a bare integer.
    # The deep vector climbs past the routines' depths with no length to mix in.
    rng = random.Random(31)
    roots = [Bytes32(rng.randbytes(32)) for _ in range(3)]
    items = [_item(rng) for _ in range(41)]
    cases: list[Callable[[], Any]] = [
        lambda: Roots.model_construct(data=list(roots)),
        lambda: Endless.model_construct(data=[Uint64(n) for n in range(3)]),
        lambda: Items.model_construct(data=[item.copy() for item in items]),
        lambda: Item.model_construct(amount=5, key=Bytes48(bytes(48)), flags=Flags(), live=True),
    ]
    for make in cases:
        assert _rooted(make, True) == _rooted(make, False)


def test_many_values_of_one_class_root_as_the_specification_does() -> None:
    # Records with a root-wide field, and wide byte vectors, each more than a batch.
    rng = random.Random(37)
    headers = [_header(rng) for _ in range(20)]
    keys = [Bytes48(rng.randbytes(48)) for _ in range(20)]
    cases: list[Callable[[], Any]] = [
        lambda: Headers(data=[header.copy() for header in headers]),
        lambda: Keys(data=list(keys)),
    ]
    for make in cases:
        assert _rooted(make, True) == _rooted(make, False)


def test_many_writes_between_roots_root_as_the_specification_does() -> None:
    # More writes than a batch, to values that are not structs, rehash only what changed.
    rng = random.Random(53)
    keys = Keys(data=[Bytes48(rng.randbytes(48)) for _ in range(40)])
    with backend_on(True):
        hash_tree_root(keys)
        for position in range(0, 40, 2):
            keys[position] = Bytes48(rng.randbytes(48))
        got = bytes(hash_tree_root(keys))
    with backend_on(False):
        assert got == bytes(hash_tree_root(keys.copy()))


def test_an_element_added_and_removed_before_the_next_root_changes_nothing() -> None:
    # The position written lies past the tree, and the count is back where the tree left it.
    rng = random.Random(41)
    numbers = Numbers(data=[Uint64(n) for n in range(16)])
    items = Items(data=[_item(rng) for _ in range(4)])
    with backend_on(True):
        before = (bytes(hash_tree_root(numbers)), bytes(hash_tree_root(items)))
        numbers.append(Uint64(99))
        numbers.pop()
        items.append(_item(rng))
        items.pop()
        assert (bytes(hash_tree_root(numbers)), bytes(hash_tree_root(items))) == before


def test_an_element_read_after_its_list_is_rooted_hears_of_its_writes(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Decoded lazily and rooted, then an element read for the first time and written.
    monkeypatch.setattr("ssz.stored.LAZY_ELEMENTS", 1)
    rng = random.Random(43)
    encoding = Headers(data=[_header(rng) for _ in range(10)]).encode_bytes()
    with backend_on(True):
        headers = Headers.decode_bytes(encoding)
        hash_tree_root(headers)
        headers[3].slot = Uint64(7)
        got = bytes(hash_tree_root(headers))
    with backend_on(False):
        want = Headers.decode_bytes(encoding)
        want[3].slot = Uint64(7)
        assert got == bytes(hash_tree_root(want))


def test_an_untouched_decode_encodes_to_its_input_reading_no_element(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr("ssz.stored.LAZY_ELEMENTS", 1)
    rng = random.Random(59)
    encoding = Keys(data=[Bytes48(rng.randbytes(48)) for _ in range(30)]).encode_bytes()
    with backend_on(True):
        keys = Keys.decode_bytes(encoding)
    assert keys.encode_bytes() == encoding
    assert all(item is UNREAD for item in keys.data.items)  # ty: ignore[unresolved-attribute]


def test_a_copy_roots_afresh_a_part_placed_past_every_mutator() -> None:
    # A part swapped in behind the backend's back keeps no root, so the copy cannot trust its own.
    rng = random.Random(47)
    items = Items(data=[_item(rng) for _ in range(3)])
    state = _state(rng)
    with backend_on(True):
        hash_tree_root(items)
        hash_tree_root(state)
        items.__dict__["data"][1] = _item(rng)
        state.__dict__["inner"] = _item(rng)
        got = [bytes(hash_tree_root(value.copy())) for value in (items, state)]
    with backend_on(False):
        assert got == [bytes(hash_tree_root(value.copy())) for value in (items, state)]


class Gwei(Uint64):
    """A named integer, which every element read must come back as."""


class Balances(List[Gwei]):
    """Named integers, four to a chunk."""

    LIMIT = 300


class Halves(List[Uint16]):
    """Integers, sixteen to a chunk."""

    LIMIT = 300


class Wides(List[Uint128]):
    """Integers wider than a word, which are read on first use instead."""

    LIMIT = 300


class Words(Vector[Uint64]):
    """A fixed run of integers."""

    LENGTH = 70


@pytest.mark.parametrize(
    ("shape", "make"),
    [
        (Small, lambda n: Uint8(n % 256)),
        (Switches, lambda n: Boolean(n % 3 == 0)),
        (Halves, lambda n: Uint16(n * 977 % 2**16)),
        (Scores, lambda n: Uint32(n * 2**27 % 2**32)),
        (Balances, lambda n: Gwei(n * 2**57 % 2**64)),
        (Words, lambda n: Uint64(n % 300)),
    ],
)
def test_integers_and_booleans_decode_to_the_elements_the_specification_builds(
    shape: type[List[Any]], make: Callable[[int], Any]
) -> None:
    # Built at once into a plain list, each element of its declared class and shared where small.
    count = shape.LENGTH or 66
    encoding = shape(data=[make(n) for n in range(count)]).encode_bytes()
    with backend_on(False):
        want = shape.decode_bytes(encoding)
    with backend_on(True):
        got = shape.decode_bytes(encoding)
        assert type(got.data) is list
        assert [type(element) for element in got] == [type(element) for element in want]
        assert got == want and got.encode_bytes() == encoding
        assert all(a is b for a, b in zip(got, want, strict=True) if int(a) < 256)
        assert bytes(hash_tree_root(got)) == bytes(hash_tree_root(want))


def test_integers_wider_than_a_word_are_still_read_on_first_use() -> None:
    encoding = Wides(data=[Uint128(n * 2**100) for n in range(70)]).encode_bytes()
    with backend_on(True):
        wides = Wides.decode_bytes(encoding)
        assert type(wides.data) is LazyElements
        assert wides[3] == Uint128(3 * 2**100)
        # Rooted from the encoding, the one element written since rooted from its value.
        wides[5] = Uint128(1)
        got = bytes(hash_tree_root(wides))
    with backend_on(False):
        assert got == bytes(hash_tree_root(wides.copy()))


@pytest.mark.parametrize(
    "write",
    [
        pytest.param(lambda headers: headers.pop(), id="pop"),
        pytest.param(lambda headers: headers.__setitem__(slice(0, 2), headers[:2]), id="range"),
    ],
)
def test_an_element_read_by_the_write_that_moves_it_roots_from_its_value(
    write: Callable[[Headers], Any], monkeypatch: pytest.MonkeyPatch
) -> None:
    # A rooted lazy list whose write itself reads elements the tree no longer stands for.
    monkeypatch.setattr("ssz.stored.LAZY_ELEMENTS", 1)
    rng = random.Random(61)
    encoding = Headers(data=[_header(rng) for _ in range(10)]).encode_bytes()
    with backend_on(True):
        headers = Headers.decode_bytes(encoding)
        hash_tree_root(headers)
        write(headers)
        got = bytes(hash_tree_root(headers))
    with backend_on(False):
        assert got == bytes(hash_tree_root(headers.copy()))


def test_writes_over_most_of_a_list_of_integers_root_as_the_specification_does() -> None:
    # Every position written, which repacks the whole leaf level rather than chunk by chunk.
    encoding = Balances(data=[Gwei(n) for n in range(250)]).encode_bytes()
    with backend_on(True):
        balances = Balances.decode_bytes(encoding)
        hash_tree_root(balances)
        for position in range(len(balances)):
            balances[position] = balances[position] + 7
        got = bytes(hash_tree_root(balances))
    with backend_on(False):
        assert got == bytes(hash_tree_root(balances.copy()))

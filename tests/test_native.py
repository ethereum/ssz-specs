"""The native backend against the specification, wherever the backend runs."""

from __future__ import annotations

import ctypes
import gc
import hashlib
import platform
import random
import threading
import weakref
from collections.abc import Generator
from contextlib import contextmanager
from pathlib import Path

import pytest

from ssz import (
    BitList,
    BitVector,
    Boolean,
    ByteList,
    ByteVector,
    Container,
    List,
    ProgressiveContainer,
    SSZType,
    Uint16,
    Uint64,
    Vector,
    backend,
    native,
)
from ssz.exceptions import SSZValueError
from ssz.gindex import get_helper_indices
from ssz.trees import merkleize
from ssz.verification import verify_merkle_multiproof, verify_merkle_proof

pytestmark = pytest.mark.skipif(
    not native.available(), reason="the native routines do not run here"
)


@contextmanager
def backend_on(on: bool) -> Generator[None]:
    """Run a block with the native backend on or off, restoring what was there before."""
    was = native.enabled()
    native.enable() if on else native.disable()
    try:
        yield
    finally:
        native.enable() if was else native.disable()


@pytest.fixture
def fresh_library() -> Generator[None]:
    """Forget the loaded routines around a test, so it loads them under its own conditions."""
    native._library.cache_clear()
    yield
    native._library.cache_clear()


def _assembly() -> Path:
    """The printed routines this checkout assembles."""
    return next(path for path in native._ASSEMBLIES if path.exists())


def test_the_routines_are_assembled_once_into_an_empty_cache(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    # A cache of its own, so the routines are assembled here rather than found.
    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path))
    library = native._build(_assembly())
    # The partial file was moved into place, leaving the library alone.
    assert list((tmp_path / "eth-ssz-specs").iterdir()) == [library]
    # Found the second time, so no compiler is needed.
    monkeypatch.setenv("CC", str(tmp_path / "no-compiler"))
    assert native._build(_assembly()) == library


def test_assembling_without_a_compiler_is_refused(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path))
    monkeypatch.setenv("CC", str(tmp_path / "no-compiler"))
    with pytest.raises(OSError, match="no C compiler"):
        native._build(_assembly())


@pytest.mark.usefixtures("fresh_library")
def test_an_explicit_library_is_loaded_rather_than_assembled(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    # With no printed routines to assemble, only the named library can load.
    library = native._build(_assembly())
    monkeypatch.setattr(native, "_ASSEMBLIES", ())
    monkeypatch.setenv("SSZ_NATIVE_LIB", str(library))
    assert native.available()
    # A name that loads nothing leaves the backend unavailable.
    native._library.cache_clear()
    monkeypatch.setenv("SSZ_NATIVE_LIB", str(tmp_path / "missing.so"))
    assert not native.available()


@pytest.mark.usefixtures("fresh_library")
def test_without_the_printed_routines_the_backend_is_unavailable(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.delenv("SSZ_NATIVE_LIB", raising=False)
    monkeypatch.setattr(native, "_ASSEMBLIES", ())
    assert not native.available()


def test_other_processors_are_unavailable(monkeypatch: pytest.MonkeyPatch) -> None:
    # The routines are x86-64 code, so another processor never loads them.
    monkeypatch.setattr(platform, "machine", lambda: "arm64")
    assert not native.available()


def test_windows_is_unavailable(monkeypatch: pytest.MonkeyPatch) -> None:
    # Windows calls functions under another convention than the routines keep.
    monkeypatch.setattr(platform, "system", lambda: "Windows")
    assert not native.available()


@pytest.mark.usefixtures("fresh_library")
def test_a_processor_with_only_the_baseline_kernel_hashes_as_the_specification(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Detection answering no feature stands for a processor with only the baseline kernel.
    class Baseline(ctypes.CDLL):
        """The routines, on a processor that offers no kernel family past the baseline."""

        ssz_cpu_features = staticmethod(lambda: 0)

    # The expected root comes before the swap, from the specification or the full kernel set.
    chunks = random.Random(5).randbytes(32 * 37)
    want = merkleize([chunks[i : i + 32] for i in range(0, len(chunks), 32)], limit=64)
    monkeypatch.setattr(ctypes, "CDLL", Baseline)
    # Buffers made now carry the empty feature mask, so every hash goes to the baseline kernel.
    native._scratch.cache_clear()
    try:
        assert native.available()
        assert native.merkleize(chunks, 6) == bytes(want)
    finally:
        # Later tests get buffers with the real feature mask.
        native._scratch.cache_clear()


def test_trees_keep_their_context_words_after_the_buffers_are_replaced() -> None:
    # The incremental trees read a thread's context words through their address.
    # A fresh thread makes fresh buffers, so its trees take the words made there.
    # The trees load the routines on import, so they come in only where the routines run.
    from ssz import kept

    outcome: list[tuple[bool, bytes]] = []

    def run() -> None:
        assert kept._BUFFERS.words
        words = weakref.ref(native._context()[0])
        # Dropping the cached buffers must not free the words the trees still read.
        native._scratch.cache_clear()
        gc.collect()
        outcome.append((words() is not None, kept._merkleize(chunks, 8)))

    chunks = random.Random(7).randbytes(32 * 8)
    want = merkleize([chunks[i : i + 32] for i in range(0, len(chunks), 32)], limit=8)
    worker = threading.Thread(target=run)
    worker.start()
    worker.join()
    assert outcome == [(True, bytes(want))]


def test_enabling_where_the_routines_cannot_run_changes_nothing(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    was = native.enabled()
    monkeypatch.setattr(native, "available", lambda: False)
    assert native.enable() is False
    assert native.enabled() == was


def _tree(leaves: list[bytes]) -> list[bytes]:
    """A perfect tree as a heap: node i has children 2i and 2i + 1, the leaves last."""
    nodes = [b""] * len(leaves) + leaves
    for i in range(len(leaves) - 1, 0, -1):
        nodes[i] = hashlib.sha256(nodes[2 * i] + nodes[2 * i + 1]).digest()
    return nodes


@pytest.mark.parametrize("count", [0, 1, 2, 3, 31, 1000])
def test_merkleize_matches_the_specification(count: int) -> None:
    # Random chunks under a capacity with room above them.
    rng = random.Random(count)
    chunks = [rng.randbytes(32) for _ in range(count)]
    limit = 1 << (max(count - 1, 0).bit_length() + 2)
    assert native.merkleize(b"".join(chunks), limit.bit_length() - 1) == bytes(
        merkleize(chunks, limit)
    )


def test_branches_verify_as_the_specification_says() -> None:
    # A tree of 64 leaves, with every leaf's branch, then the same with one tampered node.
    rng = random.Random(1)
    nodes = _tree([rng.randbytes(32) for _ in range(64)])
    for index in range(64, 128):
        branch = [nodes[index >> k ^ 1] for k in range(6)]
        for tamper in (False, True):
            proof = list(branch)
            if tamper:
                proof[rng.randrange(6)] = rng.randbytes(32)
            want = verify_merkle_proof(nodes[index], proof, index, nodes[1])
            assert native.verify_branch(nodes[index], proof, index, nodes[1]) == want


def test_multiproofs_verify_as_the_specification_says() -> None:
    # Random sets of leaves of a 64-leaf tree, with the helper nodes the specification asks for.
    rng = random.Random(2)
    nodes = _tree([rng.randbytes(32) for _ in range(64)])
    for _ in range(50):
        indices = sorted(rng.sample(range(64, 128), rng.randint(1, 6)))
        helpers = get_helper_indices(indices)
        proof = [nodes[h] for h in helpers]
        leaves = [nodes[i] for i in indices]
        root = nodes[1] if rng.random() < 0.7 else rng.randbytes(32)
        want = verify_merkle_multiproof(leaves, proof, indices, root)
        assert native.verify_multiproof(leaves, proof, indices, root) == want


class Bytes32(ByteVector):
    """Thirty-two opaque bytes."""

    LENGTH = 32


class Bytes48(ByteVector):
    """Forty-eight opaque bytes."""

    LENGTH = 48


class Header(Container):
    """A block header's shape: two integers and three roots."""

    slot: Uint64
    proposer_index: Uint64
    parent_root: Bytes32
    state_root: Bytes32
    body_root: Bytes32


class Validator(Container):
    """A validator record's shape, with a key, a flag, and integers."""

    pubkey: Bytes48
    withdrawal_credentials: Bytes32
    effective_balance: Uint64
    slashed: Boolean
    activation_epoch: Uint64


class Ints(List[Uint64]):
    """A long list of integers."""

    LIMIT = 2**40


class Validators(List[Validator]):
    """A long list of records."""

    LIMIT = 2**40


@pytest.mark.parametrize(
    ("ssz_type", "size"),
    [(Header, 112), (Ints, 8 * 1001), (Validators, 97 * 300), (Validators, 0)],
)
def test_roots_match_the_specification(ssz_type: type[SSZType], size: int) -> None:
    # Random bytes of the right size decode for each of these types, except the flag byte.
    rng = random.Random(size)
    data = bytearray(rng.randbytes(size))
    if ssz_type is Validators:
        # The flag sits 88 bytes into each 97-byte record and must be zero or one.
        for start in range(0, size, 97):
            data[start + 88] &= 1
    value = ssz_type.decode_bytes(bytes(data))
    root = native.hash_tree_root_of_accepted(ssz_type, bytes(data))
    assert root == bytes(value.hash_tree_root())


def test_roots_ignore_what_reused_scratch_holds() -> None:
    # The routines write scratch before reading it, so garbage in a reused area changes nothing.
    rng = random.Random(4)
    for count in (0, 1, 33, 1000):
        data = rng.randbytes(8 * count)
        want = bytes(Ints.decode_bytes(data).hash_tree_root())
        # Size the area, then fill it with a pattern no tree contains.
        native.hash_tree_root_of_accepted(Ints, data)
        scratch = native._scratch().scratch
        ctypes.memset(scratch, 0xA5, len(scratch))
        assert native.hash_tree_root_of_accepted(Ints, data) == want


class Deep(List[Uint64]):
    """A list whose tree is deeper than 64 levels."""

    LIMIT = 2**70


class Wide(BitList):
    """Flags under a tree deeper than 64 levels, which the routines climb a level per call."""

    LIMIT = 2**80


def test_the_backend_on_hashes_nothing_in_python(monkeypatch: pytest.MonkeyPatch) -> None:
    # With the backend on, any hash computed in Python fails the test.
    def forbidden(*_: object) -> bytes:
        raise AssertionError("hashed in Python while the native backend is on")

    with backend_on(True):
        monkeypatch.setattr(backend, "python_hash_pair", forbidden)
        monkeypatch.setattr(backend, "python_hash_level", forbidden)
        rng = random.Random(5)
        # Trees over 64 levels, and a list of records.
        deep = Deep(data=[Uint64(rng.randrange(2**64)) for _ in range(5)])
        wide = Wide(data=[Boolean(rng.random() < 0.5) for _ in range(300)])
        records = Validators.decode_bytes(bytes(97 * 3))
        for value in (deep, wide, records):
            assert bytes(value.hash_tree_root()) != bytes(32)


def test_the_backend_on_and_off_agree() -> None:
    # The same values rooted by each implementation, including a tree over 64 levels.
    rng = random.Random(6)
    values = [
        Deep(data=[Uint64(rng.randrange(2**64)) for _ in range(9)]),
        Ints(data=[Uint64(rng.randrange(2**64)) for _ in range(77)]),
        Header.decode_bytes(rng.randbytes(112)),
        Wide(data=[Boolean(rng.random() < 0.5) for _ in range(700)]),
    ]
    roots = {}
    for on in (False, True):
        with backend_on(on):
            roots[on] = [
                bytes(type(v).decode_bytes(v.encode_bytes()).hash_tree_root()) for v in values
            ]
    assert roots[True] == roots[False]


def test_malformed_requests_are_refused() -> None:
    # Index zero names no node, and a branch must have the depth of its index.
    zero = b"\0" * 32
    with pytest.raises(ValueError):
        native.verify_branch(zero, [], 0, zero)
    with pytest.raises(ValueError):
        native.verify_branch(zero, [zero], 8, zero)
    # An index past 64 bits names a node deeper than the routines walk.
    with pytest.raises(ValueError):
        native.verify_branch(zero, [zero], 1 << 64, zero)
    # Chunks are whole 32-byte nodes, and no more than the tree holds.
    with pytest.raises(ValueError):
        native.merkleize(bytes(33), 1)
    with pytest.raises(ValueError):
        native.merkleize(bytes(96), 1)


def test_a_type_outside_the_specification_has_no_plan() -> None:
    with pytest.raises(TypeError):
        native.plan(SSZType)


def test_a_layout_rewritten_out_of_step_with_its_fields_has_no_plan(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # A plan is built from the declaration as it is now, so a rewrite is seen.
    class Sparse(ProgressiveContainer):
        """Two fields with a gap between them."""

        ACTIVE_FIELDS = (1, 0, 1)

        first: Uint64
        second: Uint64

    assert native.plan(Sparse)
    monkeypatch.setattr(Sparse, "ACTIVE_FIELDS", (1, 0))
    with pytest.raises(TypeError):
        native.plan(Sparse)


def _words(*words: int) -> bytes:
    """Plan words as the little-endian bytes the routines read."""
    return b"".join(word.to_bytes(8, "little") for word in words)


@pytest.mark.parametrize(
    ("plan_bytes", "code"),
    [
        (_words(0), 0),
        (_words(*native.plan_words(Header)), 0),
        (_words(*native.plan_words(Validators)), 0),
        (b"", 2),
        (b"\0" * 7, 2),
        (_words(1, 3), 2),
        (_words(2, 0), 2),
        (_words(10, 0), 2),
        (_words(10, 2, 0), 2),
        (_words(10, 1, 0, 0), 2),
        (_words(13), 2),
        (_words(11, 2, 1, 0, 1, 0), 2),
        (_words(12, 2, 1, 1, 0, 0), 2),
        (_words(12, 1, 0, 0), 2),
        (_words(12, 2, 1, 2, 0, 1, 8), 2),
        (_words(*[7, 1] * 63, 0), 0),
        (_words(*[7, 1] * 64, 0), 3),
        (_words(*[8, 1] * 100_000, 0), 3),
    ],
)
def test_the_plan_check_refuses_corrupted_plans(plan_bytes: bytes, code: int) -> None:
    # Truncated, unknown, illegal, trailing, incompatible and too deep plans are all refused.
    assert native._plan_verdict(plan_bytes) == code


def test_a_corrupted_plan_is_refused_before_use(monkeypatch: pytest.MonkeyPatch) -> None:
    # A binding that writes a plan wrongly gets a type error, not an answer from the routines.
    monkeypatch.setattr(native, "plan_words", lambda ssz_type: (10, 2, 0))
    with pytest.raises(TypeError):
        native.hash_tree_root_of_accepted(Header, bytes(112))


class Note(ByteList):
    """A short run of opaque bytes."""

    LIMIT = 40


class Flags(BitList):
    """A short run of flags."""

    LIMIT = 20


class Entry(Container):
    """A record with a body of varying width."""

    weight: Uint16
    note: Note


class Entries(List[Entry]):
    """A few records."""

    LIMIT = 5


class Notes(Vector[Note]):
    """Exactly three notes."""

    LENGTH = 3


class Pins(BitVector):
    """Exactly ten flags."""

    LENGTH = 10


class Ledger(Container):
    """A struct mixing every encoding the decoding check walks."""

    number: Uint64
    entries: Entries
    root: Bytes32
    flags: Flags
    notes: Notes
    fixed_flags: Pins
    final: Boolean


def _ledger(rng: random.Random) -> Ledger:
    """A random ledger, with every variable part a random width."""
    return Ledger(
        number=Uint64(rng.randrange(2**64)),
        entries=Entries(
            data=[
                Entry(
                    weight=Uint16(rng.randrange(2**16)),
                    note=Note(data=rng.randbytes(rng.randrange(5))),
                )
                for _ in range(rng.randrange(4))
            ]
        ),
        root=Bytes32(rng.randbytes(32)),
        flags=Flags(data=[rng.random() < 0.5 for _ in range(rng.randrange(21))]),
        notes=Notes(data=[Note(data=rng.randbytes(rng.randrange(4))) for _ in range(3)]),
        fixed_flags=Pins(data=[rng.random() < 0.5 for _ in range(10)]),
        final=Boolean(rng.random() < 0.5),
    )


def test_the_decoding_check_refuses_as_decoding_does() -> None:
    # Encodings with a byte rewritten, dropped or inserted: refused alike, or accepted alike.
    rng = random.Random(7)
    for _ in range(3000):
        data = bytearray(_ledger(rng).encode_bytes())
        for _ in range(rng.randrange(1, 3)):
            at = rng.randrange(len(data))
            match rng.randrange(3):
                case 0:
                    data[at] = rng.randrange(256)
                case 1:
                    del data[at]
                case _:
                    data.insert(at, rng.randrange(256))
        try:
            want = Ledger.decode_bytes(bytes(data))
        except SSZValueError as refusal:
            with pytest.raises(SSZValueError) as native_refusal:
                native.validate(Ledger, bytes(data))
            assert native_refusal.value.fault == refusal.fault
        else:
            assert native.hash_tree_root(Ledger, bytes(data)) == bytes(want.hash_tree_root())

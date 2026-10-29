"""
The native backend: the proved x86-64 routines, called from Python.

The routines are printed from Lean programs that are proved to compute the specification.
Python only marshals bytes in and out; it never decides anything the routines compute.

The backend is optional.
Without an x86-64 processor with a hashing kernel, a C compiler, or the printed assembly,
it reports itself unavailable.
"""

from __future__ import annotations

import ctypes
import hashlib
import os
import platform
import shutil
import subprocess
import threading
from collections.abc import Mapping, Sequence
from functools import cache, lru_cache
from pathlib import Path
from typing import Final

from ssz import backend
from ssz.bitfields import BitList, BitVector, ProgressiveBitList
from ssz.boolean import Boolean
from ssz.byte_arrays import ByteList, ByteVector
from ssz.collections import List, ProgressiveList, Vector
from ssz.container import Container, ProgressiveContainer
from ssz.exceptions import SSZValueError, ValueFault
from ssz.ssz_base import SSZType
from ssz.uint import BaseUint
from ssz.union import CompatibleUnion

_ASSEMBLIES: Final = (
    Path(__file__).resolve().parent / "_native" / "kernels_x86.S",
    Path(__file__).resolve().parents[2] / "lean" / "native" / "kernels_x86.S",
)
"""Where the printed routines are: inside the installed package, then in a checkout."""

_PAD_BYTES: Final = 1536
"""The scratch area a padded hashing batch needs: sixteen messages, then sixteen digests."""


def _build(assembly: Path) -> Path:
    """
    The shared library assembled from the printed routines, cached by their content.

    The cache key is the assembly's hash, so a reprinted file gets a library of its own.
    """
    # One library per distinct assembly file.
    digest = hashlib.sha256(assembly.read_bytes()).hexdigest()[:16]
    cache_dir = Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache")) / "eth-ssz-specs"
    library = cache_dir / f"libssz-{digest}.so"
    if not library.exists():
        compiler = shutil.which(os.environ.get("CC", "cc"))
        if compiler is None:
            raise OSError("no C compiler to assemble the native routines with")
        cache_dir.mkdir(parents=True, exist_ok=True)
        # Assemble into a name of this process alone, then move it into place.
        # Readers never see half a file, and processes building at once never share one.
        partial = library.with_suffix(f".{os.getpid()}.tmp")
        subprocess.run(
            [compiler, "-O2", "-fPIC", "-shared", str(assembly), "-o", str(partial)], check=True
        )
        partial.replace(library)
    return library


@cache
def _library() -> ctypes.CDLL:
    """The loaded routines, from an explicit library path or assembled on first use."""
    # An explicit path wins over assembling.
    explicit = os.environ.get("SSZ_NATIVE_LIB")
    if explicit:
        library = ctypes.CDLL(explicit)
    else:
        assembly = next((path for path in _ASSEMBLIES if path.exists()), None)
        if assembly is None:
            raise OSError("the printed routines are not installed")
        library = ctypes.CDLL(str(_build(assembly)))
    # Every routine takes and returns 64-bit words.
    for name in (
        "ssz_merkleize",
        "ssz_hash_pairs",
        "ssz_verify_branch",
        "ssz_verify_multiproof",
        "ssz_root_scratch",
        "ssz_hash_tree_root",
        "ssz_check_plan",
        "ssz_validate",
        "ssz_cpu_features",
    ):
        getattr(library, name).restype = ctypes.c_uint64
    # Declared arguments let ctypes pass pointers and words without guessing their types.
    word, pointer = ctypes.c_uint64, ctypes.c_void_p
    library.ssz_root_scratch.argtypes = [ctypes.c_char_p, word]
    library.ssz_check_plan.argtypes = [ctypes.c_char_p, word]
    library.ssz_hash_pairs.argtypes = [pointer, ctypes.c_char_p, ctypes.c_char_p, word, pointer]
    library.ssz_hash_columns.restype = word
    library.ssz_hash_columns.argtypes = [pointer, ctypes.c_char_p, ctypes.c_char_p, word, pointer]
    library.ssz_hash_tree_root.argtypes = [
        ctypes.c_char_p,
        ctypes.c_char_p,
        word,
        pointer,
        pointer,
        pointer,
    ]
    library.ssz_validate.argtypes = [ctypes.c_char_p, word, ctypes.c_char_p, word, pointer]
    # Every x86-64 processor has a hashing kernel, down to the baseline one, so no routine refuses.
    return library


def available() -> bool:
    """Whether the native routines can run here."""
    # The routines are x86-64 only.
    if platform.machine().lower() not in ("x86_64", "amd64"):
        return False
    # They follow the System V calling convention, which Windows does not use.
    if platform.system() == "Windows":
        return False
    try:
        _library()
    except (OSError, subprocess.CalledProcessError):
        return False
    return True


class _Scratch(threading.local):
    """A thread's reusable buffers: its context words, padding area, scratch, and root output."""

    def __init__(self) -> None:
        """Start with an empty scratch, grown on demand."""
        library = _library()
        # The padding area must never be shared, and a thread's calls never overlap.
        self.pad = ctypes.create_string_buffer(_PAD_BYTES)
        table = ctypes.addressof(ctypes.c_uint8.in_dll(library, "ssz_sha256_table"))
        zeros = ctypes.addressof(ctypes.c_uint8.in_dll(library, "ssz_zero_roots"))
        mask = library.ssz_cpu_features()
        self.words = (ctypes.c_uint64 * 4)(mask, table, zeros, ctypes.addressof(self.pad))
        self.out = ctypes.create_string_buffer(32)
        self.scratch = ctypes.create_string_buffer(0)

    def area(self, size: int) -> ctypes.Array[ctypes.c_char]:
        """A scratch area of at least a size, grown and kept for later calls."""
        # The routines never read scratch before writing it, so a grown area needs no clearing.
        if len(self.scratch) < size:
            self.scratch = ctypes.create_string_buffer(size)
        return self.scratch


@cache
def _scratch() -> _Scratch:
    """
    Each thread's reusable buffers.

    They are made on first use, so this module imports where the routines cannot load.
    """
    return _Scratch()


def _context() -> tuple[ctypes.Array[ctypes.c_uint64], ctypes.Array[ctypes.c_char]]:
    """The calling thread's context words, and the padding area they name."""
    buffers = _scratch()
    return buffers.words, buffers.pad


def merkleize(chunks: bytes, depth: int) -> bytes:
    """
    The root of the perfect tree of a depth over 32-byte chunks, padded with zero subtrees.

    This is the specification's merkleization with a capacity of 2^depth chunks.
    """
    # Whole chunks only, and no more than the tree holds.
    count, rest = divmod(len(chunks), 32)
    if rest:
        raise ValueError("chunks must be a whole number of 32-byte nodes")
    if count > 1 << depth:
        raise ValueError("more chunks than the tree holds")
    # Each level is written after the one before it, so the scratch holds every level once.
    scratch = ctypes.create_string_buffer(32 * count + 32 * depth + 64)
    out = ctypes.create_string_buffer(32)
    nodes = ctypes.create_string_buffer(chunks, max(len(chunks), 1))
    words, _pad = _context()
    _library().ssz_merkleize(nodes, count, depth, out, scratch, words)
    return out.raw


def _declared(value: int | None) -> int:
    """A type parameter a complete declaration always gives."""
    if value is None:
        raise TypeError("an undeclared type has no plan")
    return value


@lru_cache(maxsize=4096)
def _root_scratch(plan_bytes: bytes, size: int) -> int:
    """The scratch a root of a type and size needs, asked of the routines once per pair."""
    return int(_library().ssz_root_scratch(plan_bytes, size))


def hash_tree_root_of_accepted(ssz_type: type[SSZType], data: bytes) -> bytes:
    """
    The root of the value an encoding holds, for an encoding already accepted as one of the type.

    The routine reads the encoding in place and never builds the value.
    It assumes the encoding passed the decoding check; on any other bytes its answer means nothing.
    """
    library, buffers, plan_bytes = _library(), _scratch(), plan(ssz_type)
    # The scratch the routine needs for this type and size.
    # It saturates only for an encoding far larger than memory, which then fails to allocate.
    need = _root_scratch(plan_bytes, len(data))
    # The encoding is passed in place: the routine only reads it.
    library.ssz_hash_tree_root(
        plan_bytes, data, len(data), buffers.out, buffers.area(max(need, 1)), buffers.words
    )
    return buffers.out.raw


_DECODING_REFUSALS: Final[dict[int, tuple[ValueFault, tuple[str, ...]]]] = {
    1: (ValueFault.LIMIT, ("limit", "actual")),
    2: (ValueFault.SCOPE, ("expected", "actual")),
    3: (ValueFault.SCOPE_TOO_SMALL, ("expected", "actual")),
    4: (ValueFault.SCOPE_UNDIVIDED, ("scope", "width")),
    6: (ValueFault.FIRST_OFFSET, ("expected", "actual")),
    7: (ValueFault.OFFSET_UNORDERED, ()),
    8: (ValueFault.OFFSET_PAST_SCOPE, ()),
    9: (ValueFault.OFFSET_UNALIGNED, ()),
    10: (ValueFault.OFFSET_BELOW_TABLE, ()),
    11: (ValueFault.TRUNCATED, ()),
    12: (ValueFault.NOT_A_BIT, ("value",)),
    13: (ValueFault.COUNT, ("expected", "actual")),
    14: (ValueFault.PADDING_BITS, ()),
    15: (ValueFault.EMPTY_ENCODING, ()),
    16: (ValueFault.NO_DELIMITER, ()),
    17: (ValueFault.TRAILING_ZEROS, ()),
    18: (ValueFault.NO_SELECTOR, ()),
    19: (ValueFault.UNKNOWN_SELECTOR, ("selector",)),
    59: (ValueFault.OFFSET_OVERFLOW, ("size",)),
    64: (ValueFault.PADDING_BITS, ()),
    65: (ValueFault.NO_DELIMITER, ()),
    66: (ValueFault.TRAILING_ZEROS, ()),
}
"""
The refusals the decoding check writes, by their position among the specification's refusals.

Each comes with the fault decoding raises for it, and the names of the numbers it carries.
"""


def validate(ssz_type: type[SSZType], data: bytes) -> None:
    """
    Check that an encoding holds one value of a type, as decoding it would.

    The check reads the encoding in place and builds nothing.
    It refuses exactly the encodings decoding refuses, with the same fault.
    Where decoding names the type or the path of the part that refused, this refusal does not.

    Raises:
        SSZValueError: An encoding decoding refuses.
        TypeError: A type the routines cannot read, which the specification then handles.
    """
    plan_bytes = plan(ssz_type)
    refusal = (ctypes.c_uint64 * 4)()
    # The check starts with the plan check the plan already passed, so it accepts or refuses.
    if _library().ssz_validate(plan_bytes, len(plan_bytes), data, len(data), refusal) == 0:
        return
    code, *numbers = refusal
    fault, names = _DECODING_REFUSALS[code]
    raise SSZValueError(fault, type=ssz_type.__name__, **dict(zip(names, numbers, strict=False)))


def hash_tree_root(ssz_type: type[SSZType], data: bytes) -> bytes:
    """
    The root of the value an encoding holds, after checking the encoding holds one.

    Raises:
        SSZValueError: An encoding decoding refuses.
        TypeError: A type the routines cannot read.
    """
    validate(ssz_type, data)
    return hash_tree_root_of_accepted(ssz_type, data)


_REFUSALS: Final = {
    3: "an index of zero names no node",
    4: "the root has no branch",
    5: "the branch length is not the depth of its index",
    6: "the leaves do not pair one to one with the indices",
    7: "the proof's node count is not the number of helper indices",
    8: "the request names no index",
    9: "an index is named twice",
    10: "an index lies below another of the same request",
    11: "no root can be rebuilt from the proof",
}
"""The refusals the native verifiers answer with, by code."""


def _verdict(answer: int) -> bool:
    """A verifier's answer word as a verdict, or the refusal it names."""
    # Zero and one are the verdicts.
    if answer in (0, 1):
        return answer == 1
    raise ValueError(_REFUSALS.get(answer, f"unknown answer {answer}"))


def _nodes(nodes: list[bytes]) -> ctypes.Array[ctypes.c_char]:
    """Nodes back to back in one buffer, each exactly 32 bytes."""
    if any(len(node) != 32 for node in nodes):
        raise ValueError("every node must be 32 bytes")
    joined = b"".join(nodes)
    return ctypes.create_string_buffer(joined, max(len(joined), 1))


def _index(index: int) -> int:
    """A generalized index as the routines take it: one 64-bit word."""
    if not 0 <= index < 1 << 64:
        raise ValueError(
            "generalized indices above 2^64 - 1 name trees deeper than the routines walk"
        )
    return index


def verify_branch(leaf: bytes, branch: list[bytes], index: int, root: bytes) -> bool:
    """
    Whether a leaf and its branch rebuild a root, at a generalized index.

    This is the specification's single-proof verification.
    """
    # The job the routine reads: leaf, branch, branch length, index, root, and a 64-byte scratch.
    leaf_buf, branch_buf, root_buf = _nodes([leaf]), _nodes(branch), _nodes([root])
    scratch = ctypes.create_string_buffer(64)
    job = (ctypes.c_uint64 * 6)(
        ctypes.addressof(leaf_buf),
        ctypes.addressof(branch_buf),
        len(branch),
        _index(index),
        ctypes.addressof(root_buf),
        ctypes.addressof(scratch),
    )
    words, _pad = _context()
    return _verdict(_library().ssz_verify_branch(job, words))


def verify_multiproof(
    leaves: list[bytes], proof: list[bytes], indices: list[int], root: bytes
) -> bool:
    """
    Whether leaves at generalized indices, with a proof's helper nodes, rebuild a root.

    This is the specification's multiproof verification.
    """
    # The job the routine reads, then a scratch area sized as the routine documents.
    leaves_buf, proof_buf, root_buf = _nodes(leaves), _nodes(proof), _nodes([root])
    words_buf = (ctypes.c_uint64 * max(len(indices), 1))(*(_index(i) for i in indices))
    n, p = len(indices), len(proof)
    scratch = ctypes.create_string_buffer(8 + 1536 * n + 160 * (n + p))
    job = (ctypes.c_uint64 * 8)(
        ctypes.addressof(leaves_buf),
        len(leaves),
        ctypes.addressof(proof_buf),
        p,
        ctypes.addressof(words_buf),
        n,
        ctypes.addressof(root_buf),
        ctypes.addressof(scratch),
    )
    words, _pad = _context()
    return _verdict(_library().ssz_verify_multiproof(job, words))


def _bound(limit: int | None) -> list[int]:
    """An optional bound as two plan words: whether there is one, and its value."""
    return [0, 0] if limit is None else [1, limit]


def plan_words(ssz_type: type[SSZType]) -> tuple[int, ...]:
    """
    A type as plan words: a tag, then the type's parameters and nested types, in prefix order.

    This is the format the Lean definition of plans fixes; field names never reach it.
    """
    # Order matters: a subclass is matched before the classes it extends.
    if issubclass(ssz_type, Boolean):
        return (0,)
    if issubclass(ssz_type, BaseUint):
        return (1, ssz_type.BYTE_LENGTH)
    if issubclass(ssz_type, ByteVector):
        return (2, _declared(ssz_type.LENGTH))
    if issubclass(ssz_type, ByteList):
        return (3, _declared(ssz_type.LIMIT))
    if issubclass(ssz_type, BitVector):
        return (4, _declared(ssz_type.LENGTH))
    if issubclass(ssz_type, ProgressiveBitList):
        return (6, *_bound(ssz_type.LIMIT))
    if issubclass(ssz_type, BitList):
        return (5, _declared(ssz_type.LIMIT))
    if issubclass(ssz_type, Vector):
        return (7, _declared(ssz_type.LENGTH), *plan_words(ssz_type.ELEMENT_TYPE))
    if issubclass(ssz_type, ProgressiveList):
        return (9, *_bound(ssz_type.LIMIT), *plan_words(ssz_type.ELEMENT_TYPE))
    if issubclass(ssz_type, List):
        return (8, _declared(ssz_type.LIMIT), *plan_words(ssz_type.ELEMENT_TYPE))
    if issubclass(ssz_type, ProgressiveContainer):
        fields = [plan_words(field) for _, field in ssz_type._FIELD_TYPES]
        active = [1 if bit else 0 for bit in ssz_type.ACTIVE_FIELDS]
        # A layout that does not pair one set bit with each field is the specification's to refuse.
        if sum(active) != len(fields) or not active or not active[-1]:
            raise TypeError(f"{ssz_type.__name__} has a layout that does not pair with its fields")
        return (11, len(active), *active, len(fields), *(w for f in fields for w in f))
    if issubclass(ssz_type, Container):
        fields = [plan_words(field) for _, field in ssz_type._FIELD_TYPES]
        return (10, len(fields), *(w for f in fields for w in f))
    if issubclass(ssz_type, CompatibleUnion):
        options: Mapping[int, type[SSZType]] = ssz_type.OPTIONS
        selectors = list(options)
        words = [w for s in selectors for w in plan_words(options[s])]
        return (12, len(selectors), *selectors, *words)
    raise TypeError(f"{ssz_type.__name__} has no plan")


_PLAN_REFUSALS: Final = {
    2: "the routines refuse this plan",
    3: "this plan nests deeper than the routines walk",
}
"""Why the routines' own plan check refuses a plan, by code."""


@lru_cache(maxsize=4096)
def _plan_verdict(plan_bytes: bytes) -> int:
    """
    The routines' proved check of a plan, asked once per plan: zero when accepted, else why not.

    Every routine is proved only for plans this check accepts.
    A plan built wrongly here is then refused rather than walked.
    """
    return int(_library().ssz_check_plan(plan_bytes, len(plan_bytes)))


def plan(ssz_type: type[SSZType]) -> bytes:
    """
    A type's plan, as the little-endian words the native routines read.

    It is built from the type's attributes as they are now, since a declaration can be rewritten.
    The routines' own check accepts it before it is returned.

    Raises:
        TypeError: A declaration the routines cannot read, which the specification then handles.
    """
    words = plan_words(ssz_type)
    # Every word must fit 64 bits, or the routines would read another type.
    if any(word >= 1 << 64 for word in words):
        raise TypeError("a type parameter past 64 bits has no plan")
    plan_bytes = b"".join(word.to_bytes(8, "little") for word in words)
    # A refusal is remembered too, so a plan is checked once whatever the verdict.
    code = _plan_verdict(plan_bytes)
    if code != 0:
        raise TypeError(_PLAN_REFUSALS.get(code, f"the plan check answered {code}"))
    return plan_bytes


def _merkleize_hook(chunks: Sequence[bytes], width: int) -> bytes | None:
    """Chunks under a power-of-two width, already checked by the specification."""
    # Past height 64 the specification's own climb hashes each level, through the routines too.
    if width > 1 << 64:
        return None
    return merkleize(b"".join(chunks), width.bit_length() - 1)


def _verify_hook(leaf: bytes, proof: Sequence[bytes], index: int, root: bytes) -> bool | None:
    """A single-proof verdict, or None for every request the specification must refuse itself."""
    try:
        return verify_branch(bytes(leaf), [bytes(n) for n in proof], index, bytes(root))
    except ValueError:
        return None


def _verify_multi_hook(
    leaves: Sequence[bytes], proof: Sequence[bytes], indices: Sequence[int], root: bytes
) -> bool | None:
    """A multiproof verdict, or None for every request the specification must refuse itself."""
    try:
        return verify_multiproof(
            [bytes(n) for n in leaves], [bytes(n) for n in proof], list(indices), bytes(root)
        )
    except ValueError:
        return None


def _hash_pair(left: bytes, right: bytes) -> bytes:
    """The parent of two 32-byte nodes, from the proved hashing dispatcher."""
    buffers = _scratch()
    # Two separate nodes are one pair of the two-column layout.
    _library().ssz_hash_columns(buffers.out, bytes(left), bytes(right), 1, buffers.words)
    return buffers.out.raw


def _hash_level(level: Sequence[bytes]) -> list[bytes]:
    """The parents of consecutive pairs of a level, all hashed in one call to the dispatcher."""
    count = len(level) // 2
    joined = b"".join(level)
    out = ctypes.create_string_buffer(32 * max(count, 1))
    # Adjacent nodes of one level are the pairs layout: left nodes 64 bytes apart, rights 32 past.
    _library().ssz_hash_pairs(out, joined, joined[32:], count, _scratch().words)
    raw = out.raw
    return [raw[32 * i : 32 * i + 32] for i in range(count)]


def enable() -> bool:
    """
    Route roots, merkleization and proof checks through the native routines, where they run.

    Every call keeps its signature, its answers and its errors.
    An input the routines do not cover is computed by the specification as before.
    Returns whether the routines run here; when they do not, nothing changes.
    """
    if not available():
        return False
    # Bound here, since it loads the routines this module only loads once they are known to run.
    from ssz import kept, lazy, stored

    backend.model_root, backend.model_copied = kept.model_root, kept.model_copied
    backend.decode = stored.decode
    lazy.read_hook = kept.element_read
    backend.merkleize = _merkleize_hook
    backend.hash_pair, backend.hash_level = _hash_pair, _hash_level
    backend.verify_proof, backend.verify_multiproof = _verify_hook, _verify_multi_hook
    return True


def disable() -> None:
    """Compute everything with the specification's Python again."""
    backend.reset()


def enabled() -> bool:
    """Whether calls currently go through the native routines."""
    return backend.model_root is not None

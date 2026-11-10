"""
Which implementation computes roots, trees and proof checks.

By default every hook is empty and hashing uses hashlib: the specification's Python computes it all.
Turning the native backend on fills the hooks, and every pair is hashed by the proved routines.
A whole-value hook answers None for a value it does not cover, and the Python walks that value.
The walk still hashes through the routines, so a call never changes its answer or its errors.
"""

from __future__ import annotations

from collections.abc import Callable, Sequence
from hashlib import sha256


def python_hash_pair(left: bytes, right: bytes) -> bytes:
    """The parent of two nodes: the SHA-256 digest of the left node followed by the right one."""
    return sha256(left + right).digest()


def python_hash_level(level: Sequence[bytes]) -> list[bytes]:
    """The parents of consecutive pairs of an even-length level."""
    return [sha256(level[i] + level[i + 1]).digest() for i in range(0, len(level), 2)]


hash_pair: Callable[[bytes, bytes], bytes] = python_hash_pair
"""The parent of two nodes, from whichever implementation is on."""

hash_level: Callable[[Sequence[bytes]], list[bytes]] = python_hash_level
"""The parents of consecutive pairs of a level, from whichever implementation is on."""

model_root: Callable[[object], bytes] | None = None
"""The root of a composite value, kept current by the backend in place of the remembered one."""

decode: Callable[[type, bytes], object | None] | None = None
"""A value decoded from bytes, or None to leave the input to the Python, refusals included."""

model_copied: Callable[[object, object], None] | None = None
"""Hand what the backend keeps for a composite value on to a fresh copy of it."""

merkleize: Callable[[Sequence[bytes], int], bytes | None] | None = None
"""The root of chunks under a power-of-two width, or None to leave it to the Python."""

verify_proof: Callable[[bytes, Sequence[bytes], int, bytes], bool | None] | None = None
"""A single-proof verdict, or None to leave it to the Python, refusals included."""

verify_multiproof: (
    Callable[[Sequence[bytes], Sequence[bytes], Sequence[int], bytes], bool | None] | None
) = None
"""A multiproof verdict, or None to leave it to the Python, refusals included."""


_DEFAULTS: tuple[Callable[[bytes, bytes], bytes], Callable[[Sequence[bytes]], list[bytes]]] = (
    python_hash_pair,
    python_hash_level,
)
"""The specification's own hashing, kept apart so that restoring it never reads a replaced name."""


def reset() -> None:
    """Empty every hook and hash with hashlib again: the specification's Python computes it all."""
    global model_root, model_copied, decode, merkleize
    global verify_proof, verify_multiproof, hash_pair, hash_level
    model_root = model_copied = decode = merkleize = verify_proof = verify_multiproof = None
    hash_pair, hash_level = _DEFAULTS

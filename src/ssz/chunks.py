"""The unit a Merkle tree is built from, and the roots of the trees that hold none."""

from hashlib import sha256
from itertools import accumulate, repeat
from typing import Final

from ssz.byte_arrays import ByteVector
from ssz.exceptions import SSZValueError, ValueFault

BYTES_PER_CHUNK: Final = 32
"""Width of a Merkle leaf chunk in bytes."""


BITS_PER_CHUNK: Final = BYTES_PER_CHUNK * 8
"""Width of a Merkle leaf chunk in bits."""


def next_pow2(x: int) -> int:
    """
    Smallest power of two greater than or equal to x.

    Returns 1 when x is 0 or 1.
    """
    if x <= 1:
        return 1
    return 1 << (x - 1).bit_length()


class Chunk(ByteVector):
    """Fixed-size 32-byte unit of Merkle tree input data."""

    LENGTH = BYTES_PER_CHUNK


class Root(Chunk):
    """Merkle tree root, usable anywhere a chunk is expected."""

    LENGTH = 32


ZERO_ROOT: Final = Root.zero()
"""All-zero 32-byte root, used as the merkleization padding value."""


ZERO_CHUNK: Final = bytes(BYTES_PER_CHUNK)
"""The zero chunk as plain bytes, since a typed chunk refuses to compare against them."""


_ZERO_ROOTS: Final[tuple[Root, ...]] = tuple(
    accumulate(
        repeat(None, 64),
        lambda previous, _: Root(sha256(previous + previous).digest()),
        initial=ZERO_ROOT,
    )
)
"""
Roots of perfect zero subtrees, indexed by depth.

- Index 0 is the all-zero leaf.
- Index d is the root of a perfect binary tree of 2**d zero leaves.

Depth 64 covers common capacities without further hashing.
Larger trees extend the final cached root as needed.
"""


def zero_tree_root(width: int) -> Root:
    """
    Root of the all-zero perfect binary tree spanning the given leaf count.

    Raises:
        SSZValueError: A width that is not a positive power of two.
    """
    # Subtracting one before the bit length maps a power of two to its own depth: 1 -> 0, 8 -> 3.
    depth = (width - 1).bit_length()
    # Any other width rounds up to a depth it does not span.
    if width != 1 << depth:
        raise SSZValueError(ValueFault.ZERO_TREE_WIDTH, width=width)
    # Indexing by depth skips materializing 2**depth zero leaves and the layers above them.
    if depth < len(_ZERO_ROOTS):
        return _ZERO_ROOTS[depth]
    # SSZ capacities have no depth-64 bound, so continue from the deepest cached subtree.
    root = _ZERO_ROOTS[-1]
    for _ in range(len(_ZERO_ROOTS) - 1, depth):
        # Each parent doubles the leaf count by joining two identical zero subtrees.
        root = Root(sha256(root + root).digest())
    return root

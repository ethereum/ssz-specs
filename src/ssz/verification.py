"""Rebuilding a root from chunks and the indices they sit at, reading no declaration."""

from collections.abc import Sequence
from hashlib import sha256

from ssz.chunks import Chunk, Root
from ssz.exceptions import SSZValueError, ValueFault
from ssz.gindex import (
    get_helper_indices,
    gindex_bit,
    gindex_length,
    gindex_parent,
    gindex_sibling,
)


def _hash_pair(left: bytes, right: bytes) -> Root:
    """Join two nodes into their parent."""
    # Invariant: a digest is exactly the chunk width.
    return Root._trusted(sha256(left + right).digest())


def calculate_merkle_root(leaf: Chunk, proof: Sequence[Chunk], index: int) -> Root:
    """
    Rebuild a root from one leaf and its branch.

    Each bit of the index, read from the leaf upward, says which side the branch node joins on.

    Raises:
        SSZValueError: A branch whose length is not the depth of the index.
    """
    depth = gindex_length(index)
    if len(proof) != depth:
        raise SSZValueError(
            ValueFault.BRANCH_LENGTH, index=index, expected=depth, actual=len(proof)
        )
    node = leaf
    for level, sibling in enumerate(proof):
        node = _hash_pair(sibling, node) if gindex_bit(index, level) else _hash_pair(node, sibling)
    # Invariant: the depth of a provable index is at least one.
    # The loop above therefore ran and left a digest behind.
    # Re-measuring it would only re-derive what joining two nodes already guarantees.
    return Root._trusted(node)


def verify_merkle_proof(leaf: Chunk, proof: Sequence[Chunk], index: int, root: Root) -> bool:
    """Whether one leaf and its branch rebuild the expected root, raising if it is malformed."""
    return calculate_merkle_root(leaf, proof, index) == root


def calculate_multi_merkle_root(
    leaves: Sequence[Chunk], proof: Sequence[Chunk], indices: Sequence[int]
) -> Root:
    """
    Rebuild a root from several leaves and the nodes they share.

    Pairs combine from the deepest index upward, each parent built once.

    Raises:
        SSZValueError: A request whose indices, leaves and proof do not agree.
    """
    if len(leaves) != len(indices):
        raise SSZValueError(ValueFault.LEAF_COUNT, expected=len(indices), actual=len(leaves))
    helpers = get_helper_indices(indices)
    if len(proof) != len(helpers):
        raise SSZValueError(ValueFault.PROOF_LENGTH, expected=len(helpers), actual=len(proof))

    nodes = dict(zip(indices, leaves, strict=True))
    nodes.update(zip(helpers, proof, strict=True))
    # Descending order reaches both children of a pair before their parent.
    pending = sorted(nodes, reverse=True)
    position = 0
    while position < len(pending):
        index = pending[position]
        parent = gindex_parent(index)
        if gindex_sibling(index) in nodes and parent not in nodes:
            # The even index of the pair is the left child, whichever one was reached first.
            left, right = index & ~1, index | 1
            nodes[parent] = _hash_pair(nodes[left], nodes[right])
            pending.append(parent)
        position += 1

    # Invariant: index one is refused as a claim.
    # The root can only have been built by the loop above, leaving a digest behind.
    return Root._trusted(nodes[1])


def verify_merkle_multiproof(
    leaves: Sequence[Chunk], proof: Sequence[Chunk], indices: Sequence[int], root: Root
) -> bool:
    """Whether several leaves and their nodes rebuild the expected root, raising if malformed."""
    return calculate_multi_merkle_root(leaves, proof, indices) == root

"""Reading a generalized index against a value's data, and building the proofs that carry it."""

from collections.abc import Sequence

from ssz.chunks import Root, next_pow2
from ssz.exceptions import SSZValueError, ValueFault
from ssz.gindex import (
    get_branch_indices,
    get_helper_indices,
    gindex_below,
    gindex_bit,
    gindex_length,
    gindex_rebase,
)
from ssz.layout import NestedLeaves, merkle_layout
from ssz.roots import hash_tree_root, layout_chunks
from ssz.trees import merkleize, merkleize_progressive


def node_root(value: object, index: int) -> Root:
    """
    Root of the subtree at one generalized index of a value's own Merkle tree.

    Index 1 is the root itself, whose subtree is the whole value.

    Raises:
        SSZValueError: An index this value's tree does not reach.
    """
    # The root has no branch, but it is a node.
    # This walk therefore admits the one index a proof branch refuses.
    if index < 1:
        raise SSZValueError(ValueFault.NOT_A_GINDEX, index=index)
    if index == 1:
        return hash_tree_root(value)

    layout, name = merkle_layout(value), type(value).__name__
    # Every bit below the leading one is a turn, so the bit width is the depth to walk.
    depth = gindex_length(index)

    # A mixed-in word is the right child, which puts the leaves one level down on the left.
    if layout.mixin is not None:
        depth -= 1
        if gindex_bit(index, depth):
            if depth:
                raise SSZValueError(ValueFault.PATH_INTO_MIXIN, type=name)
            # Invariant: a mixed-in word is exactly one chunk wide.
            return Root._trusted(layout.mixin)

    # First leaf of the bounded subtree the walk ends in, and that subtree's capacity.
    leaves_from, capacity = 0, layout.limit
    if capacity is None:
        # A progressive spine holds its levels on the left and the rest of itself on the right.
        #
        # A spine is only as long as its data, closing with a zero node holding nothing.
        # Turning onto a level past the last one therefore walks off the end:
        #
        #     ProgressiveList[Uint64] holding two elements  ->  chunk 0 is a node, chunk 5 is not
        #
        # The terminator itself is exempt, being a node the walk stops on rather than turns from.
        #
        # So absence is provable in a bounded shape and not in a progressive one.
        #
        # A bounded shape pads to its capacity, and that padding is a leaf like any other.
        #
        # Three packed eight-byte elements prove the fourth is zero, sharing chunk 0.
        # The fifth has no leaf to prove.
        capacity = 1
        while depth:
            if leaves_from >= layout.leaf_count:
                raise SSZValueError(ValueFault.PATH_PAST_SPINE, type=name)
            depth -= 1
            # Turning left enters this level's own bounded subtree, walked below.
            if not gindex_bit(index, depth):
                break
            # Turning right skips this level's leaves and quadruples the width of the next.
            leaves_from, capacity = leaves_from + capacity, capacity * 4
        else:
            # The turns ran out on the spine itself, so the index names a spine node,
            # whose root covers every leaf still to come.
            return merkleize_progressive(layout_chunks(layout, leaves_from), capacity)

    width = next_pow2(capacity)
    tree_depth = width.bit_length() - 1

    if depth <= tree_depth:
        # The index names a node of the bounded subtree, which spans a run of leaves.
        # Merkleizing that run alone gives its root, padding included.
        span = width >> depth
        start = leaves_from + gindex_below(index, depth) * span
        return merkleize(layout_chunks(layout, start, start + span), limit=span)

    # Deeper than the subtree: the rest of the index is measured inside one leaf's own tree.
    depth -= tree_depth
    leaf = leaves_from + gindex_below(index >> depth, tree_depth)
    if not isinstance(layout.leaves, NestedLeaves):
        raise SSZValueError(ValueFault.PATH_INTO_PACKED, type=name)
    if leaf >= layout.leaf_count or layout.leaves.values[leaf] is None:
        raise SSZValueError(ValueFault.PATH_INTO_GAP, type=name)
    return node_root(layout.leaves.values[leaf], gindex_rebase(index, depth))


def build_proof(value: object, index: int) -> list[Root]:
    """
    Branch that authenticates one generalized index of a value against its root.

    Every node on the path contributes its sibling, bottom-up, as a verifier reads it.
    """
    return [node_root(value, sibling) for sibling in get_branch_indices(index)]


def build_multiproof(value: object, indices: Sequence[int]) -> list[Root]:
    """
    Nodes that authenticate several generalized indices of a value at once.

    Only what a verifier cannot rebuild is carried.
    The claims are the caller's to supply:

        leaves = [node_root(state, index) for index in indices]
        proof = build_multiproof(state, indices)
        assert verify_merkle_multiproof(leaves, proof, indices, hash_tree_root(state))
    """
    return [node_root(value, helper) for helper in get_helper_indices(indices)]

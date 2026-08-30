"""Generalized indices: naming one node of a Merkle tree, and the nodes a proof of it needs."""

from collections.abc import Sequence

from ssz.exceptions import SSZValueError, ValueFault


def _reject_unusable(index: int) -> None:
    """
    Refuse the two indices that name no provable node.

    Raises:
        SSZValueError: The root, which proves nothing about itself, or anything below it.
    """
    if index < 1:
        raise SSZValueError(ValueFault.NOT_A_GINDEX, index=index)
    if index == 1:
        raise SSZValueError(ValueFault.ROOT_HAS_NO_BRANCH)


def gindex_length(index: int) -> int:
    """Depth of a generalized index, which is the number of nodes on its proof branch."""
    _reject_unusable(index)
    return index.bit_length() - 1


def gindex_bit(index: int, position: int) -> bool:
    """Whether the branch turns right at the given depth, counted from the leaf."""
    return bool(index & (1 << position))


def gindex_below(index: int, depth: int) -> int:
    """The bottom turns of an index, as many as the given depth, with everything above dropped."""
    return index & ((1 << depth) - 1)


def gindex_sibling(index: int) -> int:
    """The node sharing a parent with this one."""
    return index ^ 1


def gindex_child(index: int, right_side: bool) -> int:
    """One of the two nodes this one is the parent of."""
    return index * 2 + right_side


def gindex_parent(index: int) -> int:
    """The node this one is a child of."""
    return index // 2


def gindex_concat(outer: int, inner: int) -> int:
    """
    Rebase a generalized index measured from one root onto a position in a larger tree.

    An index carries its depth in its leading bit, so this splices rather than multiplies:

        outer 2, inner 24  ->  40, not 48
    """
    depth = gindex_length(inner)
    return (outer << depth) | (inner - (1 << depth))


def gindex_rebase(index: int, depth: int) -> int:
    """
    The bottom turns of an index, read as a generalized index of a tree of their own.

    Undoes a splice, handing the rest of an index to the subtree it lands in:

        splicing 2 and 24 gives 40, and 40 read back at the depth of 24 gives 24
    """
    return (1 << depth) | gindex_below(index, depth)


def progressive_chunk_gindex(chunk: int) -> int:
    """
    Position of one chunk on a progressive spine.

    A progressive tree grows to the right.
    Each step down the spine opens a subtree four times wider than the one before:

        level 1  holds chunk 0
        level 2  holds chunks 1 to 4
        level 3  holds chunks 5 to 20
        level 4  holds chunks 21 to 84

    A chunk keeps its place as the collection grows, so a proof outlives an append.
    A bounded tree renumbers every leaf instead.

    The index reported here counts from the root of the shape:

        chunk 0  ->  4       chunk 5   ->  352
        chunk 1  ->  40      chunk 21  ->  2944

    One level below the spine itself, since a progressive shape mixes a word into its root.
    """
    depth, spine = 0, 2
    while True:
        width = 1 << depth
        if chunk < width:
            # The subtree root is the spine node's left child.
            # The chunk sits that many levels below the subtree root.
            return ((spine << 1) << depth) + chunk
        chunk -= width
        depth += 2
        spine = (spine << 1) + 1


def get_path_indices(index: int) -> list[int]:
    """Nodes from the given one up to the root, excluding the root."""
    _reject_unusable(index)
    walk = [index]
    while walk[-1] > 1:
        walk.append(gindex_parent(walk[-1]))
    return walk[:-1]


def get_branch_indices(index: int) -> list[int]:
    """Siblings along the path from the given node to the root, which is its proof branch."""
    return [gindex_sibling(step) for step in get_path_indices(index)]


def _reject_related(indices: Sequence[int]) -> None:
    """
    Refuse an index set that cannot be verified soundly.

    - An empty request claims nothing, so nothing about the root is checked.
    - A repeated index keeps one value and drops the other without a word.
    - An index above another is rebuilt from below, leaving the lower one unchecked.
    """
    if not indices:
        raise SSZValueError(ValueFault.EMPTY_REQUEST)
    seen = set(indices)
    if len(seen) != len(indices):
        raise SSZValueError(ValueFault.REPEATED_INDEX)
    for index in indices:
        # A walk upward opens at the index itself, which is no ancestor of its own.
        # One claimed ancestor is already too many, so the first one ends the search.
        if any(ancestor in seen for ancestor in get_path_indices(index)[1:]):
            raise SSZValueError(ValueFault.NESTED_INDEX, index=index)


def get_helper_indices(indices: Sequence[int]) -> list[int]:
    """
    Nodes a proof must carry to authenticate all the given ones at once.

    Every sibling on every branch, less what the caller claims and what the verifier rebuilds.
    The result descends, so one index yields exactly a plain proof's branch.

    Raises:
        SSZValueError: An empty request, a repeated index, or a nested one.
    """
    _reject_related(indices)
    branches: set[int] = set()
    paths: set[int] = set()
    for index in indices:
        # A branch is the siblings of a path, so one walk upward yields both.
        path = get_path_indices(index)
        paths.update(path)
        branches.update(gindex_sibling(step) for step in path)
    return sorted(branches - paths, reverse=True)

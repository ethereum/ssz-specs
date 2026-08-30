"""The two tree shapes SSZ merkleizes into: bounded by a declared capacity, or progressive."""

from collections.abc import Sequence
from hashlib import sha256

from ssz.chunks import ZERO_CHUNK, ZERO_ROOT, Root, next_pow2, zero_tree_root
from ssz.exceptions import SSZValueError, ValueFault


def merkleize(chunks: Sequence[bytes], limit: int | None = None) -> Root:
    r"""
    Compute the SSZ Merkle root over a chunk sequence.

    Tree layout for three leaves with no limit:

        leaves   :  c0     c1     c2     ZERO     (padded to next power of two)
                     \____/        \______/
                       h01        h(c2, ZERO)
                        \______________/
                              root

    A capacity sets the width instead, rounded up to a power of two.
    Padding is a cached zero subtree, so a half-empty shape costs what its data costs.

    Every node below the root is plain bytes.
    The root alone carries a type.
    Every chunk is exactly 32 bytes wide, and one of any other width is not diagnosed.

    Three shortcuts skip the layer walk, marked below where each is taken.

    Raises:
        SSZValueError: A capacity below the chunk count, or one that is no count at all.
    """
    chunk_count = len(chunks)
    if limit is None:
        width = next_pow2(chunk_count)
    elif limit < chunk_count:
        # A capacity below the data refuses, and so does one that is no capacity at all.
        # Checking before the empty-input answer is what stops a negative bound from
        # rounding up to a one-leaf tree and handing back a root for it.
        raise SSZValueError(ValueFault.MERKLEIZE_LIMIT, count=chunk_count, limit=limit)
    else:
        width = next_pow2(limit)
    if chunk_count == 0:
        return zero_tree_root(width) if limit is not None else ZERO_ROOT
    # A one-leaf tree has no parent to hash: the leaf is the root.
    #
    # Invariant: a chunk is exactly the chunk width, which the caller states.
    #
    # Every other root below is a digest, and so 32 bytes whatever it was folded from.
    #
    # This one is handed back rather than hashed, so the caller's own width reaches it.
    if width == 1:
        return Root._trusted(chunks[0])

    # Zero data under zero padding is a zero tree, at any width.
    # The fold below fires only from a level spanning its data tree.
    # A count short of a power of two hashes its way up to one first.
    # The first chunk rules out anything that starts with data, before the join copies it all.
    if bytes(chunks[0]) == ZERO_CHUNK and b"".join(chunks) == ZERO_CHUNK * chunk_count:
        return zero_tree_root(width)

    # Width of the perfect subtree the data fills, where the layer walk ends.
    # Above it every height holds one real node beside an all-zero subtree.
    data_width = next_pow2(chunk_count)

    # Walk one tree layer per outer iteration.
    level: list[bytes] = list(chunks)
    subtree_size = 1
    while len(level) > 1:
        # Pairing a uniform level yields the same value one size up.
        # The tail below folds it once per remaining height.
        #
        # Invariant: the level must also span its data tree.
        # A shorter one meets a zero subtree as a sibling above it.
        # Zero does not fold.
        #
        # The comparison goes through plain bytes.
        # A level mixes bare digests with typed leaves that refuse equality against bytes.
        if (
            len(level) * subtree_size == data_width
            and bytes(level[0]) == bytes(level[-1])
            and b"".join(level) == level[0] * len(level)
        ):
            break

        # An odd node count is missing exactly one right sibling, at the end of the level.
        # Supplying it here, rather than once per pair, keeps the branch out of the loop.
        if len(level) & 1:
            level.append(zero_tree_root(subtree_size))
        level = [sha256(level[i] + level[i + 1]).digest() for i in range(0, len(level), 2)]
        subtree_size *= 2

    # Neither spine above this point branches.
    # A list per height would allocate only to carry a single node.
    #
    # - Up to the data tree, after a fold: every sibling is the node itself.
    # - Up to the full width: every sibling is the all-zero subtree beside the data.
    node = level[0]
    while subtree_size < data_width:
        node = sha256(node + node).digest()
        subtree_size *= 2
    while subtree_size < width:
        node = sha256(node + zero_tree_root(subtree_size)).digest()
        subtree_size *= 2
    # Invariant: a width above one leaves at least one height.
    # One spine above therefore hashed.
    # A digest is exactly the chunk width.
    return Root._trusted(node)


def merkleize_progressive(chunks: Sequence[bytes], num_leaves: int = 1) -> Root:
    r"""
    Compute the progressive Merkle root over a chunk sequence, per EIP-7916.

    A right-leaning spine of binary subtrees, closed by a zero node.
    Level n holds 4**(n - 1) chunks, so capacity grows with the data.

    An 85-chunk input fills four levels exactly:

                           root
                            /\
                           /  \
         1: chunks[0 ..< 1]   /\
                             /  \
           4: chunks[1 ..< 5]   /\
                               /  \
           16: chunks[5 ..< 21]   /\
                                 /  \
            64: chunks[21 ..< 85]    0

    A level opens only once the one before it is full.
    After n levels the total is (4**n - 1) // 3 chunks: 1, 5, 21, 85, 341.
    An empty input opens no level, and roots to the zero node itself.

    Appending extends the spine downward and moves nothing already placed.
    A chunk keeps its index, so a proof outlives every later append.

    The capacity argument is the current level's width, quadrupling as the recursion descends.
    Callers keep the default of one.
    """
    # An exhausted input terminates the spine with a zero node.
    #
    # The terminator is a plain zero leaf, not a zero subtree of some depth:
    # the level it stands for holds no data, so it has no width to pad out.
    # The deepest occupied level is padded.
    # Everything past it collapses to this one node.
    if len(chunks) == 0:
        return ZERO_ROOT

    # Left child: this level's chunks as a binary subtree, zero-padded to the level width.
    subtree_root = merkleize(chunks[:num_leaves], limit=num_leaves)

    # Right child: every chunk past this level, in a level four times as wide.
    successor_root = merkleize_progressive(chunks[num_leaves:], num_leaves * 4)

    # Invariant: a digest is exactly the chunk width.
    return Root._trusted(sha256(subtree_root + successor_root).digest())

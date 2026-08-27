"""Generalized indices and Merkle proof verification."""

import math
from collections.abc import Sequence
from hashlib import sha256
from typing import Final

from ssz.bitfields import BitList, BitVector, ProgressiveBitList
from ssz.boolean import Boolean
from ssz.byte_arrays import ByteList, ByteVector
from ssz.collections import List, ProgressiveList, Vector
from ssz.container import Container, ProgressiveContainer
from ssz.exceptions import SSZTypeError, SSZValueError
from ssz.merkleization import (
    BITS_PER_CHUNK,
    BYTES_PER_CHUNK,
    Chunk,
    Root,
    _next_pow2,
    hash_tree_root,
    merkle_layout,
    merkleize,
    merkleize_progressive,
)
from ssz.ssz_base import SSZType
from ssz.uint import BaseUint, Uint8
from ssz.union import CompatibleUnion

LENGTH_KEY: Final = "__len__"
"""Path step addressing the element count mixed into a variable-size root."""

ACTIVE_FIELDS_KEY: Final = "__active_fields__"
"""Path step addressing the field layout mixed into a progressive container root."""

SELECTOR_KEY: Final = "__selector__"
"""Path step addressing the type selector mixed into a compatible union root."""

type PathStep = int | str
"""One step of a path: a field name, an element position, or a mixed-in word."""


def _hash_pair(left: bytes, right: bytes) -> Root:
    """Join two nodes into their parent."""
    # Invariant: a digest is exactly the chunk width.
    return Root._trusted(sha256(left + right).digest())


def gindex_length(index: int) -> int:
    """
    Depth of a generalized index, which is the number of nodes on its proof branch.

    Read off the bit width rather than a logarithm.
    A float logarithm rounds the wrong way just below a power of two above 2**48.
    A deep progressive spine reaches that far.
    """
    _reject_unusable(index)
    return index.bit_length() - 1


def gindex_bit(index: int, position: int) -> bool:
    """Whether the branch turns right at the given depth, counted from the leaf."""
    return bool(index & (1 << position))


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

    A generalized index carries its depth in its leading bit.
    Rebasing therefore splices bit patterns rather than multiplying:

        outer 2, inner 24  ->  40, not 48

    Multiplying happens to work at depth one.
    It diverges immediately after, which is what makes it a mistake that passes a first test.
    """
    depth = gindex_length(inner)
    return (outer << depth) | (inner - (1 << depth))


def _progressive_chunk_gindex(chunk: int) -> int:
    """
    Position of one chunk on a progressive spine, measured from the root above the spine.

    A progressive tree is a right-leaning chain of perfect subtrees holding 1, 4, 16, 64 …
    chunks, closed by a zero node. Level n therefore holds 4**(n-1) chunks:

        level    chunks     spine node    subtree root    depth    first    last
          1      0..0            1              2           0         2       2
          2      1..4            3              6           2        24      27
          3      5..20           7             14           4       224     239
          4      21..84         15             30           6      1920    1983

    Those figures are for a spine at the root of a tree.
    Every progressive shape mixes a word into its root, which puts the spine one level down.
    The walk below therefore starts at the left child.

    This layout is written down nowhere upstream.
    Three EIPs assert that a chunk keeps its index as a collection grows.
    Each of them links to a document that cannot compute the index.
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


def item_length(ssz_type: type[SSZType]) -> int:
    """Bytes one element of this type occupies inside a chunk, or a whole chunk if composite."""
    if issubclass(ssz_type, (BaseUint, Boolean)):
        return ssz_type.get_byte_length()
    return BYTES_PER_CHUNK


def chunk_count(ssz_type: type[SSZType]) -> int:
    """
    Leaves this type merkleizes into, counting only its own level.

    A basic value is one leaf.
    Bits and basic elements pack, which puts several of them in one leaf.
    A composite element and a field each take a leaf of their own.

    Raises:
        SSZTypeError: When the type has no bounded leaf count.
    """
    if issubclass(ssz_type, (BaseUint, Boolean)):
        return 1
    if issubclass(ssz_type, BitVector):
        return math.ceil(ssz_type.LENGTH / BITS_PER_CHUNK)
    if issubclass(ssz_type, BitList):
        return math.ceil(ssz_type.LIMIT / BITS_PER_CHUNK)
    if issubclass(ssz_type, ByteVector):
        return math.ceil(ssz_type.LENGTH / BYTES_PER_CHUNK)
    if issubclass(ssz_type, ByteList):
        return math.ceil(ssz_type.LIMIT / BYTES_PER_CHUNK)
    if issubclass(ssz_type, Vector):
        return math.ceil(ssz_type.LENGTH * item_length(ssz_type.ELEMENT_TYPE) / BYTES_PER_CHUNK)
    if issubclass(ssz_type, List):
        return math.ceil(ssz_type.LIMIT * item_length(ssz_type.ELEMENT_TYPE) / BYTES_PER_CHUNK)
    if issubclass(ssz_type, Container):
        return len(ssz_type.model_fields)
    # A progressive shape grows without bound.
    # It therefore has no leaf count to report.
    raise SSZTypeError(f"{ssz_type.__name__} has no bounded chunk count")


def element_type(ssz_type: type[SSZType], step: PathStep) -> type[SSZType]:
    """
    Type reached by one step of a path.

    Raises:
        SSZTypeError: When the type has nothing to step into.
        SSZValueError: When a container has no field of that name.
    """
    if issubclass(ssz_type, (Container, ProgressiveContainer)):
        field = ssz_type.model_fields.get(str(step))
        if field is None:
            raise SSZValueError(f"{ssz_type.__name__} has no field named {step!r}")
        return field.annotation
    if issubclass(ssz_type, (BitVector, BitList, ProgressiveBitList)):
        return Boolean
    if issubclass(ssz_type, (ByteVector, ByteList)):
        # A byte array is a collection of single opaque bytes.
        return Uint8
    if issubclass(ssz_type, (Vector, List, ProgressiveList)):
        return ssz_type.ELEMENT_TYPE
    raise SSZTypeError(f"{ssz_type.__name__} cannot be stepped into")


def chunk_position(ssz_type: type[SSZType], step: PathStep) -> tuple[int, int, int]:
    """
    Where one element sits: its chunk, and the byte range it occupies inside that chunk.

    A generalized index names a chunk.
    Several packed elements share one:

        List[Uint64, 8], element 3  ->  chunk 0, bytes 24 to 32

    A proof to a packed element therefore authenticates every element sharing its chunk.
    The byte range is what tells a caller which part of the chunk was asked for.

    Raises:
        SSZTypeError: When the type has no positions to address.
        SSZValueError: When a container has no field of that name.
    """
    if issubclass(ssz_type, (Container, ProgressiveContainer)):
        names = list(ssz_type.model_fields)
        if str(step) not in names:
            raise SSZValueError(f"{ssz_type.__name__} has no field named {step!r}")
        return names.index(str(step)), 0, item_length(element_type(ssz_type, step))
    if issubclass(ssz_type, (BitVector, BitList, ProgressiveBitList)):
        # One bit occupies no whole byte.
        # A bit therefore reports a chunk with an empty range inside it.
        return int(step) // BITS_PER_CHUNK, 0, 0
    width = item_length(element_type(ssz_type, step))
    start = int(step) * width
    return start // BYTES_PER_CHUNK, start % BYTES_PER_CHUNK, start % BYTES_PER_CHUNK + width


def _field_layout_position(ssz_type: type[ProgressiveContainer], step: PathStep) -> int:
    """
    Layout position of one field of a progressive container.

    A field is merkleized at its position in the layout rather than at its ordinal.
    The n-th field therefore sits at the n-th set position, and a vacancy is skipped:

        layout (1, 0, 1, 1) with fields p, q, r  ->  p at 0, q at 2, r at 3

    Raises:
        SSZValueError: When the container has no field of that name.
    """
    names = list(ssz_type.model_fields)
    if str(step) not in names:
        raise SSZValueError(f"{ssz_type.__name__} has no field named {step!r}")
    set_positions = [i for i, bit in enumerate(ssz_type.ACTIVE_FIELDS) if bit]
    return set_positions[names.index(str(step))]


def get_generalized_index(ssz_type: type[SSZType], *path: PathStep) -> int:
    """
    Position in a Merkle tree of the value a path selects.

    A path is a sequence of field names and element positions.
    Three reserved steps address the words a root mixes in instead:

        get_generalized_index(BeaconState, "finalized_checkpoint", "root")
        get_generalized_index(Attestations, "__len__")

    Every variable-size shape hashes its contents against a mixed-in word.
    The contents therefore sit at the left child.
    The word sits at the right.

    Args:
        ssz_type: The type the path starts from.
        *path: Field names, element positions, and reserved words.

    Returns:
        The generalized index of the selected value.

    Raises:
        SSZTypeError:
            - When a step descends into a basic value, which has no parts.
            - When a reserved word is used on a type that mixes in no such word.
        SSZValueError: When a container has no field of the given name.
    """
    index = 1
    current = ssz_type
    for step in path:
        # A basic value is one leaf with nothing inside it.
        if issubclass(current, (BaseUint, Boolean)):
            raise SSZTypeError(f"{current.__name__} has no parts to address")

        if step == LENGTH_KEY:
            if not issubclass(
                current, (List, ByteList, BitList, ProgressiveList, ProgressiveBitList)
            ):
                raise SSZTypeError(f"{current.__name__} mixes in no element count")
            return gindex_child(index, right_side=True)

        if step == ACTIVE_FIELDS_KEY:
            if not issubclass(current, ProgressiveContainer):
                raise SSZTypeError(f"{current.__name__} mixes in no field layout")
            return gindex_child(index, right_side=True)

        if step == SELECTOR_KEY:
            if not issubclass(current, CompatibleUnion):
                raise SSZTypeError(f"{current.__name__} mixes in no type selector")
            return gindex_child(index, right_side=True)

        if issubclass(current, CompatibleUnion):
            option = current.OPTIONS.get(int(step))
            if option is None:
                raise SSZValueError(f"{current.__name__} has no option with selector {step!r}")
            # Every option shares the left child.
            # That is what keeps a field common to several options at one position.
            index = gindex_child(index, right_side=False)
            current = option
            continue

        if issubclass(current, ProgressiveContainer):
            position = _field_layout_position(current, step)
            index = gindex_concat(index, _progressive_chunk_gindex(position))
            current = element_type(current, step)
            continue

        if issubclass(current, (ProgressiveList, ProgressiveBitList)):
            chunk, _, _ = chunk_position(current, step)
            index = gindex_concat(index, _progressive_chunk_gindex(chunk))
            current = element_type(current, step)
            continue

        chunk, _, _ = chunk_position(current, step)
        # A mixed-in element count sits at the right child.
        # The contents therefore start one level down, on the left.
        if issubclass(current, (List, ByteList, BitList)):
            index = gindex_child(index, right_side=False)
        index = index * _next_pow2(chunk_count(current)) + chunk
        current = element_type(current, step)

    return index


def _reject_unusable(index: int) -> None:
    """
    Refuse the two indices that name no provable node.

    Raises:
        SSZValueError:
            - When the index is the root, which proves nothing about itself.
            - When the index is below the root, naming no node at all.
    """
    if index < 1:
        raise SSZValueError(f"{index} is not a generalized index")
    if index == 1:
        raise SSZValueError("the root has no proof branch of its own")


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


def get_helper_indices(indices: Sequence[int]) -> list[int]:
    """
    Nodes a proof must carry to authenticate all the given ones at once.

    Every sibling on every branch is needed, with two exceptions:

    - A node the caller already claims.
    - A node the verifier rebuilds on the way up.

    The result descends.
    A single-node request therefore produces exactly the branch a plain proof carries:
    the leaf's sibling first, the root's sibling last.

    Raises:
        SSZValueError:
            - When an index is repeated, which would drop a leaf silently.
            - When one index lies on the path of another.
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


def _reject_related(indices: Sequence[int]) -> None:
    """
    Refuse an index set that cannot be verified soundly.

    Two shapes of input are unsound rather than merely odd:

    - A repeated index keeps only one of the values given for it.
      The other is dropped without a word.
    - An index above another on the same branch is rebuilt from below.
      The value given for the lower one therefore never reaches the root, and goes unchecked.

    Raises:
        SSZValueError:
            - When an index is repeated.
            - When one index lies on the path of another.
    """
    seen = set(indices)
    if len(seen) != len(indices):
        raise SSZValueError("a generalized index is repeated")
    for index in indices:
        # A walk upward opens at the index itself, which is no ancestor of its own.
        # One claimed ancestor is already too many, so the first one ends the search.
        if any(ancestor in seen for ancestor in get_path_indices(index)[1:]):
            raise SSZValueError(f"{index} lies below another index in the same request")


def node_root(value: object, index: int) -> Root:
    """
    Root of the subtree at one generalized index of a value's own Merkle tree.

    This is the one function that reads a generalized index against real data.
    It follows the index down through the layouts the value merkleizes into.
    What it lands on may be a leaf, an internal node, or a mixed-in word.

    Index 1 is the root itself, whose subtree is the whole value.

    Args:
        value: The value whose tree the index is measured in.
        index: Generalized index of the wanted node.

    Returns:
        The root of the subtree at that index.

    Raises:
        SSZValueError:
            - When the index is not a generalized index.
            - When the index descends into a mixed-in word, which has no parts.
            - When the index descends into packed data, which has no parts.
            - When the index descends into a position this value leaves empty.
            - When the index lies past the end of a progressive spine.
    """
    if index < 1:
        raise SSZValueError(f"{index} is not a generalized index")
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
                raise SSZValueError(f"the path descends into {name}'s mixed-in word")
            # Invariant: a mixed-in word is exactly one chunk wide.
            return Root._trusted(layout.mixin)

    # First leaf of the bounded subtree the walk ends in, and that subtree's capacity.
    leaves_from, capacity = 0, layout.limit
    if capacity is None:
        # A progressive spine holds its levels on the left and the rest of itself on the right.
        # Walking right skips one level's leaves and quadruples the width of the next.
        #
        # A spine is only as long as its data, closing with a zero node holding nothing.
        # Both turns below therefore refuse once no leaf is left:
        #
        #     ProgressiveList[Uint64] holding two elements  ->  chunk 0 is a node, chunk 5 is not
        #
        # The exit between them is exempt, because a closed spine's terminator is a node.
        spine_closed = f"the path lies past the end of {name}'s progressive spine"
        capacity = 1
        while depth and gindex_bit(index, depth - 1):
            if leaves_from >= layout.leaf_count:
                raise SSZValueError(spine_closed)
            leaves_from, capacity, depth = leaves_from + capacity, capacity * 4, depth - 1
        if depth == 0:
            # The index names a spine node, whose root covers every leaf still to come.
            return merkleize_progressive(layout.chunks(leaves_from), capacity)
        # The index turns left instead, into the bounded subtree holding this level.
        if leaves_from >= layout.leaf_count:
            raise SSZValueError(spine_closed)
        depth -= 1

    width = _next_pow2(capacity)
    tree_depth = width.bit_length() - 1

    if depth <= tree_depth:
        # The index names a node of the bounded subtree, which spans a run of leaves.
        # Merkleizing that run alone gives its root, padding included.
        span = width >> depth
        start = leaves_from + (index & ((1 << depth) - 1)) * span
        return merkleize(layout.chunks(start, start + span), limit=span)

    # Deeper than the subtree: the rest of the index is measured inside one leaf's own tree.
    depth -= tree_depth
    leaf = leaves_from + ((index >> depth) & ((1 << tree_depth) - 1))
    if layout.nested is None:
        raise SSZValueError(f"the path descends into the packed data of {name}")
    if leaf >= layout.leaf_count or layout.nested[leaf] is None:
        raise SSZValueError(f"the path descends into an empty position of {name}")
    return node_root(layout.nested[leaf], (1 << depth) | (index & ((1 << depth) - 1)))


def build_proof(value: object, index: int) -> list[Root]:
    """
    Branch that authenticates one generalized index of a value against its root.

    Every node on the path from the index to the root contributes its sibling.
    The order runs bottom-up, the leaf's sibling first, as a verifier reads it.
    """
    return [node_root(value, sibling) for sibling in get_branch_indices(index)]


def build_multiproof(value: object, indices: Sequence[int]) -> list[Root]:
    """
    Nodes that authenticate several generalized indices of a value at once.

    Only the nodes a verifier cannot rebuild for itself are carried.
    The claimed nodes are the caller's to supply:

        leaves = [node_root(state, index) for index in indices]
        proof = build_multiproof(state, indices)
        assert verify_merkle_multiproof(leaves, proof, indices, hash_tree_root(state))
    """
    return [node_root(value, helper) for helper in get_helper_indices(indices)]


def calculate_merkle_root(leaf: Chunk, proof: Sequence[Chunk], index: int) -> Root:
    """
    Rebuild a root from one leaf and its branch.

    Each bit of the index, read from the leaf upward, says which side the branch node joins on.

    Raises:
        SSZValueError: When the branch length does not match the depth of the index.
    """
    depth = gindex_length(index)
    if len(proof) != depth:
        raise SSZValueError(f"a branch for index {index} holds {depth} nodes, got {len(proof)}")
    node = leaf
    for level, sibling in enumerate(proof):
        node = _hash_pair(sibling, node) if gindex_bit(index, level) else _hash_pair(node, sibling)
    # Invariant: the depth of a provable index is at least one.
    # The loop above therefore ran and
    # left a digest behind. Re-measuring it would only re-derive what _hash_pair guarantees.
    return Root._trusted(node)


def verify_merkle_proof(leaf: Chunk, proof: Sequence[Chunk], index: int, root: Root) -> bool:
    """Whether one leaf and its branch rebuild the expected root."""
    return calculate_merkle_root(leaf, proof, index) == root


def calculate_multi_merkle_root(
    leaves: Sequence[Chunk], proof: Sequence[Chunk], indices: Sequence[int]
) -> Root:
    """
    Rebuild a root from several leaves and the nodes they share.

    Pairs are combined from the deepest index upward.
    A parent is only built once, and only when neither it nor a deeper claim already holds it.

    Raises:
        SSZValueError:
            - When the request holds no index at all.
            - When the leaf count does not match the index count.
            - When the proof does not hold exactly the nodes the indices need.
            - When the indices are repeated or lie on one another's paths.
    """
    if not indices:
        raise SSZValueError("a request holds at least one index")
    if len(leaves) != len(indices):
        raise SSZValueError(f"{len(indices)} indices need as many leaves, got {len(leaves)}")
    helpers = get_helper_indices(indices)
    if len(proof) != len(helpers):
        raise SSZValueError(f"this request needs {len(helpers)} proof nodes, got {len(proof)}")

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
    """Whether several leaves and their shared nodes rebuild the expected root."""
    return calculate_multi_merkle_root(leaves, proof, indices) == root

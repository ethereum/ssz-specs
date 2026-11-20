"""
Roots kept current by change notification, for the native backend.

A value rooted here keeps its root until a mutation reaches it.
A mutation drops that root and tells each parent that relied on it, up to the outermost value.
A vector or list also keeps its whole tree, and the positions written since its last root.
Its next root rehashes the paths above those positions alone.

The specification's own roots never come here: it remembers roots by witness instead.
Every hash runs in the proved routines; Python only decides which nodes to hash.
"""

from __future__ import annotations

import ctypes
import threading
import weakref
from array import array
from collections.abc import Callable, Iterable, Sequence
from operator import itemgetter
from typing import Any, Final, cast

from ssz import native, roots, stored
from ssz.boolean import Boolean
from ssz.chunks import BYTES_PER_CHUNK, ZERO_ROOT, next_pow2
from ssz.collections import List, Vector
from ssz.container import Container
from ssz.exceptions import SSZValueError, ValueFault
from ssz.layout import NestedLeaves, _pack_basic_elements, field_names, merkle_layout
from ssz.lazy import LazyElements
from ssz.mixins import length_word
from ssz.ssz_base import SSZModel, SSZType
from ssz.uint import BaseUint

_LIBRARY: Final = native._library()
"""The proved routines, loaded once the backend is known to run."""


def _routine(name: str, *argtypes: Any) -> Any:
    """A routine of its own, so its argument types never clash with another binding's."""
    routine = _LIBRARY[name]
    routine.restype = ctypes.c_uint64
    routine.argtypes = argtypes
    return routine


_POINTER, _COUNT = ctypes.c_void_p, ctypes.c_uint64

_HASH_PAIRS: Final = _routine("ssz_hash_pairs", _POINTER, _POINTER, _POINTER, _COUNT, _POINTER)
"""Parents of adjacent pairs: lefts 64 bytes apart, each right 32 bytes past its left."""

_HASH_COLUMNS: Final = _routine("ssz_hash_columns", _POINTER, _POINTER, _POINTER, _COUNT, _POINTER)
"""Parents of two columns: the i-th left node with the i-th right node, each 32 bytes apart."""

_MERKLEIZE: Final = _routine(
    "ssz_merkleize", ctypes.c_char_p, _COUNT, _COUNT, _POINTER, _POINTER, _POINTER
)
"""The root of chunks under a tree of a given depth, padded with zero subtrees."""

_TREE_BUILD: Final = _routine("ssz_tree_build", _POINTER, _POINTER, _COUNT, _POINTER)
"""Hash a whole tree from its leaves, which already sit in its leaf level."""

_TREE_UPDATE: Final = _routine(
    "ssz_tree_update", _POINTER, _COUNT, _POINTER, _COUNT, _POINTER, _POINTER
)
"""Rehash the paths above rewritten leaves, given by increasing position, a level per pass."""

_TREE_ROOT: Final = _routine(
    "ssz_tree_root", _POINTER, _COUNT, _COUNT, _POINTER, _POINTER, _POINTER
)
"""Climb a tree's top node to a depth against zero subtrees, then mix a word in."""

_TREE_DEPTHS: Final = 64
"""The deepest tree the routines climb; a deeper one climbs here, a level per call."""


class _Buffers(threading.local):
    """A thread's buffers: its context words, a climbing area, and a scratch for small trees."""

    def __init__(self) -> None:
        """Take the context words the binding keeps for this thread, and size the rest."""
        # The routines read the words through their address, so this thread keeps them alive.
        self.context = native._context()
        self.words = ctypes.addressof(self.context[0])
        # Two nodes to climb between, then the word mixed in last.
        self.climb = (ctypes.c_char * 96)()
        self.climb_address = ctypes.addressof(self.climb)
        self.scratch = (ctypes.c_char * 0)()
        self.scratch_address = ctypes.addressof(self.scratch)
        # A tree's root, then the word mixed into it, apart from every tree.
        self.root = (ctypes.c_char * 64)()
        self.root_address = ctypes.addressof(self.root)

    def scratch_of(self, size: int) -> int:
        """The address of a scratch area of at least a size, grown and kept for later calls."""
        if len(self.scratch) < size:
            self.scratch = (ctypes.c_char * size)()
            self.scratch_address = ctypes.addressof(self.scratch)
        return self.scratch_address


_BUFFERS: Final = _Buffers()
"""Each thread's buffers."""


class _Zeros:
    """The roots of all-zero subtrees, by depth, in one buffer the routines read in place."""

    def __init__(self) -> None:
        """Start from the table the routines carry, which holds depths 0 through 64."""
        table = ctypes.c_char.in_dll(_LIBRARY, "ssz_zero_roots")
        self.depths = 65
        self.nodes = ctypes.create_string_buffer(ctypes.string_at(ctypes.addressof(table), 2080))
        self.address = ctypes.addressof(self.nodes)

    def reach(self, depth: int) -> int:
        """The address of the table, holding at least every depth below the one given."""
        if depth > self.depths:
            grown = ctypes.create_string_buffer(self.nodes.raw, 32 * depth)
            base = ctypes.addressof(grown)
            for level in range(self.depths, depth):
                below = base + 32 * (level - 1)
                _HASH_COLUMNS(base + 32 * level, below, below, 1, _BUFFERS.words)
            self.nodes, self.address, self.depths = grown, base, depth
        return self.address


_ZEROS: Final = _Zeros()
"""The zero subtree roots, grown when a tree is deeper than the routines' table."""


def _climb(node: bytes, start: int, stop: int, mixin: bytes | None) -> bytes:
    """
    Hash a node from one depth up to another against zero subtrees, then mix a word in.

    The node is the root of a subtree of depth start; the answer is a root of depth stop.
    Only trees past the routines' depths climb here, so start always lies below stop.
    """
    buffers = _BUFFERS
    area, base, words = buffers.climb, buffers.climb_address, buffers.words
    zeros = _ZEROS.reach(stop)
    area[0:32] = node
    # The node moves between the first two slots, each hash reading one and writing the other.
    at = 0
    for depth in range(start, stop):
        _HASH_COLUMNS(base + 32 - at, base + at, zeros + 32 * depth, 1, words)
        at = 32 - at
    if mixin is not None:
        area[64:96] = mixin
        _HASH_COLUMNS(base + 32 - at, base + at, base + 64, 1, words)
        at = 32 - at
    return bytes(area[at : at + 32])


def _merkleize(chunks: bytes, count: int) -> bytes:
    """The root of a few chunks under the smallest tree that holds them."""
    if count == 1:
        return chunks
    depth = (count - 1).bit_length()
    buffers = _BUFFERS
    scratch = buffers.scratch_of(32 * count + 32 * depth + 96)
    # The root lands at the start of the scratch, which the routine never reads before writing.
    _MERKLEIZE(chunks, count, depth, scratch, scratch + 32, buffers.words)
    return ctypes.string_at(scratch, 32)


class _Tree:
    """
    A sequence's whole tree, kept between roots, with the positions written since.

    Node i sits at 32 * i, its children at 2i and 2i + 1, the leaves at the width onwards.
    The width is a power of two at or above the leaf count, and never shrinks.
    Leaves past the count are zero, so the tree climbs to the same root as the smallest one.
    A position of None stands for a write that may have moved any of them.
    """

    __slots__ = ("address", "count", "depth", "nodes", "positions", "touch", "view", "width")

    def __init__(self, width: int) -> None:
        """A tree of a width, every node zero, with every position still to write."""
        self.nodes = bytearray(64 * width)
        # The routines write the buffer in place through this view, which pins it.
        self.view = (ctypes.c_char * len(self.nodes)).from_buffer(self.nodes)
        self.address = ctypes.addressof(self.view)
        self.width = width
        self.depth = 0
        self.count = 0
        self.positions: set[int | None] = {None}
        # Every write records its position here, so the set's own method takes it with no frame.
        self.touch = self.positions.add

    def clone(self) -> _Tree:
        """An independent tree with the same nodes and the same positions still to write."""
        twin = _Tree.__new__(_Tree)
        twin.nodes = bytearray(self.nodes)
        twin.view = (ctypes.c_char * len(twin.nodes)).from_buffer(twin.nodes)
        twin.address = ctypes.addressof(twin.view)
        twin.width, twin.depth, twin.count = self.width, self.depth, self.count
        twin.positions = set(self.positions)
        twin.touch = twin.positions.add
        return twin

    def rehash(self) -> None:
        """Hash every node from the leaves up, in one call."""
        base = self.address
        _TREE_BUILD(base, base + 32 * self.width, self.width, _BUFFERS.words)

    def rehash_paths(self, positions: list[int]) -> None:
        """Hash the parents above some rewritten leaves, each shared parent once, in one call."""
        indices = array("Q", sorted(positions))
        buffers = _BUFFERS
        scratch = buffers.scratch_of(104 * len(indices))
        _TREE_UPDATE(
            self.address, self.width, indices.buffer_info()[0], len(indices), scratch, buffers.words
        )

    def root(self, mixin: bytes | None) -> bytes:
        """The root of the tree at its depth, with a word mixed in where the shape has one."""
        if self.depth > _TREE_DEPTHS:
            return _climb(bytes(self.nodes[32:64]), self.width.bit_length() - 1, self.depth, mixin)
        buffers = _BUFFERS
        out = buffers.root_address
        word = 0
        if mixin is not None:
            buffers.root[32:64] = mixin
            word = out + 32
        _TREE_ROOT(self.address, self.width, self.depth, word, out, buffers.words)
        return bytes(buffers.root[0:32])


_get_kept = SSZModel.__dict__["_kept"].__get__
_set_kept = SSZModel.__dict__["_kept"].__set__
_get_links = SSZModel.__dict__["_links"].__get__
_set_links = SSZModel.__dict__["_links"].__set__
_get_tree = SSZModel.__dict__["_tree"].__get__
_set_tree = SSZModel.__dict__["_tree"].__set__


def _kept_of(value: SSZModel) -> bytes | None:
    """The root a value keeps, or None where it keeps none."""
    try:
        return _get_kept(value)
    except AttributeError:
        return None


def _link(child: SSZModel, parent: weakref.ref[SSZModel], position: int) -> None:
    """Record that a parent relies on a child's root at a position, once."""
    try:
        links = _get_links(child)
    except AttributeError:
        links = None
    if links is None:
        _set_links(child, (parent, position))
    elif type(links) is tuple:
        if links[0] is not parent or links[1] != position:
            _set_links(child, [links, (parent, position)])
    elif not any(held is parent and at == position for held, at in links):
        # Parents gone since are dropped here, so a long-lived value does not collect them.
        links[:] = [(held, at) for held, at in links if held() is not None]
        links.append((parent, position))


_COMPOSITE, _WORD, _BYTES, _NOTHING, _OTHER = range(5)
"""The kinds of leaf, each rooted by its own rule of the specification."""

_LEAF_KINDS: Final[dict[type, int]] = {}
"""The kind of leaf each class is, resolved once per class."""


def _leaf_kind(cls: type) -> int:
    """The kind of leaf a class is, by the branch of the root function its values take."""
    kind = _LEAF_KINDS.get(cls)
    if kind is None:
        if issubclass(cls, SSZModel):
            kind = _COMPOSITE
        elif issubclass(cls, (BaseUint, Boolean)) and cls.get_byte_length() <= BYTES_PER_CHUNK:
            kind = _WORD
        elif issubclass(cls, bytes):
            kind = _BYTES
        elif cls is type(None):
            kind = _NOTHING
        else:
            kind = _OTHER
        _LEAF_KINDS[cls] = kind
    return kind


def _bytes_root(value: bytes) -> bytes:
    """The root of a byte string: its chunks, under a tree just wide enough for them."""
    if len(value) <= BYTES_PER_CHUNK:
        return bytes(value).ljust(BYTES_PER_CHUNK, b"\x00")
    count = (len(value) + BYTES_PER_CHUNK - 1) // BYTES_PER_CHUNK
    return _merkleize(bytes(value).ljust(BYTES_PER_CHUNK * count, b"\x00"), count)


def _leaf(value: object, parent: weakref.ref[SSZModel], position: int) -> bytes:
    """
    The root a value contributes as a leaf, linking a composite to the parent that reads it.

    Each branch is the specification's own rule for that kind of value, read from the value.
    """
    kind = _LEAF_KINDS.get(type(value))
    if kind is None:
        kind = _leaf_kind(type(value))
    if kind == _WORD:
        return cast("int", value).to_bytes(BYTES_PER_CHUNK, "little")
    if kind == _COMPOSITE:
        composite = cast("SSZModel", value)
        root = _root(composite)
        _link(composite, parent, position)
        return root
    if kind == _BYTES:
        return _bytes_root(cast("bytes", value))
    if kind == _NOTHING:
        return ZERO_ROOT
    return bytes(roots.hash_tree_root(value))


def _paranoid(value: SSZModel, kept: bytes) -> bytes:
    """A kept root checked against one computed afresh, where paranoid mode asks for that."""
    if roots.PARANOID_ROOTS and bytes(roots._root_from_layout(value)) != bytes(kept):
        raise SSZValueError(ValueFault.STALE_ROOT, type=type(value).__name__)
    return kept


def _root_by_layout(value: SSZModel) -> bytes:
    """The root of any shape, from the layout the specification states, children kept."""
    kept = _kept_of(value)
    if kept is not None:
        return _paranoid(value, kept)
    layout = merkle_layout(value)
    if isinstance(layout.leaves, NestedLeaves):
        parent = weakref.ref(value)
        chunks = [_leaf(child, parent, at) for at, child in enumerate(layout.leaves.values)]
    else:
        chunks = list(layout.leaves.chunks)
    root = bytes(roots.root_of_layout(layout, chunks))
    _set_kept(value, root)
    return root


def _root_of_container(value: SSZModel) -> bytes:
    """The root of a struct: one leaf per field, under the smallest tree that holds them."""
    kept = _kept_of(value)
    if kept is not None:
        return _paranoid(value, kept)
    names = field_names(type(value))
    stored = value.__dict__
    parent = weakref.ref(value)
    root = _merkleize(
        b"".join([_leaf(stored[name], parent, at) for at, name in enumerate(names)]), len(names)
    )
    _set_kept(value, root)
    return root


_REHASH_SHARE: Final = 8
"""The leaves written per level of depth past which rehashing every level is cheaper."""


def _root_of_sequence(value: SSZModel) -> bytes:
    """
    The root of a vector or list from its kept tree, rehashing above written positions alone.

    A tree is built whole the first time, after a write that may have moved anything, and when
    the leaves outgrow it.
    """
    data = cast("Sequence[Any]", value.__dict__["data"])
    try:
        tree: _Tree | None = _get_tree(value)
    except AttributeError:
        tree = None
    kept = _kept_of(value)
    # A count changed without a mutator's word is caught here, as the specification's witness does.
    if kept is not None and tree is not None and tree.count == len(data):
        return _paranoid(value, kept)
    element_type: type[SSZType] = cast("type[List[Any]]", type(value)).ELEMENT_TYPE
    packed = issubclass(element_type, (BaseUint, Boolean))
    if tree is None or None in tree.positions or (tree.count != len(data) and not tree.positions):
        return _build(value, tree)
    size = element_type.get_byte_length() if packed else BYTES_PER_CHUNK
    per_chunk = BYTES_PER_CHUNK // size
    count = (len(data) + per_chunk - 1) // per_chunk
    if count > tree.width:
        return _build(value, tree)
    nodes, width = tree.nodes, tree.width
    positions = cast("set[int]", tree.positions)
    written: list[int] = []
    if packed:
        # Writes spread over more chunks than a partial rehash pays off for are packed whole.
        if len(positions) * _REHASH_SHARE > width * per_chunk:
            return _build(value, tree)
        for chunk in {position // per_chunk for position in positions}:
            if chunk < width:
                start = chunk * per_chunk
                leaf = b"".join(_pack_basic_elements(data[start : start + per_chunk], size))
                at = 32 * (width + chunk)
                nodes[at : at + 32] = leaf.ljust(BYTES_PER_CHUNK, b"\x00")
                written.append(chunk)
    else:
        written = [position for position in positions if position < width]
        _write_children(value, data, nodes, width, written)
    if written:
        if len(written) * _REHASH_SHARE > width:
            tree.rehash()
        else:
            tree.rehash_paths(written)
    tree.positions.clear()
    tree.count = len(data)
    root = tree.root(length_word(len(data)) if isinstance(value, List) else None)
    _set_kept(value, root)
    return root


def _write_children(
    value: SSZModel, data: Sequence[Any], nodes: bytearray, width: int, positions: list[int]
) -> None:
    """
    Write the roots of a sequence's children at some positions into its leaf level.

    Many structs of one class are rooted together, as a first build roots them.
    A position past the last element is a zero leaf.
    """
    parent = weakref.ref(value)
    held = len(data)
    present = [position for position in positions if position < held]
    children = [data[position] for position in present]
    classes = set(map(type, children))
    if len(children) >= _BATCH and len(classes) == 1:
        (cls,) = classes
        if issubclass(cls, SSZModel) and _rule_of(cls) is _root_of_container:
            leaves = _roots_of_structs(cls, children)
            for at, (position, child) in enumerate(zip(present, children, strict=True)):
                leaf = leaves[32 * at : 32 * at + 32]
                _set_kept(child, leaf)
                _link(child, parent, position)
                nodes[32 * (width + position) : 32 * (width + position) + 32] = leaf
            present = []
    for position in present:
        nodes[32 * (width + position) : 32 * (width + position) + 32] = _leaf(
            data[position], parent, position
        )
    for position in positions:
        if position >= held:
            nodes[32 * (width + position) : 32 * (width + position) + 32] = ZERO_ROOT


_BATCH: Final = 16
"""The element count from which a sequence of structs is rooted a field at a time."""


def _address(buffer: bytearray) -> tuple[object, int]:
    """A buffer's address for the routines, and the view that pins it while they run."""
    view = (ctypes.c_char * len(buffer)).from_buffer(buffer)
    return view, ctypes.addressof(view)


def _hash_columns(left: bytearray, right: bytearray) -> bytearray:
    """The parents of two columns of nodes, the i-th left with the i-th right."""
    out = bytearray(len(left))
    (out_view, out_at), (left_view, left_at), (right_view, right_at) = (
        _address(out),
        _address(left),
        _address(right),
    )
    _HASH_COLUMNS(out_at, left_at, right_at, len(left) // 32, _BUFFERS.words)
    del out_view, left_view, right_view
    return out


def _hash_rows(nodes: bytearray) -> bytearray:
    """The parents of adjacent pairs of nodes, which halves every row of a power-of-two width."""
    out = bytearray(len(nodes) // 2)
    (out_view, out_at), (nodes_view, nodes_at) = _address(out), _address(nodes)
    _HASH_PAIRS(out_at, nodes_at, nodes_at + 32, len(nodes) // 64, _BUFFERS.words)
    del out_view, nodes_view
    return out


def _column(values: list[Any], structs: list[SSZModel], position: int) -> bytearray:
    """
    The leaves one field gives across many structs, back to back, by the rule of each value.

    Words and equal-width bytes are laid out by bulk copies, and hashed a level per call.
    Anything else is rooted one value at a time, and linked to the struct that holds it.
    """
    count = len(values)
    kinds = {_leaf_kind(cls) for cls in set(map(type, values))}
    classes = cast("set[type[BaseUint]]", set(map(type, values)))
    if kinds == {_WORD} and all(cls.get_byte_length() <= 8 for cls in classes):
        # Each word's eight bytes, little-endian, at the start of its own chunk.
        packed = array("Q", values).tobytes()
        column = bytearray(BYTES_PER_CHUNK * count)
        for at in range(8):
            column[at::BYTES_PER_CHUNK] = packed[at::8]
        return column
    if kinds == {_BYTES} and len(widths := set(map(len, values))) == 1:
        (width,) = widths
        joined = b"".join(values)
        if width == BYTES_PER_CHUNK:
            return bytearray(joined)
        # Each value's chunks, padded to a power of two, then hashed a level per call.
        chunks = next_pow2(max((width + BYTES_PER_CHUNK - 1) // BYTES_PER_CHUNK, 1))
        stride = BYTES_PER_CHUNK * chunks
        rows = bytearray(stride * count)
        for at in range(width):
            rows[at::stride] = joined[at::width]
        while len(rows) > BYTES_PER_CHUNK * count:
            rows = _hash_rows(rows)
        return rows
    return bytearray(
        b"".join(
            [
                _leaf(value, weakref.ref(struct), position)
                for value, struct in zip(values, structs, strict=True)
            ]
        )
    )


def _roots_of_structs(cls: type[SSZModel], structs: list[SSZModel]) -> bytes:
    """
    The roots of many structs of one class, back to back, hashed a field level per call.

    The i-th leaf of every struct forms one column, and each level of the field tree hashes
    two columns into one, so the routines see every struct's tree at once.
    """
    stores = [struct.__dict__ for struct in structs]
    columns = [
        _column(list(map(itemgetter(name), stores)), structs, position)
        for position, name in enumerate(field_names(cls))
    ]
    zero = bytearray(BYTES_PER_CHUNK * len(structs))
    columns += [zero] * (next_pow2(len(columns)) - len(columns))
    while len(columns) > 1:
        columns = [_hash_columns(columns[at], columns[at + 1]) for at in range(0, len(columns), 2)]
    return bytes(columns[0])


def _nested_leaves(value: SSZModel, children: tuple[Any, ...]) -> bytes:
    """
    The leaves of a sequence of composites: the root of each, linked to the sequence.

    Many structs of one class are rooted together, and each keeps its root.
    """
    parent = weakref.ref(value)
    classes = set(map(type, children))
    if len(children) >= _BATCH and len(classes) == 1:
        (cls,) = classes
        if issubclass(cls, SSZModel) and _rule_of(cls) is _root_of_container:
            structs = list(children)
            leaves = _roots_of_structs(cls, structs)
            set_kept, get_links, set_links = _set_kept, _get_links, _set_links
            for position, struct in enumerate(structs):
                set_kept(struct, leaves[32 * position : 32 * position + 32])
                # A struct never placed before has no links, the one case worth inlining.
                try:
                    links = get_links(struct)
                except AttributeError:
                    links = None
                if links is None:
                    set_links(struct, (parent, position))
                else:
                    _link(struct, parent, position)
            return leaves
    return b"".join([_leaf(child, parent, at) for at, child in enumerate(children)])


def _build(value: SSZModel, tree: _Tree | None) -> bytes:
    """Lay a sequence's leaves out as the specification states them, then hash every level."""
    data = value.__dict__["data"]
    if type(data) is LazyElements:
        return _build_lazy(value, tree, data)
    layout = merkle_layout(value)
    if isinstance(layout.leaves, NestedLeaves):
        leaves = _nested_leaves(value, layout.leaves.values)
    else:
        leaves = b"".join(layout.leaves.chunks)
    count = len(leaves) // 32
    limit = layout.limit
    assert limit is not None
    # The specification refuses more leaves than the capacity, and names the counts.
    if count > limit:
        return bytes(
            roots.root_of_layout(layout, [leaves[i : i + 32] for i in range(0, len(leaves), 32)])
        )
    return _plant(value, tree, leaves, limit, layout.mixin)


def _plant(
    value: SSZModel, tree: _Tree | None, leaves: bytes | bytearray, limit: int, mixin: bytes | None
) -> bytes:
    """Write a sequence's leaves into its tree, grown if they outgrow it, and hash every level."""
    count = len(leaves) // 32
    width = next_pow2(max(count, 1))
    if tree is None or tree.width < width:
        tree = _Tree(width)
        _set_tree(value, tree)
    else:
        width = tree.width
        tree.nodes[32 * width + len(leaves) :] = bytes(64 * width - 32 * width - len(leaves))
    tree.nodes[32 * width : 32 * width + len(leaves)] = leaves
    tree.rehash()
    tree.depth = next_pow2(limit).bit_length() - 1
    tree.count = len(value.__dict__["data"])
    tree.positions.clear()
    root = tree.root(mixin)
    _set_kept(value, root)
    return root


def _build_lazy(value: SSZModel, tree: _Tree | None, data: LazyElements) -> bytes:
    """
    Build a lazily decoded sequence's tree from its encoding, reading no element still in it.

    The elements still in the encoding are rooted by the routines in one call.
    Each element decoded or written since is rooted from its value, and linked.
    """
    cls = cast("type[List[Any]]", type(value))
    element_type = cls.ELEMENT_TYPE
    is_list = isinstance(value, List)
    capacity = cls.LIMIT if is_list else cls.LENGTH
    assert capacity is not None
    if issubclass(element_type, (BaseUint, Boolean)):
        size = element_type.get_byte_length()
        packed = data.fixed_encoding()
        leaves: bytes | bytearray = packed.ljust(-(-len(packed) // 32) * 32, b"\x00")
        limit = (capacity * size + BYTES_PER_CHUNK - 1) // BYTES_PER_CHUNK
    else:
        leaves = stored.element_roots(cls, data) if data.original else bytearray()
        parent = weakref.ref(value)
        items = data.items
        leaves += bytes(32 * (len(items) - data.original))
        for position in data.held():
            leaves[32 * position : 32 * position + 32] = _leaf(items[position], parent, position)
        limit = capacity
    mixin = length_word(len(data)) if is_list else None
    return _plant(value, tree, leaves, limit, mixin)


def element_read(owner: weakref.ref[SSZModel], position: int, element: object) -> None:
    """
    Give an element decoded from a sequence's encoding the root its tree already holds.

    The element then tells the sequence of any write, as one rooted from its value would.
    A sequence with no current tree roots the element from its value when it next roots.
    """
    sequence = owner()
    if sequence is None or not isinstance(element, SSZModel):
        return
    try:
        tree: _Tree | None = _get_tree(sequence)
    except AttributeError:
        return
    if (
        tree is None
        or position >= tree.width
        or None in tree.positions
        or position in tree.positions
    ):
        return
    # A struct of leaves takes the root its bytes gave, and anything else roots to link its parts.
    if _is_shallow(type(element)):
        at = 32 * (tree.width + position)
        _set_kept(element, bytes(tree.nodes[at : at + 32]))
    else:
        _root(element)
    _link(element, owner, position)


_SHALLOW: Final[dict[type, bool]] = {}
"""Whether each class is a struct whose declared fields hold no composite, resolved once."""


def _is_shallow(cls: type) -> bool:
    """Whether a class is a struct whose declared fields hold no composite."""
    shallow = _SHALLOW.get(cls)
    if shallow is None:
        shallow = issubclass(cls, Container) and not any(
            issubclass(field, SSZModel) for _, field in cls._FIELD_TYPES
        )
        _SHALLOW[cls] = shallow
    return shallow


_RULES: Final[dict[type, Callable[[SSZModel], bytes]]] = {}
"""The rule each class roots by, resolved once per class."""


def _rule_of(cls: type) -> Callable[[SSZModel], bytes]:
    """The rule a class roots by: a kept tree, a struct's fields, or the stated layout."""
    rule = _RULES.get(cls)
    if rule is None:
        if issubclass(cls, (Vector, List)):
            rule = _root_of_sequence
        elif issubclass(cls, Container):
            rule = _root_of_container
        else:
            rule = _root_by_layout
        _RULES[cls] = rule
    return rule


def _root(value: SSZModel) -> bytes:
    """A composite's root, kept until a mutation reaches it."""
    return _rule_of(type(value))(value)


def model_root(value: object) -> bytes:
    """
    A composite's root, as the hook the root function asks.

    The root is kept as the one object every later call hands back until a mutation.
    """
    assert isinstance(value, SSZModel)
    root = _root(value)
    if type(root) is not roots.Root:
        root = roots.Root._trusted(root)
        _set_kept(value, root)
    return root


def model_copied(original: object, duplicate: object) -> None:
    """
    Hand a kept root and tree on to a duplicate whose parts are duplicates themselves.

    Each part's duplicate kept its own root, and now names the duplicate as its parent.
    A value keeping no root hands nothing on, and its duplicate roots from scratch.
    """
    assert isinstance(original, SSZModel) and isinstance(duplicate, SSZModel)
    kept = _kept_of(original)
    if kept is None:
        return
    try:
        tree: _Tree | None = _get_tree(original)
    except AttributeError:
        tree = None
    # Each rule links its parts at the positions it reads them from.
    rule = _rule_of(type(original))
    parts: Iterable[tuple[int, object]]
    if rule is _root_of_container:
        stored = duplicate.__dict__
        parts = enumerate([stored[name] for name in field_names(type(duplicate))])
    elif rule is _root_of_sequence:
        # A sequence keeps its root only beside the tree it was hashed from.
        assert tree is not None
        data = duplicate.__dict__["data"]
        _set_tree(duplicate, tree.clone())
        # Elements still in the encoding link themselves when they are first read.
        if type(data) is LazyElements:
            parts = [(position, data.items[position]) for position in data.held()]
        # Integers and booleans have no root of their own to link.
        elif issubclass(cast("type[List[Any]]", type(original)).ELEMENT_TYPE, (BaseUint, Boolean)):
            parts = ()
        else:
            parts = enumerate(data)
    else:
        leaves = merkle_layout(duplicate).leaves
        parts = enumerate(leaves.values if isinstance(leaves, NestedLeaves) else ())
    parent = weakref.ref(duplicate)
    for position, part in parts:
        if isinstance(part, SSZModel):
            # A part keeping no root was placed past every mutator, so the copy roots afresh.
            if _kept_of(part) is None:
                if tree is not None:
                    _get_tree(duplicate).touch(None)
                return
            _link(part, parent, position)
    _set_kept(duplicate, kept)

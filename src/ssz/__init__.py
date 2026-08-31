"""
SSZ primitive types, (de)serialization, merkleization and proofs for Ethereum.

The modules below are listed in the order they build on one another.
An alphabetical listing scrambles that order.

    exceptions    the two ways SSZ refuses something, and every reason for each
    base          pydantic glue shared by the types
    ssz_base      the abstract bases every SSZ type stands on
    offsets       the table a variable-size shape puts in front of its bodies

    boolean       a true or false value
    uint          the unsigned integers, and the byte
    byte_arrays   fixed and variable byte strings
    bitfields     fixed, bounded and progressive bit sequences
    collections   vectors, lists and progressive lists
    container     structs, with a fixed or a progressive field layout
    union         a value that is one of several declared options

    chunks        the 32-byte unit a tree is built from, and the trees that hold none
    trees         the two tree shapes: bounded by a capacity, or progressive
    mixins        the words a root is hashed against
    layout        what a value merkleizes into, stated before any of it is hashed
    roots         rooting a value, and the witness that lets a root be reused

    gindex        naming one node of a tree, and the nodes a proof of it needs
    paths         a path through a type, resolved to a generalized index
    proofs        reading an index against a value, and building the proofs
    verification  rebuilding a root from chunks and indices, reading no declaration

Serialization, deserialization and the JSON mapping have no module of their own.
Each type carries them as methods, since every shape encodes itself.
"""

from ssz.bitfields import BitList, BitVector, ProgressiveBitList
from ssz.boolean import Bit, Boolean
from ssz.byte_arrays import (
    ByteList,
    ByteVector,
)
from ssz.chunks import BITS_PER_CHUNK, BYTES_PER_CHUNK, ZERO_ROOT, Chunk, Root
from ssz.collections import List, ProgressiveList, Vector
from ssz.container import Container, ProgressiveContainer, active_fields
from ssz.exceptions import (
    SSZError,
    SSZTypeError,
    SSZValueError,
    TypeFault,
    ValueFault,
)
from ssz.gindex import (
    get_branch_indices,
    get_helper_indices,
    get_path_indices,
    gindex_below,
    gindex_bit,
    gindex_child,
    gindex_concat,
    gindex_length,
    gindex_parent,
    gindex_rebase,
    gindex_sibling,
    progressive_chunk_gindex,
)
from ssz.layout import MerkleLayout, merkle_layout
from ssz.mixins import (
    active_fields_word,
    length_word,
    mix_in_active_fields,
    mix_in_length,
    mix_in_selector,
    selector_word,
)
from ssz.paths import (
    ACTIVE_FIELDS_KEY,
    LENGTH_KEY,
    SELECTOR_KEY,
    ChunkPosition,
    PathStep,
    chunk_count,
    chunk_position,
    element_type,
    get_generalized_index,
    item_length,
)
from ssz.proofs import build_multiproof, build_proof, node_root
from ssz.roots import hash_tree_root
from ssz.ssz_base import SSZType
from ssz.trees import merkleize, merkleize_progressive
from ssz.uint import Byte, Uint8, Uint16, Uint32, Uint64, Uint128, Uint256
from ssz.union import CompatibleUnion
from ssz.verification import (
    calculate_merkle_root,
    calculate_multi_merkle_root,
    verify_merkle_multiproof,
    verify_merkle_proof,
)

__all__ = [
    "ACTIVE_FIELDS_KEY",
    "BITS_PER_CHUNK",
    "BYTES_PER_CHUNK",
    "Bit",
    "BitList",
    "BitVector",
    "Boolean",
    "Byte",
    "ByteList",
    "ByteVector",
    "Chunk",
    "ChunkPosition",
    "CompatibleUnion",
    "Container",
    "LENGTH_KEY",
    "List",
    "MerkleLayout",
    "PathStep",
    "ProgressiveBitList",
    "ProgressiveContainer",
    "ProgressiveList",
    "Root",
    "SELECTOR_KEY",
    "SSZError",
    "SSZType",
    "SSZTypeError",
    "SSZValueError",
    "TypeFault",
    "Uint128",
    "Uint16",
    "Uint256",
    "Uint32",
    "Uint64",
    "Uint8",
    "ValueFault",
    "Vector",
    "ZERO_ROOT",
    "active_fields",
    "active_fields_word",
    "build_multiproof",
    "build_proof",
    "calculate_merkle_root",
    "calculate_multi_merkle_root",
    "chunk_count",
    "chunk_position",
    "element_type",
    "get_branch_indices",
    "get_generalized_index",
    "get_helper_indices",
    "get_path_indices",
    "gindex_below",
    "gindex_bit",
    "gindex_child",
    "gindex_concat",
    "gindex_length",
    "gindex_parent",
    "gindex_rebase",
    "gindex_sibling",
    "hash_tree_root",
    "item_length",
    "length_word",
    "merkle_layout",
    "merkleize",
    "merkleize_progressive",
    "mix_in_active_fields",
    "mix_in_length",
    "mix_in_selector",
    "node_root",
    "progressive_chunk_gindex",
    "selector_word",
    "verify_merkle_multiproof",
    "verify_merkle_proof",
]

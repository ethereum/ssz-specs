"""SSZ primitive types and (de)serialization for Ethereum."""

from ssz.bitfields import BitList, BitVector, ProgressiveBitList
from ssz.boolean import Bit, Boolean
from ssz.byte_arrays import (
    ByteList,
    ByteVector,
)
from ssz.chunks import ZERO_ROOT, Chunk, Root
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
    "node_root",
    "progressive_chunk_gindex",
    "verify_merkle_multiproof",
    "verify_merkle_proof",
]

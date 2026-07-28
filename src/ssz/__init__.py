"""SSZ primitive types and (de)serialization for Ethereum."""

from ssz.bitfields import BitList, BitVector, ProgressiveBitList
from ssz.boolean import Bit, Boolean
from ssz.byte_arrays import (
    ByteList,
    ByteVector,
)
from ssz.collections import List, ProgressiveList, Vector
from ssz.container import Container, ProgressiveContainer, active_fields
from ssz.exceptions import (
    SSZActiveFieldsError,
    SSZDefaultError,
    SSZDefinitionError,
    SSZError,
    SSZFixedSizeError,
    SSZLengthError,
    SSZLimitError,
    SSZRangeError,
    SSZScopeError,
    SSZSerializationError,
    SSZTypeError,
    SSZTypeMismatch,
    SSZUnionOptionsError,
    SSZValueError,
)
from ssz.merkleization import ZERO_ROOT, Chunk, Root
from ssz.ssz_base import SSZType
from ssz.uint import Byte, Uint8, Uint16, Uint32, Uint64, Uint128, Uint256
from ssz.union import CompatibleUnion

__all__ = [
    "ZERO_ROOT",
    "Bit",
    "BitList",
    "BitVector",
    "Boolean",
    "Byte",
    "ByteList",
    "ByteVector",
    "Chunk",
    "CompatibleUnion",
    "Container",
    "List",
    "ProgressiveBitList",
    "ProgressiveContainer",
    "ProgressiveList",
    "Root",
    "SSZActiveFieldsError",
    "SSZDefaultError",
    "SSZDefinitionError",
    "SSZError",
    "SSZFixedSizeError",
    "SSZLengthError",
    "SSZLimitError",
    "SSZRangeError",
    "SSZScopeError",
    "SSZSerializationError",
    "SSZType",
    "SSZTypeError",
    "SSZTypeMismatch",
    "SSZUnionOptionsError",
    "SSZValueError",
    "Uint8",
    "Uint16",
    "Uint32",
    "Uint64",
    "Uint128",
    "Uint256",
    "Vector",
    "active_fields",
]

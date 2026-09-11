"""Snappy block encoding, the compression the `ssz_generic` tree publishes its bytes under."""

from typing import Final

TAG_LITERAL: Final = 0b00
"""Two low bits of a tag byte marking the element that follows as literal bytes."""

INLINE_LITERAL_LIMIT: Final = 60
"""Literal lengths up to this are held in the tag byte, longer ones spill into trailing bytes."""


def _varint(value: int) -> bytes:
    """Encode a non-negative integer as a base-128 varint, seven bits per byte, low group first."""
    groups = bytearray()
    while value >= 0x80:
        groups.append((value & 0x7F) | 0x80)
        value >>= 7
    groups.append(value)
    return bytes(groups)


def compress(data: bytes) -> bytes:
    """Encode bytes as one Snappy block: the decompressed length, then one literal element."""
    preamble = _varint(len(data))
    if not data:
        return preamble

    literal_length = len(data) - 1
    if literal_length < INLINE_LITERAL_LIMIT:
        return preamble + bytes([literal_length << 2 | TAG_LITERAL]) + data

    trailing = (literal_length.bit_length() + 7) // 8
    tag = (INLINE_LITERAL_LIMIT - 1 + trailing) << 2 | TAG_LITERAL
    return preamble + bytes([tag]) + literal_length.to_bytes(trailing, "little") + data

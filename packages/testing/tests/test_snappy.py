"""Bytes the Snappy block encoder emits, against the encoding the format defines."""

import pytest

from ssz_testing.snappy import compress

# Every expectation below is read off the Snappy format description rather than off the encoder.
#
# A block opens with the decompressed length as a base-128 varint, seven bits per byte, low
# group first with the high bit marking a group that is not the last. Then comes one element,
# here always a literal: a tag byte whose two low bits are zero, and whose upper six bits hold
# the literal length minus one when that fits in them. Sixty, sixty-one, sixty-two and
# sixty-three in those bits instead mean the length minus one follows in one, two, three or
# four little-endian bytes.
LITERAL_BLOCKS = [
    (b"", b"\x00"),
    (b"A", b"\x01\x00A"),
    (b"AB", b"\x02\x04AB"),
    (b"z" * 59, b"\x3b\xe8" + b"z" * 59),
    (b"z" * 60, b"\x3c\xec" + b"z" * 60),
    (b"z" * 61, b"\x3d\xf0\x3c" + b"z" * 61),
    (b"z" * 127, b"\x7f\xf0\x7e" + b"z" * 127),
    (b"z" * 128, b"\x80\x01\xf0\x7f" + b"z" * 128),
    (b"z" * 300, b"\xac\x02\xf4\x2b\x01" + b"z" * 300),
    (b"z" * 16384, b"\x80\x80\x01\xf4\xff\x3f" + b"z" * 16384),
]


@pytest.mark.parametrize("data,block", LITERAL_BLOCKS, ids=lambda value: str(len(value)))
def test_the_block_is_the_length_then_the_bytes_as_one_literal(data: bytes, block: bytes) -> None:
    """Each length spans a boundary of the varint preamble or of the literal tag."""
    assert compress(data) == block


def test_nothing_compresses_to_the_length_alone() -> None:
    """An empty input carries no element at all, so the block is the varint zero and nothing."""
    assert compress(b"") == b"\x00"


def test_the_same_bytes_always_give_the_same_block() -> None:
    """A release asset is byte-reproducible, so the encoder holds no state between calls."""
    data = bytes(range(256)) * 4

    assert compress(data) == compress(data)

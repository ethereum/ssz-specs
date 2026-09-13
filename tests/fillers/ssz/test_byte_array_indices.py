"""SSZ conformance test vectors for paths that step into a bit array or a byte array."""

import pytest

from ssz import (
    BitVector,
    ByteList,
    ByteVector,
    CompatibleUnion,
    List,
    ProgressiveContainer,
    Uint8,
    Uint16,
    Uint64,
    ValueFault,
)
from ssz.paths import LENGTH_KEY
from ssz_testing import ELEMENT_COUNT_STEP, GindexTestFiller, ProofTestFiller

pytestmark = pytest.mark.tags("gindex", "proofs")

A_NUMERIC_STRING_POSITION_IS_COERCED = (
    'merkle-proofs.md reads an element position as int(step), so it takes the string "3" for '
    "position 3 and answers a generalized index where this suite refuses the path"
)
"""What the specification does with a position spelled as the digits of an integer."""


class ByteArrayRoot(ByteVector):
    """Thirty-two bytes, the width of one chunk, as a block root or a graffiti field is."""

    LENGTH = 32


class ByteArraySignature(ByteVector):
    """Ninety-six bytes across three chunks, as a BLS signature is."""

    LENGTH = 96


class ByteArrayBitVector512(BitVector):
    """Five hundred and twelve bits across two chunks, 256 bits to a chunk."""

    LENGTH = 512


class ByteArrayBlob(ByteList):
    """A hundred and thirty-one thousand bytes of capacity, 4096 chunks of it."""

    LIMIT = 131_072


class ByteArrayUint64List8(List[Uint64]):
    """Bounded list of eight-byte elements, standing as a shape a position steps into."""

    LIMIT = 8


class ByteArraySquare(ProgressiveContainer):
    """One union option, holding a private field at position 0 and a shared one at position 2."""

    ACTIVE_FIELDS = (1, 0, 1)

    side: Uint16
    color: Uint8


class ByteArrayCircle(ProgressiveContainer):
    """The other union option, holding the same shared field at the same position."""

    ACTIVE_FIELDS = (0, 1, 1)

    radius: Uint16
    color: Uint8


class ByteArrayShape(CompatibleUnion):
    """Two options a selector picks between, that selector being a position of its own."""

    OPTIONS = {1: ByteArraySquare, 2: ByteArrayCircle}


SIGNATURE = ByteArraySignature(bytes(range(96)))
"""Ninety-six distinct bytes, so a branch to one chunk cannot pass by reading another."""

BLOB = ByteArrayBlob(data=bytes((index * 7 + 1) % 256 for index in range(128)))
"""A hundred and twenty-eight bytes filled of the declared capacity, four chunks of it."""


def test_a_byte_of_a_single_chunk_byte_vector(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A byte array no wider than one chunk merkleizes to that chunk, which is its own root.

    Given
    -----
    - a fixed array of exactly 32 bytes, one chunk and no more.
    - a path naming byte 5.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 1, the root itself, because one leaf pads to a tree one wide.
    - proving a byte of a 32-byte root therefore proves the root, and the branch is empty;
      a client expecting an index below 1 here is holding a shape that has no below.
    """
    ssz_gindex_test(
        case_id="byte_array_index/byte_vector/single_chunk_is_the_root",
        type_name="ByteArrayRoot",
        ssz_type=ByteArrayRoot,
        path=(5,),
        gindex=1,
    )


def test_a_byte_in_the_second_chunk_of_a_byte_vector(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A byte array counts its leaves in bytes, 32 to a chunk.

    Given
    -----
    - a fixed array of 96 bytes, three chunks padding to a tree four wide.
    - a path naming byte 40.

    When
    ----
    - the path is resolved.

    Then
    ----
    - byte 40 lands in chunk 1, which is index 5.
    """
    ssz_gindex_test(
        case_id="byte_array_index/byte_vector/byte_in_the_second_chunk",
        type_name="ByteArraySignature",
        ssz_type=ByteArraySignature,
        path=(40,),
        gindex=5,
    )


def test_the_last_byte_of_a_byte_vector(ssz_gindex_test: GindexTestFiller) -> None:
    """
    The last byte of a three-chunk array sits in the last chunk holding data.

    Given
    -----
    - the same fixed array of 96 bytes, whose fourth leaf is the zero padding.
    - a path naming byte 95.

    When
    ----
    - the path is resolved.

    Then
    ----
    - byte 95 lands in chunk 2, which is index 6.
    """
    ssz_gindex_test(
        case_id="byte_array_index/byte_vector/last_byte",
        type_name="ByteArraySignature",
        ssz_type=ByteArraySignature,
        path=(95,),
        gindex=6,
    )


def test_a_bit_of_a_bit_vector(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A fixed bit array mixes in nothing, so its chunks sit directly under the root.

    Given
    -----
    - a fixed array of 512 bits, two chunks of 256 bits each.
    - a path naming bit 300.

    When
    ----
    - the path is resolved.

    Then
    ----
    - bit 300 lands in chunk 1, which is index 3.
    - the matching bitlist answers 5, the element count having pushed the data one level down.
    """
    ssz_gindex_test(
        case_id="byte_array_index/bit_vector/bit_in_the_second_chunk",
        type_name="ByteArrayBitVector512",
        ssz_type=ByteArrayBitVector512,
        path=(300,),
        gindex=3,
    )


def test_the_last_bit_of_the_first_chunk_of_a_bit_vector(
    ssz_gindex_test: GindexTestFiller,
) -> None:
    """
    A bit array packs 256 positions per chunk, not 32.

    Given
    -----
    - the same fixed array of 512 bits.
    - a path naming bit 255.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 2, the first chunk, which holds bits 0 through 255.
    """
    ssz_gindex_test(
        case_id="byte_array_index/bit_vector/last_bit_of_the_first_chunk",
        type_name="ByteArrayBitVector512",
        ssz_type=ByteArrayBitVector512,
        path=(255,),
        gindex=2,
    )


def test_the_first_bit_of_the_second_chunk_of_a_bit_vector(
    ssz_gindex_test: GindexTestFiller,
) -> None:
    """
    Bit 256 opens the second chunk, where counting a bit array in bytes would place bit 32.

    Given
    -----
    - the same fixed array of 512 bits.
    - a path naming bit 256.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 3, one past the chunk bit 255 sits in.
    """
    ssz_gindex_test(
        case_id="byte_array_index/bit_vector/first_bit_of_the_second_chunk",
        type_name="ByteArrayBitVector512",
        ssz_type=ByteArrayBitVector512,
        path=(256,),
        gindex=3,
    )


def test_a_byte_of_a_byte_list(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A byte list resolves against its declared capacity, not against the bytes it holds.

    Given
    -----
    - a byte list of at most 131072 bytes, 4096 chunks of capacity.
    - a path naming byte 100.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the element count takes the right child, so the data starts at index 2.
    - byte 100 lands in chunk 3, which is index 8195.
    """
    ssz_gindex_test(
        case_id="byte_array_index/byte_list/byte_in_the_fourth_chunk",
        type_name="ByteArrayBlob",
        ssz_type=ByteArrayBlob,
        path=(100,),
        gindex=8195,
    )


def test_the_byte_count_of_a_byte_list(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A byte list mixes its byte count in, the same word any other variable-size shape does.

    Given
    -----
    - the same byte list of at most 131072 bytes.
    - a path of the one reserved step naming the element count.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 3, whatever the capacity below it is.
    """
    ssz_gindex_test(
        case_id="byte_array_index/byte_list/byte_count",
        type_name="ByteArrayBlob",
        ssz_type=ByteArrayBlob,
        path=(ELEMENT_COUNT_STEP,),
        gindex=3,
    )


def test_a_proof_of_a_byte_of_a_byte_vector(proof_test: ProofTestFiller) -> None:
    """
    A byte of a fixed byte array is proved by the chunk it shares with 31 neighbours.

    Given
    -----
    - a 96-byte array holding the bytes 0 through 95.
    - byte 40, which sits in the second of three chunks.

    When
    ----
    - the path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 5.
    - the leaf is bytes 32 through 63, so the proof reveals the whole chunk.
    - the branch holds two nodes, the second covering the third chunk and its zero pad.
    - the branch rebuilds the value's root.
    """
    proof_test(
        case_id="byte_array_index/proof/byte_of_a_byte_vector",
        type_name="ByteArraySignature",
        value=SIGNATURE,
        path=(40,),
        expected_index=5,
    )


def test_a_proof_of_a_byte_of_a_byte_list(proof_test: ProofTestFiller) -> None:
    """
    A byte of a byte list is proved against a tree as deep as the capacity, not the data.

    Given
    -----
    - a byte list of at most 131072 bytes, holding 128 of them.
    - byte 100, which sits in chunk 3.

    When
    ----
    - the path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 8195.
    - the branch holds thirteen nodes: two chunks of data, then ten zero subtrees, then
      the mixed-in byte count.
    - the value fills four chunks and the capacity declares 4096, so the depth is the
      declaration's and the padding is what most of the branch carries.
    - the branch rebuilds the value's root.
    """
    proof_test(
        case_id="byte_array_index/proof/byte_of_a_byte_list",
        type_name="ByteArrayBlob",
        value=BLOB,
        path=(100,),
        expected_index=8195,
    )


def test_a_proof_of_the_byte_count_of_a_byte_list(proof_test: ProofTestFiller) -> None:
    """
    The byte count of a byte list is a leaf of its own, one node from the root.

    Given
    -----
    - the same byte list, holding 128 bytes.
    - the reserved step naming the mixed-in byte count.

    When
    ----
    - the path is resolved, the leaf read off the tree, and the branch built.

    Then
    ----
    - the path resolves to generalized index 3.
    - the leaf is 128 as a little-endian 32-byte word, counting bytes and not chunks.
    - the branch rebuilds the value's root.
    """
    proof_test(
        case_id="byte_array_index/proof/byte_count_of_a_byte_list",
        type_name="ByteArrayBlob",
        value=BLOB,
        path=(LENGTH_KEY,),
        expected_index=3,
    )


def test_a_string_position_in_a_list_is_refused(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A position is an integer, and a string spelling one is not coerced into it.

    Given
    -----
    - a list of at most eight eight-byte elements.
    - a path whose one step is the string "3".

    When
    ----
    - the path is resolved.

    Then
    ----
    - the type refuses with NOT_A_POSITION.
    - a resolver that coerced would answer index 4 and never say that it had guessed.
    - the specification is the resolver that coerces, and the vector says so.
    """
    ssz_gindex_test(
        case_id="byte_array_index/refused/string_position_in_a_list",
        type_name="ByteArrayUint64List8",
        ssz_type=ByteArrayUint64List8,
        path=("3",),
        refusal=ValueFault.NOT_A_POSITION,
        stricter_than_spec=A_NUMERIC_STRING_POSITION_IS_COERCED,
    )


def test_a_string_position_in_a_bit_vector_is_refused(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A bit array has no field names, so a string step names nothing it can reach.

    Given
    -----
    - a fixed array of 512 bits.
    - a path whose one step is the string "256".

    When
    ----
    - the path is resolved.

    Then
    ----
    - the type refuses with NOT_A_POSITION.
    """
    ssz_gindex_test(
        case_id="byte_array_index/refused/string_position_in_a_bit_vector",
        type_name="ByteArrayBitVector512",
        ssz_type=ByteArrayBitVector512,
        path=("256",),
        refusal=ValueFault.NOT_A_POSITION,
    )


def test_a_string_selector_in_a_union_is_refused(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A union selector is a position too, and a string spelling one is refused alike.

    Given
    -----
    - a union declaring selectors 1 and 2.
    - a path naming the first option as the string "1".

    When
    ----
    - the path is resolved.

    Then
    ----
    - the type refuses with NOT_A_POSITION, rather than reading the string as a selector.
    """
    ssz_gindex_test(
        case_id="byte_array_index/refused/string_selector_in_a_union",
        type_name="ByteArrayShape",
        ssz_type=ByteArrayShape,
        path=("1",),
        refusal=ValueFault.NOT_A_POSITION,
    )

"""Unit tests for generalized indices and Merkle proof verification."""

from __future__ import annotations

from hashlib import sha256
from typing import Any, cast

import pytest

from ssz import (
    ZERO_ROOT,
    BitList,
    BitVector,
    Boolean,
    ByteList,
    ByteVector,
    Chunk,
    CompatibleUnion,
    Container,
    List,
    ProgressiveBitList,
    ProgressiveContainer,
    ProgressiveList,
    Root,
    SSZType,
    SSZTypeError,
    SSZValueError,
    Uint8,
    Uint16,
    Uint64,
    Vector,
    active_fields,
    calculate_merkle_root,
    calculate_multi_merkle_root,
    chunk_count,
    chunk_position,
    element_type,
    get_branch_indices,
    get_generalized_index,
    get_helper_indices,
    get_path_indices,
    item_length,
    verify_merkle_multiproof,
    verify_merkle_proof,
)
from ssz.merkleization import hash_tree_root, merkleize
from ssz.proofs import (
    ACTIVE_FIELDS_KEY,
    LENGTH_KEY,
    SELECTOR_KEY,
    PathStep,
    _progressive_chunk_gindex,
    build_multiproof,
    build_proof,
    gindex_bit,
    gindex_child,
    gindex_concat,
    gindex_length,
    gindex_parent,
    gindex_sibling,
    node_root,
)


def h(left: bytes, right: bytes) -> Root:
    """Pairwise SHA-256 of two 32-byte nodes, used to build expected roots by hand."""
    return Root(sha256(left + right).digest())


def word(value: int) -> Chunk:
    """One 32-byte little-endian word, the shape every mixed-in count and layout takes."""
    return Chunk(value.to_bytes(32, "little"))


class Bytes32(ByteVector):
    """Fixed 32-byte array, standing in for a block or state root."""

    LENGTH = 32


class Checkpoint(Container):
    """Two-field struct whose second field is the value a light client proves."""

    epoch: Uint64
    root: Bytes32


class SyncCommittee(Container):
    """One-field stand-in for the committee struct two published indices address."""

    pubkey: Bytes32


def state_fields(width: int) -> dict[str, Any]:
    """
    One field per position of a beacon state stand-in.

    Only three positions matter to the published indices:

        position 20   a two-field struct, stepped into for its second field
        position 22   a struct reached whole
        position 23   a struct reached whole

    Every other position holds a basic value, since only the count of them moves an index.
    """
    annotations: dict[str, Any] = {}
    for position in range(width):
        if position == 20:
            annotations[f"f{position}"] = Checkpoint
        elif position in (22, 23):
            annotations[f"f{position}"] = SyncCommittee
        else:
            annotations[f"f{position}"] = Uint64
    return annotations


# The altair beacon state declares 24 fields, which pads its leaf tree to 32.
AltairState = cast(
    "type[SSZType]",
    type("AltairState", (Container,), {"__annotations__": state_fields(24)}),
)

# The gloas beacon state declares a 46-position layout with no gaps.
GloasState = cast(
    "type[SSZType]",
    type(
        "GloasState",
        (ProgressiveContainer,),
        {"ACTIVE_FIELDS": active_fields(width=46), "__annotations__": state_fields(46)},
    ),
)


class Uint64List8(List[Uint64]):
    """Bounded list of eight-byte elements, two chunks of capacity."""

    LIMIT = 8


class Uint64Vector8(Vector[Uint64]):
    """Fixed sequence of eight-byte elements, two chunks wide."""

    LENGTH = 8


class Bitlist512(BitList):
    """Bounded bit sequence spanning two chunks of capacity."""

    LIMIT = 512


class Bitvector512(BitVector):
    """Fixed bit sequence spanning two chunks."""

    LENGTH = 512


class ByteList64(ByteList):
    """Bounded byte sequence spanning two chunks of capacity."""

    LIMIT = 64


class Bytes64(ByteVector):
    """Fixed byte sequence spanning two chunks."""

    LENGTH = 64


class Uint64ProgressiveList(ProgressiveList[Uint64]):
    """Unbounded sequence of eight-byte elements."""


class Pair(Container):
    """Two-field struct, reached as a whole and stepped into."""

    a: Uint64
    b: Uint64


class PairVector4(Vector[Pair]):
    """Fixed sequence of composite elements, one chunk each."""

    LENGTH = 4


class PairList8(List[Pair]):
    """Bounded list of composite elements, each taking a leaf of its own."""

    LIMIT = 8


class Quad(Container):
    """Four-field struct with a composite last field, filling four leaves with no padding."""

    p: Uint64
    q: Uint64
    r: Uint64
    z: Pair


class Triple(Container):
    """Three-field struct whose fourth leaf is the zero pad a multiproof must carry."""

    x: Uint64
    y: Uint64
    z: Pair


class Spine(ProgressiveContainer):
    """Three fields on a gapless layout, occupying the first two spine levels."""

    ACTIVE_FIELDS = (1, 1, 1)

    f0: Uint64
    f1: Uint64
    f2: Uint64


class GappedSpine(ProgressiveContainer):
    """Two fields with position 1 vacant, putting the second field at position 2."""

    ACTIVE_FIELDS = (1, 0, 1)

    first: Uint64
    third: Uint64


class Square(ProgressiveContainer):
    """One union option, holding a shared field at position 2."""

    ACTIVE_FIELDS = (1, 0, 1)

    side: Uint16
    color: Uint8


class Circle(ProgressiveContainer):
    """The other union option, holding the same shared field at the same position."""

    ACTIVE_FIELDS = (0, 1, 1)

    radius: Uint16
    color: Uint8


class Shape(CompatibleUnion):
    """Two options that merkleize alike, differing only in their private field."""

    OPTIONS = {1: Square, 2: Circle}


def state_value(state_type: type[SSZType], width: int) -> Any:
    """One value per position of a beacon state stand-in, matching the declared types."""
    values: dict[str, Any] = {}
    for position in range(width):
        if position == 20:
            values[f"f{position}"] = Checkpoint(
                epoch=Uint64(position), root=Bytes32(bytes([position]) * 32)
            )
        elif position in (22, 23):
            values[f"f{position}"] = SyncCommittee(pubkey=Bytes32(bytes([position]) * 32))
        else:
            values[f"f{position}"] = Uint64(position)
    return state_type(**values)


def round_trip(value: object, index: int) -> bool:
    """Whether the node at an index, the branch built for it, and the value's root agree."""
    return verify_merkle_proof(
        node_root(value, index), build_proof(value, index), index, hash_tree_root(value)
    )


def resolvable_indices(value: object, limit: int = 256) -> set[int]:
    """Every index below the limit that names a node of this value's own tree."""
    found: set[int] = set()
    for index in range(2, limit):
        try:
            node_root(value, index)
        except SSZValueError:
            continue
        found.add(index)
    return found


# One composite value, reused as a field, an element and a nested target.
PAIR = Pair(a=Uint64(4), b=Uint64(5))

# Four fields fill four leaves exactly.
# No padding sits in the way.
QUAD = Quad(p=Uint64(1), q=Uint64(2), r=Uint64(3), z=PAIR)

# Three fields pad to four leaves, leaving the fourth as the pad.
TRIPLE = Triple(x=Uint64(1), y=Uint64(2), z=PAIR)

# Two of eight eight-byte elements.
# Chunk 0 holds them both, leaving chunk 1 all zero.
SPARSE_LIST = Uint64List8(data=(Uint64(7), Uint64(8)))

# Two of eight composite elements, each taking a leaf, leaving six zero leaves.
SPARSE_PAIR_LIST = PairList8(data=(PAIR, PAIR))

VECTOR_OF_BASICS = Uint64Vector8(data=tuple(Uint64(position) for position in range(8)))
VECTOR_OF_COMPOSITES = PairVector4(data=(PAIR, PAIR, PAIR, PAIR))

# The same four positions with one element of their own at position 2.
# The ends are one value and the middle is not, so the elements are neither all one value
# nor all distinct, and a proof reads them a range at a time.
ODD_ONE_OUT = Pair(a=Uint64(6), b=Uint64(7))
VECTOR_WITH_A_REPEAT = PairVector4(data=(PAIR, PAIR, ODD_ONE_OUT, PAIR))

# 300 bits spill into the second of two capacity chunks.
BITLIST = Bitlist512(data=(Boolean(True),) * 300)
BITVECTOR = Bitvector512(data=(Boolean(True), Boolean(False)) * 256)
BYTE_LIST = ByteList64(data=b"abc")

# One chunk of data opens level 1 alone.
# The spine closes immediately after it.
SHORT_PROGRESSIVE = Uint64ProgressiveList(data=(Uint64(1), Uint64(2)))

# Six eight-byte elements pack into two chunks.
# That opens level 2 and no more.
TWO_LEVEL_PROGRESSIVE = Uint64ProgressiveList(data=tuple(Uint64(i) for i in range(6)))

# A hundred eight-byte elements pack into 25 chunks.
# That reaches level 4.
WIDE_PROGRESSIVE = Uint64ProgressiveList(data=tuple(Uint64(i) for i in range(100)))

PROGRESSIVE_BITS = ProgressiveBitList(data=(Boolean(True),) * 300)

SPINE_VALUE = Spine(f0=Uint64(11), f1=Uint64(22), f2=Uint64(33))
GAPPED_VALUE = GappedSpine(first=Uint64(1), third=Uint64(3))
SHAPE_VALUE = Shape(selector=Uint8(1), data=Square(side=Uint16(0x1234), color=Uint8(0x42)))

ALTAIR_VALUE = state_value(AltairState, 24)
GLOAS_VALUE = state_value(GloasState, 46)


class TestGindexArithmetic:
    """Index arithmetic: depth, turns, neighbours, and rebasing."""

    @pytest.mark.parametrize(
        "index, expected_depth",
        [
            pytest.param(2, 1, id="left_child_of_the_root"),
            pytest.param(3, 1, id="right_child_of_the_root"),
            pytest.param(4, 2, id="two_levels_down"),
            pytest.param(15, 3, id="three_levels_down"),
            pytest.param(105, 6, id="finalized_root_depth"),
            pytest.param(2945, 11, id="progressive_spine_depth"),
        ],
    )
    def test_depth_counts_the_nodes_on_a_branch(self, index: int, expected_depth: int) -> None:
        """The depth of an index is the number of siblings a proof against it carries."""
        assert gindex_length(index) == expected_depth
        assert len(get_branch_indices(index)) == expected_depth

    def test_depth_stays_exact_past_float_precision(self) -> None:
        """Depth is read off the bit width, which no rounding step can shift."""
        # A float logarithm rounds up at the top of a wide range:
        #
        #     2**48 - 1 = 281_474_976_710_655  ->  log2 gives 47.999..., depth 47
        #     2**49 - 1 = 562_949_953_421_311  ->  log2 gives 49.0,      depth 48
        #
        # The second reading would send a proof one level too deep.
        assert gindex_length(2**48 - 1) == 47
        assert gindex_length(2**49 - 1) == 48

    @pytest.mark.parametrize(
        "index, turns",
        [
            # Index 6 is 0b110: left from the leaf, then right.
            pytest.param(6, [False, True], id="left_then_right"),
            # Index 15 is 0b1111: right at every level.
            pytest.param(15, [True, True, True], id="right_all_the_way"),
            # Index 8 is 0b1000: left at every level.
            pytest.param(8, [False, False, False], id="left_all_the_way"),
        ],
    )
    def test_a_bit_reads_the_turn_at_one_depth(self, index: int, turns: list[bool]) -> None:
        """Each bit above the leading one says which side the branch node joins on."""
        assert [gindex_bit(index, depth) for depth in range(len(turns))] == turns

    def test_neighbours_of_one_node(self) -> None:
        """A node reaches its sibling, its two children, and its parent by arithmetic alone."""
        assert gindex_sibling(6) == 7
        assert gindex_sibling(7) == 6
        assert gindex_child(6, right_side=False) == 12
        assert gindex_child(6, right_side=True) == 13
        assert gindex_parent(13) == 6

    def test_rebasing_splices_bits_rather_than_multiplying(self) -> None:
        """An index measured from one root rebases onto a larger tree by concatenation."""
        # Multiplying agrees at depth one and diverges immediately after:
        #
        #     outer 2, inner 2   ->  concat 4,  product 4    (agree)
        #     outer 2, inner 24  ->  concat 40, product 48   (diverge)
        #
        # The leading bit of the inner index carries its depth and must be dropped, not kept.
        assert gindex_concat(2, 2) == 4
        assert gindex_concat(2, 24) == 40
        assert gindex_concat(2, 24) != 2 * 24

    def test_rebasing_onto_the_root_changes_nothing(self) -> None:
        """An index already measured from the root rebases onto it unchanged."""
        assert gindex_concat(1, 367) == 367

    @pytest.mark.parametrize(
        "index, message",
        [
            pytest.param(0, "0 is not a generalized index", id="zero"),
            pytest.param(-1, "-1 is not a generalized index", id="negative"),
            pytest.param(1, "the root has no proof branch of its own", id="the_root"),
        ],
    )
    def test_two_indices_name_no_provable_node(self, index: int, message: str) -> None:
        """Neither zero nor the root names a node a proof can address."""
        for call in (gindex_length, get_path_indices, get_branch_indices):
            with pytest.raises(SSZValueError, match=rf"^{message}$"):
                call(index)


class TestProgressiveSpine:
    """Positions on the right-leaning spine a progressive shape merkleizes into."""

    @pytest.mark.parametrize(
        "chunk, expected_index",
        [
            # Level 1 holds chunk 0 alone, one level below the mixed-in word.
            pytest.param(0, 4, id="level_1_only_chunk"),
            # Level 2 holds chunks 1 through 4 in a four-leaf subtree.
            pytest.param(1, 40, id="level_2_first_chunk"),
            # Level 3 holds chunks 5 through 20 in a sixteen-leaf subtree.
            pytest.param(5, 352, id="level_3_first_chunk"),
            pytest.param(20, 367, id="level_3_last_chunk"),
            # Level 4 opens at chunk 21 and holds 64 chunks.
            pytest.param(21, 2944, id="level_4_first_chunk"),
        ],
    )
    def test_a_chunk_sits_where_the_spine_puts_it(self, chunk: int, expected_index: int) -> None:
        """Positions are counted from the root above the spine, not from the spine itself."""
        assert _progressive_chunk_gindex(chunk) == expected_index

    def test_a_chunk_keeps_its_index_whatever_follows_it(self) -> None:
        """A position follows from the chunk alone, which is what makes appending harmless."""
        # Level 3 spans chunks 5 through 20.
        # Both ends keep their index once level 4 opens below them.
        assert _progressive_chunk_gindex(5) == 352
        assert _progressive_chunk_gindex(20) == 367


class TestChunkCount:
    """Leaf counts, which decide how far a bounded tree pads out."""

    @pytest.mark.parametrize(
        "ssz_type, expected",
        [
            pytest.param(Uint64, 1, id="uint"),
            pytest.param(Boolean, 1, id="boolean"),
            # 512 bits pack 256 to a chunk, which takes two chunks.
            pytest.param(Bitvector512, 2, id="bitvector"),
            pytest.param(Bitlist512, 2, id="bitlist"),
            # 64 bytes pack 32 to a chunk.
            pytest.param(Bytes64, 2, id="fixed_bytes"),
            pytest.param(ByteList64, 2, id="byte_list"),
            # Eight eight-byte elements pack four to a chunk.
            pytest.param(Uint64Vector8, 2, id="vector_of_basics"),
            pytest.param(Uint64List8, 2, id="list_of_basics"),
            # A composite element takes a whole chunk, which puts four of them in four.
            pytest.param(PairVector4, 4, id="vector_of_composites"),
            pytest.param(Quad, 4, id="container"),
        ],
    )
    def test_leaves_a_bounded_shape_merkleizes_into(
        self, ssz_type: type[SSZType], expected: int
    ) -> None:
        """A bounded shape reports the leaf count of its own level."""
        assert chunk_count(ssz_type) == expected

    @pytest.mark.parametrize(
        "ssz_type, name",
        [
            pytest.param(Uint64ProgressiveList, "Uint64ProgressiveList", id="progressive_list"),
            pytest.param(ProgressiveBitList, "ProgressiveBitList", id="progressive_bitlist"),
            pytest.param(Spine, "Spine", id="progressive_container"),
            pytest.param(Shape, "Shape", id="compatible_union"),
        ],
    )
    def test_a_progressive_shape_has_no_bounded_count(
        self, ssz_type: type[SSZType], name: str
    ) -> None:
        """A tree that grows with its data has no leaf count to report."""
        with pytest.raises(SSZTypeError, match=rf"^{name} has no bounded chunk count$"):
            chunk_count(ssz_type)


class TestItemLength:
    """Bytes one element occupies inside the chunk it shares."""

    @pytest.mark.parametrize(
        "ssz_type, expected",
        [
            pytest.param(Uint8, 1, id="one_byte_uint"),
            pytest.param(Uint16, 2, id="two_byte_uint"),
            pytest.param(Uint64, 8, id="eight_byte_uint"),
            pytest.param(Boolean, 1, id="boolean"),
            # A composite value contributes its own root, which is a whole chunk.
            pytest.param(Pair, 32, id="container"),
            pytest.param(Bytes64, 32, id="fixed_bytes"),
        ],
    )
    def test_width_of_one_element(self, ssz_type: type[SSZType], expected: int) -> None:
        """
        - A basic value reports its own serialized width.
        - Anything composite reports a whole chunk.
        """
        assert item_length(ssz_type) == expected


class TestElementType:
    """The type one step of a path arrives at."""

    @pytest.mark.parametrize(
        "ssz_type, step, expected",
        [
            pytest.param(Quad, "z", Pair, id="container_field"),
            pytest.param(Spine, "f1", Uint64, id="progressive_container_field"),
            pytest.param(Bitvector512, 0, Boolean, id="bitvector_bit"),
            pytest.param(Bitlist512, 0, Boolean, id="bitlist_bit"),
            pytest.param(ProgressiveBitList, 0, Boolean, id="progressive_bitlist_bit"),
            # A byte array is a sequence of single opaque bytes.
            pytest.param(Bytes64, 0, Uint8, id="fixed_bytes_byte"),
            pytest.param(ByteList64, 0, Uint8, id="byte_list_byte"),
            pytest.param(Uint64Vector8, 0, Uint64, id="vector_element"),
            pytest.param(Uint64List8, 0, Uint64, id="list_element"),
            pytest.param(Uint64ProgressiveList, 0, Uint64, id="progressive_list_element"),
        ],
    )
    def test_type_one_step_arrives_at(
        self, ssz_type: type[SSZType], step: PathStep, expected: type[SSZType]
    ) -> None:
        """
        - Stepping into a collection gives its element type.
        - Stepping into a struct gives the type of the named field.
        """
        assert element_type(ssz_type, step) is expected

    def test_a_basic_value_cannot_be_stepped_into(self) -> None:
        """A basic value is one leaf with no position inside it to address."""
        with pytest.raises(SSZTypeError, match=r"^Uint64 cannot be stepped into$"):
            element_type(Uint64, 0)

    @pytest.mark.parametrize(
        "ssz_type, name",
        [
            pytest.param(Quad, "Quad", id="container"),
            pytest.param(Spine, "Spine", id="progressive_container"),
        ],
    )
    def test_an_unknown_field_name_is_refused(self, ssz_type: type[SSZType], name: str) -> None:
        """A name no field carries is an error rather than a silent miss."""
        with pytest.raises(SSZValueError, match=rf"^{name} has no field named nope$"):
            element_type(ssz_type, "nope")


class TestChunkPosition:
    """The chunk one element lands in, and the byte range it occupies inside it."""

    @pytest.mark.parametrize(
        "step, expected",
        [
            pytest.param(0, (0, 0, 8), id="element_0"),
            pytest.param(1, (0, 8, 16), id="element_1"),
            pytest.param(2, (0, 16, 24), id="element_2"),
            pytest.param(3, (0, 24, 32), id="element_3"),
            pytest.param(4, (1, 0, 8), id="element_4_opens_the_second_chunk"),
        ],
    )
    def test_a_packed_element_shares_its_chunk(
        self, step: PathStep, expected: tuple[int, int, int]
    ) -> None:
        """Four eight-byte elements share one chunk, each holding an eighth of it."""
        # A generalized index names a chunk, never a byte range inside it.
        #
        #     chunk 0:  [ element 0 | element 1 | element 2 | element 3 ]
        #     bytes  :    0 .. 8      8 .. 16     16 .. 24    24 .. 32
        #
        # One proof against chunk 0 therefore authenticates all four elements.
        # The byte range is what tells a caller which quarter was asked for.
        assert chunk_position(Uint64List8, step) == expected

    def test_a_composite_element_takes_a_whole_chunk(self) -> None:
        """A composite element contributes its own root, filling the chunk alone."""
        assert chunk_position(PairVector4, 2) == (2, 0, 32)

    @pytest.mark.parametrize(
        "ssz_type",
        [
            pytest.param(Bitvector512, id="bitvector"),
            pytest.param(Bitlist512, id="bitlist"),
            pytest.param(ProgressiveBitList, id="progressive_bitlist"),
        ],
    )
    def test_a_bit_reports_a_chunk_and_no_byte_range(self, ssz_type: type[SSZType]) -> None:
        """A bit occupies no whole byte, leaving the range it reports empty."""
        # A bitfield packs 256 positions per chunk, not 32.
        # Bit 255 is therefore the last of chunk 0.
        # Bit 256 opens chunk 1.
        assert chunk_position(ssz_type, 255) == (0, 0, 0)
        assert chunk_position(ssz_type, 256) == (1, 0, 0)

    def test_a_field_reports_its_ordinal(self) -> None:
        """A struct gives one leaf per field, putting each field at the chunk of its ordinal."""
        assert chunk_position(Quad, "p") == (0, 0, 8)
        assert chunk_position(Quad, "z") == (3, 0, 32)

    def test_a_basic_value_has_no_positions(self) -> None:
        """A basic value is one leaf with nothing inside it to place."""
        with pytest.raises(SSZTypeError, match=r"^Uint64 cannot be stepped into$"):
            chunk_position(Uint64, 0)

    @pytest.mark.parametrize(
        "ssz_type, name",
        [
            pytest.param(Quad, "Quad", id="container"),
            pytest.param(Spine, "Spine", id="progressive_container"),
        ],
    )
    def test_an_unknown_field_name_is_refused(self, ssz_type: type[SSZType], name: str) -> None:
        """A name no field carries has no position to report."""
        with pytest.raises(SSZValueError, match=rf"^{name} has no field named nope$"):
            chunk_position(ssz_type, "nope")


class TestGeneralizedIndexPerShape:
    """Indices each SSZ shape assigns, one row per position worth pinning."""

    @pytest.mark.parametrize(
        "ssz_type, step, expected",
        [
            # A bounded list mixes in its element count, which puts its data one level down.
            # Elements 0 and 3 share chunk 0.
            # One index therefore reaches both.
            pytest.param(Uint64List8, 0, 4, id="list_element_0"),
            pytest.param(Uint64List8, 3, 4, id="list_element_3_shares_chunk_0"),
            pytest.param(Uint64List8, 7, 5, id="list_element_7"),
            # A fixed sequence mixes in nothing, leaving its data at the root.
            pytest.param(Uint64Vector8, 0, 2, id="vector_element_0"),
            pytest.param(Uint64Vector8, 3, 2, id="vector_element_3_shares_chunk_0"),
            pytest.param(Uint64Vector8, 7, 3, id="vector_element_7"),
            # A bitfield packs 256 positions per chunk, not 32.
            # Bit 255 is the last of the first chunk.
            # Bit 256 is the first of the second.
            pytest.param(Bitlist512, 0, 4, id="bitlist_bit_0"),
            pytest.param(Bitlist512, 255, 4, id="bitlist_bit_255"),
            pytest.param(Bitlist512, 256, 5, id="bitlist_bit_256"),
            pytest.param(Bitlist512, 511, 5, id="bitlist_bit_511"),
            pytest.param(Bitvector512, 0, 2, id="bitvector_bit_0"),
            pytest.param(Bitvector512, 255, 2, id="bitvector_bit_255"),
            pytest.param(Bitvector512, 256, 3, id="bitvector_bit_256"),
            pytest.param(Bitvector512, 511, 3, id="bitvector_bit_511"),
            # A byte array packs 32 bytes per chunk.
            pytest.param(ByteList64, 0, 4, id="byte_list_byte_0"),
            pytest.param(ByteList64, 32, 5, id="byte_list_byte_32"),
            pytest.param(Bytes64, 0, 2, id="fixed_bytes_byte_0"),
            pytest.param(Bytes64, 32, 3, id="fixed_bytes_byte_32"),
        ],
    )
    def test_index_of_one_position(
        self, ssz_type: type[SSZType], step: PathStep, expected: int
    ) -> None:
        """One step from the type root lands on the chunk holding the selected value."""
        assert get_generalized_index(ssz_type, step) == expected

    def test_a_bitfield_bit_at_32_stays_in_the_first_chunk(self) -> None:
        """A bit index divides by 256, since that is how many positions one chunk holds."""
        # Dividing by 32 instead would send bit 32 to chunk 1 and bit 256 to chunk 8.
        # For a two-chunk bitfield, chunk 8 lies outside the tree altogether.
        assert get_generalized_index(Bitlist512, 32) == get_generalized_index(Bitlist512, 0)
        assert get_generalized_index(Bitvector512, 32) == get_generalized_index(Bitvector512, 0)

    def test_a_progressive_list_places_its_elements_on_the_spine(self) -> None:
        """An unbounded sequence mixes in its count, which pushes its spine one level down."""
        # Four eight-byte elements share chunk 0.
        # The fifth opens chunk 1, the first of the second spine level.
        assert get_generalized_index(Uint64ProgressiveList, 0) == 4
        assert get_generalized_index(Uint64ProgressiveList, 4) == 40

    def test_a_progressive_bitlist_places_its_bits_on_the_spine(self) -> None:
        """Bits pack 256 to a chunk here too, which opens the second chunk at bit 256."""
        assert get_generalized_index(ProgressiveBitList, 255) == 4
        assert get_generalized_index(ProgressiveBitList, 256) == 40

    def test_a_progressive_container_places_a_field_at_its_layout_position(self) -> None:
        """A field sits at the position its layout assigns, skipping any vacancy."""
        # A gapless layout puts the first three fields at positions 0, 1 and 2.
        assert get_generalized_index(Spine, "f0") == 4
        assert get_generalized_index(Spine, "f1") == 40
        assert get_generalized_index(Spine, "f2") == 41
        # With position 1 vacant, the second field moves to position 2 and keeps its index.
        assert get_generalized_index(GappedSpine, "first") == 4
        assert get_generalized_index(GappedSpine, "third") == 41

    def test_an_index_follows_a_layout_reassigned_after_the_type_was_declared(self) -> None:
        """A layout is a class attribute, so it can be rewritten, and the index has to follow."""
        # Where a field is hashed is not a property of the type.
        # A type only holds whatever layout it is holding now.

        class Reassigned(ProgressiveContainer):
            ACTIVE_FIELDS = (1, 0, 1)

            head: Uint16
            tail: Uint8

        assert get_generalized_index(Reassigned, "head") == 4
        assert get_generalized_index(Reassigned, "tail") == 41

        # The same two fields, each moved one position along.
        Reassigned.ACTIVE_FIELDS = (0, 1, 1)
        assert get_generalized_index(Reassigned, "head") == 40
        assert get_generalized_index(Reassigned, "tail") == 41

    @pytest.mark.parametrize(
        "reassigned_layout, expected_counts",
        [
            pytest.param(
                (1, 1, 1), "sets 3 positions, and the struct declares 2", id="position_gained"
            ),
            pytest.param((1,), "sets 1 positions, and the struct declares 2", id="position_lost"),
        ],
    )
    def test_a_layout_that_stopped_pairing_with_the_fields_is_refused_by_name(
        self, reassigned_layout: tuple[int, ...], expected_counts: str
    ) -> None:
        """An index is refused wherever a root would be, and for the same reason."""
        # An index for a value that cannot be rooted is worse than a refusal.

        class Drifted(ProgressiveContainer):
            ACTIVE_FIELDS = (1, 0, 1)

            head: Uint16
            tail: Uint8

        Drifted.ACTIVE_FIELDS = reassigned_layout
        with pytest.raises(
            SSZTypeError,
            match=rf"^the layout {expected_counts}$",
        ) as exception_info:
            get_generalized_index(Drifted, "tail")
        # The refusal carries the layout in force, not the one the declaration approved.
        assert exception_info.value.fields["layout"] == reassigned_layout

    def test_an_empty_path_names_the_root(self) -> None:
        """A path selecting nothing lands on the root, which no proof can address."""
        assert get_generalized_index(Quad) == 1


class TestPublishedLightClientIndices:
    """The frozen indices consensus clients ship, reproduced from stand-in shapes."""

    @pytest.mark.parametrize(
        "state_type, path, expected",
        [
            # A 24-field struct pads to 32 leaves, putting field 20 at index 52.
            # Its second subfield is then index 105.
            pytest.param(AltairState, ("f20", "root"), 105, id="finalized_root"),
            pytest.param(AltairState, ("f22",), 54, id="current_sync_committee"),
            pytest.param(AltairState, ("f23",), 55, id="next_sync_committee"),
            # A 46-position layout puts position 20 at the end of the third spine level,
            # index 367, whose second subfield is index 735.
            pytest.param(GloasState, ("f20", "root"), 735, id="finalized_root_progressive"),
            # Positions 22 and 23 open the fourth spine level at index 2944.
            pytest.param(GloasState, ("f22",), 2945, id="current_sync_committee_progressive"),
            pytest.param(GloasState, ("f23",), 2946, id="next_sync_committee_progressive"),
        ],
    )
    def test_published_index(
        self, state_type: type[SSZType], path: tuple[PathStep, ...], expected: int
    ) -> None:
        """Each of these is frozen and consensus-critical, which pins the arithmetic exactly."""
        assert get_generalized_index(state_type, *path) == expected


class TestReservedPathSteps:
    """The three words a root mixes in, each addressable as a path step of its own."""

    @pytest.mark.parametrize(
        "ssz_type",
        [
            pytest.param(Uint64List8, id="list"),
            pytest.param(ByteList64, id="byte_list"),
            pytest.param(Bitlist512, id="bitlist"),
            pytest.param(Uint64ProgressiveList, id="progressive_list"),
            pytest.param(ProgressiveBitList, id="progressive_bitlist"),
        ],
    )
    def test_an_element_count_sits_at_the_right_child(self, ssz_type: type[SSZType]) -> None:
        """A variable-size shape hashes its data against its count, which takes the right side."""
        assert get_generalized_index(ssz_type, LENGTH_KEY) == 3

    def test_a_field_layout_sits_at_the_right_child(self) -> None:
        """A progressive struct hashes its spine against its layout word."""
        assert get_generalized_index(Spine, ACTIVE_FIELDS_KEY) == 3

    def test_a_type_selector_sits_at_the_right_child(self) -> None:
        """A compatible union hashes the option's own root against the selector word."""
        assert get_generalized_index(Shape, SELECTOR_KEY) == 3

    @pytest.mark.parametrize(
        "ssz_type, step, message",
        [
            pytest.param(Bytes64, LENGTH_KEY, "Bytes64 mixes in no element count", id="count"),
            pytest.param(Quad, ACTIVE_FIELDS_KEY, "Quad mixes in no field layout", id="layout"),
            pytest.param(Quad, SELECTOR_KEY, "Quad mixes in no type selector", id="selector"),
        ],
    )
    def test_a_reserved_word_on_the_wrong_shape_is_refused(
        self, ssz_type: type[SSZType], step: PathStep, message: str
    ) -> None:
        """A shape that mixes in no such word has no node to hand back for it."""
        with pytest.raises(SSZTypeError, match=rf"^{message}$"):
            get_generalized_index(ssz_type, step)

    def test_stepping_into_a_basic_value_is_refused(self) -> None:
        """A path cannot continue past a basic value, which is a single leaf."""
        with pytest.raises(SSZTypeError, match=r"^Uint64 has no parts to address$"):
            get_generalized_index(Quad, "p", 0)

    def test_an_unknown_field_name_is_refused(self) -> None:
        """A step naming no field selects nothing, on either struct shape."""
        with pytest.raises(SSZValueError, match=r"^Quad has no field named nope$"):
            get_generalized_index(Quad, "nope")
        with pytest.raises(SSZValueError, match=r"^Spine has no field named nope$"):
            get_generalized_index(Spine, "nope")


class TestCompatibleUnionPaths:
    """Why a shared field keeps one index across every option of a union."""

    def test_every_option_shares_the_left_child(self) -> None:
        """The selector takes the right child, leaving the left one to every option."""
        assert get_generalized_index(Shape, 1) == 2
        assert get_generalized_index(Shape, 2) == 2

    def test_a_shared_field_keeps_one_index_across_options(self) -> None:
        """One index reaches the shared field whichever option a value turns out to hold."""
        # Both layouts set position 2 and put the same field there.
        # A verifier therefore needs no per-option table of field positions.
        assert get_generalized_index(Shape, 1, "color") == get_generalized_index(Shape, 2, "color")

    def test_the_left_child_is_the_option_root(self) -> None:
        """A one-node branch against the left child rebuilds the union root."""
        value = Shape(selector=Uint8(1), data=Square(side=Uint16(0x1234), color=Uint8(0x42)))
        # The union adds no leaf of its own: the whole tree below the root is the option's.
        # Its sibling is the selector, zero-extended from one byte to a full chunk.
        assert verify_merkle_proof(hash_tree_root(value.data), [word(1)], 2, hash_tree_root(value))

    def test_a_selector_naming_no_option_is_refused(self) -> None:
        """A path can only descend through an option the union declares."""
        with pytest.raises(SSZValueError, match=r"^Shape has no option with selector 9$"):
            get_generalized_index(Shape, 9)


class TestPathAndBranchIndices:
    """The nodes a proof walks through, and the siblings it must carry."""

    def test_a_path_climbs_to_the_root_without_including_it(self) -> None:
        """The walk starts at the addressed node and stops one short of the root."""
        assert get_path_indices(13) == [13, 6, 3]

    def test_a_branch_is_the_sibling_of_every_node_on_the_path(self) -> None:
        """Each level contributes the one node the verifier cannot rebuild."""
        assert get_branch_indices(13) == [12, 7, 2]

    def test_a_single_node_request_asks_for_exactly_that_branch(self) -> None:
        """One index needs no shared nodes, which reduces a multiproof to a plain proof."""
        assert get_helper_indices([13]) == get_branch_indices(13)


class TestMultiproofHelperIndices:
    """Which nodes a request over several indices must carry, and which it must refuse."""

    def test_shared_nodes_are_dropped_from_the_request(self) -> None:
        """A sibling the verifier rebuilds on the way up is not asked for."""
        # Indices 4 and 6 sit in a four-leaf tree:
        #
        #     4  5  6  7      leaves
        #      \/    \/
        #      2      3       rebuilt from the leaves, never requested
        #       \____/
        #          1
        #
        # That leaves 5 and 7 to carry, in descending order.
        assert get_helper_indices([4, 6]) == [7, 5]

    def test_the_request_descends(self) -> None:
        """Descending order reaches both children of a pair before their parent."""
        assert get_helper_indices([8, 6]) == [9, 7, 5]

    def test_a_repeated_index_is_refused(self) -> None:
        """Two values for one index keep one of them and drop the other in silence."""
        with pytest.raises(SSZValueError, match=r"^a generalized index is repeated$"):
            get_helper_indices([4, 4])

    @pytest.mark.parametrize(
        "indices",
        [
            pytest.param([8, 4], id="descendant_first"),
            pytest.param([4, 8], id="ancestor_first"),
        ],
    )
    def test_an_index_below_another_is_refused(self, indices: list[int]) -> None:
        """A request holding an index and one of its ancestors cannot be verified soundly."""
        # Index 4 is rebuilt from its own children.
        # The value given for index 8 is therefore overwritten before it reaches the root:
        #
        #     claimed at 8:  anything at all
        #     rebuilt at 4:  from the children the request already fixes
        #     -> the root matches whatever 8 was said to hold
        #
        # Accepting the pair therefore lets an attacker claim any value at the deeper index
        # and still pass verification.
        with pytest.raises(
            SSZValueError, match=r"^8 lies below another index in the same request$"
        ):
            get_helper_indices(indices)


class TestSingleProofVerification:
    """One leaf, its branch, and the root they must rebuild."""

    def test_a_flat_container_field(self) -> None:
        """A field two levels down needs its sibling and its uncle."""
        value = Quad(p=Uint64(1), q=Uint64(2), r=Uint64(3), z=Pair(a=Uint64(4), b=Uint64(5)))
        # Four fields fill four leaves exactly, putting field 2 at index 6:
        #
        #     4:p  5:q  6:r  7:z
        #       \__/      \__/
        #       2:uncle    3
        #          \______/
        #             1
        index = get_generalized_index(Quad, "r")
        assert index == 6
        branch = [
            hash_tree_root(value.z),
            merkleize([hash_tree_root(value.p), hash_tree_root(value.q)]),
        ]
        assert verify_merkle_proof(hash_tree_root(value.r), branch, index, hash_tree_root(value))

    def test_a_nested_container_field(self) -> None:
        """A field of a nested struct is three levels down, giving it a three-node branch."""
        value = Quad(p=Uint64(1), q=Uint64(2), r=Uint64(3), z=Pair(a=Uint64(4), b=Uint64(5)))
        # The nested struct occupies leaf 3 of the outer tree.
        # Its second field is the right child of that leaf:
        #
        #     index 15 = 0b1111, right at every level
        index = get_generalized_index(Quad, "z", "b")
        assert index == 15
        branch = [
            hash_tree_root(value.z.a),
            hash_tree_root(value.r),
            merkleize([hash_tree_root(value.p), hash_tree_root(value.q)]),
        ]
        assert verify_merkle_proof(hash_tree_root(value.z.b), branch, index, hash_tree_root(value))

    def test_a_field_on_a_progressive_spine(self) -> None:
        """A field at the second spine level needs five nodes, three of them structural."""
        value = Spine(f0=Uint64(11), f1=Uint64(22), f2=Uint64(33))
        # Three fields open two spine levels.
        # The layout word takes the right child of the root:
        #
        #     1  = root
        #     3  = layout word (1, 1, 1) -> 0b111
        #     2  = spine root
        #     4  = level 1, holding position 0 alone
        #     5  = spine below level 1
        #     10 = level 2, a four-leaf subtree holding positions 1 through 4
        #     11 = spine below level 2, empty, a plain zero leaf
        #     40 = position 1
        #     41 = position 2
        index = get_generalized_index(Spine, "f1")
        assert index == 40
        branch = [
            hash_tree_root(value.f2),
            # Positions 3 and 4 are past the layout, leaving both leaves zero.
            h(ZERO_ROOT, ZERO_ROOT),
            ZERO_ROOT,
            hash_tree_root(value.f0),
            word(0b111),
        ]
        assert verify_merkle_proof(hash_tree_root(value.f1), branch, index, hash_tree_root(value))

    def test_a_branch_of_the_wrong_length_is_refused(self) -> None:
        """A branch is checked against the depth of the index before any hashing happens."""
        # A depth-three index needs three nodes.
        # A shorter branch would otherwise stop partway up and compare a node against
        # the root it never reached.
        with pytest.raises(SSZValueError, match=r"^a branch for index 15 holds 3 nodes, got 2$"):
            calculate_merkle_root(ZERO_ROOT, [ZERO_ROOT, ZERO_ROOT], 15)

    def test_a_tampered_leaf_fails(self) -> None:
        """Changing the claimed value changes the rebuilt root, which fails the comparison."""
        value = Quad(p=Uint64(1), q=Uint64(2), r=Uint64(3), z=Pair(a=Uint64(4), b=Uint64(5)))
        branch = [
            hash_tree_root(value.z),
            merkleize([hash_tree_root(value.p), hash_tree_root(value.q)]),
        ]
        assert not verify_merkle_proof(hash_tree_root(Uint64(99)), branch, 6, hash_tree_root(value))


class TestMultiproofVerification:
    """Several leaves and the nodes they share, against one root."""

    def test_two_leaves_sharing_a_root(self) -> None:
        """Two claims one level apart share the root and nothing else."""
        value = Triple(x=Uint64(1), y=Uint64(2), z=Pair(a=Uint64(3), b=Uint64(4)))
        # Three fields pad to four leaves, leaving leaf 7 as the zero pad:
        #
        #     4:x  5:y  6:z  7:zero
        #
        # Claiming 4 and 6 leaves 5 and 7 to carry.
        assert get_generalized_index(Triple, "x") == 4
        assert get_generalized_index(Triple, "z") == 6
        leaves = [hash_tree_root(value.x), hash_tree_root(value.z)]
        proof = [ZERO_ROOT, hash_tree_root(value.y)]
        assert get_helper_indices([4, 6]) == [7, 5]
        assert verify_merkle_multiproof(leaves, proof, [4, 6], hash_tree_root(value))

    def test_a_tampered_leaf_fails(self) -> None:
        """One wrong claim among several still changes the root."""
        value = Triple(x=Uint64(1), y=Uint64(2), z=Pair(a=Uint64(3), b=Uint64(4)))
        leaves = [hash_tree_root(Uint64(99)), hash_tree_root(value.z)]
        proof = [ZERO_ROOT, hash_tree_root(value.y)]
        assert not verify_merkle_multiproof(leaves, proof, [4, 6], hash_tree_root(value))

    def test_one_index_verifies_like_a_plain_proof(self) -> None:
        """A single-index request carries the same branch a plain proof does."""
        value = Quad(p=Uint64(1), q=Uint64(2), r=Uint64(3), z=Pair(a=Uint64(4), b=Uint64(5)))
        branch = [
            hash_tree_root(value.z),
            merkleize([hash_tree_root(value.p), hash_tree_root(value.q)]),
        ]
        root = hash_tree_root(value)
        assert verify_merkle_multiproof([hash_tree_root(value.r)], branch, [6], root)
        assert calculate_multi_merkle_root([hash_tree_root(value.r)], branch, [6]) == root

    def test_a_leaf_per_index_is_required(self) -> None:
        """Every index needs the value claimed for it, or one of them goes unchecked."""
        with pytest.raises(SSZValueError, match=r"^2 indices need as many leaves, got 1$"):
            calculate_multi_merkle_root([ZERO_ROOT], [ZERO_ROOT, ZERO_ROOT], [4, 6])

    def test_the_proof_must_hold_exactly_the_shared_nodes(self) -> None:
        """A node count other than the one the request needs is refused up front."""
        with pytest.raises(SSZValueError, match=r"^this request needs 2 proof nodes, got 1$"):
            calculate_multi_merkle_root([ZERO_ROOT, ZERO_ROOT], [ZERO_ROOT], [4, 6])

    def test_a_request_for_nothing_is_refused(self) -> None:
        """A request holding no index claims nothing to verify."""
        # An empty request would otherwise fall through the pairing loop and reach for a
        # root that was never built.
        with pytest.raises(SSZValueError, match=r"^a request holds at least one index$"):
            calculate_multi_merkle_root([], [], [])


class TestNodeRoot:
    """What an index resolves to when it is read against real data rather than a type."""

    def test_index_one_names_the_whole_value(self) -> None:
        """Index 1 is the root, the one node with nothing above it to prove against."""
        assert node_root(QUAD, 1) == hash_tree_root(QUAD)
        with pytest.raises(SSZValueError, match=r"^the root has no proof branch of its own$"):
            build_proof(QUAD, 1)

    def test_a_basic_value_has_no_node_below_its_root(self) -> None:
        """A basic value is a single leaf, whose root is the whole tree."""
        assert resolvable_indices(Uint64(9)) == set()

    @pytest.mark.parametrize(
        "value, path, expected",
        [
            pytest.param(QUAD, ("p",), QUAD.p, id="basic_field"),
            pytest.param(QUAD, ("z",), QUAD.z, id="composite_field"),
            pytest.param(QUAD, ("z", "b"), QUAD.z.b, id="nested_field"),
            pytest.param(SPARSE_PAIR_LIST, (1,), PAIR, id="list_element"),
            pytest.param(VECTOR_OF_COMPOSITES, (2,), PAIR, id="vector_element"),
            pytest.param(VECTOR_OF_COMPOSITES, (2, "b"), PAIR.b, id="vector_element_field"),
            pytest.param(SPINE_VALUE, ("f1",), SPINE_VALUE.f1, id="progressive_field"),
            pytest.param(GAPPED_VALUE, ("third",), GAPPED_VALUE.third, id="field_past_a_gap"),
            pytest.param(SHAPE_VALUE, (1,), SHAPE_VALUE.data, id="union_contents"),
            pytest.param(SHAPE_VALUE, (1, "color"), Uint8(0x42), id="union_shared_field"),
            pytest.param(ALTAIR_VALUE, ("f20",), ALTAIR_VALUE.f20, id="bounded_state_field"),
            pytest.param(
                ALTAIR_VALUE, ("f20", "root"), ALTAIR_VALUE.f20.root, id="bounded_finalized_root"
            ),
            pytest.param(GLOAS_VALUE, ("f22",), GLOAS_VALUE.f22, id="wide_state_field"),
            pytest.param(
                GLOAS_VALUE, ("f20", "root"), GLOAS_VALUE.f20.root, id="wide_finalized_root"
            ),
        ],
    )
    def test_a_resolved_node_carries_the_selected_value_root(
        self, value: Any, path: tuple[PathStep, ...], expected: SSZType
    ) -> None:
        """
        A descent landing one position off would still yield a leaf that verifies.

        Only the value reached by ordinary attribute and element access separates the two.
        """
        index = get_generalized_index(type(value), *path)
        assert node_root(value, index) == hash_tree_root(expected)

    @pytest.mark.parametrize(
        "value, step, expected",
        [
            pytest.param(SPARSE_LIST, LENGTH_KEY, word(2), id="list_count"),
            pytest.param(BYTE_LIST, LENGTH_KEY, word(3), id="byte_list_count"),
            pytest.param(BITLIST, LENGTH_KEY, word(300), id="bitlist_count"),
            pytest.param(WIDE_PROGRESSIVE, LENGTH_KEY, word(100), id="progressive_list_count"),
            pytest.param(PROGRESSIVE_BITS, LENGTH_KEY, word(300), id="progressive_bit_count"),
            pytest.param(SPINE_VALUE, ACTIVE_FIELDS_KEY, word(0b111), id="gapless_layout"),
            pytest.param(GAPPED_VALUE, ACTIVE_FIELDS_KEY, word(0b101), id="gapped_layout"),
            pytest.param(SHAPE_VALUE, SELECTOR_KEY, word(1), id="type_selector"),
        ],
    )
    def test_a_mixed_in_word_resolves_to_that_word(
        self, value: Any, step: PathStep, expected: Chunk
    ) -> None:
        """A reserved step lands on the right child.
        That child holds the word itself and nothing else.
        """
        index = get_generalized_index(type(value), step)
        assert index == 3
        assert node_root(value, index) == expected


class TestNodeRootRefusals:
    """Indices that name no node of a given value, each refused rather than guessed at."""

    @pytest.mark.parametrize(
        "value, index, message",
        [
            pytest.param(QUAD, 0, "0 is not a generalized index", id="zero"),
            pytest.param(QUAD, -1, "-1 is not a generalized index", id="negative"),
            # A packed chunk is a leaf.
            # The elements sharing it have no nodes of their own.
            pytest.param(
                SPARSE_LIST,
                8,
                "the path descends into the packed data of Uint64List8",
                id="below_a_packed_chunk",
            ),
            # A basic field fills its leaf.
            # The descent therefore stops inside the field's own type.
            pytest.param(
                QUAD,
                8,
                "the path descends into the packed data of Uint64",
                id="below_a_basic_field",
            ),
            pytest.param(
                SPARSE_LIST,
                6,
                "the path descends into the mixed-in word of Uint64List8",
                id="below_an_element_count",
            ),
            pytest.param(
                SPINE_VALUE,
                6,
                "the path descends into the mixed-in word of Spine",
                id="below_a_field_layout",
            ),
            pytest.param(
                SHAPE_VALUE,
                6,
                "the path descends into the mixed-in word of Shape",
                id="below_a_type_selector",
            ),
            pytest.param(
                SPARSE_PAIR_LIST,
                36,
                "the path descends into an empty position of PairList8",
                id="below_an_element_past_the_length",
            ),
            pytest.param(
                TRIPLE,
                14,
                "the path descends into an empty position of Triple",
                id="below_a_leaf_past_the_field_count",
            ),
            pytest.param(
                GAPPED_VALUE,
                80,
                "the path descends into an empty position of GappedSpine",
                id="below_a_cleared_position",
            ),
            # One chunk opens level 1 alone.
            # Level 3 was never opened at all.
            pytest.param(
                SHORT_PROGRESSIVE,
                352,
                "the path lies past the end of the progressive spine of Uint64ProgressiveList",
                id="slot_in_an_unopened_level",
            ),
            # The spine closes with a zero leaf.
            # A leaf has nothing under it.
            pytest.param(
                SHORT_PROGRESSIVE,
                10,
                "the path lies past the end of the progressive spine of Uint64ProgressiveList",
                id="below_the_spine_terminator",
            ),
        ],
    )
    def test_an_index_naming_no_node_is_refused(self, value: Any, index: int, message: str) -> None:
        """A refusal names the index and the shape, letting a caller see which step failed."""
        with pytest.raises(SSZValueError, match=rf"^{message}$"):
            node_root(value, index)

    def test_a_value_with_no_layout_is_refused(self) -> None:
        """A value outside SSZ merkleizes into nothing.
        No index of it names a node.
        """
        with pytest.raises(SSZTypeError, match=r"^float has no Merkle layout$"):
            node_root(3.14, 2)

    def test_a_branch_for_an_unusable_index_is_refused(self) -> None:
        """The builders refuse what the index arithmetic already refuses."""
        with pytest.raises(SSZValueError, match=r"^0 is not a generalized index$"):
            build_proof(QUAD, 0)
        with pytest.raises(SSZValueError, match=r"^a generalized index is repeated$"):
            build_multiproof(QUAD, [4, 4])
        with pytest.raises(
            SSZValueError, match=r"^14 lies below another index in the same request$"
        ):
            build_multiproof(QUAD, [7, 14])


class TestZeroPaddingIsAProvableNode:
    """Padding fills a tree with real nodes that a proof can still address."""

    @pytest.mark.parametrize(
        "value, index",
        [
            pytest.param(SPARSE_LIST, 5, id="capacity_chunk_past_the_length"),
            pytest.param(SPARSE_PAIR_LIST, 18, id="element_past_the_length"),
            pytest.param(TRIPLE, 7, id="leaf_past_the_field_count"),
            pytest.param(TWO_LEVEL_PROGRESSIVE, 41, id="slot_inside_an_open_level"),
            pytest.param(SHORT_PROGRESSIVE, 5, id="spine_terminator"),
            pytest.param(GAPPED_VALUE, 40, id="cleared_progressive_position"),
        ],
    )
    def test_a_zero_node_resolves_and_verifies(self, value: Any, index: int) -> None:
        """A position a value never filled is a node with a branch of its own."""
        assert node_root(value, index) == ZERO_ROOT
        assert round_trip(value, index)


class TestProofRoundTrip:
    """A branch built against a value, read back by the verifier, one row per shape."""

    @pytest.mark.parametrize(
        "value, index",
        [
            pytest.param(QUAD, 6, id="container_field"),
            pytest.param(QUAD, 15, id="nested_container_field"),
            pytest.param(TRIPLE, 5, id="container_needing_padding"),
            pytest.param(SPARSE_LIST, 4, id="bounded_list_chunk"),
            pytest.param(VECTOR_OF_BASICS, 3, id="fixed_sequence_chunk"),
            pytest.param(VECTOR_OF_COMPOSITES, 13, id="composite_element_field"),
            pytest.param(SPARSE_PAIR_LIST, 33, id="list_element_field"),
            pytest.param(BITLIST, 5, id="bitlist_chunk"),
            pytest.param(BITVECTOR, 3, id="bitvector_chunk"),
            pytest.param(BYTE_LIST, 4, id="byte_list_chunk"),
            pytest.param(PROGRESSIVE_BITS, 40, id="progressive_bitlist_chunk"),
            # Levels 1, 2 and 3 of a spine that reaches level 4.
            pytest.param(WIDE_PROGRESSIVE, 4, id="progressive_level_1"),
            pytest.param(WIDE_PROGRESSIVE, 40, id="progressive_level_2"),
            pytest.param(WIDE_PROGRESSIVE, 352, id="progressive_level_3"),
            pytest.param(SPINE_VALUE, 40, id="progressive_container_field"),
            pytest.param(SHAPE_VALUE, 2, id="union_contents"),
            pytest.param(SHAPE_VALUE, 73, id="union_shared_field"),
            # The frozen light-client indices, on the shape each fork uses.
            pytest.param(ALTAIR_VALUE, 105, id="published_finalized_root"),
            pytest.param(GLOAS_VALUE, 735, id="published_finalized_root_progressive"),
            pytest.param(GLOAS_VALUE, 2945, id="published_sync_committee_progressive"),
            # Each of the three words a root mixes in.
            pytest.param(SPARSE_LIST, 3, id="element_count_word"),
            pytest.param(SPINE_VALUE, 3, id="field_layout_word"),
            pytest.param(SHAPE_VALUE, 3, id="type_selector_word"),
        ],
    )
    def test_a_built_branch_rebuilds_the_root(self, value: Any, index: int) -> None:
        """The node, the branch built for it, and the value's own root all agree."""
        assert round_trip(value, index)

    def test_a_branch_holds_one_node_per_level(self) -> None:
        """A branch is as long as the index is deep, whatever the shape below it."""
        assert len(build_proof(GLOAS_VALUE, 735)) == gindex_length(735) == 9


class TestBranchOrdering:
    """The order a branch is built in, fixed by the spec only indirectly."""

    def test_a_branch_matches_the_order_a_shared_node_request_reports(self) -> None:
        """
        A single-index request descends.
        That is the order a plain branch already uses.

        The spec pins bottom-up ordering through the equivalence rather than stating it.
        """
        # Index 2856 sits eleven levels down, the depth a progressive spine reaches.
        assert gindex_length(2856) == 11
        assert get_branch_indices(2856) == get_helper_indices([2856])

    def test_a_reversed_branch_fails(self) -> None:
        """Bottom-up is load-bearing, not one of two orders that would both verify."""
        # The branch at index 15 is asymmetric.
        # Reversing it therefore cannot coincide with itself.
        branch = build_proof(QUAD, 15)
        leaf, root = node_root(QUAD, 15), hash_tree_root(QUAD)
        assert verify_merkle_proof(leaf, branch, 15, root)
        assert not verify_merkle_proof(leaf, list(reversed(branch)), 15, root)


class TestSparsePositions:
    """Empty positions a light client still needs to prove."""

    def test_every_position_of_a_two_of_eight_list_verifies(self) -> None:
        """
        A list holding two of eight elements proves all eight positions.

        An implementation that folds the six zero leaves into one node cannot address them.
        The sparse light-client case needs exactly that.
        """
        assert len(SPARSE_PAIR_LIST) == 2
        for position in range(8):
            index = get_generalized_index(PairList8, position)
            assert index == 16 + position
            assert round_trip(SPARSE_PAIR_LIST, index)
        # Each empty position is its own node, not a shared one.
        # The branches at two of them therefore differ.
        assert build_proof(SPARSE_PAIR_LIST, 18) != build_proof(SPARSE_PAIR_LIST, 22)


class TestRepeatedElements:
    """One value standing at several positions, which a layout roots once for all of them."""

    def test_every_node_of_a_vector_holding_a_repeat_verifies(self) -> None:
        """
        A proof reads leaves a range at a time, so a repeat has to survive being sliced.

        A wrong leaf inside a range would still verify against the root that range built,
        so the odd element's node is checked against the element's own root as well.
        """
        assert VECTOR_WITH_A_REPEAT[0] is VECTOR_WITH_A_REPEAT[3] is PAIR
        for index in sorted(resolvable_indices(VECTOR_WITH_A_REPEAT)):
            assert round_trip(VECTOR_WITH_A_REPEAT, index), f"index {index}"
        # Leaves 0 and 2 sit at indices 4 and 6, one holding the repeat and one not.
        assert node_root(VECTOR_WITH_A_REPEAT, 4) == hash_tree_root(PAIR)
        assert node_root(VECTOR_WITH_A_REPEAT, 6) == hash_tree_root(ODD_ONE_OUT)
        assert hash_tree_root(ODD_ONE_OUT) != hash_tree_root(PAIR)


class TestResolvableSetMatchesTheTree:
    """Which indices name a node, checked against the tree each value actually builds."""

    def test_a_two_of_eight_packed_list_has_exactly_four_nodes(self) -> None:
        """
        One whole tree, hand-checked index by index.

        Eight eight-byte elements pack four to a chunk, giving two chunks of capacity:

            1: root
            2: data root      3: element count
            4: chunk 0        5: chunk 1, all zero

        Nothing sits below a packed chunk.
        Nothing sits below the count.
        """
        assert resolvable_indices(SPARSE_LIST) == {2, 3, 4, 5}

    @pytest.mark.parametrize(
        "value, expected",
        [
            pytest.param(PAIR, {2, 3}, id="two_field_container"),
            pytest.param(TRIPLE, {2, 3, 4, 5, 6, 7, 12, 13}, id="container_with_a_pad"),
            pytest.param(QUAD, {2, 3, 4, 5, 6, 7, 14, 15}, id="container_of_four_fields"),
            pytest.param(VECTOR_OF_BASICS, {2, 3}, id="fixed_sequence_of_basics"),
            pytest.param(BITVECTOR, {2, 3}, id="fixed_bitfield"),
            pytest.param(SPARSE_LIST, {2, 3, 4, 5}, id="bounded_list_of_basics"),
            # Four composite elements fill four leaves, each with two fields under it.
            pytest.param(VECTOR_OF_COMPOSITES, set(range(2, 16)), id="fixed_sequence_of_structs"),
            # Eight leaves of capacity, the first two carrying a struct each.
            pytest.param(
                SPARSE_PAIR_LIST,
                {2, 3, 4, 5, 8, 9, 10, 11, 16, 17, 18, 19, 20, 21, 22, 23, 32, 33, 34, 35},
                id="bounded_list_of_structs",
            ),
            # Three positions open two spine levels.
            # Index 4 holds leaf 0.
            # Index 10 covers leaves 1 to 4.
            pytest.param(
                SPINE_VALUE,
                {2, 3, 4, 5, 10, 11, 20, 21, 40, 41, 42, 43},
                id="progressive_container",
            ),
            # A cleared position changes which leaves hold a value, never which nodes exist.
            pytest.param(
                GAPPED_VALUE,
                {2, 3, 4, 5, 10, 11, 20, 21, 40, 41, 42, 43},
                id="progressive_container_with_a_gap",
            ),
            # Two packed chunks open the same two levels a three-position layout does.
            pytest.param(
                TWO_LEVEL_PROGRESSIVE,
                {2, 3, 4, 5, 10, 11, 20, 21, 40, 41, 42, 43},
                id="progressive_list",
            ),
            # A union adds no leaf.
            # The option's own tree therefore sits directly under the root.
            pytest.param(
                SHAPE_VALUE,
                {2, 3, 4, 5, 8, 9, 18, 19, 36, 37, 72, 73, 74, 75},
                id="compatible_union",
            ),
        ],
    )
    def test_the_resolvable_set_is_the_tree(self, value: Any, expected: set[int]) -> None:
        """The resolvable set is exactly the tree, with no phantom node and none missing."""
        assert resolvable_indices(value) == expected

    def test_a_resolved_node_never_stands_alone(self) -> None:
        """
        The resolvable set is a tree, not an arbitrary set of indices.

        - A node that resolves has a parent that resolves.
        - It has a sibling that resolves, so a branch is never short a node.
        - Its parent is the hash of the two of them.
        """
        for value in (QUAD, SPARSE_PAIR_LIST, SPINE_VALUE, SHAPE_VALUE, TWO_LEVEL_PROGRESSIVE):
            resolved = {index: node_root(value, index) for index in resolvable_indices(value)}
            resolved[1] = hash_tree_root(value)
            for index in resolved:
                if index == 1:
                    continue
                assert index // 2 in resolved
                assert index ^ 1 in resolved
                assert resolved[index // 2] == h(resolved[index & ~1], resolved[index | 1])


class TestProofConstructionForSeveralIndices:
    """Nodes several claims share, built against one value instead of a materialized tree."""

    def test_three_claims_over_one_container(self) -> None:
        """
        Three claims need two shared nodes where three separate branches need seven.

            4:p   5:q   6:r   7:z
                                |
                          14:z.a  15:z.b

        Claiming 4, 6 and 14 leaves only 15 and 5 for the proof to carry.
        """
        indices = [4, 6, 14]
        leaves = [node_root(QUAD, index) for index in indices]
        proof = build_multiproof(QUAD, indices)
        assert get_helper_indices(indices) == [15, 5]
        assert verify_merkle_multiproof(leaves, proof, indices, hash_tree_root(QUAD))
        assert len(proof) == 2
        assert sum(len(build_proof(QUAD, index)) for index in indices) == 7

    def test_two_claims_on_a_progressive_spine(self) -> None:
        """Two fields on different spine levels share four nodes where two branches hold seven."""
        indices = [4, 41]
        leaves = [node_root(SPINE_VALUE, index) for index in indices]
        proof = build_multiproof(SPINE_VALUE, indices)
        assert get_helper_indices(indices) == [40, 21, 11, 3]
        assert verify_merkle_multiproof(leaves, proof, indices, hash_tree_root(SPINE_VALUE))
        assert len(proof) == 4
        assert sum(len(build_proof(SPINE_VALUE, index)) for index in indices) == 7

    def test_one_claim_reduces_to_a_plain_branch(self) -> None:
        """A request for a single index carries exactly the branch a plain proof does."""
        assert build_multiproof(QUAD, [15]) == build_proof(QUAD, 15)

    def test_a_tampered_claim_fails(self) -> None:
        """One wrong node among several still changes the root."""
        indices = [4, 6, 14]
        leaves = [node_root(QUAD, 4), hash_tree_root(Uint64(99)), node_root(QUAD, 14)]
        proof = build_multiproof(QUAD, indices)
        assert not verify_merkle_multiproof(leaves, proof, indices, hash_tree_root(QUAD))

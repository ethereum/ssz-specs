"""SSZ conformance test vectors for paths resolved to the generalized index they name."""

from typing import Any, cast

import pytest

from ssz import (
    BitList,
    ByteVector,
    CompatibleUnion,
    Container,
    List,
    ProgressiveContainer,
    ProgressiveList,
    SSZType,
    TypeFault,
    Uint8,
    Uint16,
    Uint64,
    ValueFault,
    Vector,
    active_fields,
)
from ssz_testing import (
    ELEMENT_COUNT_STEP,
    FIELD_LAYOUT_STEP,
    TYPE_SELECTOR_STEP,
    GindexTestFiller,
)

pytestmark = pytest.mark.tags("gindex", "proofs")

ALTAIR_STATE_WIDTH = 24
"""Fields the altair beacon state declares, which pads its leaf tree to 32."""

GLOAS_STATE_WIDTH = 46
"""Positions the post-EIP-8015 beacon state layout declares, with no gaps."""

CHECKPOINT_POSITION = 20
"""Position of the two-field struct whose second field the finalized-root index names."""

SYNC_COMMITTEE_POSITIONS = (22, 23)
"""Positions of the two committee structs a light client proves whole."""


class GindexRoot(ByteVector):
    """Fixed 32-byte array, standing in for a block or state root."""

    LENGTH = 32


class GindexCheckpoint(Container):
    """Two-field struct whose second field is the value a light client proves."""

    epoch: Uint64
    root: GindexRoot


class GindexSyncCommittee(Container):
    """One-field stand-in for the committee struct two published indices address."""

    pubkey: GindexRoot


class GindexPair(Container):
    """Two eight-byte fields, one leaf each, the flattest struct there is."""

    a: Uint64
    b: Uint64


class GindexQuad(Container):
    """Four fields whose last is a struct of its own, so a path can step twice."""

    p: Uint64
    q: Uint64
    r: Uint64
    z: GindexPair


class GindexUint64List8(List[Uint64]):
    """Bounded list of eight-byte elements, four to a chunk and two chunks of capacity."""

    LIMIT = 8


class GindexUint64Vector8(Vector[Uint64]):
    """The same eight elements with no element count mixed in."""

    LENGTH = 8


class GindexBitList512(BitList):
    """Bounded bit sequence spanning two chunks of capacity, 256 bits to a chunk."""

    LIMIT = 512


class GindexUint64ProgressiveList(ProgressiveList[Uint64]):
    """Unbounded sequence of eight-byte elements, laid out on a spine."""


class GindexSpine(ProgressiveContainer):
    """Three fields on a gapless layout, occupying the first two spine levels."""

    ACTIVE_FIELDS = (1, 1, 1)

    f0: Uint64
    f1: Uint64
    f2: Uint64


class GindexGappedSpine(ProgressiveContainer):
    """Two fields with position 1 vacant, putting the second field at position 2."""

    ACTIVE_FIELDS = (1, 0, 1)

    first: Uint64
    third: Uint64


class GindexSquare(ProgressiveContainer):
    """One union option, holding a private field at position 0 and a shared one at position 2."""

    ACTIVE_FIELDS = (1, 0, 1)

    side: Uint16
    color: Uint8


class GindexCircle(ProgressiveContainer):
    """The other union option, holding the same shared field at the same position."""

    ACTIVE_FIELDS = (0, 1, 1)

    radius: Uint16
    color: Uint8


class GindexShape(CompatibleUnion):
    """Two options that merkleize alike, differing only in their private field."""

    OPTIONS = {1: GindexSquare, 2: GindexCircle}


def state_fields(width: int) -> dict[str, Any]:
    """One field per position of a beacon state stand-in, only three of them composite."""
    annotations: dict[str, Any] = {}
    for position in range(width):
        if position == CHECKPOINT_POSITION:
            annotations[f"f{position}"] = GindexCheckpoint
        elif position in SYNC_COMMITTEE_POSITIONS:
            annotations[f"f{position}"] = GindexSyncCommittee
        else:
            annotations[f"f{position}"] = Uint64
    return annotations


GindexAltairState = cast(
    "type[SSZType]",
    type(
        "GindexAltairState",
        (Container,),
        {"__annotations__": state_fields(ALTAIR_STATE_WIDTH)},
    ),
)
"""The altair beacon state shape, whose 24 fields pad to 32 leaves."""

GindexGloasState = cast(
    "type[SSZType]",
    type(
        "GindexGloasState",
        (ProgressiveContainer,),
        {
            "ACTIVE_FIELDS": active_fields(width=GLOAS_STATE_WIDTH),
            "__annotations__": state_fields(GLOAS_STATE_WIDTH),
        },
    ),
)
"""The gloas beacon state shape, whose 46 positions run onto the fourth spine level."""


def test_the_root_itself(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A path selecting nothing names the type's own root.

    Given
    -----
    - a two-field struct.
    - a path of no steps.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 1, the root, and it sits no levels below itself.
    """
    ssz_gindex_test(
        case_id="gindex/container/the_root_itself",
        type_name="GindexPair",
        ssz_type=GindexPair,
        path=(),
        gindex=1,
    )


def test_field_of_a_flat_container(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A field of a two-field struct is one of the root's two children.

    Given
    -----
    - a struct of two eight-byte fields, each merkleizing into a leaf of its own.
    - a path naming the second field.

    When
    ----
    - the path is resolved.

    Then
    ----
    - two leaves pad to a tree two wide, so the second field is index 3.
    """
    ssz_gindex_test(
        case_id="gindex/container/flat_field",
        type_name="GindexPair",
        ssz_type=GindexPair,
        path=("b",),
        gindex=3,
    )


def test_field_of_a_nested_container(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A path steps into a struct held as a field and carries on from its root.

    Given
    -----
    - a four-field struct whose last field is a two-field struct.
    - a path naming that field and then the second field inside it.

    When
    ----
    - the path is resolved.

    Then
    ----
    - four leaves put the nested struct at index 7, and its second field at 15.
    """
    ssz_gindex_test(
        case_id="gindex/container/nested_field",
        type_name="GindexQuad",
        ssz_type=GindexQuad,
        path=("z", "b"),
        gindex=15,
    )


def test_element_of_a_list(ssz_gindex_test: GindexTestFiller) -> None:
    """
    An element of a bounded list sits one level below the root, past the mixed-in count.

    Given
    -----
    - a list of at most eight eight-byte elements, two chunks of capacity.
    - a path naming the last element.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the element count takes the right child, so the data starts at index 2.
    - element 7 lands in chunk 1, which is index 5.
    """
    ssz_gindex_test(
        case_id="gindex/list/element",
        type_name="GindexUint64List8",
        ssz_type=GindexUint64List8,
        path=(7,),
        gindex=5,
    )


def test_first_element_of_a_packed_list(ssz_gindex_test: GindexTestFiller) -> None:
    """
    The first element of a packed list names the chunk it shares with three others.

    Given
    -----
    - a list of at most eight eight-byte elements, four to a 32-byte chunk.
    - a path naming element 0.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 4, the first chunk of the data subtree.
    """
    ssz_gindex_test(
        case_id="gindex/list/first_packed_element",
        type_name="GindexUint64List8",
        ssz_type=GindexUint64List8,
        path=(0,),
        gindex=4,
    )


def test_fourth_element_of_a_packed_list(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A packed element resolves to the chunk holding it, which several elements share.

    Given
    -----
    - the same list of eight-byte elements, four to a chunk.
    - a path naming element 3, the last one packed into chunk 0.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 4, the same node element 0 resolves to.
    - a proof of one packed element therefore reveals every element in its chunk.
    """
    ssz_gindex_test(
        case_id="gindex/list/fourth_packed_element_shares_a_chunk",
        type_name="GindexUint64List8",
        ssz_type=GindexUint64List8,
        path=(3,),
        gindex=4,
    )


def test_element_of_a_vector(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A fixed sequence mixes in nothing, so its data sits at the root rather than below it.

    Given
    -----
    - a vector of exactly eight eight-byte elements, two chunks wide.
    - a path naming the last element.

    When
    ----
    - the path is resolved.

    Then
    ----
    - element 7 lands in chunk 1, which is index 3, one level above the list's answer.
    """
    ssz_gindex_test(
        case_id="gindex/vector/element",
        type_name="GindexUint64Vector8",
        ssz_type=GindexUint64Vector8,
        path=(7,),
        gindex=3,
    )


def test_last_bit_of_the_first_chunk(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A bitfield packs 256 positions per chunk, not 32.

    Given
    -----
    - a bitlist of at most 512 bits, two chunks of capacity.
    - a path naming bit 255.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 4, the first chunk, which holds bits 0 through 255.
    """
    ssz_gindex_test(
        case_id="gindex/bit_list/last_bit_of_the_first_chunk",
        type_name="GindexBitList512",
        ssz_type=GindexBitList512,
        path=(255,),
        gindex=4,
    )


def test_first_bit_of_the_second_chunk(ssz_gindex_test: GindexTestFiller) -> None:
    """
    Bit 256 is the first of the second chunk, where dividing by 32 would place bit 32.

    Given
    -----
    - the same bitlist of at most 512 bits.
    - a path naming bit 256.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 5, the second and last chunk of the capacity.
    """
    ssz_gindex_test(
        case_id="gindex/bit_list/first_bit_of_the_second_chunk",
        type_name="GindexBitList512",
        ssz_type=GindexBitList512,
        path=(256,),
        gindex=5,
    )


def test_element_count_of_a_list(ssz_gindex_test: GindexTestFiller) -> None:
    """
    The element count a variable-size shape mixes in is the root's right child.

    Given
    -----
    - a list of at most eight eight-byte elements.
    - a path of the one reserved step naming the element count.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 3, which is what a light client proves a collection's length with.
    """
    ssz_gindex_test(
        case_id="gindex/list/element_count",
        type_name="GindexUint64List8",
        ssz_type=GindexUint64List8,
        path=(ELEMENT_COUNT_STEP,),
        gindex=3,
    )


def test_field_layout_of_a_progressive_container(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A progressive container hashes its spine against the layout word on the right.

    Given
    -----
    - a progressive container of three fields on a gapless layout.
    - a path of the one reserved step naming the field layout.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 3, the leaf that tells an absent field from a zero one.
    """
    ssz_gindex_test(
        case_id="gindex/progressive_container/field_layout",
        type_name="GindexSpine",
        ssz_type=GindexSpine,
        path=(FIELD_LAYOUT_STEP,),
        gindex=3,
    )


def test_field_after_a_layout_gap(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A field of a progressive container sits where the layout puts it, not at its ordinal.

    Given
    -----
    - a layout of (1, 0, 1), whose second field therefore occupies position 2.
    - a path naming that second field.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 41, position 2 on the second spine level.
    - the ordinal would have answered 40, the vacancy at position 1.
    """
    ssz_gindex_test(
        case_id="gindex/progressive_container/field_after_a_gap",
        type_name="GindexGappedSpine",
        ssz_type=GindexGappedSpine,
        path=("third",),
        gindex=41,
    )


def test_progressive_list_on_the_first_spine_level(ssz_gindex_test: GindexTestFiller) -> None:
    """
    The first chunk of a progressive shape sits alone on the first spine level.

    Given
    -----
    - a progressive list of eight-byte elements, four to a chunk.
    - a path naming element 0.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 4: the count takes the right child and the level-one chunk sits below.
    """
    ssz_gindex_test(
        case_id="gindex/progressive_list/first_spine_level",
        type_name="GindexUint64ProgressiveList",
        ssz_type=GindexUint64ProgressiveList,
        path=(0,),
        gindex=4,
    )


def test_progressive_list_on_the_second_spine_level(ssz_gindex_test: GindexTestFiller) -> None:
    """
    The fifth element opens chunk 1, the first of the four-wide second level.

    Given
    -----
    - the same progressive list of eight-byte elements.
    - a path naming element 4.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 40, and element 0 keeps index 4 whatever the list goes on to hold.
    """
    ssz_gindex_test(
        case_id="gindex/progressive_list/second_spine_level",
        type_name="GindexUint64ProgressiveList",
        ssz_type=GindexUint64ProgressiveList,
        path=(4,),
        gindex=40,
    )


def test_progressive_list_on_the_third_spine_level(ssz_gindex_test: GindexTestFiller) -> None:
    """
    Element 20 lands in chunk 5, the first of the sixteen-wide third level.

    Given
    -----
    - the same progressive list, whose levels hold 1, 4 and 16 chunks.
    - a path naming element 20.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 352, two right turns down the spine and then into the level.
    """
    ssz_gindex_test(
        case_id="gindex/progressive_list/third_spine_level",
        type_name="GindexUint64ProgressiveList",
        ssz_type=GindexUint64ProgressiveList,
        path=(20,),
        gindex=352,
    )


def test_progressive_list_past_any_data_it_holds(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A progressive shape declares no capacity, so no position is past its end.

    Given
    -----
    - the same progressive list.
    - a path naming element 10000, which no value in this suite holds.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 1565807, on the seventh spine level.
    - a path resolves against the declaration alone, and this declaration bounds nothing;
      whether a value reaches that far is a question only a value can answer.
    """
    ssz_gindex_test(
        case_id="gindex/progressive_list/far_past_any_data",
        type_name="GindexUint64ProgressiveList",
        ssz_type=GindexUint64ProgressiveList,
        path=(10_000,),
        gindex=1_565_807,
    )


def test_union_option_root(ssz_gindex_test: GindexTestFiller) -> None:
    """
    Every option of a compatible union shares the root's left child.

    Given
    -----
    - a union of two options that merkleize alike.
    - a path naming the first option by its selector.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 2, the same node the second option resolves to.
    """
    ssz_gindex_test(
        case_id="gindex/compatible_union/option_root",
        type_name="GindexShape",
        ssz_type=GindexShape,
        path=(1,),
        gindex=2,
    )


def test_private_field_of_a_union_option(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A field only one option declares still has an index, which reads zero under the other.

    Given
    -----
    - a union whose first option declares a field at layout position 0 the second leaves vacant.
    - a path naming that option and then that field.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 8, and under the other option that node is the zero leaf of a gap.
    - the selector at index 3, or the layout beside it, is what tells the two apart.
    """
    ssz_gindex_test(
        case_id="gindex/compatible_union/private_field_of_an_option",
        type_name="GindexShape",
        ssz_type=GindexShape,
        path=(1, "side"),
        gindex=8,
    )


def test_shared_field_under_the_first_option(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A field both options put at one layout position keeps one index.

    Given
    -----
    - a union whose options both set layout position 2 and put the same field there.
    - a path naming the first option and then that field.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 73.
    """
    ssz_gindex_test(
        case_id="gindex/compatible_union/shared_field_under_the_first_option",
        type_name="GindexShape",
        ssz_type=GindexShape,
        path=(1, "color"),
        gindex=73,
    )


def test_shared_field_under_the_second_option(ssz_gindex_test: GindexTestFiller) -> None:
    """
    The same field under the other option resolves to the same node.

    Given
    -----
    - the same union.
    - a path naming the second option and then the shared field.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 73 again, so a verifier needs no per-option table of field positions.
    """
    ssz_gindex_test(
        case_id="gindex/compatible_union/shared_field_under_the_second_option",
        type_name="GindexShape",
        ssz_type=GindexShape,
        path=(2, "color"),
        gindex=73,
    )


def test_altair_finalized_root(ssz_gindex_test: GindexTestFiller) -> None:
    """
    The published index for the finalized checkpoint root of an altair beacon state.

    Given
    -----
    - a struct of 24 fields, whose position 20 holds a two-field checkpoint.
    - a path naming that field and then the root inside it.

    When
    ----
    - the path is resolved.

    Then
    ----
    - 24 fields pad to 32 leaves, putting the checkpoint at 52 and its second field at 105.
    - 105 is frozen: consensus clients ship it, and moving it breaks every light client.
    """
    ssz_gindex_test(
        case_id="gindex/light_client/altair/finalized_root",
        type_name="GindexAltairState",
        ssz_type=GindexAltairState,
        path=("f20", "root"),
        gindex=105,
    )


def test_altair_current_sync_committee(ssz_gindex_test: GindexTestFiller) -> None:
    """
    The published index for the current sync committee of an altair beacon state.

    Given
    -----
    - the same 24-field struct, whose position 22 holds a committee struct.
    - a path naming that field, reached whole.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 54, the frozen value consensus clients ship.
    """
    ssz_gindex_test(
        case_id="gindex/light_client/altair/current_sync_committee",
        type_name="GindexAltairState",
        ssz_type=GindexAltairState,
        path=("f22",),
        gindex=54,
    )


def test_altair_next_sync_committee(ssz_gindex_test: GindexTestFiller) -> None:
    """
    The published index for the next sync committee of an altair beacon state.

    Given
    -----
    - the same 24-field struct, whose position 23 holds the second committee struct.
    - a path naming that field, reached whole.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 55, the frozen value consensus clients ship.
    """
    ssz_gindex_test(
        case_id="gindex/light_client/altair/next_sync_committee",
        type_name="GindexAltairState",
        ssz_type=GindexAltairState,
        path=("f23",),
        gindex=55,
    )


def test_gloas_finalized_root(ssz_gindex_test: GindexTestFiller) -> None:
    """
    The published index for the finalized checkpoint root of a progressive beacon state.

    Given
    -----
    - a progressive container of 46 gapless positions, position 20 holding a checkpoint.
    - a path naming that field and then the root inside it.

    When
    ----
    - the path is resolved.

    Then
    ----
    - position 20 ends the sixteen-wide third spine level at index 367, so the root is 735.
    - a progressive layout keeps an index across a fork that appends a field; a padded one
      does not, which is why these two states answer differently for one path.
    """
    ssz_gindex_test(
        case_id="gindex/light_client/gloas/finalized_root",
        type_name="GindexGloasState",
        ssz_type=GindexGloasState,
        path=("f20", "root"),
        gindex=735,
    )


def test_gloas_current_sync_committee(ssz_gindex_test: GindexTestFiller) -> None:
    """
    The published index for the current sync committee of a progressive beacon state.

    Given
    -----
    - the same 46-position layout, whose position 22 holds a committee struct.
    - a path naming that field, reached whole.

    When
    ----
    - the path is resolved.

    Then
    ----
    - positions 21 onward open the 64-wide fourth spine level at index 2944, so this is 2945.
    """
    ssz_gindex_test(
        case_id="gindex/light_client/gloas/current_sync_committee",
        type_name="GindexGloasState",
        ssz_type=GindexGloasState,
        path=("f22",),
        gindex=2945,
    )


def test_gloas_next_sync_committee(ssz_gindex_test: GindexTestFiller) -> None:
    """
    The published index for the next sync committee of a progressive beacon state.

    Given
    -----
    - the same 46-position layout, whose position 23 holds the second committee struct.
    - a path naming that field, reached whole.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the index is 2946, the leaf beside the one before it.
    """
    ssz_gindex_test(
        case_id="gindex/light_client/gloas/next_sync_committee",
        type_name="GindexGloasState",
        ssz_type=GindexGloasState,
        path=("f23",),
        gindex=2946,
    )


def test_a_path_into_the_element_count_is_refused(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A mixed-in word is one leaf, so a path naming it has nowhere left to go.

    Given
    -----
    - a list of at most eight eight-byte elements.
    - a path naming the element count and then an element position inside it.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the type refuses with NO_PARTS_MIXIN.
    - dropping the extra step would answer index 3, the count, and not what was asked.
    """
    ssz_gindex_test(
        case_id="gindex/refused/into_the_element_count",
        type_name="GindexUint64List8",
        ssz_type=GindexUint64List8,
        path=(ELEMENT_COUNT_STEP, 0),
        refusal=TypeFault.NO_PARTS_MIXIN,
    )


def test_a_path_into_the_field_layout_is_refused(ssz_gindex_test: GindexTestFiller) -> None:
    """
    The layout word of a progressive container is one leaf too.

    Given
    -----
    - a progressive container of three fields.
    - a path naming the field layout and then a field name.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the type refuses with NO_PARTS_MIXIN.
    """
    ssz_gindex_test(
        case_id="gindex/refused/into_the_field_layout",
        type_name="GindexSpine",
        ssz_type=GindexSpine,
        path=(FIELD_LAYOUT_STEP, "f0"),
        refusal=TypeFault.NO_PARTS_MIXIN,
    )


def test_a_path_into_the_type_selector_is_refused(ssz_gindex_test: GindexTestFiller) -> None:
    """
    The selector word of a compatible union is one leaf too.

    Given
    -----
    - a union of two compatible options.
    - a path naming the type selector and then a field of an option.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the type refuses with NO_PARTS_MIXIN.
    """
    ssz_gindex_test(
        case_id="gindex/refused/into_the_type_selector",
        type_name="GindexShape",
        ssz_type=GindexShape,
        path=(TYPE_SELECTOR_STEP, "color"),
        refusal=TypeFault.NO_PARTS_MIXIN,
    )


def test_a_path_into_packed_data_is_refused(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A basic value is a run of bytes inside a chunk, and no node of its own.

    Given
    -----
    - a struct whose first field is an eight-byte integer.
    - a path naming that field and then a position inside it.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the type refuses with NO_PARTS.
    - the finest a generalized index addresses is a chunk, never a byte or a bit within one.
    """
    ssz_gindex_test(
        case_id="gindex/refused/into_packed_data",
        type_name="GindexPair",
        ssz_type=GindexPair,
        path=("a", 0),
        refusal=TypeFault.NO_PARTS,
    )


def test_a_mixin_the_shape_lacks_is_refused(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A shape that mixes in no such word has no node to hand back for it.

    Given
    -----
    - a vector of exactly eight elements, whose root mixes in nothing.
    - a path naming the element count.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the type refuses with NO_MIXIN, rather than answering the right child of the data.
    """
    ssz_gindex_test(
        case_id="gindex/refused/a_mixin_the_shape_lacks",
        type_name="GindexUint64Vector8",
        ssz_type=GindexUint64Vector8,
        path=(ELEMENT_COUNT_STEP,),
        refusal=TypeFault.NO_MIXIN,
    )


def test_a_path_into_a_layout_gap_is_refused(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A vacant layout position carries no field, and so has no name to reach it by.

    Given
    -----
    - a progressive container whose layout of (1, 0, 1) leaves position 1 vacant.
    - a path naming a field the struct does not declare, where that gap sits.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the type refuses with NO_SUCH_FIELD.
    - the gap is a real zero leaf of the tree; a path reaches it only through an index,
      never through a name, since a name is what a vacancy has none of.
    """
    ssz_gindex_test(
        case_id="gindex/refused/into_a_layout_gap",
        type_name="GindexGappedSpine",
        ssz_type=GindexGappedSpine,
        path=("second",),
        refusal=ValueFault.NO_SUCH_FIELD,
    )


def test_a_position_past_the_capacity_is_refused(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A position past what a bounded shape declares would land on a node outside it.

    Given
    -----
    - a list of at most eight elements.
    - a path naming element 8.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the type refuses with NO_SUCH_POSITION.
    """
    ssz_gindex_test(
        case_id="gindex/refused/past_the_declared_capacity",
        type_name="GindexUint64List8",
        ssz_type=GindexUint64List8,
        path=(8,),
        refusal=ValueFault.NO_SUCH_POSITION,
    )


def test_a_position_before_the_first_is_refused(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A negative position is arithmetic that resolves, which is worse than one that does not.

    Given
    -----
    - a list of at most eight elements.
    - a path naming element -1, as a caller subtracting one from an empty length would.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the type refuses with NO_SUCH_POSITION.
    - unchecked, the arithmetic would answer index 3, the mixed-in element count, and the
      caller would be handed a proof of a node it never asked about.
    """
    ssz_gindex_test(
        case_id="gindex/refused/before_the_first_position",
        type_name="GindexUint64List8",
        ssz_type=GindexUint64List8,
        path=(-1,),
        refusal=ValueFault.NO_SUCH_POSITION,
    )


def test_a_name_the_type_does_not_have_is_refused(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A step naming no field selects nothing.

    Given
    -----
    - a struct of two fields, named a and b.
    - a path naming a third.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the type refuses with NO_SUCH_FIELD.
    """
    ssz_gindex_test(
        case_id="gindex/refused/no_such_field",
        type_name="GindexPair",
        ssz_type=GindexPair,
        path=("nope",),
        refusal=ValueFault.NO_SUCH_FIELD,
    )


def test_a_selector_naming_no_option_is_refused(ssz_gindex_test: GindexTestFiller) -> None:
    """
    A path can only descend through an option the union declares.

    Given
    -----
    - a union declaring selectors 1 and 2.
    - a path naming selector 9.

    When
    ----
    - the path is resolved.

    Then
    ----
    - the type refuses with NO_SUCH_OPTION.
    """
    ssz_gindex_test(
        case_id="gindex/refused/no_such_option",
        type_name="GindexShape",
        ssz_type=GindexShape,
        path=(9,),
        refusal=ValueFault.NO_SUCH_OPTION,
    )

"""Tests for the compatible-merkleization relation of EIP-8016, rule by rule."""

from __future__ import annotations

import pytest

from ssz import (
    BaseByteList,
    BaseBytes,
    Boolean,
    Chunk,
    CompatibleUnion,
    Container,
    List,
    ProgressiveBitlist,
    ProgressiveContainer,
    ProgressiveList,
    Root,
    Uint8,
    Uint16,
    Uint32,
    Uint256,
    Vector,
)
from ssz.bitfields import BaseBitlist, BaseBitvector
from ssz.ssz_base import SSZType
from ssz.union import is_compatible

# --------------------------------------------------------------------------------------
# Basic types
# --------------------------------------------------------------------------------------


class Selector(Uint8):
    """Named spelling of uint8: a different class, the same eight-bit width."""


class Balance(Uint256):
    """Named spelling of uint256, used to show the rule is about width, not class."""


class Flag(Boolean):
    """Named spelling of boolean, of which there is only one width."""


# --------------------------------------------------------------------------------------
# Byte arrays and their vector / list spellings
# --------------------------------------------------------------------------------------


class Bytes4(BaseBytes):
    """Fixed byte array of four bytes: the spec's alias for Vector[byte, 4]."""

    LENGTH = 4


class Bytes4Alias(Bytes4):
    """Second spelling of the same four-byte array."""


class Bytes8(BaseBytes):
    """Fixed byte array of eight bytes, twice the width of Bytes4."""

    LENGTH = 8


class ByteList4(BaseByteList):
    """Byte list of capacity four: the spec's alias for List[byte, 4]."""

    LIMIT = 4


class ByteList4Alias(ByteList4):
    """Second spelling of the same four-byte-capacity list."""


class ByteList8(BaseByteList):
    """Byte list of capacity eight, twice the capacity of ByteList4."""

    LIMIT = 8


class Uint8Vector4(Vector[Uint8]):
    """Vector of four uint8, the type a four-byte array is an alias for."""

    LENGTH = 4


class Uint8Vector8(Vector[Uint8]):
    """Vector of eight uint8."""

    LENGTH = 8


class Uint8List4(List[Uint8]):
    """List of uint8 with capacity four, the type a four-byte list is an alias for."""

    LIMIT = 4


class Uint8List8(List[Uint8]):
    """List of uint8 with capacity eight."""

    LIMIT = 8


class BooleanVector4(Vector[Boolean]):
    """Vector of four booleans: one byte per element on the wire, and not a byte array."""

    LENGTH = 4


class BooleanList4(List[Boolean]):
    """List of booleans with capacity four, likewise not a byte list."""

    LIMIT = 4


# --------------------------------------------------------------------------------------
# Bitfields
# --------------------------------------------------------------------------------------


class Bitvector4(BaseBitvector):
    """Bitvector of four bits."""

    LENGTH = 4


class Bitvector4Alias(Bitvector4):
    """Second spelling of the same four-bit vector."""


class Bitvector8(BaseBitvector):
    """Bitvector of eight bits."""

    LENGTH = 8


class Bitlist4(BaseBitlist):
    """Bitlist of capacity four."""

    LIMIT = 4


class Bitlist4Alias(Bitlist4):
    """Second spelling of the same four-bit-capacity list."""


class Bitlist8(BaseBitlist):
    """Bitlist of capacity eight."""

    LIMIT = 8


class Flags(ProgressiveBitlist):
    """Named spelling of a progressive bitlist, of which there is only one shape."""


# --------------------------------------------------------------------------------------
# Progressive containers, the EIP-7495 shapes the union example is built from
# --------------------------------------------------------------------------------------


class Square(ProgressiveContainer):
    """EIP-7495's own example: side at position 0, a gap, then color at position 2."""

    ACTIVE_FIELDS = (1, 0, 1)

    side: Uint16
    color: Uint8


class SquareRestated(ProgressiveContainer):
    """The same layout and the same fields, declared as a second class."""

    ACTIVE_FIELDS = (1, 0, 1)

    side: Uint16
    color: Uint8


class Circle(ProgressiveContainer):
    """The other half of that example: a gap, then radius at 1 and color at 2."""

    ACTIVE_FIELDS = (0, 1, 1)

    radius: Uint16
    color: Uint8


class WideColor(ProgressiveContainer):
    """Circle's layout with a wider color, so position 2 holds one name and two types."""

    ACTIVE_FIELDS = (0, 1, 1)

    radius: Uint16
    color: Uint16


class Shade(ProgressiveContainer):
    """One position, holding a field Square does not declare at position 0."""

    ACTIVE_FIELDS = (1,)

    shade: Uint8


class Tail(ProgressiveContainer):
    """One field at position 3, a position none of the three-wide layouts set."""

    ACTIVE_FIELDS = (0, 0, 0, 1)

    tail: Uint8


class MovedSide(ProgressiveContainer):
    """Square's two field names, with side moved from position 0 to position 1."""

    ACTIVE_FIELDS = (0, 1, 1)

    side: Uint16
    color: Uint8


# --------------------------------------------------------------------------------------
# Containers
# --------------------------------------------------------------------------------------


class Pair(Container):
    """Two-field container, the reference shape the variations below depart from."""

    a: Uint16
    b: Uint8


class PairAlias(Container):
    """The same two fields in the same order, declared as a second class."""

    a: Uint16
    b: Uint8


class PairRenamed(Container):
    """The same two widths under a different second name."""

    a: Uint16
    c: Uint8


class PairReordered(Container):
    """The same two field names in the other order."""

    b: Uint8
    a: Uint16


class PairWidened(Container):
    """The same two names, with the second field one width wider."""

    a: Uint16
    b: Uint16


class PairExtended(Container):
    """The same two fields, with a third appended."""

    a: Uint16
    b: Uint8
    c: Uint8


class SquareHolder(Container):
    """Container whose second field is a progressive container."""

    tag: Uint8
    shape: Square


class CircleHolder(Container):
    """The same container over the other half of the EIP-7495 example."""

    tag: Uint8
    shape: Circle


class WideColorHolder(Container):
    """The same container over a shape that clashes with both of them."""

    tag: Uint8
    shape: WideColor


# --------------------------------------------------------------------------------------
# Sequences over composite element types
# --------------------------------------------------------------------------------------


class Uint16Vector4(Vector[Uint16]):
    """Vector of four uint16, wide enough not to read as a byte array."""

    LENGTH = 4


class Uint16Vector4Alias(Uint16Vector4):
    """Second spelling of the same vector."""


class Uint16Vector8(Vector[Uint16]):
    """Vector of eight uint16."""

    LENGTH = 8


class Uint32Vector4(Vector[Uint32]):
    """Vector of four uint32, the same length over a wider element."""

    LENGTH = 4


class SquareVector4(Vector[Square]):
    """Vector of four progressive containers."""

    LENGTH = 4


class CircleVector4(Vector[Circle]):
    """Vector of four progressive containers compatible with Square."""

    LENGTH = 4


class WideColorVector4(Vector[WideColor]):
    """Vector of four progressive containers that clash with Square."""

    LENGTH = 4


class Uint16List4(List[Uint16]):
    """List of uint16 with capacity four."""

    LIMIT = 4


class Uint16List4Alias(Uint16List4):
    """Second spelling of the same list."""


class Uint16List8(List[Uint16]):
    """List of uint16 with capacity eight."""

    LIMIT = 8


class Uint32List4(List[Uint32]):
    """List of uint32 with capacity four."""

    LIMIT = 4


class SquareList4(List[Square]):
    """List of progressive containers with capacity four."""

    LIMIT = 4


class CircleList4(List[Circle]):
    """List of the compatible shape, at the same capacity."""

    LIMIT = 4


class WideColorList4(List[WideColor]):
    """List of the clashing shape, at the same capacity."""

    LIMIT = 4


class SquareList8(List[Square]):
    """List of progressive containers with twice the capacity."""

    LIMIT = 8


class Uint16ProgressiveList(ProgressiveList[Uint16]):
    """Progressive list of uint16."""


class Uint16ProgressiveListAlias(Uint16ProgressiveList):
    """Second spelling of the same progressive list."""


class Uint32ProgressiveList(ProgressiveList[Uint32]):
    """Progressive list of uint32."""


class SquareProgressiveList(ProgressiveList[Square]):
    """Progressive list of progressive containers."""


class CircleProgressiveList(ProgressiveList[Circle]):
    """Progressive list of the compatible shape."""


class WideColorProgressiveList(ProgressiveList[WideColor]):
    """Progressive list of the clashing shape."""


# --------------------------------------------------------------------------------------
# Unions
# --------------------------------------------------------------------------------------


class Shape(CompatibleUnion):
    """EIP-8016's own example: the two halves of the EIP-7495 example as options."""

    OPTIONS = {1: Square, 2: Circle}


class ShapeRestated(CompatibleUnion):
    """The same two options under different selectors, one of them a restated class."""

    OPTIONS = {3: SquareRestated, 4: Circle}


class SquareOnly(CompatibleUnion):
    """A single option, compatible with both of Shape's."""

    OPTIONS = {5: Square}


class NumberUnion(CompatibleUnion):
    """A union over a sequence, so none of its options fits a shape option."""

    OPTIONS = {1: Uint16List4}


class NestedShape(CompatibleUnion):
    """Union of unions: every option is itself a compatible union."""

    OPTIONS = {1: Shape, 2: SquareOnly}


class NestedShapeAlias(CompatibleUnion):
    """A second union of unions, over the restated spellings."""

    OPTIONS = {6: ShapeRestated, 7: SquareOnly}


class UnionHolder(Container):
    """Container whose second field is a union."""

    tag: Uint8
    body: Shape


class RestatedUnionHolder(Container):
    """The same container over a compatible union."""

    tag: Uint8
    body: ShapeRestated


class NumberUnionHolder(Container):
    """The same container over a union that clashes with Shape."""

    tag: Uint8
    body: NumberUnion


def assert_relation(left: type[SSZType], right: type[SSZType], expected: bool) -> None:
    """Assert the relation answers as expected, and answers alike with the operands swapped."""
    assert is_compatible(left, right) is expected
    assert is_compatible(right, left) is expected


# Rule 1: a type is compatible with itself, whatever kind of type it is.
IDENTITY_PAIRS = [
    pytest.param(Uint8, Uint8, True, id="uint8_with_itself"),
    pytest.param(Bytes4, Bytes4, True, id="byte_vector_with_itself"),
    pytest.param(Bitvector4, Bitvector4, True, id="bitvector_with_itself"),
    pytest.param(Square, Square, True, id="progressive_container_with_itself"),
    pytest.param(Pair, Pair, True, id="container_with_itself"),
    pytest.param(Shape, Shape, True, id="union_with_itself"),
    pytest.param(
        ProgressiveBitlist, ProgressiveBitlist, True, id="progressive_bitlist_with_itself"
    ),
]

# Rule 2: a basic type answers for its width alone, so a named subtype still fits.
BASIC_PAIRS = [
    pytest.param(Uint8, Selector, True, id="uint8_and_a_named_uint8"),
    pytest.param(Uint256, Balance, True, id="uint256_and_a_named_uint256"),
    pytest.param(Uint8, Uint16, False, id="uint8_and_uint16"),
    pytest.param(Uint16, Uint32, False, id="uint16_and_uint32"),
    pytest.param(Boolean, Flag, True, id="boolean_and_a_named_boolean"),
    # There is one boolean width and one uint8 width, and they are still two types.
    pytest.param(Uint8, Boolean, False, id="uint8_and_boolean"),
]

# Rules 3 and 4: a byte array is the alias of a vector or list of single bytes.
BYTE_ARRAY_PAIRS = [
    pytest.param(Bytes4, Uint8Vector4, True, id="byte_vector_and_its_uint8_spelling"),
    pytest.param(Bytes4, Bytes4Alias, True, id="two_spellings_of_one_byte_vector"),
    pytest.param(Bytes4, Bytes8, False, id="byte_vectors_of_two_widths"),
    pytest.param(Bytes4, Uint8Vector8, False, id="byte_vector_and_a_wider_uint8_vector"),
    # A uint16 vector is not a byte array at any length: its elements are two bytes wide.
    pytest.param(Bytes4, Uint16Vector4, False, id="byte_vector_and_a_uint16_vector"),
    pytest.param(Uint8Vector4, BooleanVector4, False, id="uint8_vector_and_a_boolean_vector"),
    # A byte array is a vector, not the scalar its elements are.
    pytest.param(Bytes4, Uint8, False, id="byte_vector_and_a_bare_uint8"),
    pytest.param(ByteList4, Uint8List4, True, id="byte_list_and_its_uint8_spelling"),
    pytest.param(ByteList4, ByteList4Alias, True, id="two_spellings_of_one_byte_list"),
    pytest.param(ByteList4, ByteList8, False, id="byte_lists_of_two_capacities"),
    pytest.param(ByteList4, Uint8List8, False, id="byte_list_and_a_wider_uint8_list"),
    pytest.param(ByteList4, Uint16List4, False, id="byte_list_and_a_uint16_list"),
    pytest.param(Uint8List4, BooleanList4, False, id="uint8_list_and_a_boolean_list"),
    pytest.param(ByteList4, Uint8, False, id="byte_list_and_a_bare_uint8"),
    # Two 32-byte arrays declared for different purposes are still one SSZ type.
    pytest.param(Chunk, Root, True, id="chunk_and_root"),
]

# Rule 5: a bitfield answers for its capacity, and never across the three shapes.
BITFIELD_PAIRS = [
    pytest.param(Bitvector4, Bitvector4Alias, True, id="two_spellings_of_one_bitvector"),
    pytest.param(Bitvector4, Bitvector8, False, id="bitvectors_of_two_capacities"),
    pytest.param(Bitvector4, Bitlist4, False, id="bitvector_and_bitlist_of_one_size"),
    pytest.param(Bitvector4, Uint16Vector4, False, id="bitvector_and_a_uint16_vector"),
    pytest.param(Bitlist4, Bitlist4Alias, True, id="two_spellings_of_one_bitlist"),
    pytest.param(Bitlist4, Bitlist8, False, id="bitlists_of_two_capacities"),
    pytest.param(Bitlist4, ProgressiveBitlist, False, id="bitlist_and_progressive_bitlist"),
    pytest.param(Bitlist4, Uint16List4, False, id="bitlist_and_a_uint16_list"),
    pytest.param(ProgressiveBitlist, Flags, True, id="two_spellings_of_one_progressive_bitlist"),
    pytest.param(ProgressiveBitlist, Uint16List4, False, id="progressive_bitlist_and_a_list"),
]

# Rule 6: a sequence answers for its capacity and its element type.
SEQUENCE_PAIRS = [
    pytest.param(Uint16Vector4, Uint16Vector4Alias, True, id="two_spellings_of_one_vector"),
    pytest.param(Uint16Vector4, Uint16Vector8, False, id="vectors_of_two_lengths"),
    pytest.param(Uint16Vector4, Uint32Vector4, False, id="vectors_over_two_element_widths"),
    pytest.param(Uint16Vector4, Uint16List4, False, id="vector_and_list_of_one_size"),
    pytest.param(SquareVector4, CircleVector4, True, id="vectors_over_compatible_shapes"),
    pytest.param(SquareVector4, WideColorVector4, False, id="vectors_over_clashing_shapes"),
    pytest.param(Uint16List4, Uint16List4Alias, True, id="two_spellings_of_one_list"),
    pytest.param(Uint16List4, Uint16List8, False, id="lists_of_two_capacities"),
    pytest.param(Uint16List4, Uint32List4, False, id="lists_over_two_element_widths"),
    pytest.param(SquareList4, CircleList4, True, id="lists_over_compatible_shapes"),
    pytest.param(SquareList4, WideColorList4, False, id="lists_over_clashing_shapes"),
    pytest.param(SquareList4, SquareList8, False, id="lists_of_shapes_at_two_capacities"),
    pytest.param(
        Uint16ProgressiveList,
        Uint16ProgressiveListAlias,
        True,
        id="two_spellings_of_one_progressive_list",
    ),
    pytest.param(
        Uint16ProgressiveList,
        Uint32ProgressiveList,
        False,
        id="progressive_lists_over_two_element_widths",
    ),
    pytest.param(
        SquareProgressiveList,
        CircleProgressiveList,
        True,
        id="progressive_lists_over_compatible_shapes",
    ),
    pytest.param(
        SquareProgressiveList,
        WideColorProgressiveList,
        False,
        id="progressive_lists_over_clashing_shapes",
    ),
    # The two list shapes share a wire format and nothing else: one pads to its declared
    # capacity, the other grows a spine with the data.
    pytest.param(Uint16ProgressiveList, Uint16List4, False, id="progressive_and_bounded_list"),
    pytest.param(Uint8List4, ProgressiveList[Uint8], False, id="byte_list_and_progressive_list"),
    pytest.param(Uint16ProgressiveList, Square, False, id="progressive_list_and_a_shape"),
]

# Rule 7: a container answers for its field names, in order, and their types.
CONTAINER_PAIRS = [
    pytest.param(Pair, PairAlias, True, id="two_spellings_of_one_container"),
    pytest.param(Pair, PairRenamed, False, id="containers_differing_by_a_field_name"),
    pytest.param(Pair, PairReordered, False, id="containers_with_the_fields_reordered"),
    pytest.param(Pair, PairWidened, False, id="containers_differing_by_a_field_width"),
    pytest.param(Pair, PairExtended, False, id="container_and_a_longer_one"),
    # A container merkleizes into a tree sized by its field count; a progressive one does not.
    pytest.param(Pair, Square, False, id="container_and_progressive_container"),
    pytest.param(Pair, Shape, False, id="container_and_a_union"),
]

# Rule 8: a progressive container answers for the positions its layout sets.
PROGRESSIVE_CONTAINER_PAIRS = [
    pytest.param(Square, SquareRestated, True, id="two_spellings_of_one_layout"),
    # The EIP-7495 pair: the shared position 2 holds color in both.
    pytest.param(Square, Circle, True, id="square_and_circle"),
    # No position is set in both, so neither layout can move anything the other holds.
    pytest.param(Square, Tail, True, id="layouts_that_do_not_overlap"),
    pytest.param(Square, WideColor, False, id="shared_position_holding_two_widths"),
    pytest.param(Circle, WideColor, False, id="shared_position_holding_two_widths_again"),
    pytest.param(Square, Shade, False, id="shared_position_holding_two_names"),
    # A proof would follow the name to position 0 in one and position 1 in the other.
    pytest.param(Square, MovedSide, False, id="one_name_at_two_positions"),
    pytest.param(Square, Shape, False, id="progressive_container_and_a_union"),
]

# Rule 9: two unions agree when every option of one fits every option of the other.
UNION_PAIRS = [
    pytest.param(Shape, ShapeRestated, True, id="unions_over_the_same_two_shapes"),
    # Selectors play no part: the relation is about the option types alone.
    pytest.param(Shape, SquareOnly, True, id="two_options_and_one_that_fits_both"),
    pytest.param(Shape, NumberUnion, False, id="unions_over_unrelated_options"),
    pytest.param(NestedShape, NestedShapeAlias, True, id="two_unions_of_unions"),
    pytest.param(Shape, Uint8, False, id="union_and_a_basic_type"),
]

ALL_PAIRS = [
    *IDENTITY_PAIRS,
    *BASIC_PAIRS,
    *BYTE_ARRAY_PAIRS,
    *BITFIELD_PAIRS,
    *SEQUENCE_PAIRS,
    *CONTAINER_PAIRS,
    *PROGRESSIVE_CONTAINER_PAIRS,
    *UNION_PAIRS,
]
"""Every pair stated above, for the property that holds over all of them at once."""


@pytest.mark.parametrize("left, right, expected", IDENTITY_PAIRS)
def test_a_type_is_compatible_with_itself(
    left: type[SSZType], right: type[SSZType], expected: bool
) -> None:
    """The first rule holds for every kind of type, basic, composite, and union alike."""
    assert_relation(left, right, expected)


@pytest.mark.parametrize("left, right, expected", BASIC_PAIRS)
def test_basic_types_answer_for_their_width(
    left: type[SSZType], right: type[SSZType], expected: bool
) -> None:
    """A uint answers for its bit width, a boolean for being one, and never across the two."""
    assert_relation(left, right, expected)


@pytest.mark.parametrize("left, right, expected", BYTE_ARRAY_PAIRS)
def test_byte_arrays_are_aliases_of_byte_sequences(
    left: type[SSZType], right: type[SSZType], expected: bool
) -> None:
    """A byte array and the vector or list of single bytes it stands for are one type."""
    assert_relation(left, right, expected)


@pytest.mark.parametrize("left, right, expected", BITFIELD_PAIRS)
def test_bitfields_answer_for_their_capacity(
    left: type[SSZType], right: type[SSZType], expected: bool
) -> None:
    """The three bitfield shapes merkleize differently, so none of them crosses to another."""
    assert_relation(left, right, expected)


@pytest.mark.parametrize("left, right, expected", SEQUENCE_PAIRS)
def test_sequences_answer_for_their_capacity_and_element_type(
    left: type[SSZType], right: type[SSZType], expected: bool
) -> None:
    """A vector needs one length, a list one capacity, and both need compatible elements."""
    assert_relation(left, right, expected)


@pytest.mark.parametrize("left, right, expected", CONTAINER_PAIRS)
def test_containers_answer_for_their_fields_in_order(
    left: type[SSZType], right: type[SSZType], expected: bool
) -> None:
    """Field names, their order, and their types all have to line up."""
    assert_relation(left, right, expected)


@pytest.mark.parametrize("left, right, expected", PROGRESSIVE_CONTAINER_PAIRS)
def test_progressive_containers_answer_for_their_positions(
    left: type[SSZType], right: type[SSZType], expected: bool
) -> None:
    """Layouts agree when every position set in both holds one name, of compatible types."""
    assert_relation(left, right, expected)


@pytest.mark.parametrize("left, right, expected", UNION_PAIRS)
def test_unions_answer_for_every_pair_of_their_options(
    left: type[SSZType], right: type[SSZType], expected: bool
) -> None:
    """Two unions agree when every option of one fits every option of the other."""
    assert_relation(left, right, expected)


@pytest.mark.parametrize("left, right, expected", ALL_PAIRS)
def test_the_relation_is_symmetric(
    left: type[SSZType], right: type[SSZType], expected: bool
) -> None:
    """
    Swapping the operands never changes the answer.

    The relation states that two types build one tree shape, and a shape has no left
    operand and no right one. An implementation that walks only the left type's rules
    would answer one way for Bytes4 against Uint8Vector4 and the other way back.
    """
    assert is_compatible(left, right) == is_compatible(right, left) == expected


def test_compatibility_is_not_class_identity() -> None:
    """Two distinct classes are compatible, and one class is never split from itself."""
    # Different classes, one SSZ type: the relation is about the tree, not the declaration.
    assert Square is not SquareRestated
    assert is_compatible(Square, SquareRestated)
    # Different classes, different field layouts, still one tree shape wherever they overlap.
    assert is_compatible(Square, Circle)


def test_a_container_field_recurses_into_the_relation() -> None:
    """A container holding a progressive container defers to the relation on that field."""
    # tag lines up in all three; shape carries the decision.
    assert_relation(SquareHolder, CircleHolder, True)
    assert_relation(SquareHolder, WideColorHolder, False)
    assert_relation(CircleHolder, WideColorHolder, False)


def test_a_container_field_that_is_a_union_recurses_too() -> None:
    """A union nested in a container is compared by the union rule, one level down."""
    assert_relation(UnionHolder, RestatedUnionHolder, True)
    assert_relation(UnionHolder, NumberUnionHolder, False)


def test_a_union_of_unions_recurses_through_both_levels() -> None:
    """Every option of every option has to fit, since a proof may descend that far."""
    # NestedShape holds Shape and SquareOnly; NestedShapeAlias holds ShapeRestated and
    # SquareOnly. The four cross pairs all reduce to Square against Circle, or to
    # Square against Square.
    assert_relation(NestedShape, NestedShapeAlias, True)
    # A union of unions is not the union one level down from it: comparing them pits
    # Shape against Square, a union against a progressive container, which never fits.
    assert_relation(NestedShape, Shape, False)


def test_a_list_of_compatible_things_is_compatible() -> None:
    """The element rule is the relation itself, so a list inherits whatever its elements do."""
    assert_relation(SquareList4, CircleList4, True)
    assert_relation(SquareProgressiveList, CircleProgressiveList, True)
    assert_relation(SquareVector4, CircleVector4, True)
    # And the capacity still has to match, however compatible the elements are.
    assert_relation(SquareList4, SquareList8, False)


def test_recursion_reaches_through_two_levels_of_element_type() -> None:
    """A list of lists of shapes defers all the way down to the shape comparison."""

    class SquareListList(ProgressiveList[SquareList4]):
        """Progressive list whose elements are bounded lists of Square."""

        ELEMENT_TYPE = SquareList4

    class CircleListList(ProgressiveList[CircleList4]):
        """The same two levels over the compatible shape."""

        ELEMENT_TYPE = CircleList4

    class WideColorListList(ProgressiveList[WideColorList4]):
        """The same two levels over the clashing shape."""

        ELEMENT_TYPE = WideColorList4

    assert_relation(SquareListList, CircleListList, True)
    assert_relation(SquareListList, WideColorListList, False)


def test_progressive_layouts_may_share_no_position_at_all() -> None:
    """A position set in only one layout is free: the other leaves a zero leaf there."""
    # Square sets positions 0 and 2; Tail sets position 3. Nothing either holds can move.
    assert_relation(Square, Tail, True)
    # Shade sets position 0, which Square holds too, so the two do clash.
    assert_relation(Shade, Tail, True)
    assert_relation(Shade, Square, False)


def test_progressive_layouts_pin_a_shared_name_to_one_position() -> None:
    """
    A name declared by both layouts has to sit at one position.

    Square puts side at position 0 and MovedSide puts it at position 1, while both put
    color at position 2. Every position set in both agrees, so only the name rule
    catches it — and it has to, or a proof about side would read two different leaves.
    """
    assert_relation(Square, MovedSide, False)
    # The shared position is genuinely fine on its own, which is what makes the case sharp.
    square_color = Square.model_fields["color"].annotation
    moved_color = MovedSide.model_fields["color"].annotation
    assert is_compatible(square_color, moved_color)

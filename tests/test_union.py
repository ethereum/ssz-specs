"""Tests for the EIP-8016 compatible union."""

from __future__ import annotations

import io

import pytest
from pydantic import ValidationError

from ssz import (
    CompatibleUnion,
    Container,
    List,
    ProgressiveContainer,
    ProgressiveList,
    SSZDefaultError,
    SSZDefinitionError,
    SSZFixedSizeError,
    SSZLimitError,
    SSZSerializationError,
    SSZTypeError,
    SSZTypeMismatch,
    SSZUnionOptionsError,
    Uint8,
    Uint16,
    Uint32,
)
from ssz.union import MAX_SELECTOR, MIN_SELECTOR


class Square(ProgressiveContainer):
    """EIP-7495's own example: side at position 0, a gap, then color at position 2."""

    ACTIVE_FIELDS = (1, 0, 1)

    side: Uint16
    color: Uint8


class Circle(ProgressiveContainer):
    """The other half of that example: a gap, then radius at 1 and color at 2."""

    ACTIVE_FIELDS = (0, 1, 1)

    radius: Uint16
    color: Uint8


class Tail(ProgressiveContainer):
    """A field at position 3, which none of the three-wide layouts set."""

    ACTIVE_FIELDS = (0, 0, 0, 1)

    tail: Uint8


class Shade(ProgressiveContainer):
    """One position, holding a field Square does not declare at position 0."""

    ACTIVE_FIELDS = (1,)

    shade: Uint8


class Uint16List4(List[Uint16]):
    """Bounded list of two-byte elements, a variable-size option."""

    LIMIT = 4


class Uint16List4Alias(Uint16List4):
    """Second spelling of the same list, compatible with it by the first rule."""


class Uint32List4(List[Uint32]):
    """The same capacity over a wider element, so it clashes with Uint16List4."""

    LIMIT = 4


class Shape(CompatibleUnion):
    """EIP-8016's own example: Square under selector 1, Circle under selector 2."""

    OPTIONS = {1: Square, 2: Circle}


class SquareOnly(CompatibleUnion):
    """One option, so a union of unions has a second member to hold."""

    OPTIONS = {5: Square}


class NestedShape(CompatibleUnion):
    """Union of unions: each option is itself a compatible union."""

    OPTIONS = {1: Shape, 2: SquareOnly}


class Numbers(CompatibleUnion):
    """Union over a variable-size option, so the payload has no fixed width."""

    OPTIONS = {1: Uint16List4, 2: Uint16List4Alias}


class ScalarUnion(CompatibleUnion):
    """Union over a basic option, whose payload is not a sequence of anything."""

    OPTIONS = {1: Uint8}


class LowestSelector(CompatibleUnion):
    """The lowest selector a union may declare."""

    OPTIONS = {MIN_SELECTOR: Square}


class HighestSelector(CompatibleUnion):
    """The highest selector a union may declare."""

    OPTIONS = {MAX_SELECTOR: Square}


class BoundarySelectors(CompatibleUnion):
    """Both ends of the legal range in one declaration."""

    OPTIONS = {MIN_SELECTOR: Square, MAX_SELECTOR: Circle}


class ShapeHolder(Container):
    """Ordinary container reaching a union through an offset."""

    tag: Uint8
    body: Shape


class ProgressiveShapeHolder(ProgressiveContainer):
    """Progressive container reaching a union through an offset, with a gap before it."""

    ACTIVE_FIELDS = (1, 0, 1)

    tag: Uint8
    body: Shape


class ShapeProgressiveList(ProgressiveList[Shape]):
    """Progressive list of unions, so the bodies need an offset table."""


SQUARE = Square(side=Uint16(0x1234), color=Uint8(0x42))
"""The value EIP-8016 spells out: Shape(selector=1, data=Square(0x1234, 0x42))."""

CIRCLE = Circle(radius=Uint16(0x1234), color=Uint8(0x42))
"""The other option, which encodes to the same three payload bytes."""


class TestOptionDeclaration:
    """The rules a union's option map has to satisfy, checked when the class is created."""

    def test_a_union_must_declare_options(self) -> None:
        """Options are the one declaration a union needs, so omitting them is fatal."""
        with pytest.raises(SSZDefinitionError, match=r"^NoOptions must define OPTIONS$"):

            class NoOptions(CompatibleUnion):
                pass

    def test_an_empty_option_map_is_rejected(self) -> None:
        """A union with no option admits no value at all."""
        with pytest.raises(
            SSZUnionOptionsError,
            match=r"^NoVariants: invalid union options, the options are empty$",
        ):
            type("NoVariants", (CompatibleUnion,), {"OPTIONS": {}})

    @pytest.mark.parametrize(
        "selector",
        [
            # Zero is reserved, so a value that was never initialized cannot pass as valid.
            pytest.param(0, id="zero_is_reserved"),
            # The high bit is reserved for a later extension.
            pytest.param(128, id="the_high_bit_is_reserved"),
            pytest.param(255, id="the_top_of_the_byte"),
        ],
    )
    def test_a_selector_outside_one_through_127_is_rejected(self, selector: int) -> None:
        """Only 1 through 127 name an option; the rest of the byte is reserved."""
        with pytest.raises(
            SSZUnionOptionsError,
            match=(
                r"^OutOfRange: invalid union options, "
                + rf"selector {selector} falls outside 1 through 127$"
            ),
        ):
            type("OutOfRange", (CompatibleUnion,), {"OPTIONS": {selector: Square}})

    def test_the_range_boundaries_are_legal(self) -> None:
        """One and 127 are inside the range, so both declare fine."""
        assert MIN_SELECTOR == 1
        assert MAX_SELECTOR == 127
        assert list(LowestSelector.OPTIONS) == [1]
        assert list(HighestSelector.OPTIONS) == [127]
        assert list(BoundarySelectors.OPTIONS) == [1, 127]

    def test_options_given_as_a_sequence_are_rejected(self) -> None:
        """A sequence of types would read its own entries as selectors."""
        with pytest.raises(
            SSZUnionOptionsError,
            match=r"^Sequenced: invalid union options, the options are not a selector-to-type map$",
        ):
            type("Sequenced", (CompatibleUnion,), {"OPTIONS": [Square, Circle]})

    def test_a_typed_selector_key_is_rejected(self) -> None:
        """The spec writes the range with a uint, but a key here stays a plain int."""
        # A typed uint compares strictly against a plain int, so a typed key would fail
        # the range check with a bare type error instead of the union's own message.
        with pytest.raises(
            SSZUnionOptionsError,
            match=r"^TypedKey: invalid union options, selector Uint8\(1\) is not a plain int$",
        ):
            type("TypedKey", (CompatibleUnion,), {"OPTIONS": {Uint8(1): Square}})

    @pytest.mark.parametrize(
        "option",
        [
            pytest.param(int, id="builtin_type"),
            pytest.param("Square", id="a_name_rather_than_a_type"),
            pytest.param(None, id="none"),
        ],
    )
    def test_an_option_that_is_not_an_ssz_type_is_rejected(self, option: object) -> None:
        """An option has to be a type this library can serialize and merkleize."""
        with pytest.raises(
            SSZUnionOptionsError,
            match=r"^NotSSZ: invalid union options, option 1 is not an SSZ type$",
        ):
            type("NotSSZ", (CompatibleUnion,), {"OPTIONS": {1: option}})

    def test_options_that_merkleize_differently_are_rejected(self) -> None:
        """Two options that build different trees cannot both answer one proof."""
        with pytest.raises(
            SSZUnionOptionsError,
            match=r"^Clashing: invalid union options, options 1 and 2 merkleize differently$",
        ):
            type("Clashing", (CompatibleUnion,), {"OPTIONS": {1: Uint16List4, 2: Uint32List4}})

    def test_every_pair_is_checked_not_only_the_first(self) -> None:
        """
        A clash between the first and the third option is as fatal as one with the second.

        Square sets positions 0 and 2, Tail sets position 3, and Shade sets position 0.
        Square fits Tail and Tail fits Shade, since neither pair shares a position. Square
        and Shade both set position 0 and hold different fields there, so the union is
        illegal even though each option fits its neighbour.
        """
        with pytest.raises(
            SSZUnionOptionsError,
            match=r"^FirstAndThird: invalid union options, options 1 and 3 merkleize differently$",
        ):
            type(
                "FirstAndThird",
                (CompatibleUnion,),
                {"OPTIONS": {1: Square, 2: Tail, 3: Shade}},
            )

    def test_a_clash_between_the_second_and_third_options_is_caught(self) -> None:
        """The same three shapes reordered, so the clashing pair excludes the first option."""
        with pytest.raises(
            SSZUnionOptionsError,
            match=r"^SecondAndThird: invalid union options, options 2 and 3 merkleize differently$",
        ):
            type(
                "SecondAndThird",
                (CompatibleUnion,),
                {"OPTIONS": {1: Tail, 2: Square, 3: Shade}},
            )

    def test_the_error_carries_the_union_and_the_rule_it_broke(self) -> None:
        """The exception keeps its fields machine-readable, not only the formatted message."""
        with pytest.raises(SSZUnionOptionsError) as exception_info:
            type("Empty", (CompatibleUnion,), {"OPTIONS": {}})
        assert isinstance(exception_info.value, SSZTypeError)
        assert exception_info.value.type_name == "Empty"
        assert exception_info.value.reason == "the options are empty"

    def test_a_union_of_unions_is_a_legal_declaration(self) -> None:
        """A union option may itself be a union, checked by the same relation one level down."""
        assert NestedShape.OPTIONS == {1: Shape, 2: SquareOnly}

    def test_a_union_of_clashing_unions_is_rejected(self) -> None:
        """The relation descends into the options of the options, so a deep clash still fires."""
        with pytest.raises(
            SSZUnionOptionsError,
            match=r"^DeepClash: invalid union options, options 1 and 2 merkleize differently$",
        ):
            type("DeepClash", (CompatibleUnion,), {"OPTIONS": {1: Shape, 2: Numbers}})


class TestConstruction:
    """A value carries the selector of the option it holds, and has to hold that option."""

    def test_a_value_shows_both_halves(self) -> None:
        """A union reads as its two named fields, not as the contents of the option."""
        # A collection wraps its contents in a field named data, and a union names its
        # payload field the same way. Only the base class separates the two shapes,
        # so a union holding a basic value would otherwise be read as a sequence of it.
        value = ScalarUnion(selector=Uint8(1), data=Uint8(7))
        assert repr(value) == "ScalarUnion(selector=Uint8(1) data=Uint8(7))"
        assert len(value) == 2

    def test_a_value_rejects_attribute_assignment(self) -> None:
        """A union declares itself frozen, so neither half changes after construction."""
        value = ScalarUnion(selector=Uint8(1), data=Uint8(7))
        with pytest.raises(ValidationError):
            value.selector = Uint8(1)

    def test_a_value_holds_its_selector_and_its_data(self) -> None:
        """Construction keeps both halves exactly as given."""
        value = Shape(selector=Uint8(1), data=SQUARE)
        assert value.selector == Uint8(1)
        assert value.data == SQUARE

    def test_either_option_may_be_held(self) -> None:
        """The second selector names the second option, and holds a value of that type."""
        value = Shape(selector=Uint8(2), data=CIRCLE)
        assert value.selector == Uint8(2)
        assert value.data == CIRCLE

    def test_equal_values_compare_equal(self) -> None:
        """Two constructions of one value are equal, selector and payload alike."""
        assert Shape(selector=Uint8(1), data=SQUARE) == Shape(selector=Uint8(1), data=SQUARE)

    def test_the_selector_separates_two_otherwise_equal_values(self) -> None:
        """The same payload under two selectors is two different values."""
        square_under_one = LowestSelector(selector=Uint8(1), data=SQUARE)
        square_under_127 = HighestSelector(selector=Uint8(127), data=SQUARE)
        assert square_under_one.data == square_under_127.data
        assert square_under_one.selector != square_under_127.selector

    def test_a_selector_naming_no_option_is_rejected(self) -> None:
        """Selector 3 is inside the legal range and still names nothing this union declares."""
        with pytest.raises(
            SSZUnionOptionsError,
            match=r"^Shape: invalid union options, selector 3 names no option$",
        ):
            Shape(selector=Uint8(3), data=SQUARE)

    def test_the_reserved_zero_selector_names_no_option_either(self) -> None:
        """Zero can never be declared, so it can never be held."""
        with pytest.raises(
            SSZUnionOptionsError,
            match=r"^Shape: invalid union options, selector 0 names no option$",
        ):
            Shape(selector=Uint8(0), data=SQUARE)

    def test_data_of_another_option_is_rejected(self) -> None:
        """Selector 1 names Square, so a Circle payload under it is a different value."""
        with pytest.raises(SSZTypeMismatch, match=r"^Expected Square, got Circle$"):
            Shape(selector=Uint8(1), data=CIRCLE)

    def test_data_of_no_option_at_all_is_rejected(self) -> None:
        """A payload of a type the union never declared fails the same check."""
        with pytest.raises(SSZTypeMismatch, match=r"^Expected Circle, got Square$"):
            Shape(selector=Uint8(2), data=SQUARE)

    def test_a_value_is_frozen(self) -> None:
        """The selector and the payload are fixed at construction, as for every SSZ type."""
        value = Shape(selector=Uint8(1), data=SQUARE)
        with pytest.raises(Exception, match=r"frozen"):
            value.selector = Uint8(2)


class TestNoDefaultValue:
    """
    A union has no default value, because zero is not a selector.

    Every other SSZ type answers what its zeroed value is. A union cannot: a default
    would have to name an option, and the one selector an all-zero value could carry
    is reserved against exactly that.
    """

    def test_building_a_union_from_nothing_is_rejected(self) -> None:
        """No selector and no payload names no option, so there is nothing to build."""
        with pytest.raises(SSZDefaultError, match=r"^Shape has no default value$"):
            Shape.default()

    def test_the_error_is_a_type_error_carrying_the_type_name(self) -> None:
        """The failure keeps the offending type machine-readable, as every SSZ error does."""
        with pytest.raises(SSZDefaultError) as exception_info:
            Shape.default()
        assert isinstance(exception_info.value, SSZTypeError)
        assert exception_info.value.type_name == "Shape"
        assert exception_info.value.args[0] == "Shape has no default value"

    def test_the_error_names_whichever_union_was_asked(self) -> None:
        """Each union reports itself, so a nested absence points at the right type."""
        with pytest.raises(SSZDefaultError, match=r"^NestedShape has no default value$"):
            NestedShape.default()

    def test_is_zero_is_undefined_on_a_union(self) -> None:
        """The zeroed check compares against a default, and a union has none to compare to."""
        value = Shape(selector=Uint8(1), data=SQUARE)
        with pytest.raises(SSZDefaultError, match=r"^Shape has no default value$"):
            value.is_zero()

    def test_a_selector_without_a_payload_is_not_a_request_for_a_default(self) -> None:
        """Only the total absence of input reaches the refusal; a named field does not."""
        # The payload is simply missing here, which is Pydantic's own error, not this one.
        with pytest.raises(ValidationError, match=r"(?s)^1 validation error for Shape\ndata\n"):
            Shape(selector=Uint8(1))  # ty: ignore[missing-argument]


class TestSizing:
    """A union is variable-size, whatever its options are."""

    def test_a_union_is_never_fixed_size(self) -> None:
        """Both options here are three bytes wide, and the union is still variable-size."""
        assert Square.is_fixed_size() is True
        assert Circle.is_fixed_size() is True
        assert Square.get_byte_length() == 3
        assert Circle.get_byte_length() == 3
        # A parser cannot know the payload width before it has read the selector, so the
        # surrounding container has to reach the union through an offset regardless.
        assert Shape.is_fixed_size() is False

    def test_a_union_over_variable_options_is_variable_size_too(self) -> None:
        """Nothing changes when the options have no fixed width of their own."""
        assert Numbers.is_fixed_size() is False

    def test_asking_a_union_for_a_byte_length_raises(self) -> None:
        """Variable-size types have no fixed byte length, and a union is one of them."""
        with pytest.raises(SSZFixedSizeError) as exception_info:
            Shape.get_byte_length()
        assert exception_info.value.args[0] == (
            "Shape: variable-size compatible union has no fixed byte length"
        )
        assert exception_info.value.type_name == "Shape"
        assert exception_info.value.kind == "compatible union"


class TestSerialization:
    """The selector leads, and the option's own encoding follows."""

    def test_the_eip_example_encodes_to_four_bytes(self) -> None:
        """EIP-8016's own value: one selector byte, then Square's three payload bytes."""
        # byte 0     : selector = 01
        # bytes 1..2 : side  = 3412  (0x1234, little-endian)
        # byte 3     : color = 42
        value = Shape(selector=Uint8(1), data=SQUARE)
        assert value.encode_bytes().hex() == "01341242"

    def test_the_other_option_differs_only_in_the_selector(self) -> None:
        """Square and Circle encode to the same three bytes, so the selector is all there is."""
        square_bytes = Shape(selector=Uint8(1), data=SQUARE).encode_bytes()
        circle_bytes = Shape(selector=Uint8(2), data=CIRCLE).encode_bytes()
        assert square_bytes.hex() == "01341242"
        assert circle_bytes.hex() == "02341242"
        assert square_bytes[1:] == circle_bytes[1:]

    @pytest.mark.parametrize(
        "selector, expected_prefix",
        [
            pytest.param(MIN_SELECTOR, "01", id="lowest_selector"),
            pytest.param(MAX_SELECTOR, "7f", id="highest_selector"),
        ],
    )
    def test_both_range_boundaries_encode_as_one_byte(
        self, selector: int, expected_prefix: str
    ) -> None:
        """The selector occupies exactly one byte on the wire, at either end of the range."""
        value = BoundarySelectors(
            selector=Uint8(selector),
            data=SQUARE if selector == MIN_SELECTOR else CIRCLE,
        )
        assert value.encode_bytes().hex() == expected_prefix + "341242"

    def test_a_variable_size_option_follows_the_selector_directly(self) -> None:
        """No offset separates the selector from the payload: the union is the whole scope."""
        # byte 0     : selector = 01
        # bytes 1..4 : two uint16 elements, back to back
        value = Numbers(selector=Uint8(1), data=Uint16List4(data=[Uint16(1), Uint16(2)]))
        assert value.encode_bytes().hex() == "0101000200"

    def test_an_empty_variable_size_option_encodes_to_the_selector_alone(self) -> None:
        """A zero-byte payload leaves the selector as the entire encoding."""
        value = Numbers(selector=Uint8(1), data=Uint16List4(data=[]))
        assert value.encode_bytes().hex() == "01"

    def test_serialize_returns_the_byte_count_it_wrote(self) -> None:
        """The stream writer reports one byte for the selector plus the payload's own count."""
        stream = io.BytesIO()
        written = Shape(selector=Uint8(1), data=SQUARE).serialize(stream)
        assert written == 4
        assert written == len(stream.getvalue())


class TestDeserialization:
    """The selector leads, so the option is known before any of its bytes are read."""

    @pytest.mark.parametrize(
        "value",
        [
            pytest.param(Shape(selector=Uint8(1), data=SQUARE), id="fixed_size_option"),
            pytest.param(Shape(selector=Uint8(2), data=CIRCLE), id="the_other_option"),
            pytest.param(
                Numbers(selector=Uint8(2), data=Uint16List4Alias(data=[Uint16(7)])),
                id="variable_size_option",
            ),
            pytest.param(
                Numbers(selector=Uint8(1), data=Uint16List4(data=[])),
                id="empty_variable_size_option",
            ),
            pytest.param(HighestSelector(selector=Uint8(127), data=SQUARE), id="highest_selector"),
        ],
    )
    def test_round_trip(self, value: CompatibleUnion) -> None:
        """Encoding then decoding returns the very same value, selector and payload alike."""
        assert type(value).decode_bytes(value.encode_bytes()) == value

    def test_the_selector_picks_the_option_before_the_payload_is_read(self) -> None:
        """The same three payload bytes decode into two different types under two selectors."""
        assert Shape.decode_bytes(bytes.fromhex("01341242")).data == SQUARE
        assert Shape.decode_bytes(bytes.fromhex("02341242")).data == CIRCLE

    def test_an_empty_budget_holds_no_selector(self) -> None:
        """A union always carries a selector, so a zero-byte input is never one."""
        with pytest.raises(SSZSerializationError) as exception_info:
            Shape.decode_bytes(b"")
        assert exception_info.value.args[0] == "Shape: scope 0 holds no selector"

    def test_a_short_budget_is_rejected_by_deserialize_directly(self) -> None:
        """The stream decoder checks the budget before it touches the stream."""
        with pytest.raises(SSZSerializationError) as exception_info:
            Shape.deserialize(io.BytesIO(b""), 0)
        assert exception_info.value.args[0] == "Shape: scope 0 holds no selector"

    @pytest.mark.parametrize(
        "selector_byte, selector_value",
        [
            pytest.param("00", 0, id="the_reserved_zero"),
            pytest.param("03", 3, id="inside_the_range_but_undeclared"),
            pytest.param("80", 128, id="the_reserved_high_bit"),
            pytest.param("ff", 255, id="the_top_of_the_byte"),
        ],
    )
    def test_a_selector_naming_no_option_is_rejected(
        self, selector_byte: str, selector_value: int
    ) -> None:
        """A wire selector this union never declared is rejected before the payload is read."""
        with pytest.raises(SSZUnionOptionsError) as exception_info:
            Shape.decode_bytes(bytes.fromhex(selector_byte + "341242"))
        assert exception_info.value.args[0] == (
            f"Shape: invalid union options, selector {selector_value} names no option"
        )

    def test_trailing_bytes_are_rejected(self) -> None:
        """One canonical encoding per value, so a spare byte after the payload is noise."""
        with pytest.raises(SSZSerializationError) as exception_info:
            Shape.decode_bytes(bytes.fromhex("0134124200"))
        assert exception_info.value.args[0] == "Shape: 1 trailing byte(s) after decode"

    def test_a_truncated_payload_surfaces_the_option_s_own_error(self) -> None:
        """The rest of the budget belongs to the option, which reports its own shortfall."""
        with pytest.raises(SSZSerializationError) as exception_info:
            Shape.decode_bytes(bytes.fromhex("0134"))
        assert exception_info.value.args[0] == "Uint16: expected 2 bytes, got 1"

    def test_a_payload_the_option_cannot_parse_is_rejected(self) -> None:
        """A three-byte budget is not a whole number of two-byte elements."""
        with pytest.raises(SSZSerializationError) as exception_info:
            Numbers.decode_bytes(bytes.fromhex("01010002"))
        assert exception_info.value.args[0] == (
            "Uint16List4: scope 3 not divisible by element size 2"
        )

    def test_an_over_capacity_payload_is_rejected(self) -> None:
        """The option's own capacity rule still applies inside the union's budget."""
        with pytest.raises(SSZLimitError, match=r"^Uint16List4 exceeds limit of 4, got 5$"):
            Numbers.decode_bytes(bytes.fromhex("01") + b"\x00" * 10)


class TestNesting:
    """A union inside a container, inside a progressive container, and inside itself."""

    def test_a_container_reaches_a_union_through_an_offset(self) -> None:
        """
        The union is variable-size, so the container writes an offset for it.

        Layout:

            byte  0     : tag = ff        (fixed-size field, inline)
            bytes 1..4  : off_body = 5    (the union body starts at byte 5)
            bytes 5..8  : body            (selector 01, then Square's three bytes)
        """
        value = ShapeHolder(tag=Uint8(0xFF), body=Shape(selector=Uint8(1), data=SQUARE))
        assert ShapeHolder.is_fixed_size() is False
        assert value.encode_bytes().hex() == "ff0500000001341242"
        assert ShapeHolder.decode_bytes(value.encode_bytes()) == value

    def test_a_progressive_container_reaches_a_union_the_same_way(self) -> None:
        """The gap at position 1 costs no bytes, so the encoding matches the container's."""
        value = ProgressiveShapeHolder(tag=Uint8(0xFF), body=Shape(selector=Uint8(1), data=SQUARE))
        assert ProgressiveShapeHolder.is_fixed_size() is False
        assert value.encode_bytes().hex() == "ff0500000001341242"
        assert ProgressiveShapeHolder.decode_bytes(value.encode_bytes()) == value

    def test_a_union_holds_a_union(self) -> None:
        """
        Two selectors lead, one per level, before any payload byte.

        The inner union is variable-size, and so is every union, so the outer one hands it
        the rest of the budget and the inner one reads its own selector out of it.
        """
        value = NestedShape(selector=Uint8(1), data=Shape(selector=Uint8(2), data=CIRCLE))
        assert value.encode_bytes().hex() == "0102341242"
        assert NestedShape.decode_bytes(value.encode_bytes()) == value

    def test_a_progressive_list_of_unions_needs_an_offset_table(self) -> None:
        """
        Unions are variable-size elements, so each body is reached through an offset.

        Layout:

            bytes 0..3   : off_0 = 8    (first body starts at byte 8)
            bytes 4..7   : off_1 = 12   (second body starts at byte 12)
            bytes 8..11  : body_0       (selector 01, then Square's three bytes)
            bytes 12..15 : body_1       (selector 02, then Circle's three bytes)
        """
        value = ShapeProgressiveList(
            data=[
                Shape(selector=Uint8(1), data=SQUARE),
                Shape(selector=Uint8(2), data=CIRCLE),
            ]
        )
        expected_bytes = "080000000c00000001341242" + "02341242"
        assert value.encode_bytes().hex() == expected_bytes
        assert ShapeProgressiveList.decode_bytes(value.encode_bytes()) == value

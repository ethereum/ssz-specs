"""Tests for the tagged union the specification defines as `Union[type_0, type_1, ...]`."""

from __future__ import annotations

import io
from typing import Any

import pytest
from pydantic import ValidationError

from ssz import (
    ZERO_ROOT,
    Boolean,
    ByteVector,
    CompatibleUnion,
    Container,
    List,
    ProgressiveContainer,
    ProgressiveList,
    SSZTypeError,
    SSZValueError,
    TypeFault,
    Uint8,
    Uint16,
    Uint32,
    Uint64,
    Union,
    ValueFault,
    hash_tree_root,
    is_compatible,
    mix_in_selector,
)

SELECTOR_WIDTH = Uint8.get_byte_length()
"""Bytes the selector occupies, which is what every union encoding opens with."""


class Uint16List4(List[Uint16]):
    """Bounded list of two-byte elements, a variable-size option."""

    LIMIT = 4


class Uint32List4(List[Uint32]):
    """The same capacity over a wider element, so the two lists merkleize differently."""

    LIMIT = 4


class Square(ProgressiveContainer):
    """A composite option, whose own encoding follows the selector byte."""

    ACTIVE_FIELDS = (1, 0, 1)

    side: Uint16
    color: Uint8


class Maybe(Union):
    """The specification's own example shape: None first, then two integer widths."""

    OPTIONS = (None, Uint64, Uint32)


class Numbers(Union):
    """Union over two options, neither of which is None."""

    OPTIONS = (Uint16List4, Square)


class Widths(Union):
    """Two options of one fixed width, which leaves the selector as the only difference."""

    OPTIONS = (Uint32, Uint32)


class Nested(Union):
    """Union whose second option is itself a union."""

    OPTIONS = (Uint8, Maybe)


class Undefaultable(CompatibleUnion):
    """A compatible union, which is the one SSZ type with no default value."""

    OPTIONS = {1: Square}


class NoDefaultFirst(Union):
    """Union whose first option is the one type that cannot supply a default."""

    OPTIONS = (Undefaultable, Uint8)


class Holder(Container):
    """Ordinary container reaching a union through an offset."""

    tag: Uint8
    body: Maybe


class MaybeList(ProgressiveList[Maybe]):
    """Progressive list of unions, whose variable-size bodies need an offset table."""


class TestOptionDeclaration:
    """The rules a union's option list has to satisfy, checked when the class is created."""

    def test_a_union_must_declare_options(self) -> None:
        """Options are the one declaration a union needs, so omitting them is fatal."""
        with pytest.raises(SSZTypeError, match=r"^NoOptions must declare OPTIONS$") as raised:

            class NoOptions(Union):
                pass

        assert raised.value.fault is TypeFault.UNDECLARED

    def test_an_empty_option_list_is_rejected(self) -> None:
        """A union with no option admits no value at all."""
        with pytest.raises(SSZTypeError, match=r"^a union declares at least one option$") as raised:
            type("Optionless", (Union,), {"OPTIONS": ()})
        assert raised.value.fault is TypeFault.UNION_EMPTY

    @pytest.mark.parametrize(
        "options, spelling",
        [
            pytest.param({0: Uint8}, "dict", id="a_selector_to_type_map"),
            pytest.param((option for option in (Uint8,)), "generator", id="a_generator"),
        ],
    )
    def test_options_given_as_anything_but_a_sequence_are_rejected(
        self, options: Any, spelling: str
    ) -> None:
        """A selector indexes the list, so a shape with no positions names no option."""
        with pytest.raises(
            SSZTypeError,
            match=rf"^a union declares its options in selector order, got {spelling}$",
        ) as raised:
            type("Unordered", (Union,), {"OPTIONS": options})
        assert raised.value.fault is TypeFault.UNION_NOT_A_SEQUENCE

    @pytest.mark.parametrize(
        "options, selector",
        [
            pytest.param((Uint8, None), 1, id="second"),
            pytest.param((None, Uint8, None), 2, id="third_alongside_a_legal_first"),
        ],
    )
    def test_none_anywhere_but_first_is_rejected(
        self, options: tuple[type | None, ...], selector: int
    ) -> None:
        """Selector zero is the one an all-zero encoding names, which is what None is for."""
        with pytest.raises(
            SSZTypeError,
            match=rf"^option {selector} is None, which is legal only as the first option$",
        ) as raised:
            type("Misplaced", (Union,), {"OPTIONS": options})
        assert raised.value.fault is TypeFault.UNION_NONE_NOT_FIRST

    def test_a_union_of_none_alone_is_rejected(self) -> None:
        """One option that holds nothing gives a type with exactly one value and no contents."""
        with pytest.raises(
            SSZTypeError,
            match=r"^a union whose first option is None declares at least two options$",
        ) as raised:
            type("Nothing", (Union,), {"OPTIONS": (None,)})
        assert raised.value.fault is TypeFault.UNION_NONE_ALONE

    @pytest.mark.parametrize(
        "option",
        [
            pytest.param(int, id="builtin_type"),
            pytest.param("Square", id="a_name_rather_than_a_type"),
            pytest.param(7, id="a_number"),
        ],
    )
    def test_an_option_that_is_not_an_ssz_type_is_rejected(self, option: object) -> None:
        """An option has to be a type this library can serialize and merkleize."""
        with pytest.raises(SSZTypeError, match=r"^option 1 is not an SSZ type$") as raised:
            type("NotSSZ", (Union,), {"OPTIONS": (Uint8, option)})
        assert raised.value.fault is TypeFault.UNION_OPTION_TYPE

    def test_none_first_alongside_a_second_option_is_legal(self) -> None:
        """The specification's own example, whose selector zero holds nothing."""
        assert Maybe.OPTIONS == (None, Uint64, Uint32)

    def test_two_selectors_may_name_the_same_type(self) -> None:
        """Nothing separates two such values but the selector, and the specification allows it."""
        assert Widths.OPTIONS == (Uint32, Uint32)

    def test_the_option_list_is_stored_as_a_snapshot(self) -> None:
        """A union keeps a copy, so the list the caller still holds is not the one in force."""
        declared = [Uint8, Uint16]

        class Snapshot(Union):
            """Union declared from a list the caller keeps a reference to."""

            OPTIONS = declared

        assert Snapshot.OPTIONS == (Uint8, Uint16)
        declared.append(Uint32)
        assert len(Snapshot.OPTIONS) == 2


class TestConstruction:
    """A value carries the selector of the option it holds, and has to hold that option."""

    def test_a_value_shows_both_halves(self) -> None:
        """A union reads as its two named fields, not as the contents of the option."""
        value = Maybe(selector=Uint8(1), data=Uint64(7))
        assert repr(value) == "Maybe(selector=Uint8(1) data=Uint64(7))"
        assert len(value) == 2

    def test_the_none_option_holds_nothing(self) -> None:
        """Selector zero names the None option, whose payload is the absence of one."""
        value = Maybe(selector=Uint8(0), data=None)
        assert value.data is None

    def test_equal_values_compare_equal(self) -> None:
        """Two constructions of one value are equal, selector and payload alike."""
        assert Maybe(selector=Uint8(2), data=Uint32(3)) == Maybe(selector=Uint8(2), data=Uint32(3))

    def test_a_value_rejects_attribute_assignment(self) -> None:
        """A write reaches the library's own mutation door, which this shape has shut."""
        value = Maybe(selector=Uint8(1), data=Uint64(7))
        with pytest.raises(SSZTypeError, match=r"^Maybe is immutable$") as raised:
            # A frozen field reads as read-only, and the write refused here is the test.
            value.selector = Uint8(2)  # ty: ignore[invalid-assignment]
        assert raised.value.fault is TypeFault.IMMUTABLE

    def test_a_value_rejects_attribute_deletion(self) -> None:
        """Deletion is the one write the mutation door does not see, and frozen still refuses it."""
        value = Maybe(selector=Uint8(1), data=Uint64(7))
        with pytest.raises(ValidationError, match=r"frozen"):
            del value.selector
        assert value.selector == Uint8(1)

    def test_a_selector_past_the_last_option_is_rejected(self) -> None:
        """Three options are declared, so selector 3 indexes past the end of the list."""
        # The refusal is a ValueError, which pydantic collects out of the model validator.
        with pytest.raises(ValidationError, match=r"selector 3 names no option of Maybe"):
            Maybe(selector=Uint8(3), data=Uint64(7))

    def test_data_of_another_option_is_rejected(self) -> None:
        """Selector 1 names the eight-byte integer, so a four-byte one under it is another value."""
        with pytest.raises(SSZTypeError, match=r"^expected Uint64, got Uint32$") as raised:
            Maybe(selector=Uint8(1), data=Uint32(7))
        assert raised.value.fault is TypeFault.WRONG_TYPE

    def test_no_data_at_all_under_a_declared_option_is_rejected(self) -> None:
        """Only selector zero may hold nothing, and only where the first option is None."""
        with pytest.raises(SSZTypeError, match=r"^expected Uint64, got None$") as raised:
            Maybe(selector=Uint8(1), data=None)
        assert raised.value.fault is TypeFault.WRONG_TYPE

    def test_data_under_the_none_option_is_rejected(self) -> None:
        """The None option holds nothing, so a payload under it belongs to no option."""
        with pytest.raises(SSZTypeError, match=r"^expected None, got Uint64$") as raised:
            Maybe(selector=Uint8(0), data=Uint64(7))
        assert raised.value.fault is TypeFault.WRONG_TYPE


class TestDefaultValue:
    """The default of a union is the default of its first option, under selector zero."""

    def test_the_default_is_the_first_option_s_own(self) -> None:
        """Selector zero names the first option, and the payload is that option's default."""
        assert Numbers.default() == Numbers(selector=Uint8(0), data=Uint16List4(data=[]))

    def test_the_default_of_a_union_opening_on_none_holds_nothing(self) -> None:
        """The first option is None, so the default is the one value that holds no payload."""
        assert Maybe.default() == Maybe(selector=Uint8(0), data=None)

    def test_the_default_is_the_zeroed_value(self) -> None:
        """The zeroed check compares against the default, which every union has."""
        assert Maybe.default().is_zero() is True
        assert Maybe(selector=Uint8(1), data=Uint64(0)).is_zero() is False

    def test_a_first_option_with_no_default_leaves_the_union_none(self) -> None:
        """The default recurses into the first option, and one SSZ type refuses to supply one."""
        with pytest.raises(SSZTypeError, match=r"^Undefaultable has no default value$") as raised:
            NoDefaultFirst.default()
        assert raised.value.fault is TypeFault.NO_DEFAULT

    def test_a_selector_without_a_payload_is_not_a_request_for_a_default(self) -> None:
        """Only the total absence of input builds a default; a named field does not."""
        with pytest.raises(ValidationError, match=r"(?s)^1 validation error for Maybe\ndata\n"):
            Maybe(selector=Uint8(1))  # ty: ignore[missing-argument]


class TestSizing:
    """A union is variable-size, whatever its options are."""

    def test_a_union_over_one_fixed_width_is_still_variable_size(self) -> None:
        """Both options here are the same fixed width, and the union is still variable-size."""
        first, second = Widths.OPTIONS
        assert first is not None and second is not None
        assert first.get_byte_length() == second.get_byte_length()
        # A parser cannot know the payload width before it has read the selector.
        assert Widths.is_fixed_size() is False

    def test_a_union_over_variable_options_is_variable_size_too(self) -> None:
        """Nothing changes when an option has no fixed width of its own."""
        assert Numbers.is_fixed_size() is False

    def test_asking_a_union_for_a_byte_length_raises(self) -> None:
        """Variable-size types have no fixed byte length, and a union is one of them."""
        with pytest.raises(SSZTypeError) as raised:
            Maybe.get_byte_length()
        assert raised.value.fault is TypeFault.NOT_FIXED_SIZE
        assert raised.value.args[0] == "Maybe is a variable-size union, and has no one byte length"


class TestSerialization:
    """The selector leads, and the option's own encoding follows."""

    def test_the_none_option_encodes_to_a_single_zero_byte(self) -> None:
        """The specification writes this encoding out on its own, rather than deriving it."""
        encoded = Maybe(selector=Uint8(0), data=None).encode_bytes()
        assert encoded == b"\x00"
        assert len(encoded) == SELECTOR_WIDTH

    def test_a_declared_option_follows_the_selector_directly(self) -> None:
        """No offset separates the selector from the payload: the union is the whole scope."""
        # byte 0    : selector = 01
        # bytes 1..8: the eight-byte integer, little-endian
        value = Maybe(selector=Uint8(1), data=Uint64(7))
        assert value.encode_bytes().hex() == "010700000000000000"

    def test_two_options_of_one_width_differ_only_in_the_selector(self) -> None:
        """The payload bytes are identical, so the selector byte is all there is to read."""
        first = Widths(selector=Uint8(0), data=Uint32(9)).encode_bytes()
        second = Widths(selector=Uint8(1), data=Uint32(9)).encode_bytes()
        assert first.hex() == "0009000000"
        assert second.hex() == "0109000000"
        assert first[SELECTOR_WIDTH:] == second[SELECTOR_WIDTH:]

    def test_an_empty_variable_size_option_encodes_to_the_selector_alone(self) -> None:
        """A zero-byte payload leaves the selector as the entire encoding."""
        assert Numbers(selector=Uint8(0), data=Uint16List4(data=[])).encode_bytes().hex() == "00"

    def test_serialize_returns_the_byte_count_it_wrote(self) -> None:
        """The stream writer reports one byte for the selector plus the payload's own count."""
        stream = io.BytesIO()
        written = Maybe(selector=Uint8(2), data=Uint32(1)).serialize(stream)
        assert written == SELECTOR_WIDTH + Uint32.get_byte_length()
        assert written == len(stream.getvalue())

    def test_the_none_option_writes_nothing_past_its_selector(self) -> None:
        """The payload contributes no bytes, so the count is the selector's alone."""
        stream = io.BytesIO()
        assert Maybe(selector=Uint8(0), data=None).serialize(stream) == SELECTOR_WIDTH


class TestDeserialization:
    """The selector leads, so the option is known before any of its bytes are read."""

    @pytest.mark.parametrize(
        "value",
        [
            pytest.param(Maybe(selector=Uint8(0), data=None), id="none_option"),
            pytest.param(Maybe(selector=Uint8(1), data=Uint64(7)), id="first_declared_option"),
            pytest.param(Maybe(selector=Uint8(2), data=Uint32(7)), id="second_declared_option"),
            pytest.param(
                Numbers(selector=Uint8(0), data=Uint16List4(data=[Uint16(1), Uint16(2)])),
                id="variable_size_option",
            ),
            pytest.param(
                Numbers(selector=Uint8(0), data=Uint16List4(data=[])),
                id="empty_variable_size_option",
            ),
            pytest.param(
                Numbers(selector=Uint8(1), data=Square(side=Uint16(0x1234), color=Uint8(0x42))),
                id="composite_option",
            ),
        ],
    )
    def test_round_trip(self, value: Union) -> None:
        """Encoding then decoding returns the very same value, selector and payload alike."""
        assert type(value).decode_bytes(value.encode_bytes()) == value

    def test_the_selector_picks_the_option_before_the_payload_is_read(self) -> None:
        """The same four payload bytes decode under either selector of a two-option union."""
        assert Widths.decode_bytes(bytes.fromhex("0009000000")).selector == Uint8(0)
        assert Widths.decode_bytes(bytes.fromhex("0109000000")).selector == Uint8(1)

    def test_an_empty_budget_holds_no_selector(self) -> None:
        """A union always carries a selector, so a zero-byte input is never one."""
        with pytest.raises(SSZValueError) as raised:
            Maybe.decode_bytes(b"")
        assert raised.value.fault is ValueFault.NO_SELECTOR
        assert raised.value.args[0] == "a budget of 0 holds no selector"

    def test_a_short_budget_is_rejected_by_deserialize_directly(self) -> None:
        """The stream decoder checks the budget before it touches the stream."""
        with pytest.raises(SSZValueError, match=r"^a budget of 0 holds no selector$"):
            Maybe.deserialize(io.BytesIO(b""), 0)

    @pytest.mark.parametrize(
        "selector_byte, selector_value",
        [
            pytest.param("03", 3, id="one_past_the_last_option"),
            pytest.param("80", 128, id="the_reserved_high_bit"),
            pytest.param("ff", Uint8.MAX_VALUE, id="the_top_of_the_byte"),
        ],
    )
    def test_a_selector_naming_no_option_is_rejected(
        self, selector_byte: str, selector_value: int
    ) -> None:
        """A wire selector past the declared list is rejected before the payload is read."""
        with pytest.raises(SSZValueError) as raised:
            Maybe.decode_bytes(bytes.fromhex(selector_byte + "07"))
        assert raised.value.fault is ValueFault.UNKNOWN_SELECTOR
        assert raised.value.args[0] == f"selector {selector_value} names no option of Maybe"

    def test_the_none_option_refuses_a_budget_beyond_its_selector(self) -> None:
        """Nothing follows the byte, so a wider scope carries bytes belonging to no option."""
        with pytest.raises(SSZValueError) as raised:
            Maybe.deserialize(io.BytesIO(bytes.fromhex("0000")), 2)
        assert raised.value.fault is ValueFault.SCOPE
        assert raised.value.args[0] == "Maybe spans 1 bytes, and the budget is 2"

    def test_trailing_bytes_after_a_payload_are_rejected(self) -> None:
        """One canonical encoding per value, so a spare byte after the payload is noise."""
        # The rest of the budget belongs to the option, so the option refuses a wide one.
        with pytest.raises(SSZValueError) as raised:
            Maybe.decode_bytes(bytes.fromhex("02" + "09000000" + "00"))
        assert raised.value.fault is ValueFault.SCOPE
        assert str(raised.value) == "[2]: Uint32 spans 4 bytes, and the budget is 5"

    def test_a_truncated_payload_surfaces_the_option_s_own_error(self) -> None:
        """The rest of the budget belongs to the option, which reports its own shortfall."""
        with pytest.raises(SSZValueError) as raised:
            Maybe.decode_bytes(bytes.fromhex("0107"))
        assert raised.value.fault is ValueFault.SCOPE
        # The selector the payload was read under is a path step, in front of the sentence.
        assert str(raised.value) == "[1]: Uint64 spans 8 bytes, and the budget is 1"

    def test_an_over_capacity_payload_is_rejected(self) -> None:
        """The option's own capacity rule still applies inside the union's budget."""
        with pytest.raises(SSZValueError) as raised:
            Numbers.decode_bytes(bytes.fromhex("00") + b"\x00" * 10)
        assert raised.value.fault is ValueFault.LIMIT
        assert str(raised.value) == "[0]: Uint16List4 holds at most 4 elements, got 5"


class TestNesting:
    """A union inside a container, inside a progressive list, and inside itself."""

    def test_a_container_reaches_a_union_through_an_offset(self) -> None:
        """The union is variable-size, so the container writes an offset for it."""
        # byte  0    : tag = ff        (fixed-size field, inline)
        # bytes 1..4 : off_body = 5    (the union body starts at byte 5)
        # byte  5    : body            (selector 00, the None option's whole encoding)
        value = Holder(tag=Uint8(0xFF), body=Maybe(selector=Uint8(0), data=None))
        assert Holder.is_fixed_size() is False
        assert value.encode_bytes().hex() == "ff0500000000"
        assert Holder.decode_bytes(value.encode_bytes()) == value

    def test_a_container_holding_a_declared_option(self) -> None:
        """The same layout with a payload behind the selector, which the offset covers."""
        value = Holder(tag=Uint8(0xFF), body=Maybe(selector=Uint8(2), data=Uint32(1)))
        assert value.encode_bytes().hex() == "ff050000000201000000"
        assert Holder.decode_bytes(value.encode_bytes()) == value

    def test_a_union_holds_a_union(self) -> None:
        """Two selectors lead, one per level, before any payload byte."""
        value = Nested(selector=Uint8(1), data=Maybe(selector=Uint8(2), data=Uint32(1)))
        assert value.encode_bytes().hex() == "010201000000"
        assert Nested.decode_bytes(value.encode_bytes()) == value

    def test_a_progressive_list_of_unions_needs_an_offset_table(self) -> None:
        """Unions are variable-size elements, so each body is reached through an offset."""
        # bytes 0..3 : off_0 = 8    (first body starts at byte 8)
        # bytes 4..7 : off_1 = 9    (second body starts at byte 9)
        # byte  8    : body_0       (selector 00, holding nothing)
        # bytes 9..13: body_1       (selector 01, then the eight-byte integer)
        value = MaybeList(
            data=[
                Maybe(selector=Uint8(0), data=None),
                Maybe(selector=Uint8(1), data=Uint64(7)),
            ]
        )
        assert value.encode_bytes().hex() == "080000000900000000" + "010700000000000000"
        assert MaybeList.decode_bytes(value.encode_bytes()) == value


class TestMerkleization:
    """A union roots to the option's own root with the selector mixed in beside it."""

    def test_a_declared_option_mixes_its_selector_into_the_option_s_root(self) -> None:
        """The option is the whole tree below, so its root is the left child of the mixin."""
        value = Maybe(selector=Uint8(1), data=Uint64(7))
        assert value.hash_tree_root() == mix_in_selector(hash_tree_root(Uint64(7)), 1)

    def test_the_none_option_mixes_its_selector_into_the_zero_root(self) -> None:
        """Nothing is held, so the left child is the all-zero chunk the specification names."""
        value = Maybe(selector=Uint8(0), data=None)
        assert value.hash_tree_root() == mix_in_selector(ZERO_ROOT, 0)

    def test_the_selector_separates_two_otherwise_identical_values(self) -> None:
        """Both options are the same type holding the same number, and the roots still differ."""
        first = Widths(selector=Uint8(0), data=Uint32(9))
        second = Widths(selector=Uint8(1), data=Uint32(9))
        assert first.encode_bytes()[SELECTOR_WIDTH:] == second.encode_bytes()[SELECTOR_WIDTH:]
        assert first.hash_tree_root() != second.hash_tree_root()

    @pytest.mark.parametrize(
        "value",
        [
            pytest.param(Maybe(selector=Uint8(0), data=None), id="none_option"),
            pytest.param(Maybe(selector=Uint8(1), data=Uint64(7)), id="declared_option"),
        ],
    )
    def test_a_root_asked_for_twice_is_the_same_root(self, value: Union) -> None:
        """The second answer comes from the memo, which has to witness the option it holds."""
        assert value.hash_tree_root() == value.hash_tree_root()


class TestCompatibleMerkleization:
    """The compatibility relation is a closed list, and the tagged union is not on it."""

    def test_a_union_is_compatible_with_itself(self) -> None:
        """Every type is, which is the relation's first rule."""
        assert is_compatible(Maybe, Maybe) is True

    def test_two_unions_declaring_the_same_options_are_incompatible(self) -> None:
        """The relation names no rule for the tagged union, so it falls to the closing one."""

        class Twin(Union):
            """A second union declaring exactly the options of the first."""

            OPTIONS = (None, Uint64, Uint32)

        assert Twin.OPTIONS == Maybe.OPTIONS
        assert is_compatible(Maybe, Twin) is False

    def test_a_union_and_a_compatible_union_are_incompatible(self) -> None:
        """The two union kinds merkleize alike and are still two different declarations."""
        assert is_compatible(Maybe, Undefaultable) is False

    def test_one_union_may_stand_under_several_selectors_of_a_compatible_union(self) -> None:
        """Identity is enough to satisfy the pairwise check a compatible union runs."""

        class Repeated(CompatibleUnion):
            """Compatible union naming one tagged union under two selectors."""

            OPTIONS = {1: Maybe, 2: Maybe}

        assert Repeated.OPTIONS == {1: Maybe, 2: Maybe}

    def test_two_different_unions_cannot_share_a_compatible_union(self) -> None:
        """Two declarations are incompatible however alike they read, so the union is illegal."""
        with pytest.raises(SSZTypeError, match=r"^options 1 and 2 merkleize differently$"):
            type("Clashing", (CompatibleUnion,), {"OPTIONS": {1: Maybe, 2: Nested}})


class Bytes4(ByteVector):
    """Four opaque bytes, spelled as a hexadecimal string."""

    LENGTH = 4


class Spellings(Union):
    """Union over options that spell themselves as hexadecimal, as a boolean, and as nothing."""

    OPTIONS = (None, Bytes4, Boolean)


class TestJsonMapping:
    """The mapping writes a union as an object of a selector and the data behind it."""

    def test_the_selector_is_a_string_and_the_payload_its_own_spelling(self) -> None:
        """Each half is written the way its own type spells itself."""
        value = Spellings(selector=Uint8(1), data=Bytes4(bytes([0xFF, 0x00, 0x41, 0x42])))
        assert value.model_dump(mode="json") == {"selector": "1", "data": "0xff004142"}

    def test_a_boolean_option_is_a_json_boolean(self) -> None:
        """The field is annotated with the base every option shares, which spells nothing."""
        value = Spellings(selector=Uint8(2), data=Boolean(True))
        assert value.model_dump(mode="json") == {"selector": "2", "data": True}

    def test_the_none_option_writes_a_null_payload(self) -> None:
        """The option holds nothing, and the mapping has one spelling for that."""
        value = Spellings(selector=Uint8(0), data=None)
        assert value.model_dump(mode="json") == {"selector": "0", "data": None}

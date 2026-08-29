"""Tests for the two catalogues, the sentence each renders, and the path one collects."""

from string import Formatter

import pytest

from ssz import Container, List, SSZValueError, TypeFault, Uint8, Uint16, Uint64, ValueFault
from ssz.exceptions import SSZTypeError, _Fields
from tests.test_container import ListFieldProgressive, Uint16List4


class Shapes(List[ListFieldProgressive]):
    """Four of the EIP-7495 shape, so an element sits behind both a table and a count."""

    LIMIT = 4


class Board(Container):
    """A leaf field ahead of the sequence, so the sequence is reached through an offset."""

    tag: Uint8
    shapes: Shapes


class TestTheRenderedSentence:
    """What a fault turns into once the raise site's numbers are in it."""

    def test_a_field_the_raise_site_left_out_is_reported_in_its_place(self) -> None:
        """A missing number never costs the sentence, since that would hide the refusal."""
        # RANGE asks for three fields, and only two are passed.
        error = SSZValueError(ValueFault.RANGE, value=300, type="Uint8")
        assert error.message == "300 is out of range for Uint8 [0, <no max>]"

    def test_the_gap_marker_names_the_field_that_was_missing(self) -> None:
        """The mapping answers for any key, so no template can raise while rendering."""
        assert _Fields()["limit"] == "<no limit>"

    def test_the_message_is_the_first_argument(self) -> None:
        """The sentence alone is what an unadorned traceback prints."""
        error = SSZTypeError(TypeFault.IMMUTABLE, type="Uint8")
        assert error.args[0] == "Uint8 is immutable"
        assert error.message == error.args[0]


class TestThePathInFront:
    """How a refusal prints before and after it has travelled out through a value."""

    def test_a_refusal_with_no_path_prints_the_sentence_alone(self) -> None:
        """Nothing collected a step, so there is no path to put in front of it."""
        error = SSZValueError(ValueFault.EMPTY_ENCODING)
        assert error.loc == ()
        assert str(error) == "an empty input encodes no value"

    def test_each_step_is_recorded_outermost_first(self) -> None:
        """A decoder records its own step on the way out, so the path builds in reverse."""
        error = SSZValueError(ValueFault.TRUNCATED, type="Uint64", expected=8, actual=6)
        error.at("head")
        error.at(1)
        error.at("shapes")
        assert error.loc == ("shapes", 1, "head")
        # A name is reached with a dot and a position with brackets, and the leading dot goes.
        assert str(error) == "shapes[1].head: Uint64 needs 8 bytes, the input holds 6"

    def test_a_path_opening_on_a_position_keeps_its_brackets(self) -> None:
        """Only a leading name loses its separator, since a bracket is not one."""
        error = SSZValueError(ValueFault.NO_DELIMITER)
        error.at(2)
        assert str(error) == "[2]: the encoding sets no delimiter bit"


@pytest.mark.parametrize("fault", [*TypeFault, *ValueFault], ids=lambda fault: fault.name)
def test_every_template_asks_for_each_field_once_and_by_name(
    fault: TypeFault | ValueFault,
) -> None:
    """A template is filled from a mapping, so a field it names twice is a field asked twice."""
    named = [field for _, field, _, _ in Formatter().parse(fault.value) if field]
    assert all(name.isidentifier() for name in named)
    assert len(set(named)) == len(named)


def test_a_refusal_deep_inside_a_value_arrives_naming_where_it_happened() -> None:
    """Four levels down, the path is what tells one Uint64 of the value from the other."""
    # Fixture state: two shapes, each a Uint64 head and a list body.
    #
    #     ff 05000000 08000000 16000000 07000000 00000000 0c000000 0100
    #                                   ^ shapes[0] starts here
    #        09000000 00000000 0c000000 0200
    #        ^ shapes[1] starts here, at byte 25
    value = Board(
        tag=Uint8(0xFF),
        shapes=Shapes(
            data=[
                ListFieldProgressive(head=Uint64(7), body=Uint16List4(data=[Uint16(1)])),
                ListFieldProgressive(head=Uint64(9), body=Uint16List4(data=[Uint16(2)])),
            ]
        ),
    )
    encoded = value.encode_bytes()

    # Mutation: two bytes cut from the end, which is the second head's final two.
    with pytest.raises(SSZValueError) as exception_info:
        Board.decode_bytes(encoded[:33])

    # One step per level travelled out through: the field, the position, the field again.
    error = exception_info.value
    assert error.loc == ("shapes", 1, "head")
    assert error.fault is ValueFault.TRUNCATED
    assert error.fields == {"type": "Uint64", "expected": 8, "actual": 6}
    assert str(error) == "shapes[1].head: Uint64 needs 8 bytes, the input holds 6"

"""What the generalized-index format emits, and what it refuses to call a passing test."""

import pytest

from ssz import (
    ACTIVE_FIELDS_KEY,
    LENGTH_KEY,
    SELECTOR_KEY,
    CompatibleUnion,
    Container,
    List,
    ProgressiveContainer,
    ProgressiveList,
    SSZType,
    Uint8,
    Uint64,
)
from ssz_testing import (
    ELEMENT_COUNT_STEP,
    FIELD_LAYOUT_STEP,
    TYPE_SELECTOR_STEP,
    GindexPathStep,
    GindexTest,
    TypeFault,
    ValueFault,
)
from ssz_testing.gindex_fixtures import resolver_path


class Pair(Container):
    """A struct of two leaves, the flattest shape a path can step into."""

    a: Uint64
    b: Uint64


class Numbers(List[Uint64]):
    """A bounded list, which mixes in an element count."""

    LIMIT = 8


class Spine(ProgressiveContainer):
    """A progressive container, whose shape reports no bounded leaf count."""

    ACTIVE_FIELDS = (1, 1)

    head: Uint64
    tail: Uint64


class Trail(ProgressiveList[Uint64]):
    """A progressive list, laid out on a spine rather than in a bounded tree."""


class Square(ProgressiveContainer):
    """One union option, sharing the position of its second field."""

    ACTIVE_FIELDS = (1, 0, 1)

    side: Uint8
    color: Uint8


class Circle(ProgressiveContainer):
    """The compatible option, differing only in its private field."""

    ACTIVE_FIELDS = (0, 1, 1)

    radius: Uint8
    color: Uint8


class Shape(CompatibleUnion):
    """A union of the two, which mixes in a type selector."""

    OPTIONS = {1: Square, 2: Circle}


def test_a_reserved_word_resolves_to_the_step_the_resolver_takes() -> None:
    """The three spelled words stand for the three reserved steps, and nothing else moves."""
    assert resolver_path((ELEMENT_COUNT_STEP,)) == (LENGTH_KEY,)
    assert resolver_path((FIELD_LAYOUT_STEP,)) == (ACTIVE_FIELDS_KEY,)
    assert resolver_path((TYPE_SELECTOR_STEP,)) == (SELECTOR_KEY,)
    assert resolver_path(("a", 3)) == ("a", 3)


def test_a_resolved_path_emits_the_index_and_the_arithmetic_behind_it() -> None:
    """A vector carries the index, its depth, and the two numbers that produced it."""
    fixture = GindexTest(type_name="Pair", ssz_type=Pair, path=("b",), gindex=3).generate()

    assert fixture.json_dict == {
        "typeName": "Pair",
        "path": ["b"],
        "gindex": "3",
        "depth": 1,
        "valid": True,
        "chunkCount": 2,
        "treeWidth": 2,
        "typeDescriptor": {
            "kind": "Container",
            "fields": [
                {"name": "a", "type": {"kind": "Uint64", "bits": 64}},
                {"name": "b", "type": {"kind": "Uint64", "bits": 64}},
            ],
        },
    }
    assert fixture.declared_types() == {"Pair": fixture.type_descriptor}
    assert fixture.case_type_name() == "Pair"
    assert fixture.case_kind() == "container"


def test_a_reserved_word_is_emitted_as_an_object_no_field_name_can_be() -> None:
    """A field is a string and an element an integer, so a word takes a shape of its own."""
    fixture = GindexTest(
        type_name="Numbers", ssz_type=Numbers, path=(ELEMENT_COUNT_STEP,), gindex=3
    ).generate()

    assert fixture.json_dict["path"] == [{"mixin": "elementCount"}]
    assert fixture.json_dict["gindex"] == "3"


def test_an_empty_path_names_the_root() -> None:
    """The root is index 1, and it sits no levels below itself."""
    fixture = GindexTest(type_name="Pair", ssz_type=Pair, gindex=1).generate()

    assert fixture.gindex == "1"
    assert fixture.depth == 0


def test_a_progressive_shape_reports_no_leaf_count() -> None:
    """A spine grows with its data, so neither number it would be padded to exists."""
    fixture = GindexTest(type_name="Trail", ssz_type=Trail, path=(4,), gindex=40).generate()

    assert fixture.chunk_count is None
    assert fixture.tree_width is None
    assert "chunkCount" not in fixture.json_dict
    assert "treeWidth" not in fixture.json_dict
    assert fixture.case_kind() == "progressive_list"


@pytest.mark.parametrize(
    "type_name, ssz_type, path, refusal",
    [
        pytest.param(
            "Numbers", Numbers, (ELEMENT_COUNT_STEP, 0), TypeFault.NO_PARTS_MIXIN, id="mixin"
        ),
        pytest.param(
            "Spine", Spine, (FIELD_LAYOUT_STEP, "head"), TypeFault.NO_PARTS_MIXIN, id="layout"
        ),
        pytest.param(
            "Shape", Shape, (TYPE_SELECTOR_STEP, "color"), TypeFault.NO_PARTS_MIXIN, id="selector"
        ),
        pytest.param("Pair", Pair, ("a", 0), TypeFault.NO_PARTS, id="packed"),
        pytest.param("Pair", Pair, ("nope",), ValueFault.NO_SUCH_FIELD, id="field"),
        pytest.param("Numbers", Numbers, (8,), ValueFault.NO_SUCH_POSITION, id="position"),
        pytest.param("Shape", Shape, (9,), ValueFault.NO_SUCH_OPTION, id="option"),
    ],
)
def test_a_refused_path_emits_the_fault_from_either_catalogue(
    type_name: str,
    ssz_type: type[SSZType],
    path: tuple[GindexPathStep, ...],
    refusal: TypeFault | ValueFault,
) -> None:
    """A path is refused by the type as often as by a step, and both names are emitted."""
    fixture = GindexTest(
        type_name=type_name, ssz_type=ssz_type, path=path, refusal=refusal
    ).generate()

    assert fixture.valid is False
    assert fixture.json_dict["rejectionReason"] == refusal.name
    assert "gindex" not in fixture.json_dict
    assert "depth" not in fixture.json_dict


def test_a_resolved_path_states_the_index_it_names() -> None:
    """A vector that only records what the resolver said would pin nothing."""
    with pytest.raises(ValueError, match="must state the generalized index"):
        GindexTest(type_name="Pair", ssz_type=Pair, path=("b",)).generate()


def test_an_index_the_resolver_disagrees_with_fails_the_fill() -> None:
    """The authored number is the contract, and the resolver has to reproduce it."""
    with pytest.raises(AssertionError, match="resolves .* to generalized index 3"):
        GindexTest(type_name="Pair", ssz_type=Pair, path=("b",), gindex=2).generate()


def test_a_refusal_that_never_fired_fails_the_fill() -> None:
    """A path the type accepts is no refusal vector, whatever the author expected."""
    with pytest.raises(AssertionError, match="to refuse .* but the path resolved"):
        GindexTest(
            type_name="Pair", ssz_type=Pair, path=("b",), refusal=ValueFault.NO_SUCH_FIELD
        ).generate()


def test_a_refusal_for_another_reason_fails_the_fill() -> None:
    """A vector names which refusal has to fire, not merely that one did."""
    with pytest.raises(AssertionError, match="Expected fault: NO_SUCH_POSITION"):
        GindexTest(
            type_name="Pair", ssz_type=Pair, path=("nope",), refusal=ValueFault.NO_SUCH_POSITION
        ).generate()

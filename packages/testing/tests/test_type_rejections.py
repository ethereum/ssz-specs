"""What the illegal-declaration format emits, and what it refuses to call a passing test."""

import pytest

from ssz import Uint8
from ssz_testing import FIXTURE_FORMATS, TypeDescriptor, TypeFault, describe_type
from ssz_testing.type_builder import build_declaration
from ssz_testing.type_rejections import TypeRejectionTest

UINT8 = describe_type(Uint8)

ZERO_LENGTH_VECTOR = TypeRejectionTest(
    type_name="IllegalZeroLengthVector",
    type_descriptor=TypeDescriptor(kind="Vector", length=0, element_type=UINT8),
    rejection_reason=TypeFault.VECTOR_EMPTY,
    exact_message=(
        "IllegalZeroLengthVector declares a length of zero, and a fixed count is at least one"
    ),
)


def test_the_format_is_registered_as_fillable() -> None:
    """A format nothing registers fills nothing, so the registry is what makes it exist."""
    assert TypeRejectionTest in FIXTURE_FORMATS


def test_a_refused_declaration_is_emitted_with_the_fault_that_fired() -> None:
    """The vector carries the declaration, the fault's stable name, and no claim of validity."""
    emitted = ZERO_LENGTH_VECTOR.generate()

    assert emitted.case_type_name() == "IllegalZeroLengthVector"
    assert emitted.case_kind() == "vector"
    assert emitted.declared_types() == {
        "IllegalZeroLengthVector": ZERO_LENGTH_VECTOR.type_descriptor
    }
    assert emitted.json_dict == {
        "typeName": "IllegalZeroLengthVector",
        "typeDescriptor": {
            "kind": "Vector",
            "length": 0,
            "elementType": {"kind": "Uint8", "bits": 8},
        },
        "rejectionReason": "VECTOR_EMPTY",
        "valid": False,
    }


def test_a_multi_word_kind_names_a_snake_cased_directory() -> None:
    """A kind is CamelCase and a directory is not, so the vector files under the spelled-out one."""
    union = TypeRejectionTest(
        type_name="IllegalOptionlessUnion",
        type_descriptor=TypeDescriptor(kind="CompatibleUnion", options=()),
        rejection_reason=TypeFault.UNION_EMPTY,
        exact_message="a union declares at least one option",
    )

    assert union.generate().case_kind() == "compatible_union"


def test_a_declaration_that_stands_is_not_a_vector() -> None:
    """A rule nothing enforces is worse than no vector, so a legal declaration fails the fill."""
    legal = ZERO_LENGTH_VECTOR.model_copy(
        update={"type_descriptor": TypeDescriptor(kind="Vector", length=4, element_type=UINT8)}
    )

    with pytest.raises(AssertionError, match="to be refused, but it stands"):
        legal.generate()


def test_a_declaration_refused_for_another_reason_is_not_a_vector() -> None:
    """The fault the vector emits has to be the one that fired, not merely some refusal."""
    misnamed = ZERO_LENGTH_VECTOR.model_copy(update={"rejection_reason": TypeFault.UNION_EMPTY})

    with pytest.raises(AssertionError, match="Actual fault: VECTOR_EMPTY"):
        misnamed.generate()


def test_a_refusal_saying_something_else_is_not_a_vector() -> None:
    """The message pins the parameters the fault carried, which the fault's name alone does not."""
    misquoted = ZERO_LENGTH_VECTOR.model_copy(update={"exact_message": "something else"})

    with pytest.raises(AssertionError, match="wrong message"):
        misquoted.generate()


def test_the_outermost_declaration_carries_the_authored_name() -> None:
    """A refusal quotes the type it refused, so the author's name has to reach the declaration."""
    rebuilt = build_declaration(
        {"kind": "Vector", "length": 2, "elementType": {"kind": "Uint8", "bits": 8}}, "Pair"
    )

    assert rebuilt.__name__ == "Pair"
    # Two positions of one byte, so the nested descriptor was rebuilt as a byte-wide integer.
    assert rebuilt.get_byte_length() == 2

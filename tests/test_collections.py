"""Tests for the Vector and List types."""

import io
from typing import Any, cast

import pytest
from hypothesis import given, strategies as st
from pydantic import BaseModel, ValidationError

from ssz import Uint8, Uint16, Uint32
from ssz.boolean import Boolean
from ssz.byte_arrays import ByteVector
from ssz.collections import List, ProgressiveList, Vector
from ssz.container import Container
from ssz.exceptions import (
    SSZDefaultError,
    SSZSerializationError,
    SSZTypeError,
    SSZTypeMismatch,
    SSZValueError,
)
from ssz.union import CompatibleUnion


class Bytes32(ByteVector):
    """A 32-byte array, as applications typically define for roots and hashes."""

    LENGTH = 32


ValueOrValidationError = (SSZValueError, ValidationError)
TypeOrValidationError = (SSZTypeError, ValidationError)


class Uint16List4(List[Uint16]):
    """A list with up to 4 Uint16 values."""

    LIMIT = 4


class FixedContainer(Container):
    """A simple fixed-size container for testing composite types in collections."""

    a: Uint8
    b: Uint16


class VariableContainer(Container):
    """A variable-size container for testing composite types in collections."""

    a: Uint8
    b: Uint16List4


class Uint16Vector2(Vector[Uint16]):
    """A vector of exactly 2 Uint16 values."""

    LENGTH = 2


class Uint8Vector4(Vector[Uint8]):
    """A vector of exactly 4 Uint8 values."""

    LENGTH = 4


class Uint8Vector48(Vector[Uint8]):
    """A vector of exactly 48 Uint8 values."""

    LENGTH = 48


class Uint8Vector96(Vector[Uint8]):
    """A vector of exactly 96 Uint8 values."""

    LENGTH = 96


class FixedContainerVector2(Vector[FixedContainer]):
    """A vector of exactly 2 FixedContainer values."""

    LENGTH = 2


class VariableContainerVector2(Vector[VariableContainer]):
    """A vector of exactly 2 VariableContainer values."""

    LENGTH = 2


class Uint16List32(List[Uint16]):
    """A list with up to 32 Uint16 values."""

    LIMIT = 32


class Uint8List10(List[Uint8]):
    """A list with up to 10 Uint8 values."""

    LIMIT = 10


class Uint32List128(List[Uint32]):
    """A list with up to 128 Uint32 values."""

    LIMIT = 128


class Bytes32List32(List[Bytes32]):
    """A list with up to 32 Bytes32 values."""

    LIMIT = 32


class Bytes32List128(List[Bytes32]):
    """A list with up to 128 Bytes32 values."""

    LIMIT = 128


class VariableContainerList2(List[VariableContainer]):
    """A list with up to 2 VariableContainer values."""

    LIMIT = 2


class FixedContainerList2(List[FixedContainer]):
    """A list with up to 2 FixedContainer values."""

    LIMIT = 2


class Uint8Vector32(Vector[Uint8]):
    """A vector of exactly 32 Uint8 values."""

    LENGTH = 32


class Uint16Vector32(Vector[Uint16]):
    """A vector of exactly 32 Uint16 values."""

    LENGTH = 32


class Uint8Vector64(Vector[Uint8]):
    """A vector of exactly 64 Uint8 values."""

    LENGTH = 64


class Uint8Vector2(Vector[Uint8]):
    """A vector of exactly 2 Uint8 values."""

    LENGTH = 2


class Uint8List32(List[Uint8]):
    """A list with up to 32 Uint8 values."""

    LIMIT = 32


class Uint8List64(List[Uint8]):
    """A list with up to 64 Uint8 values."""

    LIMIT = 64


class Uint8List4(List[Uint8]):
    """A list with up to 4 Uint8 values."""

    LIMIT = 4


class BooleanList4(List[Boolean]):
    """A list with up to 4 Boolean values."""

    LIMIT = 4


class Uint8ProgressiveList(ProgressiveList[Uint8]):
    """A progressive list of Uint8 values with no capacity."""


class Uint16ProgressiveList(ProgressiveList[Uint16]):
    """A progressive list of Uint16 values with no capacity."""


class Bytes32ProgressiveList(ProgressiveList[Bytes32]):
    """A progressive list of fixed-size 32-byte elements."""


class FixedContainerProgressiveList(ProgressiveList[FixedContainer]):
    """A progressive list of fixed-size containers."""


class VariableContainerProgressiveList(ProgressiveList[VariableContainer]):
    """A progressive list of variable-size containers."""


class NestedProgressiveList(ProgressiveList[Uint16ProgressiveList]):
    """A progressive list whose elements are themselves progressive lists."""


class FixedContainerUnion(CompatibleUnion):
    """Union over a single option, a shape the spec gives no default value."""

    OPTIONS = {1: FixedContainer}


class FixedContainerUnionVector2(Vector[FixedContainerUnion]):
    """Vector of two unions, so a default would need an element default there is none of."""

    LENGTH = 2


class FixedContainerUnionList2(List[FixedContainerUnion]):
    """List of unions, whose default is the empty value whatever the element type is."""

    LIMIT = 2


class Uint8Vector2Model(BaseModel):
    """Model for testing Pydantic validation of Uint8Vector2."""

    value: Uint8Vector2


class Uint8List4Model(BaseModel):
    """Model for testing Pydantic validation of Uint8List4."""

    value: Uint8List4


class Uint8ProgressiveListModel(BaseModel):
    """Model for testing Pydantic validation of Uint8ProgressiveList."""

    value: Uint8ProgressiveList


class TestVectorValidator:
    """Tests for the Vector field validator and its rejection paths."""

    def test_missing_element_type_and_length_rejected(self) -> None:
        """A subclass without ELEMENT_TYPE or LENGTH cannot validate any input."""

        class MissingBoth(Vector):
            pass

        with pytest.raises(TypeOrValidationError) as exception_info:
            MissingBoth(data=cast(Any, [1]))
        assert str(exception_info.value) == "MissingBoth must define ELEMENT_TYPE and LENGTH"

    def test_missing_length_rejected(self) -> None:
        """A subclass with ELEMENT_TYPE but no LENGTH cannot validate."""

        class MissingLengthVector(Vector[Uint8]):
            pass

        with pytest.raises(TypeOrValidationError) as exception_info:
            MissingLengthVector(data=cast(Any, [1]))
        assert (
            str(exception_info.value) == "MissingLengthVector must define ELEMENT_TYPE and LENGTH"
        )

    @pytest.mark.parametrize(
        "bad_input, type_name",
        [
            ("ab", "str"),
            (b"ab", "bytes"),
            (bytearray(b"ab"), "bytearray"),
        ],
    )
    def test_byte_like_inputs_rejected(self, bad_input: Any, type_name: str) -> None:
        """Strings, bytes, and bytearrays never iterate as element collections."""
        with pytest.raises(TypeOrValidationError) as exception_info:
            Uint8Vector2(data=bad_input)
        assert str(exception_info.value) == f"Expected iterable of Uint8, got {type_name}"

    def test_non_iterable_scalar_rejected(self) -> None:
        """Scalar inputs without an iterator interface raise an iterable error."""
        with pytest.raises(TypeOrValidationError) as exception_info:
            Uint8Vector2(data=cast(Any, 42))
        assert str(exception_info.value) == "Expected iterable, got int"

    def test_generator_input_coerced(self) -> None:
        """A generator is materialized and each value is coerced to ELEMENT_TYPE."""
        instance = Uint8Vector4(data=cast(Any, (number for number in range(1, 5))))

        assert tuple(instance) == (Uint8(1), Uint8(2), Uint8(3), Uint8(4))

    def test_already_typed_elements_pass_through(self) -> None:
        """Inputs already typed as ELEMENT_TYPE skip the coercion constructor."""
        original = [Uint8(1), Uint8(2), Uint8(3), Uint8(4)]
        instance = Uint8Vector4(data=original)

        assert tuple(instance) == tuple(original)

    def test_raw_values_coerced_through_element_type(self) -> None:
        """Raw Python ints are coerced through the declared element type."""
        instance = Uint8Vector4(data=cast(Any, [1, 2, 3, 4]))

        assert tuple(instance) == (Uint8(1), Uint8(2), Uint8(3), Uint8(4))

    def test_unrelated_element_class_rejected(self) -> None:
        """A value whose class is not the element class or an ancestor is rejected."""
        with pytest.raises(TypeOrValidationError) as exception_info:
            Uint8Vector4(data=cast(Any, [1, "bad", 3, 4]))
        assert str(exception_info.value) == "Expected Uint8, got str"

    def test_too_few_elements_rejected(self) -> None:
        """A vector requires exactly LENGTH elements and rejects shorter inputs."""
        with pytest.raises(ValueOrValidationError) as exception_info:
            Uint8Vector4(data=cast(Any, [1, 2, 3]))
        assert str(exception_info.value) == "Uint8Vector4 requires exactly 4 elements, got 3"

    def test_too_many_elements_rejected(self) -> None:
        """A vector requires exactly LENGTH elements and rejects longer inputs."""
        with pytest.raises(ValueOrValidationError) as exception_info:
            Uint8Vector4(data=cast(Any, [1, 2, 3, 4, 5]))
        assert str(exception_info.value) == "Uint8Vector4 requires exactly 4 elements, got 5"


class TestElementAcceptance:
    """
    Tests for which classes an element may arrive as.

    Asking whether the class is the declared one before asking whether the declared one
    descends from it cannot change what is accepted, only what the common case costs.
    """

    def test_an_element_of_the_declared_class_is_stored_untouched(self) -> None:
        """The element that arrives is the element that is stored, not a copy of it."""
        element = Uint8(7)
        values = Uint8List10(data=[element])

        # The same object, not merely an equal one.
        # A rebuilt element would be a second value with the same contents, and a composite
        # element rebuilt on entry would stop reporting the mutations made through it.
        assert values[0] is element

    def test_an_element_of_an_ancestor_class_is_built(self) -> None:
        """A plain integer is an ancestor value the declared class knows how to take."""
        values = Uint8List10(data=cast(Any, [7]))
        assert type(values[0]) is Uint8
        assert values[0] == Uint8(7)

    def test_an_element_of_a_class_below_the_declared_one_is_refused(self) -> None:
        """A named subtype is a different type, and is not rewrapped into its parent."""

        class TypedUint8(Uint8):
            """A Uint8 subtype, as applications define semantic integer types."""

        # The declared class does not descend from this one, so the value is not one the
        # declared class can be built from.
        #
        # Reading the element's class first settles nothing here: the two classes are not
        # the same object, so the descent test is still what answers.
        with pytest.raises(TypeOrValidationError) as exception_info:
            Uint8List10(data=[TypedUint8(7)])
        assert str(exception_info.value) == "Expected Uint8, got TypedUint8"

    def test_an_unrelated_class_is_refused_and_names_itself(self) -> None:
        """A boolean is neither the declared class nor an ancestor of it."""
        with pytest.raises(TypeOrValidationError) as exception_info:
            Uint8List10(data=cast(Any, [Boolean(True)]))
        assert str(exception_info.value) == "Expected Uint8, got Boolean"

    def test_an_ancestor_value_out_of_range_reports_both_the_type_and_the_detail(self) -> None:
        """A value the declared class refuses keeps the reason it refused it."""
        with pytest.raises(TypeOrValidationError) as exception_info:
            Uint8List10(data=cast(Any, [256]))
        assert str(exception_info.value) == (
            "Expected Uint8, got int: 256 out of range for Uint8 [0, 255]"
        )


class TestVectorClassMetadata:
    """Tests for Vector class-level metadata and inference."""

    def test_class_getitem_creates_specialized_type(self) -> None:
        """Explicit subclasses keep distinct LENGTH and ELEMENT_TYPE bindings."""
        assert Uint8Vector32 is not Uint8Vector64
        assert Uint8Vector32 is not Uint16Vector32
        assert Uint8Vector32.LENGTH == 32
        assert Uint8Vector32.ELEMENT_TYPE is Uint8
        assert "Uint8Vector32" in repr(Uint8Vector32)

    def test_init_subclass_infers_element_type_from_generic(self) -> None:
        """Generic subclasses copy the bracketed type into ELEMENT_TYPE."""

        class LocalVector(Vector[Uint16]):
            LENGTH = 1

        assert LocalVector.ELEMENT_TYPE is Uint16

    def test_init_subclass_preserves_explicit_element_type(self) -> None:
        """An explicit ELEMENT_TYPE in the class body wins over generic inference."""

        class LocalVector(Vector[Uint8]):
            ELEMENT_TYPE = Uint16
            LENGTH = 1

        assert LocalVector.ELEMENT_TYPE is Uint16

    def test_instantiate_raw_type_raises_error(self) -> None:
        """The raw Vector base cannot be instantiated as a Pydantic model."""
        with pytest.raises(
            TypeError,
            match=r"^BaseModel\.__init__\(\) takes 1 positional argument but 2 were given\Z",
        ):
            Vector([])  # type: ignore[misc]

    def test_fixed_size_vector_reports_fixed_size_true(self) -> None:
        """A vector of fixed-size elements is itself fixed-size."""
        assert Uint8Vector4.is_fixed_size() is True

    def test_variable_size_vector_reports_fixed_size_false(self) -> None:
        """A vector of variable-size elements is not fixed-size."""
        assert VariableContainerVector2.is_fixed_size() is False

    def test_fixed_size_vector_byte_length_matches_total(self) -> None:
        """Byte length equals the element width times the element count."""
        assert Uint8Vector4.get_byte_length() == 4
        assert Uint16Vector2.get_byte_length() == 4
        assert FixedContainerVector2.get_byte_length() == 6

    def test_variable_size_vector_has_no_fixed_byte_length(self) -> None:
        """Variable-size vectors raise when asked for a fixed byte length."""
        with pytest.raises(SSZTypeError) as exception_info:
            VariableContainerVector2.get_byte_length()
        assert (
            str(exception_info.value)
            == "VariableContainerVector2: variable-size vector has no fixed byte length"
        )


class TestVectorAccessors:
    """Tests for Vector accessor and immutability behavior."""

    def test_instantiation_success(self) -> None:
        """Building with the exact element count yields a sequence of typed values."""
        instance = Uint8Vector4(data=[Uint8(1), Uint8(2), Uint8(3), Uint8(4)])

        assert len(instance) == 4
        assert list(instance) == [Uint8(1), Uint8(2), Uint8(3), Uint8(4)]

    def test_integer_index_returns_typed_element(self) -> None:
        """Positive integer indexing returns the corresponding typed element."""
        instance = Uint8Vector4(data=[Uint8(10), Uint8(20), Uint8(30), Uint8(40)])

        assert instance[0] == Uint8(10)
        assert instance[2] == Uint8(30)

    def test_negative_index_returns_typed_element(self) -> None:
        """Negative integer indexing addresses elements from the end of the sequence."""
        instance = Uint8Vector4(data=[Uint8(10), Uint8(20), Uint8(30), Uint8(40)])

        assert instance[-1] == Uint8(40)
        assert instance[-4] == Uint8(10)

    def test_slice_returns_sequence(self) -> None:
        """Slicing returns the underlying list slice of typed elements."""
        instance = Uint8Vector4(data=[Uint8(1), Uint8(2), Uint8(3), Uint8(4)])

        assert instance[1:3] == [Uint8(2), Uint8(3)]

    def test_elements_returns_mutable_copy(self) -> None:
        """The elements property exposes a mutable list copy of the data."""
        instance = Uint8Vector4(data=[Uint8(1), Uint8(2), Uint8(3), Uint8(4)])

        copy = instance.elements
        copy.append(Uint8(9))

        assert copy == [Uint8(1), Uint8(2), Uint8(3), Uint8(4), Uint8(9)]
        assert list(instance) == [Uint8(1), Uint8(2), Uint8(3), Uint8(4)]

    def test_vector_item_assignment_revalidates(self) -> None:
        """Item assignment replaces the element through full revalidation."""
        instance = Uint8Vector2(data=[Uint8(1), Uint8(2)])
        instance[0] = Uint8(3)
        assert instance == Uint8Vector2(data=[Uint8(3), Uint8(2)])

    def test_pydantic_dict_input_coerces_to_vector(self) -> None:
        """Pydantic coerces a dict payload into an Vector with typed elements."""
        instance = Uint8Vector2Model(value=cast(Any, {"data": [10, 20]}))

        assert instance.value == Uint8Vector2(data=[Uint8(10), Uint8(20)])

    def test_pydantic_dict_input_rejects_wrong_length(self) -> None:
        """A dict payload with the wrong element count surfaces the length error."""
        with pytest.raises(ValueOrValidationError) as exception_info:
            Uint8Vector2Model(value=cast(Any, {"data": [10]}))
        assert str(exception_info.value) == "Uint8Vector2 requires exactly 2 elements, got 1"


class TestListValidator:
    """Tests for the List field validator and its rejection paths."""

    def test_missing_element_type_and_limit_rejected(self) -> None:
        """A subclass without ELEMENT_TYPE or LIMIT cannot validate any input."""

        class MissingBoth(List):
            pass

        with pytest.raises(TypeOrValidationError) as exception_info:
            MissingBoth(data=cast(Any, [1]))
        assert str(exception_info.value) == "MissingBoth must define ELEMENT_TYPE and LIMIT"

    def test_missing_limit_rejected(self) -> None:
        """A subclass with ELEMENT_TYPE but no LIMIT cannot validate."""

        class MissingLimitList(List[Uint8]):
            pass

        with pytest.raises(TypeOrValidationError) as exception_info:
            MissingLimitList(data=cast(Any, [1]))
        assert str(exception_info.value) == "MissingLimitList must define ELEMENT_TYPE and LIMIT"

    def test_raw_base_class_rejected(self) -> None:
        """Instantiating the raw List base surfaces the metadata-missing error."""
        with pytest.raises(SSZTypeError) as exception_info:
            List(data=[])
        assert str(exception_info.value) == "List must define ELEMENT_TYPE and LIMIT"

    @pytest.mark.parametrize(
        "bad_input, type_name",
        [
            ("ab", "str"),
            (b"ab", "bytes"),
            (bytearray(b"ab"), "bytearray"),
        ],
    )
    def test_byte_like_inputs_rejected(self, bad_input: Any, type_name: str) -> None:
        """Strings, bytes, and bytearrays never iterate as element collections."""
        with pytest.raises(TypeOrValidationError) as exception_info:
            Uint8List4(data=bad_input)
        assert str(exception_info.value) == f"Expected iterable of Uint8, got {type_name}"

    def test_non_iterable_scalar_rejected(self) -> None:
        """Scalar inputs without an iterator interface raise an iterable error."""
        with pytest.raises(TypeOrValidationError) as exception_info:
            Uint8List4(data=cast(Any, 5))
        assert str(exception_info.value) == "Expected iterable, got int"

    def test_generator_input_coerced(self) -> None:
        """A generator is materialized and each value is coerced to ELEMENT_TYPE."""
        instance = Uint8List4(data=cast(Any, (number for number in range(3))))

        assert list(instance) == [Uint8(0), Uint8(1), Uint8(2)]

    def test_already_typed_elements_pass_through(self) -> None:
        """Inputs already typed as ELEMENT_TYPE skip the coercion constructor."""
        instance = Uint8List4(data=[Uint8(1), Uint8(2)])

        assert list(instance) == [Uint8(1), Uint8(2)]

    def test_raw_values_coerced_through_element_type(self) -> None:
        """Raw Python ints are coerced through the declared element type."""
        instance = Uint8List4(data=cast(Any, [1, 2, 3]))

        assert list(instance) == [Uint8(1), Uint8(2), Uint8(3)]

    def test_unrelated_element_class_rejected(self) -> None:
        """A value whose class is not the element class or an ancestor is rejected."""
        with pytest.raises(TypeOrValidationError) as exception_info:
            Uint8List4(data=cast(Any, [1, "bad"]))
        assert str(exception_info.value) == "Expected Uint8, got str"

    def test_empty_list_allowed(self) -> None:
        """A list with zero elements is always valid, regardless of LIMIT."""
        instance = Uint8List4(data=[])

        assert list(instance) == []
        assert len(instance) == 0

    def test_construction_at_limit_allowed(self) -> None:
        """A list with exactly LIMIT elements is valid."""
        instance = Uint8List4(data=cast(Any, [1, 2, 3, 4]))

        assert list(instance) == [Uint8(1), Uint8(2), Uint8(3), Uint8(4)]

    def test_over_limit_rejected(self) -> None:
        """A list with more than LIMIT elements raises the exceeds-limit error."""
        with pytest.raises(ValueOrValidationError) as exception_info:
            Uint8List4(data=cast(Any, [1, 2, 3, 4, 5]))
        assert str(exception_info.value) == "Uint8List4 exceeds limit of 4, got 5"

    def test_over_limit_rejected_for_boolean_list(self) -> None:
        """The same exceeds-limit error fires for a list of booleans."""
        with pytest.raises(ValueOrValidationError) as exception_info:
            BooleanList4(data=[Boolean(True)] * 5)
        assert str(exception_info.value) == "BooleanList4 exceeds limit of 4, got 5"


class TestListClassMetadata:
    """Tests for List class-level metadata and inference."""

    def test_class_getitem_creates_specialized_type(self) -> None:
        """Explicit subclasses keep distinct LIMIT and ELEMENT_TYPE bindings."""
        assert Uint8List32 is not Uint8List64
        assert Uint8List32 is not Uint16List32
        assert Uint8List32.LIMIT == 32
        assert Uint8List32.ELEMENT_TYPE is Uint8
        assert "Uint8List32" in repr(Uint8List32)

    def test_init_subclass_infers_element_type_from_generic(self) -> None:
        """Generic subclasses copy the bracketed type into ELEMENT_TYPE."""

        class LocalList(List[Uint16]):
            LIMIT = 2

        assert LocalList.ELEMENT_TYPE is Uint16

    def test_list_is_never_fixed_size(self) -> None:
        """A list never collapses to a fixed-size encoding."""
        assert Uint8List4.is_fixed_size() is False
        assert VariableContainerList2.is_fixed_size() is False

    def test_get_byte_length_always_raises(self) -> None:
        """A list type has no fixed byte length even for fixed-size elements."""
        with pytest.raises(SSZTypeError) as exception_info:
            Uint8List4.get_byte_length()
        assert (
            str(exception_info.value) == "Uint8List4: variable-size list has no fixed byte length"
        )

    def test_get_byte_length_raises_for_variable_element_list(self) -> None:
        """The same error fires for lists whose elements are variable-size."""
        with pytest.raises(SSZTypeError) as exception_info:
            VariableContainerList2.get_byte_length()
        assert (
            str(exception_info.value)
            == "VariableContainerList2: variable-size list has no fixed byte length"
        )


class TestListAccessors:
    """Tests for List accessor and concatenation behavior."""

    def test_integer_index_returns_typed_element(self) -> None:
        """Positive integer indexing returns the corresponding typed element."""
        instance = Uint8List4(data=[Uint8(10), Uint8(20), Uint8(30)])

        assert instance[0] == Uint8(10)
        assert instance[2] == Uint8(30)

    def test_negative_index_returns_typed_element(self) -> None:
        """Negative integer indexing addresses elements from the end of the sequence."""
        instance = Uint8List4(data=[Uint8(10), Uint8(20), Uint8(30)])

        assert instance[-1] == Uint8(30)
        assert instance[-3] == Uint8(10)

    def test_hashes_by_root(self) -> None:
        """A sequence hashes by Merkle root, so it serves as a set member."""
        instance = Uint8List4(data=[Uint8(1), Uint8(2)])
        same = Uint8List4(data=[Uint8(1), Uint8(2)])

        assert len({instance, same}) == 1

    def test_slice_returns_its_own_type(self) -> None:
        """Slicing returns a shorter value of the same shape."""
        instance = Uint8List4(data=[Uint8(1), Uint8(2), Uint8(3)])

        result = instance[1:3]

        assert type(result) is Uint8List4
        assert list(result) == [Uint8(2), Uint8(3)]

    def test_slice_concatenates_as_its_own_type(self) -> None:
        """A slice composes with concatenation without naming the type again."""
        instance = Uint8List4(data=[Uint8(1), Uint8(2), Uint8(3)])

        result = instance[1:] + [Uint8(9)]

        assert type(result) is Uint8List4
        assert list(result) == [Uint8(2), Uint8(3), Uint8(9)]

    def test_elements_returns_mutable_copy(self) -> None:
        """The elements property exposes a mutable list copy of the data."""
        instance = Uint8List4(data=[Uint8(1), Uint8(2), Uint8(3)])

        copy = instance.elements
        copy.append(Uint8(9))

        assert copy == [Uint8(1), Uint8(2), Uint8(3), Uint8(9)]
        assert list(instance) == [Uint8(1), Uint8(2), Uint8(3)]

    def test_pydantic_dict_input_coerces_to_list(self) -> None:
        """Pydantic coerces a list payload into an List with typed elements."""
        instance = Uint8List4Model(value=Uint8List4(data=[Uint8(10), Uint8(20)]))

        assert instance.value == Uint8List4(data=[Uint8(10), Uint8(20)])

    def test_add_with_sszlist(self) -> None:
        """Concatenating two Lists yields a fresh list of the same type."""
        concatenated = Uint8List10(data=[Uint8(1), Uint8(2)]) + Uint8List10(
            data=[Uint8(3), Uint8(4)]
        )

        assert concatenated == Uint8List10(data=[Uint8(1), Uint8(2), Uint8(3), Uint8(4)])
        assert isinstance(concatenated, Uint8List10)

    def test_add_with_plain_list(self) -> None:
        """Concatenating with a plain list coerces the right-hand values."""
        concatenated = Uint8List10(data=[Uint8(1), Uint8(2), Uint8(3)]) + [4, 5]

        assert concatenated == Uint8List10(data=[Uint8(1), Uint8(2), Uint8(3), Uint8(4), Uint8(5)])

    def test_add_with_tuple(self) -> None:
        """Concatenating with a tuple coerces the right-hand values."""
        concatenated = Uint8List10(data=[Uint8(1), Uint8(2)]) + (3, 4)

        assert concatenated == Uint8List10(data=[Uint8(1), Uint8(2), Uint8(3), Uint8(4)])

    def test_add_empty_to_empty(self) -> None:
        """Concatenating two empty lists yields an empty list of the same type."""
        concatenated = Uint8List10(data=[]) + Uint8List10(data=[])

        assert concatenated == Uint8List10(data=[])

    def test_add_empty_to_non_empty(self) -> None:
        """Concatenating an empty list to a populated one preserves the populated list."""
        populated = Uint8List10(data=[Uint8(1), Uint8(2)])
        concatenated = Uint8List10(data=[]) + populated

        assert concatenated == populated

    def test_add_non_empty_to_empty(self) -> None:
        """Concatenating a populated list to an empty one preserves the populated list."""
        populated = Uint8List10(data=[Uint8(1), Uint8(2)])
        concatenated = populated + Uint8List10(data=[])

        assert concatenated == populated

    def test_add_unsupported_type_returns_not_implemented(self) -> None:
        """Unsupported operands return NotImplemented from the add hook."""
        instance = Uint8List10(data=[Uint8(1), Uint8(2)])

        assert instance.__add__(object()) is NotImplemented

    def test_add_exceeding_limit_raises_error(self) -> None:
        """Concatenation that overflows LIMIT raises the exceeds-limit error."""
        base = Uint8List4(data=[Uint8(1), Uint8(2), Uint8(3)])
        with pytest.raises(ValueOrValidationError) as exception_info:
            base + [4, 5]
        assert str(exception_info.value) == "Uint8List4 exceeds limit of 4, got 5"


class TestVectorSerialization:
    """Tests SSZ serialization and deserialization for Vector."""

    @pytest.mark.parametrize(
        "vector_type, elements, expected_hex",
        [
            (Uint16Vector2, (0x4567, 0x0123), "67452301"),
            (Uint8Vector4, (1, 2, 3, 4), "01020304"),
            (
                Uint8Vector48,
                tuple(range(48)),
                "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
                + "202122232425262728292a2b2c2d2e2f",
            ),
            (
                Uint8Vector96,
                tuple(
                    1 if i == 0 else 2 if i == 32 else 3 if i == 64 else 0xFF if i == 95 else 0
                    for i in range(96)
                ),
                "0100000000000000000000000000000000000000000000000000000000000000"
                + "0200000000000000000000000000000000000000000000000000000000000000"
                + "03000000000000000000000000000000000000000000000000000000000000ff",
            ),
            (
                FixedContainerVector2,
                (
                    FixedContainer(a=Uint8(1), b=Uint16(2)),
                    FixedContainer(a=Uint8(3), b=Uint16(4)),
                ),
                "010200030400",
            ),
        ],
    )
    def test_fixed_size_element_vector_roundtrip(
        self,
        vector_type: type[Vector],
        elements: tuple[Any, ...],
        expected_hex: str,
    ) -> None:
        """Fixed-size vectors encode to a known hex layout and round-trip back."""
        instance = vector_type(data=elements)
        encoded = instance.encode_bytes()

        assert encoded.hex() == expected_hex
        assert vector_type.decode_bytes(encoded) == instance

    def test_variable_size_element_vector_roundtrip(self) -> None:
        """Variable-size vectors emit the offset table followed by buffered bodies."""
        val1 = VariableContainer(a=Uint8(1), b=Uint16List4(data=[Uint16(10), Uint16(20)]))
        val2 = VariableContainer(a=Uint8(2), b=Uint16List4(data=[Uint16(30)]))
        instance = VariableContainerVector2(data=[val1, val2])

        expected_hex = "080000001100000001050000000a00140002050000001e00"
        encoded = instance.encode_bytes()

        assert encoded.hex() == expected_hex
        assert VariableContainerVector2.decode_bytes(encoded) == instance

    def test_fixed_size_vector_rejects_scope_too_small(self) -> None:
        """A fixed-size vector rejects payloads shorter than its byte budget."""
        with pytest.raises(SSZSerializationError) as exception_info:
            Uint8Vector4.decode_bytes(b"\x00\x01\x02")
        assert str(exception_info.value) == "Uint8Vector4: expected 4 bytes, got 3"

    def test_fixed_size_vector_rejects_scope_too_large(self) -> None:
        """A fixed-size vector rejects payloads larger than its byte budget."""
        with pytest.raises(SSZSerializationError) as exception_info:
            Uint8Vector4.decode_bytes(b"\x00\x01\x02\x03\x04")
        assert str(exception_info.value) == "Uint8Vector4: expected 4 bytes, got 5"

    def test_variable_size_vector_rejects_scope_below_offset_table(self) -> None:
        """A scope smaller than the offset table cannot describe any layout."""
        with pytest.raises(SSZSerializationError) as exception_info:
            VariableContainerVector2.decode_bytes(b"\x00\x00\x00")
        assert (
            str(exception_info.value)
            == "VariableContainerVector2: scope 3 too small, expected at least 8"
        )

    def test_variable_size_vector_rejects_invalid_first_offset(self) -> None:
        """The first offset must point past the offset table."""
        with pytest.raises(SSZSerializationError) as exception_info:
            VariableContainerVector2.decode_bytes(b"\x04\x00\x00\x00\x08\x00\x00\x00")
        assert str(exception_info.value) == "VariableContainerVector2: invalid offset 4, expected 8"

    def test_variable_size_vector_rejects_non_monotonic_offsets(self) -> None:
        """A later offset smaller than an earlier one means a body would have negative width."""
        # Invariant: an offset never exceeds the one after it, or the span between them
        # is a body of negative width.
        #
        # Fixture state: a 2-element vector, so a table of two offsets and no bodies.
        #
        # Mutation: the second offset points behind the first.
        #
        #     offsets       8       6
        #     boundaries    8       6       8
        #     spans         8..6            -> negative width, refused at element 0
        encoded_bytes = b"\x08\x00\x00\x00\x06\x00\x00\x00"
        with pytest.raises(SSZSerializationError) as exception_info:
            VariableContainerVector2.decode_bytes(encoded_bytes)
        assert (
            str(exception_info.value)
            == "VariableContainerVector2[0]: offset 8 is above the next offset 6"
        )

    def test_variable_size_vector_rejects_final_offset_overflow(self) -> None:
        """A last offset past the byte budget is reported as the overrun it is."""
        # Invariant: the last body ends at the budget, so the last offset cannot exceed it.
        #
        # Fixture state: a 2-element vector over 20 bytes, so a table of two offsets
        # followed by 12 bytes of bodies.
        #
        # Mutation: the second offset points past the end of the input.
        #
        #     offsets       8       100
        #     boundaries    8       100      20
        #     spans         8..100  100..20  -> element 1 starts past the budget
        #
        # The failing pair is the one closed by the budget, which is what separates this
        # fault from a table that is merely out of order.
        encoded_bytes = b"\x08\x00\x00\x00\x64\x00\x00\x00" + b"\x00" * 12
        with pytest.raises(SSZSerializationError) as exception_info:
            VariableContainerVector2.decode_bytes(encoded_bytes)
        assert (
            str(exception_info.value)
            == "VariableContainerVector2[1]: offset 100 runs past the scope of 20"
        )


class TestListSerialization:
    """Tests SSZ serialization and deserialization for List."""

    @pytest.mark.parametrize(
        "list_type, elements, expected_hex",
        [
            (Uint16List32, (0xAABB, 0xC0AD, 0xEEFF), "bbaaadc0ffee"),
            (Uint8List10, (), ""),
            (Uint8List10, (0, 1, 2, 3, 4, 5, 6), "00010203040506"),
            (Uint32List128, (0xAABB, 0xC0AD, 0xEEFF), "bbaa0000adc00000ffee0000"),
            (
                Bytes32List32,
                (
                    b"\xbb\xaa" + b"\x00" * 30,
                    b"\xad\xc0" + b"\x00" * 30,
                    b"\xff\xee" + b"\x00" * 30,
                ),
                (
                    "bbaa000000000000000000000000000000000000000000000000000000000000"
                    + "adc0000000000000000000000000000000000000000000000000000000000000"
                    + "ffee000000000000000000000000000000000000000000000000000000000000"
                ),
            ),
            (
                Bytes32List128,
                tuple(i.to_bytes(32, "little") for i in range(1, 20)),
                "".join(i.to_bytes(32, "little").hex() for i in range(1, 20)),
            ),
        ],
    )
    def test_fixed_size_element_list_roundtrip(
        self,
        list_type: type[List],
        elements: tuple[Any, ...],
        expected_hex: str,
    ) -> None:
        """Fixed-size lists pack bodies back-to-back without separators."""
        instance = list_type(data=elements)
        encoded = instance.encode_bytes()

        assert encoded.hex() == expected_hex
        assert list_type.decode_bytes(encoded) == instance

    def test_variable_size_element_list_roundtrip(self) -> None:
        """Variable-size lists emit a runtime-sized offset table before the bodies."""
        val1 = VariableContainer(a=Uint8(1), b=Uint16List4(data=[Uint16(10)]))
        val2 = VariableContainer(a=Uint8(2), b=Uint16List4(data=[Uint16(30), Uint16(40)]))
        instance = VariableContainerList2(data=[val1, val2])

        expected_hex = "080000000f00000001050000000a0002050000001e002800"
        encoded = instance.encode_bytes()

        assert encoded.hex() == expected_hex
        assert VariableContainerList2.decode_bytes(encoded) == instance

    def test_empty_scope_decodes_to_empty_list(self) -> None:
        """An empty payload always decodes to an empty list."""
        assert VariableContainerList2.decode_bytes(b"") == VariableContainerList2(data=[])

    def test_fixed_size_list_rejects_scope_not_divisible_by_element_size(self) -> None:
        """A fixed-size list rejects payloads whose length is not a multiple of the stride."""
        with pytest.raises(SSZSerializationError) as exception_info:
            Uint16List4.decode_bytes(b"\x01")
        assert str(exception_info.value) == "Uint16List4: scope 1 not divisible by element size 2"

    def test_fixed_size_list_rejects_count_beyond_limit(self) -> None:
        """A fixed-size list rejects payloads that decode to more than LIMIT elements."""
        with pytest.raises(SSZValueError) as exception_info:
            Uint8List4.decode_bytes(b"\x00\x01\x02\x03\x04")
        assert str(exception_info.value) == "Uint8List4 exceeds limit of 4, got 5"

    def test_variable_size_list_rejects_scope_below_offset_word(self) -> None:
        """A variable-size list requires at least one offset word in the payload."""
        # An offset word is 4 bytes, so 3 bytes cannot even hold the first one.
        with pytest.raises(SSZSerializationError) as exception_info:
            VariableContainerList2.decode_bytes(b"\x00\x00\x00")
        assert (
            str(exception_info.value)
            == "VariableContainerList2: scope 3 too small, " + "expected at least 4"
        )

    def test_variable_size_list_rejects_first_offset_past_scope(self) -> None:
        """A first offset larger than the available scope is invalid."""
        # The first offset is the table's own width, so 100 claims a 100-byte table
        # inside a 4-byte payload, leaving every body outside the input.
        with pytest.raises(SSZSerializationError) as exception_info:
            VariableContainerList2.decode_bytes(b"\x64\x00\x00\x00")
        assert (
            str(exception_info.value)
            == "VariableContainerList2: first offset 100 runs past the scope of 4"
        )

    def test_variable_size_list_rejects_misaligned_first_offset(self) -> None:
        """A first offset that is not a multiple of the offset width is invalid."""
        # The table is a whole number of 4-byte words, so 5 divides into no element count.
        with pytest.raises(SSZSerializationError) as exception_info:
            VariableContainerList2.decode_bytes(b"\x05\x00\x00\x00\x00\x00\x00\x00")
        assert (
            str(exception_info.value)
            == "VariableContainerList2: first offset 5 is not a multiple of 4"
        )

    def test_variable_size_list_rejects_zero_first_offset(self) -> None:
        """A zero first offset is contradictory and rejected before building the boundary list."""
        # Zero says the table is empty, so there are no elements — yet the payload then
        # claims one body spanning the whole budget.
        with pytest.raises(SSZSerializationError) as exception_info:
            VariableContainerList2.decode_bytes(bytes.fromhex("00000000aabbccdd"))
        assert (
            str(exception_info.value)
            == "VariableContainerList2: first offset 0 is below the table's own width of 4"
        )

    def test_variable_size_list_rejects_count_beyond_limit(self) -> None:
        """A first offset that implies more than LIMIT elements is rejected."""
        # Layout:
        #
        #     first_offset = 12   (count = 12 / 4 = 3, above LIMIT=2)
        encoded_bytes = b"\x0c\x00\x00\x00" + b"\x00" * 8
        with pytest.raises(SSZValueError) as exception_info:
            VariableContainerList2.decode_bytes(encoded_bytes)
        assert str(exception_info.value) == "VariableContainerList2 exceeds limit of 2, got 3"

    def test_variable_size_list_rejects_non_monotonic_offsets(self) -> None:
        """A later offset smaller than an earlier one means a body would have negative width."""
        # Fixture state: first offset 8, so the table is 8 bytes and holds 2 offsets.
        #
        # Mutation: the second offset points behind the first.
        #
        #     offsets       8       6
        #     spans         8..6            -> negative width, refused at element 0
        encoded_bytes = b"\x08\x00\x00\x00\x06\x00\x00\x00" + b"\x00" * 12
        with pytest.raises(SSZSerializationError) as exception_info:
            VariableContainerList2.decode_bytes(encoded_bytes)
        assert (
            str(exception_info.value)
            == "VariableContainerList2[0]: offset 8 is above the next offset 6"
        )

    def test_variable_size_list_rejects_final_offset_overflow(self) -> None:
        """A last offset past the byte budget is reported as the overrun it is."""
        # Fixture state: 20 bytes of payload, so the budget closing the table is 20.
        #
        # Mutation: the second offset points past the end of the input.
        #
        #     offsets       8       100
        #     spans         8..100  100..20  -> element 1 starts past the budget
        encoded_bytes = b"\x08\x00\x00\x00\x64\x00\x00\x00" + b"\x00" * 12
        with pytest.raises(SSZSerializationError) as exception_info:
            VariableContainerList2.decode_bytes(encoded_bytes)
        assert (
            str(exception_info.value)
            == "VariableContainerList2[1]: offset 100 runs past the scope of 20"
        )

    def test_variable_size_list_single_element_decodes(self) -> None:
        """A single-element list reads no further offsets after the first."""
        element = VariableContainer(a=Uint8(1), b=Uint16List4(data=[Uint16(10)]))
        encoded = VariableContainerList2(data=[element]).encode_bytes()

        assert VariableContainerList2.decode_bytes(encoded) == VariableContainerList2(
            data=[element]
        )


class TestProgressiveListValidator:
    """Tests for the ProgressiveList field validator and its rejection paths."""

    def test_missing_element_type_rejected(self) -> None:
        """A subclass without ELEMENT_TYPE cannot validate any input."""

        class MissingElementType(ProgressiveList):
            pass

        with pytest.raises(TypeOrValidationError) as exception_info:
            MissingElementType(data=cast(Any, [1]))
        assert str(exception_info.value) == "MissingElementType must define ELEMENT_TYPE"

    def test_raw_base_class_rejected(self) -> None:
        """Instantiating the raw ProgressiveList base surfaces the metadata-missing error."""
        with pytest.raises(SSZTypeError) as exception_info:
            ProgressiveList(data=[])
        assert str(exception_info.value) == "ProgressiveList must define ELEMENT_TYPE"

    @pytest.mark.parametrize(
        "bad_input, type_name",
        [
            ("ab", "str"),
            (b"ab", "bytes"),
            (bytearray(b"ab"), "bytearray"),
        ],
    )
    def test_byte_like_inputs_rejected(self, bad_input: Any, type_name: str) -> None:
        """Strings, bytes, and bytearrays never iterate as element collections."""
        with pytest.raises(TypeOrValidationError) as exception_info:
            Uint8ProgressiveList(data=bad_input)
        assert str(exception_info.value) == f"Expected iterable of Uint8, got {type_name}"

    def test_non_iterable_scalar_rejected(self) -> None:
        """Scalar inputs without an iterator interface raise an iterable error."""
        with pytest.raises(TypeOrValidationError) as exception_info:
            Uint8ProgressiveList(data=cast(Any, 5))
        assert str(exception_info.value) == "Expected iterable, got int"

    def test_generator_input_coerced(self) -> None:
        """A generator is materialized and each value is coerced to ELEMENT_TYPE."""
        instance = Uint8ProgressiveList(data=cast(Any, (number for number in range(3))))

        assert list(instance) == [Uint8(0), Uint8(1), Uint8(2)]

    def test_already_typed_elements_pass_through(self) -> None:
        """Inputs already typed as ELEMENT_TYPE skip the coercion constructor."""
        instance = Uint8ProgressiveList(data=[Uint8(1), Uint8(2)])

        assert list(instance) == [Uint8(1), Uint8(2)]

    def test_raw_values_coerced_through_element_type(self) -> None:
        """Raw Python ints are coerced through the declared element type."""
        instance = Uint8ProgressiveList(data=cast(Any, [1, 2, 3]))

        assert list(instance) == [Uint8(1), Uint8(2), Uint8(3)]

    def test_unrelated_element_class_rejected(self) -> None:
        """A value whose class is not the element class or an ancestor is rejected."""
        with pytest.raises(TypeOrValidationError) as exception_info:
            Uint8ProgressiveList(data=cast(Any, [1, "bad"]))
        assert str(exception_info.value) == "Expected Uint8, got str"

    def test_empty_list_allowed(self) -> None:
        """A progressive list with zero elements is valid and is the default value."""
        assert list(Uint8ProgressiveList(data=[])) == []
        assert len(Uint8ProgressiveList()) == 0

    def test_no_element_count_is_ever_rejected(self) -> None:
        """No capacity is declared, so any element count validates."""
        instance = Uint8ProgressiveList(data=cast(Any, list(range(256)) * 4))

        assert len(instance) == 1024

    def test_pydantic_dict_input_coerces_to_progressive_list(self) -> None:
        """Pydantic coerces a dict payload into a ProgressiveList with typed elements."""
        instance = Uint8ProgressiveListModel(value=cast(Any, {"data": [10, 20]}))

        assert instance.value == Uint8ProgressiveList(data=[Uint8(10), Uint8(20)])


class TestProgressiveListClassMetadata:
    """Tests for ProgressiveList class-level metadata and inference."""

    def test_subclasses_keep_distinct_element_type_bindings(self) -> None:
        """Explicit subclasses keep distinct ELEMENT_TYPE bindings."""
        assert Uint8ProgressiveList is not Uint16ProgressiveList
        assert Uint8ProgressiveList.ELEMENT_TYPE is Uint8
        assert Uint16ProgressiveList.ELEMENT_TYPE is Uint16
        assert "Uint8ProgressiveList" in repr(Uint8ProgressiveList)

    def test_no_limit_is_declared(self) -> None:
        """The shape declares no capacity, so the name holds None rather than a count."""
        assert "LIMIT" not in Uint8ProgressiveList.__dict__
        assert Uint8ProgressiveList.LIMIT is None

    def test_init_subclass_infers_element_type_from_generic(self) -> None:
        """Generic subclasses copy the bracketed type into ELEMENT_TYPE."""

        class LocalProgressiveList(ProgressiveList[Uint16]):
            pass

        assert LocalProgressiveList.ELEMENT_TYPE is Uint16

    def test_progressive_list_is_never_fixed_size(self) -> None:
        """A progressive list never collapses to a fixed-size encoding."""
        assert Uint8ProgressiveList.is_fixed_size() is False
        assert VariableContainerProgressiveList.is_fixed_size() is False

    def test_get_byte_length_always_raises(self) -> None:
        """A progressive list has no fixed byte length even for fixed-size elements."""
        with pytest.raises(SSZTypeError) as exception_info:
            Uint8ProgressiveList.get_byte_length()
        assert (
            str(exception_info.value)
            == "Uint8ProgressiveList: variable-size list has no fixed byte length"
        )

    def test_get_byte_length_raises_for_variable_element_list(self) -> None:
        """The same error fires for progressive lists whose elements are variable-size."""
        with pytest.raises(SSZTypeError) as exception_info:
            VariableContainerProgressiveList.get_byte_length()
        assert (
            str(exception_info.value)
            == "VariableContainerProgressiveList: variable-size list has no fixed byte length"
        )


class TestProgressiveListAccessors:
    """Tests for ProgressiveList accessor, factory, and concatenation behavior."""

    def test_iteration_yields_elements(self) -> None:
        """Iterating a progressive list yields its elements, not field name/value pairs."""
        instance = Uint8ProgressiveList(data=[Uint8(1), Uint8(2), Uint8(3)])

        assert tuple(instance) == (Uint8(1), Uint8(2), Uint8(3))
        assert len(instance) == 3

    def test_integer_index_returns_typed_element(self) -> None:
        """Positive integer indexing returns the corresponding typed element."""
        instance = Uint8ProgressiveList(data=[Uint8(10), Uint8(20), Uint8(30)])

        assert instance[0] == Uint8(10)
        assert instance[2] == Uint8(30)

    def test_negative_index_returns_typed_element(self) -> None:
        """Negative integer indexing addresses elements from the end of the sequence."""
        instance = Uint8ProgressiveList(data=[Uint8(10), Uint8(20), Uint8(30)])

        assert instance[-1] == Uint8(30)
        assert instance[-3] == Uint8(10)

    def test_slice_returns_its_own_type(self) -> None:
        """Slicing returns a shorter value of the same shape."""
        instance = Uint8ProgressiveList(data=[Uint8(1), Uint8(2), Uint8(3)])

        result = instance[1:3]

        assert type(result) is Uint8ProgressiveList
        assert list(result) == [Uint8(2), Uint8(3)]

    def test_slice_concatenates_as_its_own_type(self) -> None:
        """A slice composes with concatenation without naming the type again."""
        instance = Uint8ProgressiveList(data=[Uint8(1), Uint8(2), Uint8(3)])

        result = instance[1:] + [Uint8(9)]

        assert type(result) is Uint8ProgressiveList
        assert list(result) == [Uint8(2), Uint8(3), Uint8(9)]

    def test_elements_returns_mutable_copy(self) -> None:
        """The elements property exposes a mutable list copy of the data."""
        instance = Uint8ProgressiveList(data=[Uint8(1), Uint8(2)])

        copy = instance.elements
        copy.append(Uint8(9))

        assert copy == [Uint8(1), Uint8(2), Uint8(9)]
        assert list(instance) == [Uint8(1), Uint8(2)]

    def test_progressive_list_item_assignment_revalidates(self) -> None:
        """Item assignment replaces the element through full revalidation."""
        instance = Uint8ProgressiveList(data=[Uint8(1), Uint8(2)])
        instance[0] = Uint8(3)
        assert instance == Uint8ProgressiveList(data=[Uint8(3), Uint8(2)])

    def test_progressive_list_grows_without_a_capacity(self) -> None:
        """Append and pop work, and no capacity bounds the growth."""
        instance = Uint8ProgressiveList(data=[Uint8(1)])
        instance.append(Uint8(2))
        assert instance == Uint8ProgressiveList(data=[Uint8(1), Uint8(2)])
        assert instance.pop() == Uint8(2)
        assert instance == Uint8ProgressiveList(data=[Uint8(1)])

    def test_progressive_list_appends_past_a_bounded_limit(self) -> None:
        """Growth runs past the count a bounded list of the same element type refuses."""
        bounded = Uint8List4(data=[Uint8(0)] * 4)
        with pytest.raises(ValueOrValidationError):
            bounded.append(Uint8(0))

        # The same element type with no capacity keeps going, well past that limit.
        instance = Uint8ProgressiveList(data=[])
        for value in range(100):
            instance.append(Uint8(value))
        assert len(instance) == 100
        assert instance == Uint8ProgressiveList(data=[Uint8(value) for value in range(100)])

    def test_progressive_list_slice_assignment_resizes(self) -> None:
        """Slice assignment replaces a range, and may change the length either way."""
        instance = Uint8ProgressiveList(data=[Uint8(1), Uint8(2), Uint8(3)])
        instance[1:] = [Uint8(9)]
        assert instance == Uint8ProgressiveList(data=[Uint8(1), Uint8(9)])
        instance[0:1] = [Uint8(7), Uint8(8), Uint8(9)]
        assert instance == Uint8ProgressiveList(data=[Uint8(7), Uint8(8), Uint8(9), Uint8(9)])

    def test_progressive_list_mutation_coerces_raw_values(self) -> None:
        """Mutation coerces a raw value into the element type, exactly as construction does."""
        instance = Uint8ProgressiveList(data=[Uint8(1)])
        instance.append(2)  # ty: ignore[invalid-argument-type]
        instance[0] = 3  # ty: ignore[invalid-assignment]
        assert instance == Uint8ProgressiveList(data=[Uint8(3), Uint8(2)])
        assert all(type(element) is Uint8 for element in instance)

    def test_progressive_list_mutation_rejects_a_foreign_element(self) -> None:
        """An element of another type is refused, leaving the stored elements untouched."""
        instance = Uint8ProgressiveList(data=[Uint8(1)])
        with pytest.raises(SSZTypeMismatch):
            instance.append(Uint16(2))  # ty: ignore[invalid-argument-type]
        assert instance == Uint8ProgressiveList(data=[Uint8(1)])

    def test_of_builds_from_positional_elements(self) -> None:
        """The of factory takes each argument as exactly one element."""
        assert Uint8ProgressiveList.of(1, 2, 3) == Uint8ProgressiveList(
            data=[Uint8(1), Uint8(2), Uint8(3)]
        )

    def test_of_with_no_arguments_builds_the_empty_list(self) -> None:
        """The of factory with no arguments yields the empty progressive list."""
        assert Uint8ProgressiveList.of() == Uint8ProgressiveList(data=[])

    def test_add_with_progressive_list(self) -> None:
        """Concatenating two progressive lists yields a fresh list of the same type."""
        concatenated = Uint8ProgressiveList(data=[Uint8(1), Uint8(2)]) + Uint8ProgressiveList(
            data=[Uint8(3), Uint8(4)]
        )

        assert concatenated == Uint8ProgressiveList(data=[Uint8(1), Uint8(2), Uint8(3), Uint8(4)])
        assert isinstance(concatenated, Uint8ProgressiveList)

    def test_add_with_bounded_list_keeps_the_left_shape(self) -> None:
        """Both list shapes share the concatenation hook; the left operand's type wins."""
        concatenated = Uint8ProgressiveList(data=[Uint8(1)]) + Uint8List4(data=[Uint8(2)])

        assert concatenated == Uint8ProgressiveList(data=[Uint8(1), Uint8(2)])
        assert isinstance(concatenated, Uint8ProgressiveList)

    def test_add_with_plain_list(self) -> None:
        """Concatenating with a plain list coerces the right-hand values."""
        concatenated = Uint8ProgressiveList(data=[Uint8(1), Uint8(2)]) + [3, 4]

        assert concatenated == Uint8ProgressiveList(data=[Uint8(1), Uint8(2), Uint8(3), Uint8(4)])

    def test_add_with_tuple(self) -> None:
        """Concatenating with a tuple coerces the right-hand values."""
        concatenated = Uint8ProgressiveList(data=[Uint8(1)]) + (2, 3)

        assert concatenated == Uint8ProgressiveList(data=[Uint8(1), Uint8(2), Uint8(3)])

    def test_add_unsupported_type_returns_not_implemented(self) -> None:
        """Unsupported operands return NotImplemented from the add hook."""
        instance = Uint8ProgressiveList(data=[Uint8(1)])

        assert instance.__add__(object()) is NotImplemented

    def test_add_never_overflows_a_capacity(self) -> None:
        """Concatenation has no capacity to overflow, so it always revalidates cleanly."""
        base = Uint8ProgressiveList(data=[Uint8(index) for index in range(200)])

        assert len(base + base) == 400


class TestProgressiveListSerialization:
    """Tests SSZ serialization and deserialization for ProgressiveList."""

    @pytest.mark.parametrize(
        "elements, expected_hex",
        [
            # Empty: no offsets, no bodies, no length prefix.
            ((), ""),
            # One element: a single little-endian body.
            ((0xAABB,), "bbaa"),
            ((0xAABB, 0xC0AD, 0xEEFF), "bbaaadc0ffee"),
            # Sixteen Uint16 fill exactly one Merkle chunk of packed bytes.
            (
                tuple(range(16)),
                b"".join(value.to_bytes(2, "little") for value in range(16)).hex(),
            ),
        ],
    )
    def test_fixed_size_element_list_roundtrip(
        self, elements: tuple[Any, ...], expected_hex: str
    ) -> None:
        """Fixed-size elements pack back-to-back without separators."""
        instance = Uint16ProgressiveList(data=elements)
        encoded = instance.encode_bytes()

        assert encoded.hex() == expected_hex
        assert Uint16ProgressiveList.decode_bytes(encoded) == instance

    def test_composite_fixed_size_element_list_roundtrip(self) -> None:
        """Fixed-size composite elements pack back-to-back at their known stride."""
        instance = Bytes32ProgressiveList(
            data=[
                Bytes32(b"\xbb\xaa" + b"\x00" * 30),
                Bytes32(b"\xad\xc0" + b"\x00" * 30),
            ]
        )
        encoded = instance.encode_bytes()

        assert encoded.hex() == (
            "bbaa000000000000000000000000000000000000000000000000000000000000"
            + "adc0000000000000000000000000000000000000000000000000000000000000"
        )
        assert Bytes32ProgressiveList.decode_bytes(encoded) == instance

    def test_container_element_list_roundtrip(self) -> None:
        """Fixed-size container elements need no offset table."""
        instance = FixedContainerProgressiveList(
            data=[
                FixedContainer(a=Uint8(1), b=Uint16(2)),
                FixedContainer(a=Uint8(3), b=Uint16(4)),
            ]
        )
        encoded = instance.encode_bytes()

        assert encoded.hex() == "010200030400"
        assert FixedContainerProgressiveList.decode_bytes(encoded) == instance

    def test_variable_size_element_list_roundtrip(self) -> None:
        """Variable-size elements emit a runtime-sized offset table before the bodies."""
        val1 = VariableContainer(a=Uint8(1), b=Uint16List4(data=[Uint16(10)]))
        val2 = VariableContainer(a=Uint8(2), b=Uint16List4(data=[Uint16(30), Uint16(40)]))
        instance = VariableContainerProgressiveList(data=[val1, val2])

        # Layout:
        #
        #     bytes 0..3   : off_0 = 8    (table is two offsets wide)
        #     bytes 4..7   : off_1 = 15   (first body is 7 bytes)
        #     bytes 8..14  : body_0
        #     bytes 15..23 : body_1
        expected_hex = "080000000f00000001050000000a0002050000001e002800"
        encoded = instance.encode_bytes()

        assert encoded.hex() == expected_hex
        assert VariableContainerProgressiveList.decode_bytes(encoded) == instance

    def test_nested_progressive_list_roundtrip(self) -> None:
        """A progressive list of progressive lists uses the offset-table layout."""
        instance = NestedProgressiveList(
            data=[
                Uint16ProgressiveList(data=[Uint16(1), Uint16(2)]),
                Uint16ProgressiveList(data=[]),
            ]
        )

        # Layout:
        #
        #     bytes 0..3  : off_0 = 8     (table is two offsets wide)
        #     bytes 4..7  : off_1 = 12    (first inner list is 4 bytes)
        #     bytes 8..11 : body_0        (two Uint16)
        #     bytes 12..  : body_1        (empty, zero-width body)
        encoded = instance.encode_bytes()

        assert encoded.hex() == "080000000c00000001000200"
        assert NestedProgressiveList.decode_bytes(encoded) == instance

    def test_bytes_match_the_bounded_list_encoding(self) -> None:
        """The wire format is identical to a bounded list of the same elements."""
        elements = (Uint16(0xAABB), Uint16(0xC0AD), Uint16(0xEEFF))
        progressive = Uint16ProgressiveList(data=elements)
        bounded = Uint16List32(data=elements)

        assert progressive.encode_bytes() == bounded.encode_bytes()
        # The same bytes therefore decode under either shape.
        assert Uint16List32.decode_bytes(progressive.encode_bytes()) == bounded
        assert Uint16ProgressiveList.decode_bytes(bounded.encode_bytes()) == progressive

    def test_empty_scope_decodes_to_empty_list(self) -> None:
        """An empty payload always decodes to an empty progressive list."""
        assert VariableContainerProgressiveList.decode_bytes(
            b""
        ) == VariableContainerProgressiveList(data=[])

    def test_fixed_size_decode_accepts_any_element_count(self) -> None:
        """No capacity bounds the decode; only the byte budget does."""
        decoded = Uint8ProgressiveList.decode_bytes(bytes(1000))

        assert len(decoded) == 1000

    def test_variable_size_decode_accepts_any_element_count(self) -> None:
        """An offset table wider than any bounded limit still decodes."""
        element = VariableContainer(a=Uint8(1), b=Uint16List4(data=[Uint16(10)]))
        instance = VariableContainerProgressiveList(data=[element] * 3)

        assert VariableContainerProgressiveList.decode_bytes(instance.encode_bytes()) == instance

    def test_fixed_size_list_rejects_scope_not_divisible_by_element_size(self) -> None:
        """A fixed-size payload whose length is not a multiple of the stride is invalid."""
        with pytest.raises(SSZSerializationError) as exception_info:
            Uint16ProgressiveList.decode_bytes(b"\x01")
        assert (
            str(exception_info.value)
            == "Uint16ProgressiveList: scope 1 not divisible by element size 2"
        )

    def test_variable_size_list_rejects_scope_below_offset_word(self) -> None:
        """A variable-size list requires at least one offset word in the payload."""
        # An offset word is 4 bytes, so 3 bytes cannot even hold the first one.
        with pytest.raises(SSZSerializationError) as exception_info:
            VariableContainerProgressiveList.decode_bytes(b"\x00\x00\x00")
        assert (
            str(exception_info.value)
            == "VariableContainerProgressiveList: scope 3 too small, expected at least 4"
        )

    def test_variable_size_list_rejects_first_offset_past_scope(self) -> None:
        """A first offset larger than the available scope is invalid."""
        # The first offset is the table's own width, so 100 claims a 100-byte table
        # inside a 4-byte payload, leaving every body outside the input.
        with pytest.raises(SSZSerializationError) as exception_info:
            VariableContainerProgressiveList.decode_bytes(b"\x64\x00\x00\x00")
        assert (
            str(exception_info.value)
            == "VariableContainerProgressiveList: first offset 100 runs past the scope of 4"
        )

    def test_variable_size_list_rejects_misaligned_first_offset(self) -> None:
        """A first offset that is not a multiple of the offset width is invalid."""
        # The table is a whole number of 4-byte words, so 5 divides into no element count.
        with pytest.raises(SSZSerializationError) as exception_info:
            VariableContainerProgressiveList.decode_bytes(b"\x05\x00\x00\x00\x00\x00\x00\x00")
        assert (
            str(exception_info.value)
            == "VariableContainerProgressiveList: first offset 5 is not a multiple of 4"
        )

    def test_variable_size_list_rejects_zero_first_offset(self) -> None:
        """A zero first offset is contradictory and rejected before any body is read."""
        # Zero says the table is empty, so there are no elements — yet the payload then
        # claims one body spanning the whole budget.
        with pytest.raises(SSZSerializationError) as exception_info:
            VariableContainerProgressiveList.decode_bytes(bytes.fromhex("00000000aabbccdd"))
        assert (
            str(exception_info.value)
            == "VariableContainerProgressiveList: first offset 0 "
            + "is below the table's own width of 4"
        )

    def test_variable_size_list_rejects_non_monotonic_offsets(self) -> None:
        """A later offset smaller than an earlier one means a body would have negative width."""
        # Fixture state: first offset 8, so the table is 8 bytes and holds 2 offsets.
        #
        # Mutation: the second offset points behind the first.
        #
        #     offsets       8       6
        #     spans         8..6            -> negative width, refused at element 0
        encoded_bytes = b"\x08\x00\x00\x00\x06\x00\x00\x00" + b"\x00" * 12
        with pytest.raises(SSZSerializationError) as exception_info:
            VariableContainerProgressiveList.decode_bytes(encoded_bytes)
        assert (
            str(exception_info.value)
            == "VariableContainerProgressiveList[0]: offset 8 is above the next offset 6"
        )

    def test_variable_size_list_rejects_interior_offset_past_scope(self) -> None:
        """A last offset past the byte budget is reported as the overrun it is."""
        # Fixture state: 20 bytes of payload, so the budget closing the table is 20.
        #
        # Mutation: the second offset points past the end of the input.
        #
        #     offsets       8       100
        #     spans         8..100  100..20  -> element 1 starts past the budget
        encoded_bytes = b"\x08\x00\x00\x00\x64\x00\x00\x00" + b"\x00" * 12
        with pytest.raises(SSZSerializationError) as exception_info:
            VariableContainerProgressiveList.decode_bytes(encoded_bytes)
        assert (
            str(exception_info.value)
            == "VariableContainerProgressiveList[1]: offset 100 runs past the scope of 20"
        )

    def test_variable_size_list_single_element_decodes(self) -> None:
        """A single-element list reads no further offsets after the first."""
        element = VariableContainer(a=Uint8(1), b=Uint16List4(data=[Uint16(10)]))
        encoded = VariableContainerProgressiveList(data=[element]).encode_bytes()

        assert VariableContainerProgressiveList.decode_bytes(
            encoded
        ) == VariableContainerProgressiveList(data=[element])

    def test_stream_serialization_reports_the_written_byte_count(self) -> None:
        """Serializing to a stream returns the total width, offsets and bodies included."""
        instance = NestedProgressiveList(
            data=[
                Uint16ProgressiveList(data=[Uint16(1), Uint16(2)]),
                Uint16ProgressiveList(data=[Uint16(3)]),
            ]
        )
        stream = io.BytesIO()
        written = instance.serialize(stream)

        assert written == len(stream.getvalue())
        stream.seek(0)
        assert NestedProgressiveList.deserialize(stream, scope=written) == instance


class TestSequenceDefaults:
    """The default value of the three sequence shapes, and the zeroed check over it."""

    def test_vector_default_is_the_element_default_at_every_position(self) -> None:
        """The spec gives a vector the element default, LENGTH times."""
        assert Uint8Vector4() == Uint8Vector4(data=[Uint8(0)] * 4)
        assert len(Uint8Vector4()) == 4

    def test_vector_of_composite_elements_defaults_element_by_element(self) -> None:
        """A composite element type contributes its own default at each position."""
        zero_element = FixedContainer(a=Uint8(0), b=Uint16(0))
        assert FixedContainerVector2() == FixedContainerVector2(data=[zero_element, zero_element])

    def test_vector_empty_input_stays_a_length_error(self) -> None:
        """Zero elements is a count mismatch against LENGTH, never a request for the default."""
        with pytest.raises(ValueOrValidationError) as exception_info:
            Uint8Vector4(data=[])
        assert str(exception_info.value) == "Uint8Vector4 requires exactly 4 elements, got 0"

    def test_vector_data_is_no_longer_a_required_field(self) -> None:
        """The elements carry a default, so Pydantic itself reports them as optional."""
        assert Uint8Vector4.model_fields["data"].is_required() is False

    def test_a_vector_missing_its_declarations_reports_its_own_error(self) -> None:
        """A shape with no element type or length keeps the inherited empty default."""
        # The default is injected only once both declarations are present, so such a shape
        # falls through to its own declaration check rather than a new failure mode.

        class MissingBothDeclarations(Vector):
            pass

        with pytest.raises(TypeOrValidationError) as exception_info:
            MissingBothDeclarations()
        expected = "MissingBothDeclarations must define ELEMENT_TYPE and LENGTH"
        assert str(exception_info.value) == expected

    def test_a_vector_missing_only_its_length_reports_its_own_error(self) -> None:
        """An element type alone is not enough to know how many defaults to build."""

        class MissingOnlyLength(Vector[Uint8]):
            pass

        with pytest.raises(TypeOrValidationError) as exception_info:
            MissingOnlyLength()
        assert str(exception_info.value) == "MissingOnlyLength must define ELEMENT_TYPE and LENGTH"

    def test_each_default_element_is_built_on_its_own(self) -> None:
        """One instance placed at every position would alias, and elements are mutable."""
        # Across two instances: neither default shares an element with the other.
        assert FixedContainerVector2().data[0] is not FixedContainerVector2().data[0]
        # Within one instance: the two positions hold two distinct values.
        instance = FixedContainerVector2()
        assert instance.data[0] is not instance.data[1]
        # So mutating position 0 moves nothing else, here or in the next default built.
        instance.data[0].a = Uint8(9)
        assert instance.data[1].a == Uint8(0)
        assert FixedContainerVector2() == FixedContainerVector2(
            data=[FixedContainer(a=Uint8(0), b=Uint16(0))] * 2
        )

    def test_list_and_progressive_list_default_to_empty(self) -> None:
        """A variable-size shape defaults to its empty value, whatever its element type."""
        assert Uint8List4() == Uint8List4(data=[])
        assert Uint8ProgressiveList() == Uint8ProgressiveList(data=[])

    def test_each_list_default_holds_its_own_element_sequence(self) -> None:
        """Appending to one empty default leaves the next one empty."""
        first = Uint8List4()
        first.append(Uint8(1))
        assert first == Uint8List4(data=[Uint8(1)])
        assert Uint8List4() == Uint8List4(data=[])

    @pytest.mark.parametrize(
        "default_value, non_default_value",
        [
            # A vector of zeros is the default; setting element 0 moves away from it.
            pytest.param(
                Uint8Vector4(),
                Uint8Vector4(data=[Uint8(1), Uint8(0), Uint8(0), Uint8(0)]),
                id="vector",
            ),
            # An empty list is the default; one zero element is a different value of length 1.
            pytest.param(Uint8List4(), Uint8List4(data=[Uint8(0)]), id="list"),
            pytest.param(
                Uint8ProgressiveList(),
                Uint8ProgressiveList(data=[Uint8(0)]),
                id="progressive_list",
            ),
        ],
    )
    def test_is_zero_holds_only_for_the_default(
        self, default_value: Any, non_default_value: Any
    ) -> None:
        """A default reads as zeroed and any other value of the same type does not."""
        assert default_value.is_zero() is True
        assert non_default_value.is_zero() is False

    @pytest.mark.parametrize(
        "default_value, expected_encoding",
        [
            # Four zero Uint8 pack into four zero bytes.
            pytest.param(Uint8Vector4(), b"\x00\x00\x00\x00", id="vector"),
            # An empty sequence has no body at all, and no length prefix on the wire.
            pytest.param(Uint8List4(), b"", id="list"),
            pytest.param(Uint8ProgressiveList(), b"", id="progressive_list"),
        ],
    )
    def test_the_default_round_trips(self, default_value: Any, expected_encoding: bytes) -> None:
        """Each default encodes to known bytes and decodes back unchanged."""
        assert default_value.encode_bytes() == expected_encoding
        assert type(default_value).decode_bytes(expected_encoding) == default_value

    def test_a_list_of_unions_defaults_to_empty(self) -> None:
        """A list's default is empty regardless of element type, so a union element is fine."""
        assert FixedContainerUnionList2() == FixedContainerUnionList2(data=[])
        assert FixedContainerUnionList2().is_zero() is True

    def test_a_vector_of_unions_has_no_default(self) -> None:
        """A vector needs an element default at every position, and a union has none."""
        with pytest.raises(SSZDefaultError, match=r"^FixedContainerUnion has no default value$"):
            FixedContainerUnionVector2()

    def test_a_vector_of_unions_still_builds_from_given_elements(self) -> None:
        """Only the absence of elements fails: the shape itself is perfectly constructible."""
        element = FixedContainerUnion(
            selector=Uint8(1), data=FixedContainer(a=Uint8(1), b=Uint16(2))
        )
        assert len(FixedContainerUnionVector2(data=[element, element])) == 2


class TestJsonSerialization:
    """Tests for the JSON field serializer on SSZ sequences."""

    def test_byte_array_elements_render_as_hex_strings(self) -> None:
        """Byte-array leaves render as 0x-prefixed hex strings in JSON output."""
        instance = Bytes32List32(data=[Bytes32.zero()])

        assert instance.model_dump(mode="json") == {"data": ["0x" + ("00" * 32)]}

    def test_boolean_elements_render_as_true_false(self) -> None:
        """Booleans are excluded from the int branch and stay as true/false."""
        instance = BooleanList4(data=[Boolean(True), Boolean(False), Boolean(True)])

        assert instance.model_dump(mode="json") == {"data": [True, False, True]}

    def test_container_elements_pass_through_to_pydantic(self) -> None:
        """Container elements fall through the else branch and recurse via Pydantic."""
        instance = FixedContainerList2(
            data=[
                FixedContainer(a=Uint8(1), b=Uint16(2)),
                FixedContainer(a=Uint8(3), b=Uint16(4)),
            ]
        )

        assert instance.model_dump(mode="json") == {"data": [{"a": 1, "b": 2}, {"a": 3, "b": 4}]}


@given(values=st.lists(st.integers(min_value=0, max_value=2**16 - 1), max_size=4))
def test_list_round_trip_random_values(values: list[int]) -> None:
    """Any element sequence up to the limit, including empty, round-trips unchanged."""
    instance = Uint16List4(data=[Uint16(value) for value in values])
    assert Uint16List4.decode_bytes(instance.encode_bytes()) == instance


@given(values=st.lists(st.integers(min_value=0, max_value=255), min_size=4, max_size=4))
def test_vector_round_trip_random_values(values: list[int]) -> None:
    """Any fixed-length element sequence round-trips unchanged."""
    instance = Uint8Vector4(data=[Uint8(value) for value in values])
    assert Uint8Vector4.decode_bytes(instance.encode_bytes()) == instance


@given(values=st.lists(st.integers(min_value=0, max_value=2**16 - 1), max_size=100))
def test_progressive_list_round_trip_random_values(values: list[int]) -> None:
    """Any element count, including counts past a bounded list's usual limits, round-trips."""
    instance = Uint16ProgressiveList(data=[Uint16(value) for value in values])
    assert Uint16ProgressiveList.decode_bytes(instance.encode_bytes()) == instance


@given(
    inner_values=st.lists(
        st.lists(st.integers(min_value=0, max_value=2**16 - 1), max_size=6), max_size=6
    )
)
def test_progressive_list_of_progressive_lists_round_trip_random_values(
    inner_values: list[list[int]],
) -> None:
    """Variable-size elements round-trip through the offset table at any nesting width."""
    instance = NestedProgressiveList(
        data=[
            Uint16ProgressiveList(data=[Uint16(value) for value in inner]) for inner in inner_values
        ]
    )
    assert NestedProgressiveList.decode_bytes(instance.encode_bytes()) == instance


@given(values=st.lists(st.integers(min_value=0, max_value=2**16 - 1), max_size=32))
def test_progressive_and_bounded_list_encode_identically(values: list[int]) -> None:
    """The two list shapes agree byte for byte on every sequence they both hold."""
    elements = [Uint16(value) for value in values]
    progressive_bytes = Uint16ProgressiveList(data=elements).encode_bytes()

    assert progressive_bytes == Uint16List32(data=elements).encode_bytes()


class TestDeclarationIsolation:
    """A shape installing its own default leaves the field it inherits alone."""

    def test_a_vector_declaration_does_not_change_other_shapes(self) -> None:
        """A vector's default reaches its own type and no other."""
        # The contents field is declared once, on the base the three shapes share.
        #
        # A vector installs its default by writing through that field's descriptor, so a
        # shape declared after it would inherit the vector's default if that write reached
        # the shared descriptor rather than a copy of it.

        class LaterVector(Vector[Uint8]):
            LENGTH = 7

        class LaterList(List[Uint8]):
            LIMIT = 7

        class LaterProgressive(ProgressiveList[Uint8]):
            pass

        # The vector gets the default it declared: 7 zero bytes.
        assert list(LaterVector()) == [Uint8(0)] * 7

        # Every other shape keeps the empty default of the shared base.
        assert len(LaterList()) == 0
        assert len(LaterProgressive()) == 0

        # A shape declared before the vector is untouched too.
        assert len(Uint16List4()) == 0

    def test_two_vector_declarations_keep_their_own_defaults(self) -> None:
        """A later vector does not reach back into an earlier one."""

        class FirstVector(Vector[Uint8]):
            LENGTH = 3

        class SecondVector(Vector[Uint8]):
            LENGTH = 9

        # Both counts survive, so neither declaration overwrote the other's default.
        assert len(FirstVector()) == 3
        assert len(SecondVector()) == 9


class TestZeroLengthVector:
    """The SSZ spec writes a vector as Vector[type, N] with N > 0."""

    def test_zero_length_is_refused_at_declaration(self) -> None:
        """A vector of no elements is refused where it is written, not where it is used."""
        # A zero-length vector has no offset table, so a variable-size body would have
        # nowhere to be read from.
        with pytest.raises(SSZValueError) as exception_info:

            class EmptyVector(Vector[Uint8]):
                LENGTH = 0

        assert str(exception_info.value) == "EmptyVector: LENGTH must be positive, got 0"

    def test_negative_length_is_refused_at_declaration(self) -> None:
        """A negative count is refused the same way, and for the same reason."""
        with pytest.raises(SSZValueError) as exception_info:

            class NegativeVector(Vector[Uint8]):
                LENGTH = -1

        assert str(exception_info.value) == "NegativeVector: LENGTH must be positive, got -1"


class TestNegativeListLimit:
    """A bound counts the elements a list may hold, and no count is below zero."""

    def test_a_negative_limit_is_refused_at_declaration(self) -> None:
        """A negative bound is refused where it is written, not where it is used."""
        # A negative bound admits no value at all: the empty list already breaks it, so
        # the type has no default and no constructor call can succeed.
        with pytest.raises(SSZValueError) as exception_info:

            class NegativeList(List[Uint8]):
                LIMIT = -1

        assert str(exception_info.value) == "NegativeList: LIMIT must not be negative, got -1"

    def test_a_limit_of_zero_admits_the_empty_value_and_nothing_else(self) -> None:
        """A bound of zero is where the line falls: one value, and it holds no elements."""

        class EmptyList(List[Uint8]):
            LIMIT = 0

        assert EmptyList.decode_bytes(b"") == EmptyList()

        with pytest.raises(SSZValueError) as exception_info:
            EmptyList.decode_bytes(b"\x01")

        assert str(exception_info.value) == "EmptyList exceeds limit of 0, got 1"


class TestJsonRoundTrip:
    """Whatever a sequence renders to JSON, it reads back in."""

    def test_a_sequence_of_containers_round_trips(self) -> None:
        """A container element renders as a mapping, and validates back from one."""
        # Rendering:  {"data": [{"a": 1, "b": [2, 3]}]}
        instance = VariableContainerList2(
            data=[VariableContainer(a=Uint8(1), b=Uint16List4(data=[Uint16(2), Uint16(3)]))]
        )

        assert VariableContainerList2.model_validate_json(instance.model_dump_json()) == instance

    def test_a_sequence_of_byte_arrays_round_trips(self) -> None:
        """A fixed byte array renders as a 0x-prefixed hex string, and validates back."""
        # Rendering:  {"data": ["0xaaaa...", "0xbbbb..."]}
        instance = Bytes32List32(data=[Bytes32(b"\xaa" * 32), Bytes32(b"\xbb" * 32)])

        assert Bytes32List32.model_validate_json(instance.model_dump_json()) == instance

    def test_a_bare_hex_string_element_is_still_refused(self) -> None:
        """Only the 0x-prefixed rendering is accepted, never a bare hex string."""
        # A byte count read as characters is the mistake this refusal exists to catch,
        # so an unprefixed string stays a type error rather than becoming 64 bytes.
        with pytest.raises(SSZTypeMismatch) as exception_info:
            Bytes32List32(data=cast(Any, ["ab" * 32]))

        assert str(exception_info.value) == "Expected Bytes32, got str"

    def test_a_sequence_of_uints_round_trips(self) -> None:
        """An integer leaf renders as a plain int, which is already an ancestor class."""
        instance = Uint16List4(data=[Uint16(7), Uint16(8)])

        assert Uint16List4.model_validate_json(instance.model_dump_json()) == instance

    def test_a_nested_sequence_round_trips(self) -> None:
        """A sequence element is Pydantic-backed, so it renders and validates as a mapping."""
        # Rendering:  {"data": [{"data": [1, 2]}, {"data": []}]}
        instance = NestedProgressiveList(
            data=[
                Uint16ProgressiveList(data=[Uint16(1), Uint16(2)]),
                Uint16ProgressiveList(data=[]),
            ]
        )

        assert NestedProgressiveList.model_validate_json(instance.model_dump_json()) == instance


class TestTruncatedOffsetTable:
    """A stream that ends mid-table is refused before any span is derived from it."""

    def test_a_vector_refuses_a_table_the_stream_cannot_back(self) -> None:
        """A budget larger than the stream is caught while the table is read."""
        # A 2-element vector needs a table of 2 offsets, so 8 bytes before any body.
        #
        # Fixture state: the caller promises 20 bytes, but the stream holds only 4.
        #
        #     promised   [ off_0 | off_1 | bodies... ]   20 bytes
        #     actual     [ off_0 ]                        4 bytes
        #
        # This is what a corrupt outer offset table looks like from the inside: the
        # span handed down is wider than the bytes that back it.
        stream = io.BytesIO(b"\x08\x00\x00\x00")
        with pytest.raises(SSZSerializationError) as exception_info:
            VariableContainerVector2.deserialize(stream, 20)

        assert str(exception_info.value) == "VariableContainerVector2: expected 8 bytes, got 4"

    def test_a_list_refuses_a_table_the_stream_cannot_back(self) -> None:
        """The same truncation is caught when the count came from the first offset."""
        # First offset 12 means a 12-byte table, so 3 elements and 2 offsets still to read.
        #
        # Fixture state: the caller promises 24 bytes, but only the first offset is there.
        stream = io.BytesIO(b"\x0c\x00\x00\x00")
        with pytest.raises(SSZSerializationError) as exception_info:
            VariableContainerProgressiveList.deserialize(stream, 24)

        assert (
            str(exception_info.value) == "VariableContainerProgressiveList: expected 8 bytes, got 0"
        )


class TestNegativeScope:
    """A byte budget below zero describes no payload, and no shape decodes one."""

    def test_a_list_refuses_a_budget_below_zero(self) -> None:
        """A negative budget over fixed-size elements is refused rather than read as empty."""
        # Fixed-size elements recover their count by dividing the budget by the stride.
        # A budget of -4 divides into -4 elements, and iterating that many yields none,
        # so the input would decode to the empty list while consuming nothing.
        stream = io.BytesIO(b"\x01\x02\x03\x04")
        with pytest.raises(SSZSerializationError) as exception_info:
            Uint8List4.deserialize(stream, -4)

        assert str(exception_info.value) == "Uint8List4: scope -4 is negative"
        assert stream.tell() == 0

    def test_a_progressive_list_refuses_a_budget_below_zero(self) -> None:
        """The unbounded shape refuses it on the same grounds, holding no capacity to trip."""
        with pytest.raises(SSZSerializationError) as exception_info:
            Uint8ProgressiveList.deserialize(io.BytesIO(b"\x01"), -1)

        assert str(exception_info.value) == "Uint8ProgressiveList: scope -1 is negative"

    def test_a_vector_refuses_a_budget_below_zero(self) -> None:
        """A vector needs an exact width, and no width is negative."""
        with pytest.raises(SSZSerializationError) as exception_info:
            Uint8Vector4.deserialize(io.BytesIO(b"\x01\x02\x03\x04"), -4)

        assert str(exception_info.value) == "Uint8Vector4: expected 4 bytes, got -4"

    def test_a_variable_size_vector_refuses_a_budget_below_zero(self) -> None:
        """A table of its own width does not fit in a negative budget either."""
        with pytest.raises(SSZSerializationError) as exception_info:
            VariableContainerVector2.deserialize(io.BytesIO(b"\x08\x00\x00\x00"), -8)

        assert (
            str(exception_info.value)
            == "VariableContainerVector2: scope -8 too small, expected at least 8"
        )

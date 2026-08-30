"""Unsigned Integer Type Tests."""

import io
import operator
from decimal import Decimal
from fractions import Fraction
from itertools import permutations
from typing import Any, Type

import pytest
from hypothesis import given, strategies as st
from pydantic import BaseModel, ValidationError

import ssz
from ssz import (
    Byte,
    Chunk,
    Container,
    List,
    ProgressiveList,
    Uint8,
    Uint16,
    Uint32,
    Uint64,
    Uint128,
    Uint256,
    Vector,
)
from ssz.exceptions import SSZTypeError, SSZValueError
from ssz.roots import hash_tree_root
from ssz.uint import BaseUint

ALL_UINT_TYPES = (Uint8, Uint16, Uint32, Uint64, Uint128, Uint256)
"""A collection of all Uint types to test against."""

CROSS_UINT_TYPE_PAIRS = list(permutations(ALL_UINT_TYPES, 2))
"""Every ordered pair of distinct unsigned integer widths."""


# Model classes for Pydantic validation tests
class UintModel(BaseModel):
    # Each width below restates this field as its own type.
    # The base says only that the field is there, and that validation decides what it holds.
    value: Any


class Uint8Model(UintModel):
    value: Uint8


class Uint16Model(UintModel):
    value: Uint16


class Uint32Model(UintModel):
    value: Uint32


class Uint64Model(UintModel):
    value: Uint64


class Uint128Model(UintModel):
    value: Uint128


class Uint256Model(UintModel):
    value: Uint256


UINT_MODELS: dict[Type[BaseUint], Type[UintModel]] = {
    Uint8: Uint8Model,
    Uint16: Uint16Model,
    Uint32: Uint32Model,
    Uint64: Uint64Model,
    Uint128: Uint128Model,
    Uint256: Uint256Model,
}
"""Mapping from Uint types to their corresponding Pydantic model classes."""


@pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
def test_pydantic_validation_accepts_valid_int(uint_class: Type[BaseUint]) -> None:
    """Tests that Pydantic validation correctly accepts a valid integer."""
    model = UINT_MODELS[uint_class]
    instance = model(value=10)
    validated_value = instance.value
    assert isinstance(validated_value, uint_class)
    assert validated_value == uint_class(10)


@pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
@pytest.mark.parametrize("invalid_value", [1.0, "1", True, False])
def test_pydantic_strict_mode_rejects_invalid_types(
    uint_class: Type[BaseUint], invalid_value: Any
) -> None:
    """Tests that Pydantic's strict mode rejects types that could be coerced to an int."""
    model = UINT_MODELS[uint_class]
    with pytest.raises(ValidationError):
        model(value=invalid_value)


@pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
@pytest.mark.parametrize(
    "invalid_value, expected_type_name",
    [
        (1.0, "float"),
        ("1", "str"),
        (True, "bool"),
        (False, "bool"),
        (b"1", "bytes"),
        (None, "NoneType"),
    ],
)
def test_instantiation_from_invalid_types_raises_error(
    uint_class: Type[BaseUint], invalid_value: Any, expected_type_name: str
) -> None:
    """Tests that instantiating with non-integer types raises SSZTypeError."""
    expected_message = f"expected int, got {expected_type_name}"
    with pytest.raises(SSZTypeError) as exception_info:
        uint_class(invalid_value)
    assert str(exception_info.value) == expected_message


@pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
def test_instantiation_and_type(uint_class: Type[BaseUint]) -> None:
    """Tests that Uint types are instances of int and their own class."""
    uint_instance = uint_class(5)
    assert isinstance(uint_instance, int)
    assert isinstance(uint_instance, BaseUint)
    assert isinstance(uint_instance, uint_class)


@pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
def test_instantiation_negative(uint_class: Type[BaseUint]) -> None:
    """Tests that instantiating with a negative number raises SSZValueError."""
    # A negative also indexes the shared table from the end, so this refusal blocks that.
    expected_message = f"-5 is out of range for {uint_class.__name__} [0, {2**uint_class.BITS - 1}]"
    with pytest.raises(SSZValueError) as exception_info:
        uint_class(-5)
    assert str(exception_info.value) == expected_message


@pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
def test_instantiation_too_large(uint_class: Type[BaseUint]) -> None:
    """Tests that instantiating with a value >= MAX raises SSZValueError."""
    max_value = 2**uint_class.BITS
    expected_message = f"{max_value} is out of range for {uint_class.__name__} [0, {max_value - 1}]"
    with pytest.raises(SSZValueError) as exception_info:
        uint_class(max_value)
    assert str(exception_info.value) == expected_message


@pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
def test_instantiation_from_another_uint_instance(uint_class: Type[BaseUint]) -> None:
    """
    An instance of any width is an acceptable input value for any other width.

    - A plain integer is not the only accepted input form.
    - The declared width of the input never leaks into the result.
    """
    for source_class in ALL_UINT_TYPES:
        # Invariant: an input already typed at some width is re-typed at the target width.
        #
        # Every width holds 5, so one value covers every ordered pair of widths:
        #
        #     input : 8-bit, 16-bit, 32-bit, 64-bit, 128-bit, 256-bit
        #     target: the parametrized width
        uint_instance = uint_class(source_class(5))
        # Widening and narrowing both land on the target width, never the input width.
        assert type(uint_instance) is uint_class
        # Equality is strict, so a matching value alone would not satisfy it.
        assert uint_instance == uint_class(5)


@pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
def test_instantiation_from_a_subclass_instance(uint_class: Type[BaseUint]) -> None:
    """A value whose class derives from the target class is accepted and re-typed."""
    # Applications derive semantic integer types from a width, such as a 64-bit slot number.
    subclass = type("Typed", (uint_class,), {})
    # The derived class inherits the width, so 5 is in range on both sides.
    uint_instance = subclass(5)
    # Construction moves the value one step up the hierarchy, from derived to base.
    assert type(uint_class(uint_instance)) is uint_class
    assert uint_class(uint_instance) == uint_class(5)


def test_instantiation_from_an_out_of_range_uint_instance() -> None:
    """A typed input above the target bound is reported as a range error."""
    # Fixture state: 256 sits inside a 16-bit input and above an 8-bit bound.
    #
    #     input : 256, valid in [0, 65535]
    #     target: bound is 255
    #     -> out of range, reported against the bound rather than as a type conflict
    expected_message = f"{2**8} is out of range for Uint8 [0, {2**8 - 1}]"
    with pytest.raises(SSZValueError) as exception_info:
        Uint8(Uint16(2**8))
    assert str(exception_info.value) == expected_message


@pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
def test_max_method_returns_correct_value(uint_class: Type[BaseUint]) -> None:
    """Tests that the max_value() class method returns the correct value."""
    expected_max_int = (2**uint_class.BITS) - 1
    assert uint_class.max_value() == uint_class(expected_max_int)


@pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
def test_arithmetic_operators(uint_class: Type[BaseUint]) -> None:
    """Tests all standard arithmetic operators."""
    # Use smaller values for high-bit integers to avoid massive numbers
    a_value, b_value = (100, 3) if uint_class.BITS > 8 else (20, 3)
    left = uint_class(a_value)
    right = uint_class(b_value)
    max_int = (2**uint_class.BITS) - 1
    max_value = uint_class(max_int)
    name = uint_class.__name__

    # Addition
    assert left + right == uint_class(a_value + b_value)
    expected_message = f"{max_int + b_value} is out of range for {name} [0, {max_int}]"
    with pytest.raises(SSZValueError) as exception_info:
        _ = max_value + right
    assert str(exception_info.value) == expected_message

    # Subtraction
    assert left - right == uint_class(a_value - b_value)
    expected_message = f"{b_value - a_value} is out of range for {name} [0, {max_int}]"
    with pytest.raises(SSZValueError) as exception_info:
        _ = right - left
    assert str(exception_info.value) == expected_message

    # Multiplication
    assert left * right == uint_class(a_value * b_value)
    expected_message = f"{max_int * b_value} is out of range for {name} [0, {max_int}]"
    with pytest.raises(SSZValueError) as exception_info:
        _ = max_value * right
    assert str(exception_info.value) == expected_message

    # Floor Division
    assert left // right == uint_class(a_value // b_value)

    # Modulo
    assert left % right == uint_class(a_value % b_value)

    # Exponentiation
    assert uint_class(b_value) ** uint_class(4) == uint_class(b_value**4)
    if uint_class.BITS <= 16:  # Pow gets too big quickly
        expected_message = f"{a_value**b_value} is out of range for {name} [0, {max_int}]"
        with pytest.raises(SSZValueError) as exception_info:
            _ = left**right
        assert str(exception_info.value) == expected_message


@pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
def test_reverse_arithmetic_operators_with_a_bare_literal(uint_class: Type[BaseUint]) -> None:
    """A literal on the left keeps the typed operand's type, since it carries no unit."""
    # 20 and 3 so that every result below fits in eight bits as well as in 256.
    assert 20 + uint_class(3) == uint_class(23)
    assert 20 - uint_class(3) == uint_class(17)
    assert 20 * uint_class(3) == uint_class(60)
    assert 20 // uint_class(3) == uint_class(6)
    assert 20 % uint_class(3) == uint_class(2)
    # The result is typed, not a plain int, so the unit survives the reflected call.
    assert type(20 + uint_class(3)) is uint_class


@pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
def test_divmod(uint_class: Type[BaseUint]) -> None:
    """Tests the divmod function."""
    quotient, remainder = divmod(uint_class(100), uint_class(3))
    assert quotient == uint_class(33)
    assert remainder == uint_class(1)
    assert isinstance(quotient, uint_class)
    assert isinstance(remainder, uint_class)

    # A literal divided by a typed value keeps the type on both halves of the pair.
    quotient, remainder = divmod(100, uint_class(3))
    assert (quotient, remainder) == (uint_class(33), uint_class(1))
    assert type(quotient) is uint_class
    assert type(remainder) is uint_class

    # A bool is not a bare literal: it counts nothing, so it is still refused.
    expected_message = f"Unsupported operand type(s) for divmod: '{uint_class.__name__}' and 'bool'"
    with pytest.raises(TypeError) as exception_info:
        _ = divmod(uint_class(10), True)
    assert str(exception_info.value) == expected_message


@pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
def test_inplace_immutability(uint_class: Type[BaseUint]) -> None:
    """Tests that in-place operators return a new instance."""
    value1 = uint_class(10)
    value2 = value1
    value1 += uint_class(5)

    assert isinstance(value1, uint_class)
    assert value1 == uint_class(15)
    # The original variable reference is unchanged
    assert value2 == uint_class(10)


@pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
def test_bitwise_operators(uint_class: Type[BaseUint]) -> None:
    """Tests all standard bitwise operators."""
    left = uint_class(0b1100)  # 12
    right = uint_class(0b1010)  # 10
    name = uint_class.__name__

    assert left & right == uint_class(0b1000)
    assert left | right == uint_class(0b1110)
    assert left ^ right == uint_class(0b0110)
    assert left << uint_class(2) == uint_class(0b110000)
    assert left >> uint_class(2) == uint_class(0b11)

    # A bare literal is admitted as a mask or a shift count, and keeps the type.
    assert left & 1 == uint_class(0)
    assert left | 1 == uint_class(0b1101)
    assert left ^ 1 == uint_class(0b1101)
    assert left << 1 == uint_class(0b11000)
    assert left >> 1 == uint_class(0b110)
    assert type(left & 1) is uint_class

    # A bool is not a literal count, so every one of the five still refuses it.
    for operator_symbol, apply in (
        ("&", lambda: left & True),
        ("|", lambda: left | True),
        ("^", lambda: left ^ True),
        ("<<", lambda: left << True),
        (">>", lambda: left >> True),
    ):
        expected_message = f"Unsupported operand type(s) for {operator_symbol}: '{name}' and 'bool'"
        with pytest.raises(TypeError) as exception_info:
            apply()
        assert str(exception_info.value) == expected_message


@pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
def test_comparison_with_same_type(uint_class: Type[BaseUint]) -> None:
    """Tests all comparison operators between two Uint instances."""
    assert uint_class(5) < uint_class(10)
    assert uint_class(5) <= uint_class(10)
    assert uint_class(10) == uint_class(10)
    assert uint_class(10) != uint_class(5)
    assert uint_class(10) > uint_class(5)
    assert uint_class(10) >= uint_class(5)


@pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
def test_all_comparisons_with_a_bare_literal(uint_class: Type[BaseUint]) -> None:
    """A bare literal compares in either position, because it carries no unit."""
    assert uint_class(10) == 10
    assert not (10 != uint_class(10))
    assert uint_class(10) > 5
    # 5 < uint(10) routes to uint(10).__gt__(5) because uint is a strict int subclass.
    assert 5 < uint_class(10)
    assert uint_class(10) >= 10
    # 10 <= uint(10) routes to uint(10).__ge__(10) by subclass priority.
    assert 10 <= uint_class(10)
    assert uint_class(10) <= 10
    assert uint_class(5) < 10


@pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
def test_all_comparisons_with_other_types_raise_error(
    uint_class: Type[BaseUint],
) -> None:
    """Tests that all comparisons with unrelated types raise TypeError."""
    name = uint_class.__name__

    # A bool is an int subclass but not an int, so it is not a bare literal.
    for operator_symbol, apply in (
        ("==", lambda: uint_class(1) == True),  # noqa: E712
        ("!=", lambda: uint_class(1) != True),  # noqa: E712
        ("<", lambda: uint_class(1) < True),
        ("<=", lambda: uint_class(1) <= True),
        (">", lambda: uint_class(1) > True),
        (">=", lambda: uint_class(1) >= True),
    ):
        expected_message = f"Unsupported operand type(s) for {operator_symbol}: '{name}' and 'bool'"
        with pytest.raises(TypeError) as exception_info:
            apply()
        assert str(exception_info.value) == expected_message

    # A string is not an int at all.
    expected_message = f"Unsupported operand type(s) for ==: '{name}' and 'str'"
    with pytest.raises(TypeError) as exception_info:
        _ = uint_class(10) == "10"
    assert str(exception_info.value) == expected_message


@pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
def test_repr_and_str(uint_class: Type[BaseUint]) -> None:
    """Tests the string and official representations."""
    uint_instance = uint_class(42)
    assert str(uint_instance) == "42"
    assert repr(uint_instance) == f"{uint_class.__name__}(42)"


@pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
def test_hash(uint_class: Type[BaseUint]) -> None:
    """Tests that a uint hashes exactly as the integer it holds."""
    assert hash(uint_class(1)) == hash(1)
    assert hash(uint_class(1)) == hash(uint_class(1))
    assert hash(uint_class(1)) != hash(uint_class(2))


@pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
def test_index_list_access(uint_class: Type[BaseUint]) -> None:
    """Tests that Uint types can be used directly for list indexing."""
    letters = ["a", "b", "c", "d", "e"]
    index = uint_class(2)
    assert letters[index] == "c"
    assert letters[uint_class(0)] == "a"
    assert letters[uint_class(4)] == "e"


@pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
def test_index_slicing(uint_class: Type[BaseUint]) -> None:
    """Tests that Uint types can be used in slice operations."""
    numbers = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    start = uint_class(2)
    stop = uint_class(7)
    step = uint_class(2)

    assert numbers[start:stop] == [2, 3, 4, 5, 6]
    assert numbers[:stop] == [0, 1, 2, 3, 4, 5, 6]
    assert numbers[start:] == [2, 3, 4, 5, 6, 7, 8, 9]
    assert numbers[start:stop:step] == [2, 4, 6]


@pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
def test_index_range(uint_class: Type[BaseUint]) -> None:
    """Tests that Uint types can be used in range()."""
    stop = uint_class(5)
    single_argument_range = list(range(stop))
    assert single_argument_range == [0, 1, 2, 3, 4]

    start = uint_class(2)
    stop = uint_class(8)
    step = uint_class(2)
    strided_range = list(range(start, stop, step))
    assert strided_range == [2, 4, 6]


@pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
def test_index_hex_bin_oct(uint_class: Type[BaseUint]) -> None:
    """Tests that Uint types work with hex(), bin(), oct()."""
    uint_instance = uint_class(42)
    assert hex(uint_instance) == "0x2a"
    assert bin(uint_instance) == "0b101010"
    assert oct(uint_instance) == "0o52"


@pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
def test_index_operator_index(uint_class: Type[BaseUint]) -> None:
    """Tests that operator.index() works with Uint types."""
    uint_instance = uint_class(42)
    assert operator.index(uint_instance) == 42
    assert isinstance(operator.index(uint_instance), int)


class TestUintDefault:
    """The default value of every unsigned integer width, and the zeroed check over it."""

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_construction_without_an_argument_is_zero(self, uint_class: Type[BaseUint]) -> None:
        """The spec gives a uint the default zero, whatever its width."""
        assert uint_class() == uint_class(0)

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_the_default_is_zeroed(self, uint_class: Type[BaseUint]) -> None:
        """A default equals a freshly built default of its own type, so it reads as zeroed."""
        assert uint_class().is_zero() is True

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_a_non_default_value_is_not_zeroed(self, uint_class: Type[BaseUint]) -> None:
        """One and the widest value the type holds are both away from the default."""
        assert uint_class(1).is_zero() is False
        assert uint_class.max_value().is_zero() is False

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_the_default_round_trips(self, uint_class: Type[BaseUint]) -> None:
        """The default encodes to its own width in zero bytes and decodes back unchanged."""
        default_value = uint_class()
        # One zero byte for a uint8, two for a uint16, and so on up to 32 for a uint256.
        assert default_value.encode_bytes() == b"\x00" * (uint_class.BITS // 8)
        assert uint_class.decode_bytes(default_value.encode_bytes()) == default_value


class TestUintSSZ:
    """A collection of tests for the SSZ interface of Uint types."""

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_is_fixed_size(self, uint_class: Type[BaseUint]) -> None:
        """Tests that all Uint types are correctly identified as fixed-size."""
        assert uint_class.is_fixed_size() is True

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_get_byte_length(self, uint_class: Type[BaseUint]) -> None:
        """Tests that the byte length is correctly calculated from the bit width."""
        expected_length = uint_class.BITS // 8
        assert uint_class.get_byte_length() == expected_length

    @pytest.mark.parametrize(
        "uint_class, value, expected_hex",
        [
            (Uint8, 0x00, "00"),
            (Uint8, 0x01, "01"),
            (Uint8, 0xAB, "ab"),
            (Uint16, 0x0000, "0000"),
            (Uint16, 0xABCD, "cdab"),
            (Uint32, 0x00000000, "00000000"),
            (Uint32, 0x01234567, "67452301"),
            (Uint64, 0x0000000000000000, "0000000000000000"),
            (Uint64, 0x0123456789ABCDEF, "efcdab8967452301"),
        ],
    )
    def test_encode_decode_roundtrip(
        self, uint_class: Type[BaseUint], value: int, expected_hex: str
    ) -> None:
        """Tests the roundtrip of encoding and decoding for specific values."""
        # Create an instance of the specific Uint type.
        instance = uint_class(value)

        # 1. Test encoding (serialization)
        encoded = instance.encode_bytes()
        assert encoded.hex() == expected_hex

        # 2. Test decoding (deserialization)
        decoded = uint_class.decode_bytes(encoded)
        assert decoded == instance

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_decode_bytes_invalid_length(self, uint_class: Type[BaseUint]) -> None:
        """Tests that decode_bytes raises SSZValueError for wrong length data."""
        # Create byte string that is one byte too short.
        expected_length = uint_class.get_byte_length()
        invalid_data = b"\x00" * (expected_length - 1)
        expected_message = (
            f"{uint_class.__name__} needs {expected_length} bytes, "
            + f"the input holds {expected_length - 1}"
        )
        with pytest.raises(SSZValueError) as exception_info:
            uint_class.decode_bytes(invalid_data)
        assert str(exception_info.value) == expected_message

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_serialize_deserialize_stream_roundtrip(self, uint_class: Type[BaseUint]) -> None:
        """Tests the round trip of serializing to and deserializing from a stream."""
        # Create a test instance with a non-zero value.
        instance = uint_class(123)
        byte_length = uint_class.get_byte_length()

        # 1. Test serialization to a stream
        stream = io.BytesIO()
        bytes_written = instance.serialize(stream)
        assert bytes_written == byte_length
        stream.seek(0)  # Rewind stream to the beginning for reading.
        assert stream.read() == instance.encode_bytes()

        # 2. Test deserialization from a stream
        stream.seek(0)  # Rewind again for the deserialization test.
        decoded = uint_class.deserialize(stream, scope=byte_length)
        assert decoded == instance

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_deserialize_invalid_scope(self, uint_class: Type[BaseUint]) -> None:
        """Tests that deserialize raises an SSZValueError if the scope is incorrect."""
        byte_length = uint_class.get_byte_length()
        stream = io.BytesIO(b"\x00" * byte_length)
        invalid_scope = byte_length - 1
        expected_message = (
            f"{uint_class.__name__} spans {byte_length} bytes, and the budget is {invalid_scope}"
        )
        with pytest.raises(SSZValueError) as exception_info:
            uint_class.deserialize(stream, scope=invalid_scope)
        assert str(exception_info.value) == expected_message

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_deserialize_stream_too_short(self, uint_class: Type[BaseUint]) -> None:
        """Tests that deserialize raises SSZValueError if stream ends prematurely."""
        byte_length = uint_class.get_byte_length()
        # Create a stream that is shorter than what the type requires.
        stream = io.BytesIO(b"\x00" * (byte_length - 1))
        expected_message = (
            f"{uint_class.__name__} needs {byte_length} bytes, the input holds {byte_length - 1}"
        )
        with pytest.raises(SSZValueError) as exception_info:
            uint_class.deserialize(stream, scope=byte_length)
        assert str(exception_info.value) == expected_message


class AccessorNarrowerThanTheWidth(Uint64):
    """A subtype that answers the width question with something other than its declared width."""

    @classmethod
    def get_byte_length(cls) -> int:
        """Answer with half the width the type is declared at."""
        return 4


class TestTheDeclaredWidthIsTheWireWidth:
    """
    ``BYTE_LENGTH`` is the width both directions of the wire read.

    An encode has always taken the width off the declared attribute, so a subtype that
    overrides only the accessor cannot move the width it writes at. A decode reads the
    same attribute, which is what keeps the pair total: the bytes such a subtype writes
    are bytes it reads back. The accessor is left to the callers that ask a type its
    width, and answering them differently is that subtype's own business.
    """

    def test_an_overridden_accessor_does_not_move_the_width_a_value_round_trips_at(self) -> None:
        """The declared eight bytes are written, and the same eight are read back."""
        value = AccessorNarrowerThanTheWidth(7)
        assert AccessorNarrowerThanTheWidth.get_byte_length() == 4
        assert value.encode_bytes() == (7).to_bytes(8, "little")
        assert AccessorNarrowerThanTheWidth.decode_bytes(value.encode_bytes()) == value

    def test_a_payload_of_the_wrong_width_is_refused_against_the_declared_width(self) -> None:
        """A payload of the accessor's four bytes is short of the width, and reported as such."""
        with pytest.raises(
            SSZValueError,
            match=r"^AccessorNarrowerThanTheWidth needs 8 bytes, the input holds 4$",
        ):
            AccessorNarrowerThanTheWidth.decode_bytes(b"\x00" * 4)

    def test_a_scope_of_the_wrong_width_is_refused_against_the_declared_width(self) -> None:
        """A stream read is scoped by the declared width too, and says which width it wanted."""
        stream = io.BytesIO(b"\x00" * 8)
        with pytest.raises(
            SSZValueError,
            match=r"^AccessorNarrowerThanTheWidth spans 8 bytes, and the budget is 4$",
        ):
            AccessorNarrowerThanTheWidth.deserialize(stream, scope=4)


class TestForwardArithmeticTypeErrors:
    """Tests which operand types a forward arithmetic operator admits."""

    ARITHMETIC_DUNDERS = [
        ("__add__", "+"),
        ("__sub__", "-"),
        ("__mul__", "*"),
        ("__floordiv__", "//"),
        ("__mod__", "%"),
    ]
    """Every forward arithmetic dunder, paired with the symbol its error message names."""

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    @pytest.mark.parametrize("method, op_symbol", ARITHMETIC_DUNDERS)
    def test_forward_operator_accepts_plain_int(
        self, uint_class: Type[BaseUint], method: str, op_symbol: str
    ) -> None:
        """Forward arithmetic operator takes a plain int and keeps its own type."""
        # 5 and 3 so that no result of the five leaves the eight-bit range.
        result = getattr(uint_class(5), method)(3)
        assert type(result) is uint_class

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    @pytest.mark.parametrize("method, op_symbol", ARITHMETIC_DUNDERS)
    @pytest.mark.parametrize("bad", [True, 1.5])
    def test_forward_operator_rejects_an_unrelated_operand(
        self, uint_class: Type[BaseUint], method: str, op_symbol: str, bad: Any
    ) -> None:
        """Forward arithmetic operator raises TypeError for a number no relation admits."""
        # Call the dunder method directly so no reflected fallback can intervene.
        expected_message = (
            f"Unsupported operand type(s) for {op_symbol}: "
            + f"'{uint_class.__name__}' and '{type(bad).__name__}'"
        )
        with pytest.raises(TypeError) as exception_info:
            getattr(uint_class(5), method)(bad)
        assert str(exception_info.value) == expected_message


NOT_A_NUMBER: Any = "2"
"""A stand-in for an operand that is not a number, held loosely so a bad call type-checks."""


class TestANonNumberIsDeclined:
    """
    An operand that is not a number at all is declined rather than refused.

    A refusal ends the expression where it stands.
    Declining hands the question to the other operand, which is what a sequence needs:
    it repeats by reading its count through the index protocol, never seeing a uint.
    """

    DECLINING_DUNDERS = [
        "__add__",
        "__radd__",
        "__sub__",
        "__rsub__",
        "__mul__",
        "__rmul__",
        "__floordiv__",
        "__rfloordiv__",
        "__mod__",
        "__rmod__",
        "__divmod__",
        "__rdivmod__",
        "__and__",
        "__or__",
        "__xor__",
        "__lshift__",
        "__rlshift__",
        "__rshift__",
        "__rrshift__",
    ]
    """Every arithmetic and bitwise dunder that settles a result type of its own."""

    @pytest.mark.parametrize("method", DECLINING_DUNDERS)
    def test_every_operator_declines_a_non_number(self, method: str) -> None:
        """Called directly, a declining dunder answers NotImplemented instead of raising."""
        assert getattr(Uint64(6), method)(NOT_A_NUMBER) is NotImplemented

    @pytest.mark.parametrize(
        "apply",
        [
            lambda: Uint64(2).__pow__(NOT_A_NUMBER),
            lambda: Uint64(2).__pow__(3, NOT_A_NUMBER),
            lambda: Uint64(2).__rpow__(NOT_A_NUMBER),
            lambda: Uint64(2).__rpow__(3, NOT_A_NUMBER),
        ],
    )
    def test_pow_declines_in_either_argument(self, apply: Any) -> None:
        """Exponent and modulus each decline, in the forward form and in the reverse one."""
        assert apply() is NotImplemented

    @pytest.mark.parametrize(
        "apply, expected",
        [
            (lambda: [1] * Uint64(3), [1, 1, 1]),
            (lambda: Uint64(3) * [1], [1, 1, 1]),
            (lambda: "ab" * Uint64(2), "abab"),
            (lambda: b"x" * Uint64(2), b"xx"),
            (lambda: (1,) * Uint64(2), (1, 1)),
            (lambda: bytearray(b"x") * Uint64(2), bytearray(b"xx")),
        ],
    )
    def test_a_sequence_repeats_by_a_typed_count(self, apply: Any, expected: Any) -> None:
        """Every builtin sequence repeats by a uint, in either operand position."""
        assert apply() == expected

    @pytest.mark.parametrize("bad", ["2", None])
    def test_the_host_language_reports_what_both_sides_decline(self, bad: Any) -> None:
        """With nobody left to answer, Python raises the TypeError any other type would."""
        # Lower case where this library's own message is capitalised.
        # The message here is the interpreter's.
        with pytest.raises(TypeError, match="^unsupported operand type"):
            _ = Uint64(1) + bad

    @pytest.mark.parametrize("bad", [Decimal(2), Fraction(1, 2)])
    def test_a_number_outside_the_integers_is_refused_by_name(self, bad: Any) -> None:
        """The refusal reaches the whole numeric tower, not only the builtin widths."""
        expected_message = f"Unsupported operand type(s) for +: 'Uint64' and '{type(bad).__name__}'"
        with pytest.raises(TypeError) as exception_info:
            _ = Uint64(1) + bad
        assert str(exception_info.value) == expected_message


class TestReverseArithmeticSuccessPaths:
    """Tests that reverse arithmetic operators succeed when both operands are BaseUint."""

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_radd_success(self, uint_class: Type[BaseUint]) -> None:
        """Reverse add returns the correct sum when called directly."""
        # __radd__(other) computes other + self
        reverse_sum = uint_class(3).__radd__(uint_class(5))
        assert reverse_sum == uint_class(8)
        assert isinstance(reverse_sum, uint_class)

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_rsub_success(self, uint_class: Type[BaseUint]) -> None:
        """Reverse sub returns the correct difference when called directly."""
        # __rsub__(other) computes other - self
        reverse_difference = uint_class(3).__rsub__(uint_class(10))
        assert reverse_difference == uint_class(7)
        assert isinstance(reverse_difference, uint_class)

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_rmul_success(self, uint_class: Type[BaseUint]) -> None:
        """Reverse mul returns the correct product when called directly."""
        # __rmul__(other) computes other * self
        reverse_product = uint_class(3).__rmul__(uint_class(5))
        assert reverse_product == uint_class(15)
        assert isinstance(reverse_product, uint_class)

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_rfloordiv_success(self, uint_class: Type[BaseUint]) -> None:
        """Reverse floordiv returns the correct quotient when called directly."""
        # __rfloordiv__(other) computes other // self
        reverse_quotient = uint_class(3).__rfloordiv__(uint_class(10))
        assert reverse_quotient == uint_class(3)
        assert isinstance(reverse_quotient, uint_class)

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_rmod_success(self, uint_class: Type[BaseUint]) -> None:
        """Reverse mod returns the correct remainder when called directly."""
        # __rmod__(other) computes other % self
        reverse_remainder = uint_class(3).__rmod__(uint_class(10))
        assert reverse_remainder == uint_class(1)
        assert isinstance(reverse_remainder, uint_class)


class TestPowAndRpow:
    """Tests for exponentiation operators including modulo and reverse paths."""

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_pow_with_modulo(self, uint_class: Type[BaseUint]) -> None:
        """Three-argument pow(base, exp, mod) validates the modulo and returns correct result."""
        # pow(2, 10, 100) == 1024 % 100 == 24
        modular_power = pow(uint_class(2), uint_class(10), uint_class(100))
        assert modular_power == uint_class(24)
        assert isinstance(modular_power, uint_class)

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_rpow_success(self, uint_class: Type[BaseUint]) -> None:
        """Reverse pow computes base ** self when called directly."""
        # __rpow__(base) computes base ** self => 2 ** 3 == 8
        reverse_power = uint_class(3).__rpow__(uint_class(2))
        assert reverse_power == uint_class(8)
        assert isinstance(reverse_power, uint_class)

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_rpow_with_modulo(self, uint_class: Type[BaseUint]) -> None:
        """Three-argument reverse pow validates the modulo and returns the correct result."""
        # __rpow__(base, mod) computes pow(base, self, mod) => pow(2, 10, 100) == 24
        reverse_modular_power = uint_class(10).__rpow__(uint_class(2), uint_class(100))
        assert reverse_modular_power == uint_class(24)
        assert isinstance(reverse_modular_power, uint_class)


class TestPowShiftStrictOperands:
    """Pow and shift apply the same operand rule as every other binary op."""

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_pow_and_shift_accept_a_plain_int(self, uint_class: Type[BaseUint]) -> None:
        """A bare literal serves as an exponent, a modulus, or a shift count."""
        assert uint_class(2) ** 3 == uint_class(8)
        assert pow(uint_class(2), 10, 100) == uint_class(24)
        assert uint_class(1) << 3 == uint_class(8)
        assert uint_class(8) >> 3 == uint_class(1)
        # The type is kept in every one of the four.
        assert type(uint_class(2) ** 3) is uint_class
        assert type(pow(uint_class(2), 10, 100)) is uint_class
        assert type(uint_class(1) << 3) is uint_class
        assert type(uint_class(8) >> 3) is uint_class

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    @pytest.mark.parametrize("bad", [True, 1.5])
    def test_pow_rejects_non_uint_exponent(self, uint_class: Type[BaseUint], bad: Any) -> None:
        """Exponentiation rejects any exponent that is a number of another type."""
        expected_message = (
            "Unsupported operand type(s) for **: "
            + f"'{uint_class.__name__}' and '{type(bad).__name__}'"
        )
        with pytest.raises(TypeError) as exception_info:
            uint_class(2) ** bad
        assert str(exception_info.value) == expected_message

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    @pytest.mark.parametrize("bad", [True])
    def test_pow_rejects_non_uint_modulo(self, uint_class: Type[BaseUint], bad: Any) -> None:
        """Three-argument pow rejects any modulo that is a number of another type."""
        expected_message = (
            "Unsupported operand type(s) for **: "
            + f"'{uint_class.__name__}' and '{type(bad).__name__}'"
        )
        with pytest.raises(TypeError) as exception_info:
            pow(uint_class(2), uint_class(10), bad)
        assert str(exception_info.value) == expected_message

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    @pytest.mark.parametrize("bad", [True])
    def test_rpow_rejects_non_uint_base(self, uint_class: Type[BaseUint], bad: Any) -> None:
        """Reverse pow rejects any base that is a number of another type."""
        expected_message = (
            "Unsupported operand type(s) for **: "
            + f"'{uint_class.__name__}' and '{type(bad).__name__}'"
        )
        with pytest.raises(TypeError) as exception_info:
            uint_class(3).__rpow__(bad)
        assert str(exception_info.value) == expected_message

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    @pytest.mark.parametrize("bad", [True])
    def test_rpow_rejects_non_uint_modulo(self, uint_class: Type[BaseUint], bad: Any) -> None:
        """Three-argument reverse pow rejects any modulo that is a number of another type."""
        expected_message = (
            "Unsupported operand type(s) for **: "
            + f"'{uint_class.__name__}' and '{type(bad).__name__}'"
        )
        with pytest.raises(TypeError) as exception_info:
            uint_class(10).__rpow__(uint_class(2), bad)
        assert str(exception_info.value) == expected_message

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    @pytest.mark.parametrize("bad", [True])
    def test_lshift_rejects_non_uint(self, uint_class: Type[BaseUint], bad: Any) -> None:
        """Left shift rejects any shift amount that is a number of another type."""
        expected_message = (
            "Unsupported operand type(s) for <<: "
            + f"'{uint_class.__name__}' and '{type(bad).__name__}'"
        )
        with pytest.raises(TypeError) as exception_info:
            uint_class(1) << bad
        assert str(exception_info.value) == expected_message

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    @pytest.mark.parametrize("bad", [True])
    def test_rshift_rejects_non_uint(self, uint_class: Type[BaseUint], bad: Any) -> None:
        """Right shift rejects any shift amount that is a number of another type."""
        expected_message = (
            "Unsupported operand type(s) for >>: "
            + f"'{uint_class.__name__}' and '{type(bad).__name__}'"
        )
        with pytest.raises(TypeError) as exception_info:
            uint_class(8) >> bad
        assert str(exception_info.value) == expected_message


class TestDivmodEdgeCases:
    """Tests for divmod type error and reverse divmod paths."""

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_divmod_accepts_plain_int(self, uint_class: Type[BaseUint]) -> None:
        """Forward divmod takes a plain int divisor and types both halves of the pair."""
        quotient, remainder = divmod(uint_class(10), 3)
        assert (quotient, remainder) == (uint_class(3), uint_class(1))
        assert type(quotient) is uint_class
        assert type(remainder) is uint_class

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    @pytest.mark.parametrize("bad", [True])
    def test_divmod_rejects_an_unrelated_divisor(
        self, uint_class: Type[BaseUint], bad: Any
    ) -> None:
        """Forward divmod raises TypeError when the divisor is a number no relation admits."""
        expected_message = (
            "Unsupported operand type(s) for divmod: "
            + f"'{uint_class.__name__}' and '{type(bad).__name__}'"
        )
        with pytest.raises(TypeError) as exception_info:
            divmod(uint_class(10), bad)
        assert str(exception_info.value) == expected_message

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_rdivmod_success(self, uint_class: Type[BaseUint]) -> None:
        """Reverse divmod returns correct (quotient, remainder) when called directly."""
        # __rdivmod__(other) computes divmod(other, self) => divmod(10, 3) == (3, 1)
        quotient, remainder = uint_class(3).__rdivmod__(uint_class(10))
        assert quotient == uint_class(3)
        assert remainder == uint_class(1)
        assert isinstance(quotient, uint_class)
        assert isinstance(remainder, uint_class)


class TestReverseBitwiseOperators:
    """Tests for reverse bitwise operator delegation paths."""

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_rand_delegates_to_and(self, uint_class: Type[BaseUint]) -> None:
        """Reverse AND delegates to forward AND and returns the correct result."""
        # __rand__ delegates to __and__
        reverse_and_result = uint_class(0b1100).__rand__(uint_class(0b1010))
        assert reverse_and_result == uint_class(0b1000)
        assert isinstance(reverse_and_result, uint_class)

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_ror_delegates_to_or(self, uint_class: Type[BaseUint]) -> None:
        """Reverse OR delegates to forward OR and returns the correct result."""
        # __ror__ delegates to __or__
        reverse_or_result = uint_class(0b1100).__ror__(uint_class(0b1010))
        assert reverse_or_result == uint_class(0b1110)
        assert isinstance(reverse_or_result, uint_class)

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_rxor_delegates_to_xor(self, uint_class: Type[BaseUint]) -> None:
        """Reverse XOR delegates to forward XOR and returns the correct result."""
        # __rxor__ delegates to __xor__
        reverse_xor_result = uint_class(0b1100).__rxor__(uint_class(0b1010))
        assert reverse_xor_result == uint_class(0b0110)
        assert isinstance(reverse_xor_result, uint_class)


class TestReverseShiftOperators:
    """Tests for reverse left-shift and right-shift operator paths."""

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_rlshift_success(self, uint_class: Type[BaseUint]) -> None:
        """Reverse left shift computes other << self."""
        # __rlshift__(other) computes other << self => 1 << 2 == 4
        reverse_left_shift = uint_class(2).__rlshift__(uint_class(1))
        assert reverse_left_shift == uint_class(4)
        assert isinstance(reverse_left_shift, uint_class)
        # A bare literal on the left is admitted, so the receiver's type carries the result.
        assert type(1 << uint_class(2)) is uint_class

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    @pytest.mark.parametrize("bad", [True])
    def test_rlshift_rejects_non_uint(self, uint_class: Type[BaseUint], bad: Any) -> None:
        """Reverse left shift rejects any operand that is a number of another type."""
        expected_message = (
            "Unsupported operand type(s) for <<: "
            + f"'{uint_class.__name__}' and '{type(bad).__name__}'"
        )
        with pytest.raises(TypeError) as exception_info:
            uint_class(2).__rlshift__(bad)
        assert str(exception_info.value) == expected_message

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_rrshift_success(self, uint_class: Type[BaseUint]) -> None:
        """Reverse right shift computes other >> self."""
        # __rrshift__(other) computes other >> self => 8 >> 2 == 2
        reverse_right_shift = uint_class(2).__rrshift__(uint_class(8))
        assert reverse_right_shift == uint_class(2)
        assert isinstance(reverse_right_shift, uint_class)
        # A bare literal on the left is admitted, so the receiver's type carries the result.
        assert type(8 >> uint_class(2)) is uint_class

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    @pytest.mark.parametrize("bad", [True])
    def test_rrshift_rejects_non_uint(self, uint_class: Type[BaseUint], bad: Any) -> None:
        """Reverse right shift rejects any operand that is a number of another type."""
        expected_message = (
            "Unsupported operand type(s) for >>: "
            + f"'{uint_class.__name__}' and '{type(bad).__name__}'"
        )
        with pytest.raises(TypeError) as exception_info:
            uint_class(2).__rrshift__(bad)
        assert str(exception_info.value) == expected_message


class TestComparisonTypeErrors:
    """Tests which operand types the ordering comparisons admit."""

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_lt_and_le_accept_plain_int(self, uint_class: Type[BaseUint]) -> None:
        """The two dunders that no reflected route reaches still take a plain int."""
        # Called directly, because 5 < 10 with the uint on the right routes to __gt__.
        assert uint_class(5).__lt__(10) is True
        assert uint_class(5).__le__(10) is True

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    @pytest.mark.parametrize("bad", [True, "10", 1.5])
    def test_lt_rejects_an_unrelated_operand(self, uint_class: Type[BaseUint], bad: Any) -> None:
        """Less-than raises TypeError for anything but a uint or an int."""
        expected_message = (
            f"Unsupported operand type(s) for <: '{uint_class.__name__}' and '{type(bad).__name__}'"
        )
        with pytest.raises(TypeError) as exception_info:
            uint_class(5).__lt__(bad)
        assert str(exception_info.value) == expected_message

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    @pytest.mark.parametrize("bad", [True, "10", 1.5])
    def test_le_rejects_an_unrelated_operand(self, uint_class: Type[BaseUint], bad: Any) -> None:
        """Less-than-or-equal raises TypeError for anything but a uint or an int."""
        expected_message = (
            "Unsupported operand type(s) for <=: "
            + f"'{uint_class.__name__}' and '{type(bad).__name__}'"
        )
        with pytest.raises(TypeError) as exception_info:
            uint_class(5).__le__(bad)
        assert str(exception_info.value) == expected_message


class TestIndexReturnsPlainInt:
    """Tests that __index__ returns a plain int, not a BaseUint subclass."""

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_index_returns_plain_int(self, uint_class: Type[BaseUint]) -> None:
        """__index__ returns a plain int so that built-in operations receive a raw integer."""
        index_value = uint_class(42).__index__()
        # The value must be correct.
        assert index_value == 42
        # The type must be plain int, not a BaseUint subclass.
        assert type(index_value) is int


class TestCrossWidthEqualityIsStrict:
    """Equality across different unsigned integer widths must raise."""

    @pytest.mark.parametrize("type_a, type_b", CROSS_UINT_TYPE_PAIRS)
    def test_eq_across_widths_raises(self, type_a: Type[BaseUint], type_b: Type[BaseUint]) -> None:
        """Equality across two distinct widths raises."""
        expected_message = (
            f"Unsupported operand type(s) for ==: '{type_a.__name__}' and '{type_b.__name__}'"
        )
        with pytest.raises(TypeError) as exception_info:
            _ = type_a(5) == type_b(5)
        assert str(exception_info.value) == expected_message

    @pytest.mark.parametrize("type_a, type_b", CROSS_UINT_TYPE_PAIRS)
    def test_ne_across_widths_raises(self, type_a: Type[BaseUint], type_b: Type[BaseUint]) -> None:
        """Inequality across two distinct widths raises."""
        expected_message = (
            f"Unsupported operand type(s) for !=: '{type_a.__name__}' and '{type_b.__name__}'"
        )
        with pytest.raises(TypeError) as exception_info:
            _ = type_a(5) != type_b(5)
        assert str(exception_info.value) == expected_message

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_eq_same_width_same_value_still_equal(self, uint_class: Type[BaseUint]) -> None:
        """Within a single width, equal values still compare equal."""
        assert uint_class(7) == uint_class(7)
        assert not (uint_class(7) != uint_class(7))

    @pytest.mark.parametrize("type_a, type_b", CROSS_UINT_TYPE_PAIRS)
    def test_hash_is_the_value_across_widths(
        self, type_a: Type[BaseUint], type_b: Type[BaseUint]
    ) -> None:
        """A uint hashes as its value, so two widths holding 5 share the hash of 5."""
        assert hash(type_a(5)) == hash(type_b(5)) == hash(5)

    @pytest.mark.parametrize("type_a, type_b", CROSS_UINT_TYPE_PAIRS)
    def test_a_cross_width_dict_probe_raises_rather_than_missing(
        self, type_a: Type[BaseUint], type_b: Type[BaseUint]
    ) -> None:
        """One bucket holds both, so the container reaches the refusal above.

        A type-mixing hash sent the probe to a different bucket, which answered
        "absent" without ever consulting the comparison that decides the question.
        """
        with pytest.raises(TypeError):
            _ = {type_a(5): 1}[type_b(5)]

    @pytest.mark.parametrize("type_a, type_b", CROSS_UINT_TYPE_PAIRS)
    def test_a_cross_width_dict_probe_of_another_value_is_simply_absent(
        self, type_a: Type[BaseUint], type_b: Type[BaseUint]
    ) -> None:
        """Different values hash apart, so the comparison is never reached."""
        with pytest.raises(KeyError):
            _ = {type_a(5): 1}[type_b(6)]


class Slot(Uint64):
    """A 64-bit slot number, declared the way the consensus specification declares it."""


class Epoch(Uint64):
    """A 64-bit epoch number, a sibling of Slot and not interchangeable with it."""


class Gwei(Uint64):
    """A 64-bit amount of currency, a sibling of both."""


class Wei(Gwei):
    """A second step down the chain, to show the rule is about depth, not one level."""


class TestRelatedTypesMeet:
    """Two uints may meet in an operation only when inheritance relates them."""

    def test_a_domain_type_meets_its_own_base(self) -> None:
        """The idiom that blocks the port: state.slot % SLOTS_PER_EPOCH."""
        # SLOTS_PER_EPOCH is declared uint64(2**5), not Slot, in the specification.
        assert Slot(37) % Uint64(8) == Slot(5)
        assert type(Slot(37) % Uint64(8)) is Slot

    def test_the_base_meets_a_domain_type_and_the_derived_type_wins(self) -> None:
        """Order does not decide the result type; depth in the hierarchy does."""
        assert type(Uint64(1) + Slot(2)) is Slot
        assert type(Slot(1) + Uint64(2)) is Slot
        # Two steps of derivation is no different from one.
        assert type(Uint64(1) + Wei(2)) is Wei
        assert type(Gwei(1) + Wei(2)) is Wei

    def test_a_bare_literal_meets_a_domain_type(self) -> None:
        """The 17 specification sites that write epoch + 1 rather than epoch + Epoch(1)."""
        assert type(Epoch(5) + 1) is Epoch
        assert type(1 + Epoch(5)) is Epoch
        assert type(Slot(5) + 1) is Slot
        # Both spellings of the same increment agree, which is why the literal is admitted.
        assert Epoch(5) + 1 == Epoch(5) + Epoch(1)

    def test_sum_of_domain_values_keeps_the_domain_type(self) -> None:
        """sum seeds the accumulator with a plain 0, so the first addition is uint + int."""
        total = sum([Gwei(1), Gwei(2), Gwei(3)])
        assert total == Gwei(6)
        assert type(total) is Gwei

    def test_min_and_max_span_a_domain_type_and_its_base(self) -> None:
        """min compares with <, which needs the same relation the arithmetic needs."""
        assert min(Epoch(3), Uint64(4)) == Epoch(3)
        assert max(Epoch(3), Uint64(4)) == Uint64(4)

    def test_a_unit_carried_by_the_exponent_survives_a_bare_base_and_modulus(self) -> None:
        """
        Three-argument pow resolves its modulus against the type the exponent settled on.

        The base and the modulus here are the plain width, which carries no unit.
        Resolving the modulus against the receiver instead would discard the unit the
        exponent contributed and hand back that width.
        """
        assert type(pow(Uint64(2), Slot(10), Uint64(100))) is Slot
        assert type(Slot(10).__rpow__(Uint64(2), Uint64(100))) is Slot

    @pytest.mark.parametrize(
        "apply, op_symbol, left_name, right_name",
        [
            (lambda: Slot(1) + Epoch(2), "+", "Slot", "Epoch"),
            (lambda: Gwei(1) + Slot(2), "+", "Gwei", "Slot"),
            (lambda: Slot(8) // Epoch(2), "//", "Slot", "Epoch"),
            (lambda: Slot(8) % Epoch(2), "%", "Slot", "Epoch"),
            (lambda: Slot(8) & Epoch(2), "&", "Slot", "Epoch"),
            (lambda: Slot(8) << Epoch(1), "<<", "Slot", "Epoch"),
            (lambda: divmod(Slot(8), Epoch(2)), "divmod", "Slot", "Epoch"),
            (lambda: Slot(2) ** Epoch(3), "**", "Slot", "Epoch"),
            (lambda: Slot(1) == Epoch(1), "==", "Slot", "Epoch"),
            (lambda: Slot(1) != Epoch(1), "!=", "Slot", "Epoch"),
            (lambda: Slot(1) < Epoch(2), "<", "Slot", "Epoch"),
            (lambda: Slot(1) >= Epoch(2), ">=", "Slot", "Epoch"),
            # Two branches of the same tree that never touch, three levels apart.
            (lambda: Wei(1) + Slot(2), "+", "Wei", "Slot"),
            # Width confusion, which is the same refusal for a different reason.
            (lambda: Uint64(1) + Uint32(2), "+", "Uint64", "Uint32"),
            (lambda: Slot(1) + Uint32(2), "+", "Slot", "Uint32"),
        ],
    )
    def test_siblings_never_meet(
        self, apply: Any, op_symbol: str, left_name: str, right_name: str
    ) -> None:
        """Neither unit confusion nor width confusion is admitted anywhere."""
        expected_message = (
            f"Unsupported operand type(s) for {op_symbol}: '{left_name}' and '{right_name}'"
        )
        with pytest.raises(TypeError) as exception_info:
            apply()
        assert str(exception_info.value) == expected_message

    def test_a_bool_counts_nothing(self) -> None:
        """bool is an int subclass, but a flag is not a quantity, so it stays out."""
        expected_message = "Unsupported operand type(s) for +: 'Slot' and 'bool'"
        with pytest.raises(TypeError) as exception_info:
            _ = Slot(1) + True
        assert str(exception_info.value) == expected_message

    def test_a_non_int_stays_out_even_when_it_answers_to_int(self) -> None:
        """The rule tests the operand's type, not whether a number could be extracted."""
        expected_message = "Unsupported operand type(s) for +: 'Slot' and 'float'"
        with pytest.raises(TypeError) as exception_info:
            _ = Slot(1) + 1.0
        assert str(exception_info.value) == expected_message

    @pytest.mark.parametrize(
        "apply, expected_type",
        [
            (lambda: Uint8(255) + 1, Uint8),
            (lambda: 1 + Uint8(255), Uint8),
            (lambda: Uint8(255) + Uint8(1), Uint8),
            (lambda: Gwei(0) - 1, Gwei),
            (lambda: Uint64(0) - Slot(1), Slot),
            (lambda: Uint64(2**64 - 1) + Slot(1), Slot),
        ],
    )
    def test_the_range_check_survives_on_the_resolved_type(
        self, apply: Any, expected_type: Type[BaseUint]
    ) -> None:
        """
        Admitting a wider set of operands does not widen the range of a result.

        The bound is read off whichever type won the resolution, so a Gwei underflow
        and an epoch overflow are caught exactly as before:

            Uint8(255) + 1     ->  256 out of range for Uint8  [0, 255]
            Gwei(0) - 1        ->   -1 out of range for Gwei   [0, 2**64 - 1]
        """
        with pytest.raises(SSZValueError) as exception_info:
            apply()
        # The error names the type the result would have had, so the diagnosis is exact.
        assert f"out of range for {expected_type.__name__} " in str(exception_info.value)

    def test_equality_holds_between_a_domain_type_and_its_base(self) -> None:
        """A related comparison answers by value, since neither type can win a bool."""
        assert Slot(5) == Uint64(5)
        assert Uint64(5) == Slot(5)
        assert Slot(5) != Uint64(6)
        assert Slot(4) < Uint64(5)
        assert Uint64(5) >= Slot(5)


@pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
@given(data=st.data())
def test_encode_decode_round_trip_random_values(uint_class: Type[BaseUint], data) -> None:
    """Any in-range value survives an encode and decode round trip unchanged."""
    raw_value = data.draw(st.integers(min_value=0, max_value=2**uint_class.BITS - 1))
    instance = uint_class(raw_value)
    assert uint_class.decode_bytes(instance.encode_bytes()) == instance


# The spec's eight bits of opaque data, and the shapes it aliases.
#
# Each shape below is declared twice, once with each spelling.
# The two declarations are separate classes.
# No comparison between them is therefore vacuous.


class OpaqueByteVector4(Vector[Byte]):
    """The spec's four-byte array: a vector of four of the opaque spelling."""

    LENGTH = 4


class Uint8Vector4(Vector[Uint8]):
    """The same four-element shape, declared with the numeric spelling."""

    LENGTH = 4


class OpaqueByteList4(List[Byte]):
    """The spec's byte list of capacity four: a list of the opaque spelling."""

    LIMIT = 4


class Uint8List4(List[Uint8]):
    """The same four-capacity shape, declared with the numeric spelling."""

    LIMIT = 4


class OpaqueByteProgressiveList(ProgressiveList[Byte]):
    """The spec's unbounded byte list: a progressive list of the opaque spelling."""


class OpaqueByteHolder(Container):
    """One field of opaque data, beside one field the spec reads as a number."""

    payload: Byte
    count: Uint16


class TestOpaqueByteSpelling:
    """
    The spec's eight bits of opaque data, against the eight-bit number beside it.

    Two things the spec says of the pair:

    - They are equivalent in serialization and in hashing.
    - Each is compatible with the other.

    One type under two names satisfies both for free.
    What follows pins that equivalence, and the alias shapes built on it.
    The arithmetic and comparison surface belongs to the eight-bit number.
    It is covered above rather than repeated here.
    """

    def test_the_two_spellings_name_one_type(self) -> None:
        """One class stands behind both names, rather than one subclassing the other."""
        # Why not a real subclass, measured with one declared over the eight-bit number:
        #
        #     Sub(5) == Uint8(5)      TypeError: Unsupported operand type(s) for ==
        #     Uint8List4.of(Sub(5))   SSZTypeError: Expected Uint8, got Sub
        #
        # Integers here compare by exact class.
        # Collections coerce their elements by exact class too.
        # A subclass would be a type the spec calls interchangeable.
        # This library would refuse to interchange it.
        assert Byte is Uint8
        # The visible cost of one class under two names.
        # A value built through the opaque name shows the numeric name back.
        assert repr(Byte(7)) == "Uint8(7)"

    @pytest.mark.parametrize(
        "value, expected_wire",
        [
            pytest.param(0x00, b"\x00", id="zero"),
            pytest.param(0x01, b"\x01", id="one"),
            pytest.param(0xFF, b"\xff", id="widest_value_eight_bits_hold"),
        ],
    )
    def test_the_two_spellings_agree_on_equality_bytes_and_root(
        self, value: int, expected_wire: bytes
    ) -> None:
        """Equality, the encoded byte, and the root all answer alike across the two names."""
        opaque, number = Byte(value), Uint8(value)

        # Equality is the property a real subclass would lose first.
        assert opaque == number

        # Eight bits occupy one byte.
        # The encoding is therefore the value itself.
        assert opaque.encode_bytes() == expected_wire
        assert number.encode_bytes() == expected_wire

        # A basic type roots as its encoding right-padded to a full 32-byte chunk:
        #
        #     value 0xff  ->  ff 00 00 ... 00     1 byte of value, 31 of padding
        assert hash_tree_root(opaque) == Chunk(expected_wire + b"\x00" * 31)
        assert hash_tree_root(number) == hash_tree_root(opaque)

    @pytest.mark.parametrize(
        "declared_shape, element",
        [
            pytest.param(Uint8List4, Byte(5), id="numeric_shape_given_an_opaque_value"),
            pytest.param(OpaqueByteList4, Uint8(5), id="opaque_shape_given_a_numeric_value"),
        ],
    )
    def test_a_value_of_either_spelling_fits_a_shape_declared_with_the_other(
        self, declared_shape: type[List[Uint8]], element: Uint8
    ) -> None:
        """A collection declared with one name accepts a value built with the other."""
        # Element coercion admits the declared class and its ancestors, nothing else.
        # Two names for one class therefore pass straight through, in either direction.
        held = declared_shape.of(element)
        assert held[0] == Uint8(5)
        assert held.encode_bytes() == b"\x05"

    def test_the_fixed_byte_array_shape(self) -> None:
        """A four-byte array declared over the opaque spelling encodes and roots alike."""
        # Two declarations, two classes.
        # Nothing below therefore compares an object with itself.
        assert OpaqueByteVector4 is not Uint8Vector4

        opaque = OpaqueByteVector4.of(0x01, 0x02, 0x03, 0x04)
        numeric = Uint8Vector4.of(0x01, 0x02, 0x03, 0x04)

        # Fixed-size elements pack back to back.
        # There is no length prefix and no separator.
        assert opaque.encode_bytes() == bytes.fromhex("01020304")
        assert numeric.encode_bytes() == opaque.encode_bytes()

        # Four bytes fit one chunk, padded out to 32:
        #
        #     01 02 03 04 00 00 ... 00
        assert hash_tree_root(opaque) == Chunk(bytes.fromhex("01020304") + b"\x00" * 28)
        assert hash_tree_root(numeric) == hash_tree_root(opaque)

    def test_the_byte_list_shape(self) -> None:
        """A byte list declared over the opaque spelling encodes and roots alike."""
        assert OpaqueByteList4 is not Uint8List4

        opaque = OpaqueByteList4.of(0x11, 0x22)
        numeric = Uint8List4.of(0x11, 0x22)

        # A list writes its elements bare.
        # The count is recovered from the byte budget on the way back in.
        assert opaque.encode_bytes() == bytes.fromhex("1122")
        assert numeric.encode_bytes() == opaque.encode_bytes()

        # The root mixes the element count into the padded chunks.
        # Capacity fixes the tree depth.
        # Both declarations were given capacity four.
        assert hash_tree_root(numeric) == hash_tree_root(opaque)

    def test_the_unbounded_byte_list_shape(self) -> None:
        """The spec's unbounded byte list is a progressive list of the opaque spelling."""
        # An inline parameterization over one name resolves to a single class.
        # The other name parameterizes to that same class.
        # The named subclass is what gives two classes to compare.
        assert OpaqueByteProgressiveList is not ProgressiveList[Uint8]

        opaque = OpaqueByteProgressiveList.of(0x11, 0x22)
        numeric = ProgressiveList[Uint8].of(0x11, 0x22)

        # The wire format is the bounded shape's, byte for byte.
        assert opaque.encode_bytes() == bytes.fromhex("1122")
        assert numeric.encode_bytes() == opaque.encode_bytes()

        # Only the tree differs from a bounded list.
        # That tree grows with the data rather than with a capacity.
        # Neither declaration therefore has a capacity to pad differently to.
        assert hash_tree_root(numeric) == hash_tree_root(opaque)

    def test_a_container_field_declared_with_it_round_trips(self) -> None:
        """A field declared with the opaque spelling survives an encode and decode."""
        holder = OpaqueByteHolder(payload=Byte(0xAB), count=Uint16(0x0102))

        # One byte of opaque data, then two little-endian bytes of the number:
        #
        #     ab      02 01
        #     payload count
        assert holder.encode_bytes() == bytes.fromhex("ab0201")
        assert OpaqueByteHolder.decode_bytes(holder.encode_bytes()) == holder

    def test_json_output_does_not_follow_the_spec_mapping(self) -> None:
        """
        Pin what JSON output looks like today, which records a gap rather than a decision.

        The spec's mapping asks for three things, none of which appears below:

        - A decimal string from an eight-bit number.
        - A hex byte string from eight bits of opaque data.
        - A bare hex byte string from any collection of them.

        The mapping is unimplemented across this library.
        No string asserted below is spec-correct.
        Each is expected to change when the mapping lands.
        """
        # The spec asks for "1" from both of these fields.
        assert (
            OpaqueByteHolder(payload=Byte(1), count=Uint16(1)).model_dump_json()
            == '{"payload":1,"count":1}'
        )

        # The spec asks for the bare string "0x11223344" from a byte collection.
        # Each collection instead comes out as an object, keyed by the field holding its elements.
        # Those elements are decimal numbers rather than hex.
        assert (
            OpaqueByteVector4.of(0x11, 0x22, 0x33, 0x44).model_dump_json()
            == '{"data":[17,34,51,68]}'
        )
        assert OpaqueByteList4.of(0x11, 0x22).model_dump_json() == '{"data":[17,34]}'
        assert OpaqueByteProgressiveList.of(0x11, 0x22).model_dump_json() == '{"data":[17,34]}'

    def test_the_package_exports_the_spelling(self) -> None:
        """The export list is what a star import and the documentation tooling read."""
        # Importing the name at the top of this module proves it is reachable.
        # Only the export list proves it is public.
        assert "Byte" in ssz.__all__


class NarrowerThanTheTable(BaseUint):
    """A width narrower than the shared table, to exercise the clamp."""

    BITS = 2


class LiesInComparisons(int):
    """An integer subclass that answers every ordering question the way it prefers."""

    def __lt__(self, other: Any) -> bool:
        """Claim to be below anything it is compared against."""
        return False

    def __le__(self, other: Any) -> bool:
        """Claim to be within any upper bound."""
        return True

    def __gt__(self, other: Any) -> bool:
        """Claim never to exceed anything."""
        return False

    def __ge__(self, other: Any) -> bool:
        """Claim to be above any lower bound."""
        return True


class TestSmallValuesAreShared:
    """The smallest values of each width come from a shared table rather than an allocation."""

    @pytest.mark.parametrize("uint_class", ALL_UINT_TYPES)
    def test_a_small_value_is_the_same_object_every_time(self, uint_class: Type[BaseUint]) -> None:
        """Two constructions of one small value answer with one instance."""
        # Every width shares its low values, so 7 is served from the table in all of them.
        assert uint_class(7) is uint_class(7)
        # Arithmetic returns through the same path, so a small result is shared too.
        assert uint_class(5) + uint_class(2) is uint_class(7)

    def test_a_value_past_the_table_is_allocated(self) -> None:
        """Sharing stops where the table does."""
        # 256 is one past the last shared entry.
        assert Uint64(256) is not Uint64(256)
        assert Uint64(256) == 256

    def test_arithmetic_across_the_edge_of_the_table_stays_correct(self) -> None:
        """The last shared value and the first allocated one meet without an off-by-one."""
        # 255 is the final entry, so it is shared while the 256 just past it is not.
        assert Uint64(255) is Uint64(255)
        assert Uint64(254) + Uint64(1) is Uint64(255)
        # Stepping up out of the table and back down again returns the shared instance.
        assert Uint64(255) + Uint64(1) == 256
        assert Uint64(256) - Uint64(1) is Uint64(255)

    def test_each_width_and_subtype_holds_its_own_table(self) -> None:
        """A named subtype keeps answering as itself instead of as the width it is built on."""
        assert type(Slot(7)) is Slot
        assert Slot(7) is Slot(7)
        # Two types over the same width therefore hold two different instances of one value.
        assert Slot(7) is not Uint64(7)
        assert Slot(7) is not Epoch(7)

    def test_a_narrow_width_refuses_what_its_table_would_not_reach(self) -> None:
        """The table is clamped to the width, so it cannot serve a value out of range."""
        # Two bits hold 0 through 3, and the clamp keeps the top of that range shared.
        assert NarrowerThanTheTable(3) == 3
        # An unclamped table would answer with a shared 10 here instead of refusing it.
        with pytest.raises(SSZValueError):
            NarrowerThanTheTable(10)

    def test_an_operand_that_lies_about_its_size_is_still_refused(self) -> None:
        """The bound is checked against a plain integer, never against the input's own answers."""
        # An input that answers its own ordering questions would pass on its own word.
        with pytest.raises(SSZValueError):
            Uint8(LiesInComparisons(999))


class TestAValueCarriesNoState:
    """A shared instance reaches every holder of that value, so it accepts no attributes."""

    def test_attaching_state_to_a_value_is_refused(self) -> None:
        """Setting an attribute would publish it to every other holder of the same value."""
        expected_message = "Uint64 is immutable"
        with pytest.raises(SSZTypeError) as exception_info:
            # __setattr__ never returns, which ty reads as a write that cannot stand.
            Uint64(7).note = "mine"  # ty: ignore[invalid-assignment]
        assert str(exception_info.value) == expected_message

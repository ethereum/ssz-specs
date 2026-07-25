"""Unsigned Integer Type Specification."""

from __future__ import annotations

from typing import IO, Any, ClassVar, NoReturn, Self, SupportsInt, overload, override

from pydantic.annotated_handlers import GetCoreSchemaHandler
from pydantic_core import core_schema

from ssz.exceptions import (
    SSZRangeError,
    SSZScopeError,
    SSZSerializationError,
    SSZTypeMismatch,
)
from ssz.ssz_base import SSZType


class BaseUint(int, SSZType):
    """Base class for fixed-width unsigned integer types."""

    __slots__ = ()

    BITS: ClassVar[int]
    """The number of bits in the integer (overridden by subclasses)."""

    MAX_VALUE: ClassVar[int]
    """Cached inclusive upper bound ``2**BITS - 1``, computed once per width."""

    BYTE_LENGTH: ClassVar[int]
    """Cached serialized byte width ``BITS // 8``, computed once per width."""

    def __init_subclass__(cls, **kwargs: Any) -> None:
        """
        Cache the per-width constants so hot paths never recompute them.

        ``BITS`` is fixed for each concrete width, so its derived bound and byte
        length are hoisted to class attributes here instead of being recomputed
        (an expensive ``2**BITS``) on every construction and arithmetic result.
        """
        super().__init_subclass__(**kwargs)
        cls.MAX_VALUE = 2**cls.BITS - 1
        cls.BYTE_LENGTH = cls.BITS // 8

    def __new__(cls, value: SupportsInt) -> Self:
        """
        Create and range-check a new instance.

        Raises:
            SSZTypeError: If value is not an int. Bool, string, and float are rejected.
            SSZValueError: If value is outside [0, 2**BITS - 1].
        """
        # Bool subclasses int, so reject it explicitly before the value check.
        if not isinstance(value, int) or isinstance(value, bool):
            raise SSZTypeMismatch("int", type(value))
        return cls._wrap(value)

    @classmethod
    def _wrap(cls, value: int) -> Self:
        """
        Range-check an integer and wrap it into a typed instance.

        This is the shared fast path for both construction and arithmetic
        results. It assumes ``value`` is already a non-bool integer, so it skips
        the type guards the public constructor runs, uses the cached bound, and
        constructs directly via ``int.__new__``.

        Raises:
            SSZValueError: If value is outside [0, 2**BITS - 1].
        """
        max_value = cls.MAX_VALUE
        if not (0 <= value <= max_value):
            raise SSZRangeError(cls.__name__, value, max_value)
        return int.__new__(cls, value)

    @classmethod
    def __get_pydantic_core_schema__(
        cls, source_type: Any, handler: GetCoreSchemaHandler
    ) -> core_schema.CoreSchema:
        """Hook into Pydantic's validation system."""
        # A plain validator wraps a pre-validated int into a typed instance.
        from_int_validator = core_schema.no_info_plain_validator_function(cls)
        # Strict int validation enforces the unsigned range before construction.
        #
        # The lt bound is exclusive, so a value equal to 2**BITS is rejected.
        python_schema = core_schema.chain_schema(
            [core_schema.int_schema(ge=0, lt=2**cls.BITS, strict=True), from_int_validator]
        )
        # Existing instances bypass validation.
        #
        # Raw values flow through the strict chain instead.
        return core_schema.union_schema(
            [
                # Case 1: The value is already the correct type.
                core_schema.is_instance_schema(cls),
                # Case 2: The value needs to be parsed and validated.
                python_schema,
            ],
            # Round-trip to JSON drops the subtype back to a plain int.
            serialization=core_schema.plain_serializer_function_ser_schema(int),
        )

    @classmethod
    @override
    def is_fixed_size(cls) -> bool:
        """All unsigned integer types are fixed-size."""
        return True

    @classmethod
    @override
    def get_byte_length(cls) -> int:
        """Byte length derived from the bit width."""
        return cls.BYTE_LENGTH

    @override
    def encode_bytes(self) -> bytes:
        """Serialize to little-endian bytes."""
        return self.to_bytes(length=self.get_byte_length(), byteorder="little")

    @classmethod
    @override
    def decode_bytes(cls, data: bytes) -> Self:
        """
        Deserialize from little-endian bytes.

        Raises:
            SSZSerializationError: If the byte string has the wrong length.
        """
        # Ensure the input data has the correct number of bytes.
        expected_length = cls.get_byte_length()
        if len(data) != expected_length:
            raise SSZScopeError(cls.__name__, expected_length, len(data))
        return cls(int.from_bytes(data, "little"))

    @override
    def serialize(self, stream: IO[bytes]) -> int:
        """Write little-endian bytes to a stream and return the count written."""
        encoded_data = self.encode_bytes()
        # Write the data to the stream.
        stream.write(encoded_data)
        # Return the number of bytes written.
        return len(encoded_data)

    @classmethod
    @override
    def deserialize(cls, stream: IO[bytes], scope: int) -> Self:
        """
        Read little-endian bytes from a stream within a fixed scope.

        Raises:
            SSZSerializationError: If the scope mismatches, or the stream ends early.
        """
        byte_length = cls.get_byte_length()
        if scope != byte_length:
            raise SSZSerializationError(
                f"{cls.__name__}: invalid scope, expected {byte_length} bytes, got {scope}"
            )
        # Read the required number of bytes from the stream.
        serialized_bytes = stream.read(byte_length)
        # Ensure the correct number of bytes was read.
        if len(serialized_bytes) != byte_length:
            raise SSZScopeError(cls.__name__, byte_length, len(serialized_bytes))
        # Decode the bytes into a new instance.
        return cls.decode_bytes(serialized_bytes)

    @classmethod
    def max_value(cls) -> Self:
        """The maximum value for this unsigned integer."""
        return cls(cls.MAX_VALUE)

    def _raise_type_error(self, other: Any, op_symbol: str) -> NoReturn:
        """Helper to raise a consistent TypeError."""
        raise TypeError(
            f"Unsupported operand type(s) for {op_symbol}: "
            f"'{type(self).__name__}' and '{type(other).__name__}'"
        )

    def __add__(self, other: Any) -> Self:
        """Forward addition."""
        cls = type(self)
        if type(other) is not cls:
            self._raise_type_error(other, "+")
        return cls._wrap(int.__add__(self, other))

    def __radd__(self, other: Any) -> Self:
        """Reverse addition."""
        cls = type(self)
        if type(other) is not cls:
            self._raise_type_error(other, "+")
        return cls._wrap(int.__add__(other, self))

    def __sub__(self, other: Any) -> Self:
        """Forward subtraction."""
        cls = type(self)
        if type(other) is not cls:
            self._raise_type_error(other, "-")
        return cls._wrap(int.__sub__(self, other))

    def __rsub__(self, other: Any) -> Self:
        """Reverse subtraction."""
        cls = type(self)
        if type(other) is not cls:
            self._raise_type_error(other, "-")
        return cls._wrap(int.__sub__(other, self))

    def __mul__(self, other: Any) -> Self:
        """Forward multiplication."""
        cls = type(self)
        if type(other) is not cls:
            self._raise_type_error(other, "*")
        return cls._wrap(int.__mul__(self, other))

    def __rmul__(self, other: Any) -> Self:
        """Reverse multiplication."""
        cls = type(self)
        if type(other) is not cls:
            self._raise_type_error(other, "*")
        return cls._wrap(int.__mul__(other, self))

    def __floordiv__(self, other: Any) -> Self:
        """Forward floor division."""
        cls = type(self)
        if type(other) is not cls:
            self._raise_type_error(other, "//")
        return cls._wrap(int.__floordiv__(self, other))

    def __rfloordiv__(self, other: Any) -> Self:
        """Reverse floor division."""
        cls = type(self)
        if type(other) is not cls:
            self._raise_type_error(other, "//")
        return cls._wrap(int.__floordiv__(other, self))

    def __mod__(self, other: Any) -> Self:
        """Forward modulo."""
        cls = type(self)
        if type(other) is not cls:
            self._raise_type_error(other, "%")
        return cls._wrap(int.__mod__(self, other))

    def __rmod__(self, other: Any) -> Self:
        """Reverse modulo."""
        cls = type(self)
        if type(other) is not cls:
            self._raise_type_error(other, "%")
        return cls._wrap(int.__mod__(other, self))

    @overload
    def __pow__(self, value: int, mod: None = None, /) -> Self: ...
    @overload
    def __pow__(self, value: int, mod: int, /) -> Self: ...
    # The parent declaration uses two stub overloads with different return types.
    #
    # Narrowing both to a single subtype is safe by Liskov substitution.
    # The strict overload-match check rejects it regardless.
    def __pow__(self, value: int, mod: int | None = None, /) -> Self:  # ty: ignore[invalid-method-override]
        """Forward exponentiation and three-argument pow."""
        if type(value) is not type(self):
            self._raise_type_error(value, "**")
        if mod is not None and type(mod) is not type(self):
            self._raise_type_error(mod, "**")
        power = pow(int(self), int(value), int(mod) if mod is not None else None)
        return type(self)._wrap(power)

    def __rpow__(self, base: int, modulo: int | None = None, /) -> Self:
        """Reverse exponentiation and three-argument pow."""
        if type(base) is not type(self):
            self._raise_type_error(base, "**")
        if modulo is not None and type(modulo) is not type(self):
            self._raise_type_error(modulo, "**")
        power = pow(int(base), int(self), int(modulo) if modulo is not None else None)
        return type(self)._wrap(power)

    def __divmod__(self, other: Any) -> tuple[Self, Self]:
        """Forward divmod."""
        cls = type(self)
        if type(other) is not cls:
            self._raise_type_error(other, "divmod")
        quotient, remainder = int.__divmod__(self, other)
        return cls._wrap(quotient), cls._wrap(remainder)

    def __rdivmod__(self, other: Any) -> tuple[Self, Self]:
        """Reverse divmod."""
        cls = type(self)
        if type(other) is not cls:
            self._raise_type_error(other, "divmod")
        quotient, remainder = int.__rdivmod__(self, other)
        return cls._wrap(quotient), cls._wrap(remainder)

    def __and__(self, other: Any) -> Self:
        """Forward bitwise AND."""
        cls = type(self)
        if type(other) is not cls:
            self._raise_type_error(other, "&")
        return cls._wrap(int.__and__(self, other))

    def __rand__(self, other: Any) -> Self:
        """Reverse bitwise AND."""
        return self.__and__(other)

    def __or__(self, other: Any) -> Self:
        """Forward bitwise OR."""
        cls = type(self)
        if type(other) is not cls:
            self._raise_type_error(other, "|")
        return cls._wrap(int.__or__(self, other))

    def __ror__(self, other: Any) -> Self:
        """Reverse bitwise OR."""
        return self.__or__(other)

    def __xor__(self, other: Any) -> Self:
        """Forward bitwise XOR."""
        cls = type(self)
        if type(other) is not cls:
            self._raise_type_error(other, "^")
        return cls._wrap(int.__xor__(self, other))

    def __rxor__(self, other: Any) -> Self:
        """Reverse bitwise XOR."""
        return self.__xor__(other)

    def __lshift__(self, other: Any) -> Self:
        """Forward left bit-shift."""
        cls = type(self)
        if type(other) is not cls:
            self._raise_type_error(other, "<<")
        return cls._wrap(int.__lshift__(self, other))

    def __rlshift__(self, other: Any) -> Self:
        """Reverse left bit-shift."""
        cls = type(self)
        if type(other) is not cls:
            self._raise_type_error(other, "<<")
        return cls._wrap(int.__lshift__(other, self))

    def __rshift__(self, other: Any) -> Self:
        """Forward right bit-shift."""
        cls = type(self)
        if type(other) is not cls:
            self._raise_type_error(other, ">>")
        return cls._wrap(int.__rshift__(self, other))

    def __rrshift__(self, other: Any) -> Self:
        """Reverse right bit-shift."""
        cls = type(self)
        if type(other) is not cls:
            self._raise_type_error(other, ">>")
        return cls._wrap(int.__rshift__(other, self))

    def __eq__(self, other: object) -> bool:
        """Equality."""
        if type(other) is not type(self):
            self._raise_type_error(other, "==")
        return super().__eq__(other)

    def __ne__(self, other: object) -> bool:
        """Inequality."""
        if type(other) is not type(self):
            self._raise_type_error(other, "!=")
        return super().__ne__(other)

    def __lt__(self, other: Any) -> bool:
        """Less-than."""
        if type(other) is not type(self):
            self._raise_type_error(other, "<")
        return super().__lt__(other)

    def __le__(self, other: Any) -> bool:
        """Less-than-or-equal."""
        if type(other) is not type(self):
            self._raise_type_error(other, "<=")
        return super().__le__(other)

    def __gt__(self, other: Any) -> bool:
        """Greater-than."""
        if type(other) is not type(self):
            self._raise_type_error(other, ">")
        return super().__gt__(other)

    def __ge__(self, other: Any) -> bool:
        """Greater-than-or-equal."""
        if type(other) is not type(self):
            self._raise_type_error(other, ">=")
        return super().__ge__(other)

    def __repr__(self) -> str:
        """Official representation includes the subtype name."""
        return f"{type(self).__name__}({int(self)})"

    def __str__(self) -> str:
        """Informal representation matches the underlying value."""
        return str(int(self))

    def __hash__(self) -> int:
        """Hash mixes in the concrete subtype so distinct widths never collide."""
        return hash((type(self), int(self)))

    def __index__(self) -> int:
        """Return a plain integer for slicing and indexing."""
        return int(self)


class Uint8(BaseUint):
    """A type representing an 8-bit unsigned integer (uint8)."""

    BITS = 8


class Uint16(BaseUint):
    """A type representing a 16-bit unsigned integer (uint16)."""

    BITS = 16


class Uint32(BaseUint):
    """A type representing a 32-bit unsigned integer (uint32)."""

    BITS = 32


class Uint64(BaseUint):
    """A type representing a 64-bit unsigned integer (uint64)."""

    BITS = 64


class Uint128(BaseUint):
    """A type representing a 128-bit unsigned integer (uint128)."""

    BITS = 128


class Uint256(BaseUint):
    """A type representing a 256-bit unsigned integer (uint256)."""

    BITS = 256
